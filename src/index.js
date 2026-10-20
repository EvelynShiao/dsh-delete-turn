// dsh-delete-turn - host half.
//
// Two loopback-only JSON routes:
//
//   GET  /dsh-delete-turn/state?sessionId=<id>
//   POST /dsh-delete-turn/delete   { sessionId, mode, seq?, messageId?, turn? }
//
// A deletion appends ONE empty `system/message` event carrying the official
// surface intent `{ surfaceOp: { op: 'replace', startSeq, endSeq } }` and the
// complete shadowed-node list in `sourceEventSeqs`. Empty system messages
// project to no model message, so the addressed content leaves the derived
// context while the append-only log keeps every original byte. The replacement
// message source records the deletion mode, which is how the browser half
// rebuilds its hidden-row ledger after a reload without any private sidecar.
//
// The module imports nothing from the DSH SDK: `sessions`, `sessionQuery` and
// `sessionController` are resolved through the cordis context at call time, so
// the plugin loads on any profile and degrades to a clear HTTP failure when a
// service is absent.
import { randomUUID } from 'node:crypto'
import { readFile, writeFile, rm, rename } from 'node:fs/promises'
import { readdirSync, existsSync } from 'node:fs'
import { zstdCompressSync, zstdDecompressSync } from 'node:zlib'
import { join } from 'node:path'
import { homedir } from 'node:os'
import { PLUGIN_ID, PlanError, deletableReplyTurns, foldSurface, hiddenEntriesOfFold, isBusy, isSurfaceEvent, planRange } from './logic.js'

export const name = PLUGIN_ID

const ROUTE_PREFIX = '/dsh-delete-turn'
const SESSION_ID_RE = /^(session-)?[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i
const MODES = new Set(['message', 'step', 'reply'])
// 非 surface 但会在 UI 上渲染成可见残余行的事件类型：物理擦除其内容
const RESIDUE_TYPES = new Set(['assistant/attempt', 'llm/retry', 'llm/retry-started'])

class HttpError extends Error {
  constructor(status, code, message) {
    super(message)
    this.name = 'HttpError'
    this.status = status
    this.code = code
  }
}

// A session id travels in two spellings: the raw uuid and `session-<uuid>`.
// The store, the persistence directories and the workspace rows disagree about
// which one they hold, so every lookup tries both.
function idVariants(sessionId) {
  const out = new Set([sessionId])
  if (sessionId.startsWith('session-')) out.add(sessionId.slice('session-'.length))
  else out.add(`session-${sessionId}`)
  return [...out]
}

function findLiveSession(ctx, sessionId) {
  const sessions = ctx.get('sessions')
  if (!sessions || typeof sessions.get !== 'function') return undefined
  for (const variant of idVariants(sessionId)) {
    const found = sessions.get(variant)
    if (found) return found
  }
  return undefined
}

// Resolve the live Session that owns the append. An already-open session is
// used directly; a cold one is resumed through the official controller, which
// is exactly what the web UI does when the user opens it.
async function resolveSession(ctx, sessionId) {
  const live = findLiveSession(ctx, sessionId)
  if (live) return live
  const controller = ctx.get('sessionController')
  if (controller && typeof controller.resolveAgent === 'function') {
    try {
      const result = await controller.resolveAgent(sessionId)
      if (result && result.agent && result.agent.session) return result.agent.session
    } catch {
      // fall through to the explicit failure below
    }
  }
  return undefined
}

function eventsFromLive(session) {
  if (session && typeof session.snapshotEvents === 'function') {
    try {
      const events = session.snapshotEvents()
      if (Array.isArray(events)) return events
    } catch {
      // fall through to the query service
    }
  }
  return undefined
}

// Live-preferred read through the public query service; the live session's own
// snapshot is the fallback when the service is absent.
async function readEvents(ctx, sessionId) {
  const query = ctx.get('sessionQuery')
  if (query && typeof query.readSession === 'function') {
    try {
      const snapshot = await query.readSession(sessionId)
      if (snapshot && Array.isArray(snapshot.events)) return snapshot.events
    } catch {
      // fall through to the live snapshot
    }
  }
  const events = eventsFromLive(findLiveSession(ctx, sessionId))
  return events ?? null
}

function surfaceOf(ctx, sessionId, events) {
  const live = findLiveSession(ctx, sessionId)
  const nodes = live && live.surface && Array.isArray(live.surface.nodes) ? live.surface.nodes : undefined
  return nodes ?? foldSurface(events).nodes
}

// The append is committed in memory the moment `session.append` returns; the
// persistence writer buffers asynchronously. Await the official durability
// checkpoint so a reload or a DSH restart still sees the deletion. A failed
// flush is not fatal — the event is already committed — but the request waits
// for the checkpoint when one exists.
async function flushSession(ctx, session) {
  const errors = []
  const sessions = ctx.get('sessions')
  if (sessions && typeof sessions.flush === 'function') {
    try {
      await Promise.race([sessions.flush(session), new Promise((resolve) => setTimeout(resolve, 5000))])
      return { flushed: true }
    } catch (error) {
      errors.push(String((error && error.message) || error))
    }
  } else {
    errors.push('sessions.flush unavailable')
  }
  const persistence = ctx.get('sessionPersistence')
  if (persistence && typeof persistence.flush === 'function') {
    try {
      await Promise.race([persistence.flush(), new Promise((resolve) => setTimeout(resolve, 5000))])
      return { flushed: true }
    } catch (error) {
      errors.push(String((error && error.message) || error))
    }
  } else {
    errors.push('sessionPersistence.flush unavailable')
  }
  return { flushed: false, flushError: errors.join(' | ') }
}

// --- 真删除：物理擦除会话日志中被删事件的内容 ---
/* 要擦的文本键 —— 与 dsh-adapter-compat/purge.js 的 TEXT_KEYS 同一份清单（三插件同步规矩）。 */
const TEXT_KEYS = new Set(['text', 'texts', 'delta', 'deltas', 'reasoning', 'reasoning_content', 'reasoningContent', 'thinking'])
/* 占位正文：与 adapter-compat/purge.js、slim.js 的 [内容已清除] 统一（三插件同步规矩）。 */
const TEXT_PLACEHOLDER = '[内容已清除]'
/* 按 key 名深度擦文本：只清字符串，键/数组长度/chunk 结构原样保留。
   插件之间不互相 import，这里内联一份同语义实现。 */
function scrubDeep(node, depth = 0) {
  if (depth > 14 || node === null || typeof node !== 'object') return node
  for (const key of Object.keys(node)) {
    const value = node[key]
    if (TEXT_KEYS.has(key)) {
      if (typeof value === 'string') node[key] = ''
      else if (Array.isArray(value)) node[key] = value.map((x) => (typeof x === 'string' ? '' : x))
      else if (value && typeof value === 'object') {
        for (const inner of Object.keys(value)) if (typeof value[inner] === 'string') value[inner] = ''
      }
      continue
    }
    if (value && typeof value === 'object') scrubDeep(value, depth + 1)
  }
  return node
}

export function redactEventPayload(event) {
  if (!event || typeof event !== 'object' || !event.data || typeof event.data !== 'object') return event
  /* 残余事件（assistant/attempt、llm/retry*）：**只擦文本载体，结构标量一个都不动**。
     2026-10-20 实锤（session-beae66b3）：旧实现用白名单只留 turn/step/retryId/attemptId/reason，
     把宿主校验必需的 llm/retry.provider / mode / policyKey / retry / delayMs / failure
     和 llm/retry-started.retry 一起吃掉 → 加载直接抛
       "retry must be a non-negative safe integer"，整个会话打不开。
     跟 2026-10-12 那次 stream 被吃掉是**同一个 bug 换了个字段**：白名单永远会漏。
     正确手法（与 adapter-compat/purge.js 的 RESIDUE 分支一致）：**黑名单** —— 只删文本键，
     其余原样保留。真删除语义不变（正文照样一个字节读不到）。 */
  if (RESIDUE_TYPES.has(event.type)) {
    const data = structuredClone(event.data)
    for (const k of ['content', 'text', 'messages', 'prompt', 'reasoning', 'reasoning_content', 'reasoningContent', 'thinking']) {
      if (data[k] !== undefined) delete data[k]
    }
    /* stream 必须留住且结构不动（宿主种子校验要求 attempt 的 stream 是数组）：
       只把里面的文本擦空。必须 structuredClone 后再擦，绝不改宿主内存里的同一批对象。 */
    if (data.stream !== undefined) {
      try { scrubDeep({ stream: data.stream }) } catch { /* 保结构优先，擦失败不阻断 */ }
    } else if (event.type === 'assistant/attempt') {
      data.stream = [] // 本就没有 stream 的 attempt：补空数组以满足 settlement 校验
    }
    return { ...event, data }
  }
  /* developer/message 的 content 装的是 tool-addition/tool-removal 结构块，不是对话正文：
     整块清空会让 headerSeq 失去依据，宿主抛
       "format v4 developer/message must omit headerSeq without tool additions"
     （2026-10-20 实证 session-4ce9464e）。这里只擦块里的文本，块本身保留。 */
  if (event.type === 'developer/message') {
    const data = structuredClone(event.data)
    if (data.message && typeof data.message === 'object') {
      const msg = { ...data.message }
      if (Array.isArray(msg.content)) {
        msg.content = msg.content.map((b) => (b && typeof b === 'object' && typeof b.text === 'string' ? { ...b, text: '' } : b))
      }
      data.message = msg
    }
    const blocks = data.message?.content
    const hasAdd = Array.isArray(blocks) && blocks.some((b) => b && b.type === 'tool-addition')
    if (!hasAdd && Object.hasOwn(data, 'headerSeq')) delete data.headerSeq
    return { ...event, data }
  }
  const data = { ...event.data }
  if (Array.isArray(data.content)) data.content = []
  if (data.message && typeof data.message === 'object') {
    const msg = { ...data.message }
    if (Array.isArray(msg.content)) msg.content = []
    if (typeof msg.text === 'string') msg.text = ''
    if (typeof msg.reasoning_content === 'string') msg.reasoning_content = ''
    if (typeof msg.reasoning === 'string') msg.reasoning = ''
    data.message = msg
  }
  if (typeof data.text === 'string') data.text = ''
  if (typeof data.result === 'string') data.result = ''
  if (data.output && typeof data.output === 'object') data.output = {}
  if (typeof data.output === 'string') data.output = ''
  /* assistant/message 的推理与正文**也**存放在 data.stream 的 chunk 文本里，
     只清 message.content 会留残留（2026-10-11 实锤，adapter purge.js 同款教训）。
     只擦文本、结构不动；先 structuredClone 再擦，绝不动入参里的同一批对象。 */
  if (Array.isArray(data.stream)) {
    try { data.stream = scrubDeep({ stream: structuredClone(data.stream) }).stream } catch { /* 保结构优先，擦失败不阻断 */ }
  }
  /* 出口修（与 adapter-compat/purge.js 同款占位符）：擦完不能留「正文全空的 tool 结果」——
     provider（Anthropic 风格）把 tool_result.content=[] 当成没有结果，整轮拒收：
       `tool_use` ids were found without `tool_result` blocks immediately after
     清空语义不变（正文确实没了），但结构合法。 */
  if (event.type === 'tool/result' && data.message && typeof data.message === 'object') {
    const blocks = Array.isArray(data.message.content) ? data.message.content : []
    const hasText = blocks.some((b) => b && b.type === 'text' && typeof b.text === 'string' && b.text.length > 0)
    if (!hasText) data.message = { ...data.message, content: [{ type: 'text', text: TEXT_PLACEHOLDER }] }
  }
  return { ...event, data }
}

const ZSTD_MAGIC = Buffer.from([0x28, 0xb5, 0x2f, 0xfd])

/* 按**帧边界**切分 zstd 文件。
   原实现用 `zstdDecompressSync(raw.subarray(i))`（从 magic 解到文件末尾）——
   实测在 68 帧的会话上只读到 850/1310 行，少 460 行。它从没成功纯属侥幸：
   一旦真跑通，会把少读的那 460 行事件直接从文件里抹掉。 */
function splitFrames(buf) {
  const idx = []
  let i = -1
  while ((i = buf.indexOf(ZSTD_MAGIC, i + 1)) !== -1) idx.push(i)
  idx.push(buf.length)
  const frames = []
  for (let k = 0; k < idx.length - 1; k++) {
    const raw = buf.subarray(idx[k], idx[k + 1])
    frames.push({ raw, text: k === 0 ? null : zstdDecompressSync(raw).toString('utf8') })
  }
  return frames
}

/* 定位会话文件：persistence 优先；拿不到就自己扫 sessions 目录。
   原实现只依赖 sessionPersistence.list/locate，服务缺席即静默返回
   diskRewritten:false —— 这就是「purge 从没真正执行过」的原因。 */
async function locateSessionFile(persistence, sessionId) {
  try {
    if (persistence && typeof persistence.list === 'function' && typeof persistence.locate === 'function') {
      const entries = await persistence.list()
      const wanted = idVariants(sessionId)
      const meta = (entries || []).find((e) => wanted.has(e?.id) || wanted.has(e?.header?.id))
      const loc = meta && persistence.locate(meta)
      if (loc && loc.path && existsSync(loc.path)) return loc.path
    }
  } catch { /* 落到目录扫描 */ }
  const home = process.env.DSH_HOME || join(homedir(), '.dsh')
  const root = join(home, 'sessions')
  let workspaces = []
  try { workspaces = readdirSync(root) } catch { return undefined }
  const wanted = idVariants(sessionId)
  for (const ws of workspaces) {
    let ids = []
    try { ids = readdirSync(join(root, ws)) } catch { continue }
    for (const id of ids) {
      if (!wanted.has(id)) continue
      const p = join(root, ws, id, 'session.v4.jsonl.zstd')
      if (existsSync(p)) return p
    }
  }
  return undefined
}

async function purgeDeletedEvents(ctx, sessionId, shadowedSeqs, replacementSeq) {
  const removeSet = new Set([...shadowedSeqs, replacementSeq])
  const redacted = []
  try {
    const live = findLiveSession(ctx, sessionId)
    if (live && Array.isArray(live.log)) {
      for (const seq of removeSet) {
        if (seq >= 0 && seq < live.log.length && live.log[seq]) {
          live.log[seq] = redactEventPayload(live.log[seq])
          redacted.push(seq)
        }
      }
      live.eventsSnapshot = undefined
    }
  } catch {}
  /* 磁盘段：失败必须抛出。
     原实现把失败吞成 diskRewritten:false、调用方再 catch 一次 ——
     于是「真删除」悄悄退化成「只留墓碑」，正文原样留在文件里（2026-10-11 事故）。 */
  const persistence = ctx.get('sessionPersistence')
  const filePath = await locateSessionFile(persistence, sessionId)
  if (!filePath) throw new Error(`purge: cannot locate session file for ${sessionId}`)
  const raw = await readFile(filePath)
  const frames = splitFrames(raw)
  if (frames.length < 1) throw new Error('purge: session file has no zstd frame')

  const parts = []
  let before = 0
  let changed = 0
  for (let k = 0; k < frames.length; k++) {
    const f = frames[k]
    if (k === 0) { parts.push(f.raw); continue }   // header 帧原字节保留，勿重压
    const lines = f.text.split('\n').filter((l) => l.trim())
    before += lines.length
    const out = []
    for (const line of lines) {
      let event
      try { event = JSON.parse(line) } catch { out.push(line); continue }
      if (typeof event.seq === 'number' && removeSet.has(event.seq)) {
        out.push(JSON.stringify(redactEventPayload(event)))
        changed++
      } else out.push(line)
    }
    parts.push(zstdCompressSync(Buffer.from(out.join('\n') + '\n', 'utf8')))
  }
  if (changed === 0) return { redacted, diskRewritten: false, why: 'no matching rows' }

  // 临时文件 + rename：绝不让半截写入损坏会话
  const tmp = `${filePath}.purge-${Date.now()}`
  await writeFile(tmp, Buffer.concat(parts))
  // 安全阀：复读校验事件行数，任何丢行都拒绝提交（原实现会丢 460 行）
  const vFrames = splitFrames(await readFile(tmp))
  let vLines = 0
  for (let k = 1; k < vFrames.length; k++) for (const l of vFrames[k].text.split('\n')) if (l.trim()) vLines++
  if (vLines !== before) { await rm(tmp, { force: true }); throw new Error(`purge: 行数不一致 ${before}→${vLines}，拒绝写盘`) }
  await rename(tmp, filePath)
  try {
    const home = process.env.DSH_HOME || join(homedir(), '.dsh')
    await rm(join(home, 'storages', 'session_projcache', 'sessions', sessionId + '.json'), { force: true })
  } catch {}
  return { redacted, diskRewritten: true, erased: changed, eventsVerified: vLines }
}

// --- operations --------------------------------------------------------------

async function stateOf(ctx, sessionId) {
  const events = await readEvents(ctx, sessionId)
  if (!events) throw new HttpError(404, 'session-not-found', 'no session log for this id')
  const folded = foldSurface(events)
  return {
    hidden: hiddenEntriesOfFold(folded, events),
    // The current surface lets the browser half tell a row that still has
    // context content from one whose content a compaction already removed;
    // `replyTurns` narrows that to turns with an actually deletable reply.
    surface: folded.nodes,
    replyTurns: deletableReplyTurns(events, folded.nodes),
    live: Boolean(findLiveSession(ctx, sessionId)),
    busy: isBusy(events),
    lastSeq: events.length > 0 ? events[events.length - 1].seq : -1,
  }
}

async function deleteTarget(ctx, sessionId, body) {
  const mode = typeof body.mode === 'string' ? body.mode : ''
  if (!MODES.has(mode)) throw new HttpError(400, 'invalid', 'mode must be message, step or reply')
  const session = await resolveSession(ctx, sessionId)
  if (!session || typeof session.append !== 'function') {
    throw new HttpError(409, 'session-not-active', 'the session is not open in DSH')
  }
  const events = await readEvents(ctx, sessionId)
  if (!events) throw new HttpError(404, 'session-not-found', 'no session log for this id')
  // Busy check removed: allow deletion even when turn is open (truncated replies)

  const surfaceNodes = surfaceOf(ctx, sessionId, events)
  let plan
  try {
    plan = planRange(events, surfaceNodes, {
      mode,
      seq: typeof body.seq === 'number' ? body.seq : undefined,
      messageId: typeof body.messageId === 'string' ? body.messageId : undefined,
      turn: typeof body.turn === 'number' ? body.turn : undefined,
    })
  } catch (error) {
    if (error instanceof PlanError) {
      const status = error.code === 'not-deletable' ? 400 : 409
      throw new HttpError(status, error.code, error.message)
    }
    throw error
  }

  // The live surface is the append authority; a node that vanished between the
  // read and this check means another writer landed first.
  for (const seq of plan.shadowed) {
    if (!surfaceNodes.includes(seq)) throw new HttpError(409, 'stale', 'the session changed, retry')
  }

  // 残余行：replace 只遮蔽 surface 节点，窗口内的非 surface 事件
  // （assistant/attempt、llm/retry*、tool/call、turn/end 等）不会被遮蔽，
  // UI 会把它们渲染成残余行（红字错误、重试提示、思考尝试）。
  // 这里把它们计入隐藏台账（立即隐藏 + 重载后由 hiddenEntriesOfFold 重建），
  // 其中 RESIDUE_TYPES 还会在 purge 阶段被物理擦除。
  const windowLo = Math.min(...plan.shadowed)
  const windowHi = Math.max(...plan.shadowed)
  const shadowedSet = new Set(plan.shadowed)
  const windowExtras = new Set()
  const residueSeqs = new Set()
  const planTurn = (() => {
    const first = events.find((e) => e.seq === plan.shadowed[0])
    const t = first?.data?.turn
    return typeof t === 'number' ? t : undefined
  })()
  for (const ev of events) {
    if (ev.seq < windowLo) continue
    if (shadowedSet.has(ev.seq) || isSurfaceEvent(ev)) continue
    const inWindow = ev.seq <= windowHi
    const inTurn = (plan.mode === 'reply' || plan.mode === 'step') &&
      planTurn !== undefined && ev.data && ev.data.turn === planTurn
    if (!inWindow && !inTurn) continue
    windowExtras.add(ev.seq)
    if (RESIDUE_TYPES.has(ev.type)) residueSeqs.add(ev.seq)
  }

  let replacement
  try {
    // A replacement carrier must be a user/message: the official format
    // validation pins system/message to an open step (so it cannot carry an
    // out-of-band deletion) and forbids sourceEventSeqs on assistant/message
    // (so it cannot cite the shadowed nodes). A compaction checkpoint is the
    // same shape. The carrier text is a short marker rather than an empty
    // array: strict gateways reject a user message with no content
    // ("user message must have content"), while a marker keeps the deleted
    // span's position legible without replaying what was removed.
    replacement = session.append(
      'user/message',
      {
        id: randomUUID(),
        role: 'user',
        content: [{ type: 'text', text: '[deleted]' }],
        // v4 format: plugin wrappers are retired; the producer kind carries the id.
        source: { kind: `plugin:${PLUGIN_ID}` },
      },
      {
        surfaceOp: { op: 'replace', startSeq: plan.startSeq, endSeq: plan.endSeq },
        sourceEventSeqs: plan.shadowed,
      },
    )
  } catch (error) {
    throw new HttpError(409, 'stale', `the surface refused the replacement: ${String((error && error.message) || error)}`)
  }
  const flush = await flushSession(ctx, session)
  let purged
  try {
    purged = await purgeDeletedEvents(ctx, sessionId, [...plan.shadowed, ...residueSeqs], replacement.seq)
  } catch (error) {
    // 绝不静默：purge 失败 = 正文仍留在文件里，「真删除」退化成「只留墓碑」。
    // 必须同时进响应体和控制台（原实现 `catch { purged = {...} }` 把事故吞掉了）。
    const msg = String((error && error.message) || error)
    purged = { redacted: [], diskRewritten: false, error: msg }
    console.error(`[dsh-delete-turn] purge FAILED (sessionId=${sessionId}, shadowed=${JSON.stringify([...plan.shadowed])}): ${msg}`)
  }

  return {
    replacementSeq: replacement.seq,
    ...flush,
    purged,
    hidden: [
      ...plan.shadowed.map((seq) => ({ seq, mode: plan.mode })),
      ...[...windowExtras].map((seq) => ({ seq, mode: plan.mode })),
    ],
  }
}

// --- http --------------------------------------------------------------------

function isLoopbackAddress(address) {
  if (typeof address !== 'string' || address.length === 0) return false
  return address === '127.0.0.1' || address === '::1' || address === '::ffff:127.0.0.1' || address.startsWith('127.')
}

function isLocalHostHeader(host) {
  if (typeof host !== 'string' || host.length === 0) return false
  const name = host.split(':')[0].replace(/^\[|\]$/g, '').toLowerCase()
  return name === 'localhost' || name === '127.0.0.1' || name === '::1'
}

function sendJson(res, status, body) {
  const payload = JSON.stringify(body)
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(payload),
  })
  res.end(payload)
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let data = ''
    req.on('data', (chunk) => {
      data += chunk
      if (data.length > 1e6) req.destroy()
    })
    req.on('end', () => resolve(data))
    req.on('error', reject)
    req.on('aborted', () => reject(new Error('aborted')))
  })
}

// Context rewriting is destructive for the model: loopback socket, loopback
// Host header, and a same-origin check when the browser sends Origin.
function guard(req, res) {
  if (!isLoopbackAddress(req.socket && req.socket.remoteAddress)) {
    sendJson(res, 403, { ok: false, code: 'forbidden', error: 'loopback only' })
    return false
  }
  const host = req.headers.host
  if (!isLocalHostHeader(host)) {
    sendJson(res, 403, { ok: false, code: 'forbidden', error: 'unexpected host' })
    return false
  }
  const origin = req.headers.origin
  if (typeof origin === 'string' && origin.length > 0) {
    let originHost = null
    try {
      originHost = new URL(origin).host
    } catch {
      originHost = null
    }
    if (originHost !== host) {
      sendJson(res, 403, { ok: false, code: 'forbidden', error: 'cross-origin request' })
      return false
    }
  }
  return true
}

function sessionIdFromQuery(url) {
  try {
    const value = new URL(url, 'http://localhost').searchParams.get('sessionId') || ''
    return value.trim()
  } catch {
    return ''
  }
}

function requireSessionId(value) {
  if (!value) throw new HttpError(400, 'invalid', 'sessionId required')
  if (!SESSION_ID_RE.test(value)) throw new HttpError(400, 'invalid', 'invalid session id')
  return value
}

// --- plugin ------------------------------------------------------------------

export function apply(ctx) {
  const registerRoutes = (webServer, fiber) => {
    fiber.effect(() =>
      webServer.register({
        kind: 'exact',
        path: `${ROUTE_PREFIX}/state`,
        handler: async (req, res) => {
          if (!guard(req, res)) return
          if (req.method !== 'GET') {
            sendJson(res, 405, { ok: false, code: 'method', error: 'GET only' })
            return
          }
          try {
            const sessionId = requireSessionId(sessionIdFromQuery(req.url))
            sendJson(res, 200, { ok: true, ...(await stateOf(ctx, sessionId)) })
          } catch (error) {
            const status = error instanceof HttpError ? error.status : 500
            const code = error instanceof HttpError ? error.code : 'internal'
            sendJson(res, status, { ok: false, code, error: String((error && error.message) || error) })
          }
        },
      }),
    )

    fiber.effect(() =>
      webServer.register({
        kind: 'exact',
        path: `${ROUTE_PREFIX}/delete`,
        handler: async (req, res) => {
          if (!guard(req, res)) return
          if (req.method !== 'POST') {
            sendJson(res, 405, { ok: false, code: 'method', error: 'POST only' })
            return
          }
          let body = {}
          try {
            const raw = await readBody(req)
            if (raw) body = JSON.parse(raw)
          } catch {
            sendJson(res, 400, { ok: false, code: 'invalid', error: 'malformed JSON body' })
            return
          }
          try {
            const sessionId = requireSessionId(typeof body.sessionId === 'string' ? body.sessionId.trim() : '')
            const result = await deleteTarget(ctx, sessionId, body)
            sendJson(res, 200, { ok: true, ...result })
          } catch (error) {
            const status = error instanceof HttpError ? error.status : 500
            const code = error instanceof HttpError ? error.code : 'internal'
            sendJson(res, status, { ok: false, code, error: String((error && error.message) || error) })
          }
        },
      }),
    )
  }

  const webServer = ctx.get('webServer')
  if (webServer) {
    registerRoutes(webServer, ctx)
  } else {
    ctx.inject(['webServer'], (sub) => registerRoutes(sub.webServer, sub))
  }
}