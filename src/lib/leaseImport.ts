// 静态租约批量导入：粘贴含表头的 CSV（网段 CIDR、设备名、IPv4、MAC），
// 与现有 hostAssignments 合并出「应用后的完整登记快照」做统一校验并生成逐行预览。
//
// 关键不变量：
//   1. 网段 CIDR 必须在当前成功分配的固定 / 自动网段中唯一匹配（保留区 / 空闲区不行）；
//   2. MAC 规范化（复用 mac.ts）后作为设备身份：已有 MAC 更新名称、网段与地址，新 MAC 新增；
//   3. 应用前先构造「未更新登记 + 全部导入行」的合并快照一次性校验，
//      故两台已有设备在 CSV 中互换地址不会因处理顺序被误报为冲突；
//   4. 冲突类型：缺失/非法字段、输入内重复 MAC、网段内重复 IP、
//      网络地址 / 广播地址 / 越界地址、与未更新登记的地址或 MAC 冲突；
//   5. CSV 语法严格校验：引号只允许出现在字段首位，闭引号后只允许逗号、换行或文件结束；
//      未闭合引号、未加引号字段内的引号、闭引号后杂字符均为语法错误，
//      任一语法错误即禁用整批应用、保持既有登记不变（迁移编排随之停止生成）；
//   6. 任一冲突禁止应用；全部通过后由调用方一次性替换状态（原子应用）。
//
// 本模块与其他生成模块一样只读规划与既有登记，绝不修改规划、基线、路由汇总与导出。

import { intToIp, ipToInt, parseCidr } from './ip'
import { allocatableSegments, type AllocSegment } from './hosts'
import { normalizeMacInput } from './mac'
import type { HostAssignment, PlanResult } from './types'

/* ---------- CSV 解析 ---------- */

export interface CsvRecord {
  /** 记录起始物理行号（从 1 开始，含表头），便于错误定位 */
  line: number
  cells: string[]
}

/** CSV 语法错误类别 */
export type CsvSyntaxErrorKind =
  | 'unclosed-quote' // 字段首位的开引号直到文件结束都没有对应闭引号
  | 'stray-quote' // 未加引号的字段内出现引号
  | 'junk-after-quote' // 闭引号后紧跟逗号 / 换行 / 文件结束以外的字符

export interface CsvSyntaxError {
  kind: CsvSyntaxErrorKind
  /** 物理行号（从 1 开始） */
  line: number
  /** 列号（从 1 开始）；未闭合引号定位为开引号所在位置 */
  column: number
  /** 含行列定位的中文说明 */
  message: string
}

export interface CsvParseResult {
  /** 完整结束且语法合法的记录（语法错误点所在的半截记录不纳入） */
  records: CsvRecord[]
  /** 首个语法错误（无错误为 null） */
  error: CsvSyntaxError | null
}

/**
 * 解析 CSV 文本为记录列表（不做表头映射），字段状态机严格校验引号用法。
 * 支持：引号包裹的字段、字段内逗号/换行、双引号转义（""）；
 * 跳过完全空白的物理行；BOM 自动去除；CRLF 算一次换行，单独 CR / LF 各算一次，
 * 引号内一律保留原始换行字符。
 * 语法规则：引号只允许出现在字段首位；闭引号后只允许逗号、换行或文件结束。
 * 首个语法错误即停止解析并返回错误（含物理行、列定位）。
 */
export function parseCsv(input: string): CsvParseResult {
  const text = input.replace(/^﻿/, '')
  const records: CsvRecord[] = []
  let cells: string[] = []
  let field = ''
  // 字段状态机：
  //   start    —— 字段尚未开始：引号只允许出现在这个位置
  //   unquoted —— 未加引号字段进行中：其中出现引号即语法错误
  //   quoted   —— 引号字段进行中："" 转义为一个引号，逗号 / 换行都是字段内容
  //   closed   —— 闭引号之后：只允许逗号、换行或文件结束
  let state: 'start' | 'unquoted' | 'quoted' | 'closed' = 'start'
  let recordStart = 1
  let line = 1
  let column = 1
  let hasContent = false // 当前记录是否出现过任何非空白内容（引号字段本身也算内容）
  // 当前引号字段的开引号位置（未闭合引号错误定位用）
  let quoteLine = 1
  let quoteColumn = 1
  let error: CsvSyntaxError | null = null

  function pushField() {
    cells.push(field)
    field = ''
    state = 'start'
  }
  function endRecord() {
    pushField()
    if (hasContent) records.push({ line: recordStart, cells })
    cells = []
    hasContent = false
    recordStart = line + 1
  }

  for (let i = 0; i < text.length; i++) {
    const ch = text[i]
    // 换行：CRLF 算一次；单独 CR / LF 各算一次，引号内保留原始换行字符
    if (ch === '\n' || ch === '\r') {
      let newline = ch
      if (ch === '\r' && text[i + 1] === '\n') {
        newline = '\r\n'
        i++
      }
      if (state === 'quoted') {
        field += newline
      } else {
        endRecord()
      }
      line++
      column = 1
      continue
    }
    if (state === 'quoted') {
      if (ch === '"') {
        if (text[i + 1] === '"') {
          field += '"'
          i++
          column += 2
        } else {
          state = 'closed'
          column++
        }
      } else {
        field += ch
        column++
      }
      continue
    }
    if (state === 'closed') {
      if (ch === ',') {
        pushField()
        column++
        continue
      }
      error = {
        kind: 'junk-after-quote',
        line,
        column,
        message: `第 ${line} 行第 ${column} 列：闭引号后只允许逗号、换行或文件结束，不允许出现其他字符（“${ch}”）`,
      }
      break
    }
    if (ch === '"') {
      if (state === 'start') {
        state = 'quoted'
        quoteLine = line
        quoteColumn = column
        hasContent = true
        column++
        continue
      }
      error = {
        kind: 'stray-quote',
        line,
        column,
        message: `第 ${line} 行第 ${column} 列：未加引号的字段内不允许出现引号（"）；引号只允许出现在字段首位`,
      }
      break
    }
    if (ch === ',') {
      pushField()
      column++
      continue
    }
    field += ch
    state = 'unquoted'
    if (!/\s/.test(ch)) hasContent = true
    column++
  }

  // 文件结束仍在引号内：未闭合引号，定位到开引号
  if (!error && state === 'quoted') {
    error = {
      kind: 'unclosed-quote',
      line: quoteLine,
      column: quoteColumn,
      message: `第 ${quoteLine} 行第 ${quoteColumn} 列：字段开引号（"）未闭合——到文件结束都没有对应的闭引号`,
    }
  }
  // 末尾记录（文件无尾换行时）；语法错误点所在的半截记录一律丢弃
  if (!error && (cells.length > 0 || field.length > 0 || state === 'closed')) {
    endRecord()
  }
  return { records, error }
}

/* ---------- 表头映射 ---------- */

export type LeaseImportColumn = 'cidr' | 'name' | 'ip' | 'mac'

/** 各列可接受的表头写法（去空白、转小写后精确匹配） */
const HEADER_ALIASES: Record<LeaseImportColumn, string[]> = {
  cidr: ['网段cidr', '网段', 'cidr', '子网cidr', '子网', '网段地址', 'subnet', 'subnetcidr', 'network'],
  name: ['设备名', '设备名称', '名称', '主机名', 'name', 'hostname', 'devicename', 'host'],
  ip: ['ipv4', 'ip', 'ip地址', '地址', 'ipv4地址', '主机地址', 'ipaddress', 'address'],
  mac: ['mac', 'mac地址', '物理地址', 'hardwareaddress', 'hwaddr'],
}

function normalizeHeader(raw: string): string {
  return raw.replace(/\s+/g, '').toLowerCase()
}

export type HeaderError =
  | { kind: 'empty' } // CSV 为空或只有空白
  | { kind: 'missing'; columns: LeaseImportColumn[] } // 表头缺少必需列
  | { kind: 'duplicate'; column: LeaseImportColumn; headers: string[] } // 同一必需列匹配到多个表头

export interface HeaderMap {
  cidr: number
  name: number
  ip: number
  mac: number
}

/**
 * 依据首行记录识别四列表头。
 * 必需列缺失 / 同一列被多个表头匹配时返回对应错误（调用方据此停止逐行解析）。
 */
export function mapHeader(header: CsvRecord | undefined): { map?: HeaderMap; error?: HeaderError } {
  if (!header) return { error: { kind: 'empty' } }
  const normalized = header.cells.map(normalizeHeader)
  const resolved: Record<LeaseImportColumn, number[]> = { cidr: [], name: [], ip: [], mac: [] }
  for (const col of Object.keys(HEADER_ALIASES) as LeaseImportColumn[]) {
    normalized.forEach((h, idx) => {
      if (HEADER_ALIASES[col].includes(h)) resolved[col].push(idx)
    })
  }
  const missing = (Object.keys(resolved) as LeaseImportColumn[]).filter((c) => resolved[c].length === 0)
  if (missing.length > 0) return { error: { kind: 'missing', columns: missing } }
  const dup = (Object.keys(resolved) as LeaseImportColumn[]).find((c) => resolved[c].length > 1)
  if (dup) {
    return {
      error: { kind: 'duplicate', column: dup, headers: resolved[dup].map((i) => header.cells[i]) },
    }
  }
  return {
    map: { cidr: resolved.cidr[0], name: resolved.name[0], ip: resolved.ip[0], mac: resolved.mac[0] },
  }
}

export const COLUMN_LABEL: Record<LeaseImportColumn, string> = {
  cidr: '网段 CIDR',
  name: '设备名',
  ip: 'IPv4',
  mac: 'MAC',
}

/* ---------- 预览模型 ---------- */

export type LeaseImportStatus = 'add' | 'update' | 'unchanged' | 'conflict'

export const LEASE_STATUS_LABEL: Record<LeaseImportStatus, string> = {
  add: '新增',
  update: '更新',
  unchanged: '无变化',
  conflict: '冲突',
}

/** 一条导入数据行的逐行预览 */
export interface LeaseImportRow {
  /** CSV 物理行号（含表头，从 1 开始） */
  line: number
  /** 录入序号（仅数据行，从 1 开始） */
  index: number
  rawCidr: string
  rawName: string
  rawIp: string
  rawMac: string
  /** 规范后的字段（解析成功时存在） */
  cidr?: string
  name?: string
  address?: number
  ip?: string
  mac?: string
  /** 唯一匹配到的当前网段 */
  segment?: AllocSegment
  /** 命中的既有登记（按规范 MAC 匹配） */
  existing?: HostAssignment
  status: LeaseImportStatus
  /** 本行的全部冲突 / 错误原因（空数组表示本行可用） */
  errors: string[]
}

export interface LeaseImportCounts {
  rows: number
  add: number
  update: number
  unchanged: number
  conflict: number
}

export interface LeaseImportResult {
  /** 首个 CSV 语法错误（无错误为 null）；存在时 rows 为空、禁止应用、merged 保持既有登记 */
  syntaxError: CsvSyntaxError | null
  headerMap: HeaderMap | null
  headerError: HeaderError | null
  /** 表头级错误的中文说明（无错误为空数组） */
  headerErrors: string[]
  rows: LeaseImportRow[]
  counts: LeaseImportCounts
  /** 是否存在任何阻止应用的问题（表头错误或至少一行冲突） */
  hasConflicts: boolean
  /** 是否可应用：无语法错误、无冲突且至少有一条数据行 */
  canApply: boolean
  /** 应用后的完整登记快照（canApply 为 true 时可信） */
  merged: HostAssignment[]
  /** 本次导入将新增的登记数（canApply 时） */
  addCount: number
  /** 本次导入将更新的登记数（canApply 时） */
  updateCount: number
}

let importIdCounter = 0
/** 新增登记的稳定 ID 生成（默认实现；测试可注入确定性生成器） */
export function defaultLeaseIdGen(): string {
  importIdCounter += 1
  return `lease-${Date.now()}-${importIdCounter}`
}

/**
 * 构造「应用 CSV 后」的完整登记快照：
 * 未被 CSV 命中（按规范 MAC）的既有登记原样保留，
 * 命中的既有登记用导入行替换（名称 / 网段 / 地址 / MAC 全量更新），
 * 新 MAC 追加为新登记。仅收集自身字段（CIDR / 名称 / IP / MAC）全部解析成功的行。
 */
function buildMergedAssignments(
  existing: HostAssignment[],
  rows: LeaseImportRow[],
  genId: () => string,
): HostAssignment[] {
  const matchedIds = new Set(rows.filter((r) => r.existing).map((r) => r.existing!.id))
  const merged: HostAssignment[] = existing
    .filter((a) => !matchedIds.has(a.id))
    .map((a) => ({ ...a }))
  // 同一既有 ID 只允许被一条导入行替换；输入内重复 MAC 时其余行退化为新 ID 条目
  //（这些行本身已因输入内重复 MAC 判为冲突，这里仅保证快照内 ID 唯一）
  const consumedExisting = new Set<string>()
  for (const row of rows) {
    if (row.cidr === undefined || row.name === undefined || row.address === undefined || row.mac === undefined || !row.segment) {
      continue
    }
    const target =
      row.existing && !consumedExisting.has(row.existing.id) ? row.existing : undefined
    if (target) consumedExisting.add(target.id)
    if (target) {
      merged.push({
        ...target,
        ownerId: row.segment.ownerId,
        name: row.name,
        address: row.address,
        mode: 'manual',
        mac: row.mac,
      })
    } else {
      merged.push({
        id: genId(),
        ownerId: row.segment.ownerId,
        name: row.name,
        address: row.address,
        mode: 'manual',
        mac: row.mac,
      })
    }
  }
  return merged
}

/**
 * 用当前规划与既有登记校验整段 CSV 文本，生成逐行预览。
 * 纯函数：规划变化、登记增删改、CSV 文本变化后由调用方重新执行即可实时重算，
 * 原始 CSV 由调用方原样保留。
 */
export function buildLeaseImport(
  csv: string,
  existing: HostAssignment[],
  result: PlanResult,
  genId: () => string = defaultLeaseIdGen,
): LeaseImportResult {
  const { records, error: syntaxError } = parseCsv(csv)

  const empty: LeaseImportResult = {
    syntaxError: null,
    headerMap: null,
    headerError: null,
    headerErrors: [],
    rows: [],
    counts: { rows: 0, add: 0, update: 0, unchanged: 0, conflict: 0 },
    hasConflicts: false,
    canApply: false,
    merged: existing.map((a) => ({ ...a })),
    addCount: 0,
    updateCount: 0,
  }

  // 任一语法错误：禁用整批应用、保持既有登记不变（canApply=false 使迁移编排同步停止生成）；
  // 原始 CSV 由调用方保留，修正后重新执行本函数即自动恢复
  if (syntaxError) {
    return { ...empty, syntaxError }
  }

  const { map: headerMap, error: headerError } = mapHeader(records[0])
  if (headerError) {
    return { ...empty, headerError, headerErrors: [headerErrorText(headerError)] }
  }
  const map = headerMap!

  // 当前成功分配的固定 / 自动网段：规划保证各段 CIDR 互不相同，CIDR 命中即唯一匹配
  const segs = allocatableSegments(result)
  const segByCidr = new Map<string, AllocSegment>()
  for (const seg of segs) segByCidr.set(seg.cidr, seg)
  // 既有登记按规范 MAC 建索引（异常重复数据只保留最早一条作为命中目标）
  const existingByMac = new Map<string, HostAssignment>()
  for (const a of existing) {
    if (a.mac && !existingByMac.has(a.mac)) existingByMac.set(a.mac, a)
  }

  // 输入内重复检测的占用表（在逐行解析时即时填充）
  const macFirstIndex = new Map<string, number>()
  const addrFirstIndex = new Map<string, number>() // 键：ownerId#address

  const dataRecords = records.slice(1)
  const rows: LeaseImportRow[] = dataRecords.map((rec, i) => {
    const index = i + 1
    const rawCidr = (rec.cells[map.cidr] ?? '').trim()
    const rawName = (rec.cells[map.name] ?? '').trim()
    const rawIp = (rec.cells[map.ip] ?? '').trim()
    const rawMac = (rec.cells[map.mac] ?? '').trim()
    const errors: string[] = []

    // --- 网段 CIDR ---
    let segment: AllocSegment | undefined
    let canonicalCidr: string | undefined
    if (!rawCidr) {
      errors.push(`缺少${COLUMN_LABEL.cidr}`)
    } else {
      const parsed = parseCidr(rawCidr, true)
      if ('error' in parsed) {
        errors.push(`${COLUMN_LABEL.cidr}无效：${parsed.error}`)
      } else {
        canonicalCidr = `${intToIp(parsed.network)}/${parsed.prefix}`
        segment = segByCidr.get(canonicalCidr)
        if (!segment) {
          errors.push(`网段 ${canonicalCidr} 不是当前成功分配的固定或自动网段（必须与规划结果中的网段 CIDR 完全一致）`)
        }
      }
    }

    // --- 设备名 ---
    let name: string | undefined
    if (!rawName) {
      errors.push(`缺少${COLUMN_LABEL.name}`)
    } else {
      name = rawName
    }

    // --- IPv4 ---
    let address: number | undefined
    let ip: string | undefined
    if (!rawIp) {
      errors.push(`缺少${COLUMN_LABEL.ip}`)
    } else {
      const addr = ipToInt(rawIp)
      if (Number.isNaN(addr)) {
        errors.push(`IPv4“${rawIp}”不是合法地址`)
      } else {
        address = addr
        ip = intToIp(addr)
        if (segment) {
          if (addr === segment.start) {
            errors.push(`${ip} 是网段 ${segment.cidr} 的网络地址，不能分配给主机`)
          } else if (addr === segment.end) {
            errors.push(`${ip} 是网段 ${segment.cidr} 的广播地址，不能分配给主机`)
          } else if (addr < segment.start || addr > segment.end) {
            errors.push(
              `${ip} 不在网段 ${segment.cidr} 的可用范围 ${segment.firstUsable} ~ ${segment.lastUsable} 内（越界）`,
            )
          }
        }
      }
    }

    // --- MAC（批量导入中必填：它是设备身份） ---
    let mac: string | undefined
    if (!rawMac) {
      errors.push(`缺少${COLUMN_LABEL.mac}（批量导入以规范化 MAC 作为设备身份）`)
    } else {
      const macResult = normalizeMacInput(rawMac)
      if (macResult.error) {
        errors.push(macResult.error)
      } else if (macResult.mac) {
        mac = macResult.mac
      }
    }

    // --- 输入内重复 MAC（规范化后比较） ---
    if (mac) {
      const first = macFirstIndex.get(mac)
      if (first !== undefined) {
        errors.push(`MAC ${mac} 在本次导入的第 ${first} 行已出现（输入内 MAC 必须唯一）`)
      } else {
        macFirstIndex.set(mac, index)
      }
    }

    // --- 同网段内重复 IP（仅在网段与地址都解析成功时检测；越界/网络/广播另有错误） ---
    if (segment && address !== undefined && address > segment.start && address < segment.end) {
      const key = `${segment.ownerId}#${address}`
      const first = addrFirstIndex.get(key)
      if (first !== undefined) {
        errors.push(`地址 ${intToIp(address)} 在本次导入的网段 ${segment.cidr} 内第 ${first} 行已使用（网段内 IP 必须唯一）`)
      } else {
        addrFirstIndex.set(key, index)
      }
    }

    const existingAssignment = mac ? existingByMac.get(mac) : undefined

    const row: LeaseImportRow = {
      line: rec.line,
      index,
      rawCidr,
      rawName,
      rawIp,
      rawMac,
      ...(canonicalCidr !== undefined ? { cidr: canonicalCidr } : {}),
      ...(name !== undefined ? { name } : {}),
      ...(address !== undefined ? { address } : {}),
      ...(ip !== undefined ? { ip } : {}),
      ...(mac !== undefined ? { mac } : {}),
      ...(segment ? { segment } : {}),
      ...(existingAssignment ? { existing: existingAssignment } : {}),
      status: 'conflict',
      errors,
    }
    return row
  })

  // --- 构造合并后的完整登记快照，做统一的顺序无关校验 ---
  const merged = buildMergedAssignments(existing, rows, genId)
  // 合并快照中每条登记的当前规划有效性（地址级冲突：与未更新登记 / 其他导入行的地址重复等）
  const mergedById = new Map<string, HostAssignment>(merged.map((a) => [a.id, a]))
  const ownerByMac = new Map<string, string>() // 合并后 MAC -> 登记 ID（防御既有异常重复 MAC）

  // 用与主机面板完全相同的口径校验合并快照
  // 直接内联等价检查，避免与 rows 的局部错误相互覆盖：这里只补「合并后」才能发现的冲突
  const segByOwner = new Map<string, AllocSegment>()
  for (const seg of segs) segByOwner.set(seg.ownerId, seg)
  const firstAddrOwner = new Map<string, string>() // ownerId#address -> 最早登记 ID
  const validity = new Map<string, { valid: boolean; reason: string }>()

  for (const a of merged) {
    const seg = segByOwner.get(a.ownerId)
    if (!seg) {
      // 未更新的失效登记（owner 删除 / 分配失败）不阻断导入；导入行自身字段错误已含 CIDR 检查
      validity.set(a.id, { valid: false, reason: 'owner-missing' })
    } else if (a.address === seg.start) {
      validity.set(a.id, { valid: false, reason: `地址 ${intToIp(a.address)} 是网段 ${seg.cidr} 的网络地址` })
    } else if (a.address === seg.end) {
      validity.set(a.id, { valid: false, reason: `地址 ${intToIp(a.address)} 是网段 ${seg.cidr} 的广播地址` })
    } else if (a.address < seg.start || a.address > seg.end) {
      validity.set(a.id, {
        valid: false,
        reason: `地址 ${intToIp(a.address)} 不在网段 ${seg.cidr} 的可用范围 ${seg.firstUsable} ~ ${seg.lastUsable} 内`,
      })
    } else {
      const key = `${seg.ownerId}#${a.address}`
      const first = firstAddrOwner.get(key)
      if (first !== undefined) {
        validity.set(a.id, { valid: false, reason: `dup:${first}` })
      } else {
        firstAddrOwner.set(key, a.id)
        validity.set(a.id, { valid: true, reason: '' })
      }
    }
    if (a.mac) {
      const prev = ownerByMac.get(a.mac)
      if (prev === undefined) ownerByMac.set(a.mac, a.id)
      else if (validity.get(a.id)?.valid) {
        validity.set(a.id, { valid: false, reason: `mac-dup:${prev}` })
      }
    }
  }

  // 将合并快照层面的问题回填到对应导入行
  const mergedIdByImportIndex = new Map<number, string>()
  for (const row of rows) {
    if (row.existing) mergedIdByImportIndex.set(row.index, row.existing.id)
    else if (row.segment && row.name !== undefined && row.address !== undefined && row.mac !== undefined) {
      // 新登记 ID：在 merged 中按 owner+mac+address 找到（genId 生成的那条）
      const found = merged.find(
        (a) =>
          a.ownerId === row.segment!.ownerId &&
          a.mac === row.mac &&
          a.address === row.address &&
          !existing.some((e) => e.id === a.id),
      )
      if (found) mergedIdByImportIndex.set(row.index, found.id)
    }
  }

  for (const row of rows) {
    const mergedId = mergedIdByImportIndex.get(row.index)
    if (mergedId === undefined) continue
    const state = validity.get(mergedId)
    if (!state || state.valid) continue
    if (state.reason.startsWith('dup:')) {
      const otherId = state.reason.slice(4)
      const otherRowIndex = [...mergedIdByImportIndex.entries()].find(([, id]) => id === otherId)?.[0]
      const otherExisting = mergedById.get(otherId)
      const who =
        otherRowIndex !== undefined
          ? `本次导入的第 ${otherRowIndex} 行`
          : `未在本次导入中更新的既有设备“${otherExisting?.name || '未命名'}”`
      const msg = `地址 ${row.ip ?? row.rawIp} 与${who}在同一网段重复`
      if (!row.errors.includes(msg)) row.errors.push(msg)
    } else if (state.reason.startsWith('mac-dup:')) {
      const otherId = state.reason.slice(8)
      const otherRowIndex = [...mergedIdByImportIndex.entries()].find(([, id]) => id === otherId)?.[0]
      const otherExisting = mergedById.get(otherId)
      const who =
        otherRowIndex !== undefined
          ? `本次导入的第 ${otherRowIndex} 行`
          : `未在本次导入中更新的既有设备“${otherExisting?.name || '未命名'}”`
      const msg = `MAC ${row.mac ?? row.rawMac} 与${who}重复`
      if (!row.errors.includes(msg)) row.errors.push(msg)
    } else if (state.reason !== 'owner-missing') {
      // 网络/广播/越界已在字段阶段对导入行报错（CIDR 解析成功时），这里不重复添加
    }
  }

  // --- 行状态判定 ---
  let addCount = 0
  let updateCount = 0
  for (const row of rows) {
    if (row.errors.length > 0) {
      row.status = 'conflict'
      continue
    }
    if (row.existing) {
      const same =
        row.existing.ownerId === row.segment!.ownerId &&
        row.existing.address === row.address &&
        row.existing.name === row.name &&
        (row.existing.mac ?? '') === row.mac
      if (same) {
        row.status = 'unchanged'
      } else {
        row.status = 'update'
        updateCount++
      }
    } else {
      row.status = 'add'
      addCount++
    }
  }

  const counts: LeaseImportCounts = {
    rows: rows.length,
    add: rows.filter((r) => r.status === 'add').length,
    update: rows.filter((r) => r.status === 'update').length,
    unchanged: rows.filter((r) => r.status === 'unchanged').length,
    conflict: rows.filter((r) => r.status === 'conflict').length,
  }
  const hasConflicts = counts.conflict > 0

  return {
    syntaxError: null,
    headerMap: map,
    headerError: null,
    headerErrors: [],
    rows,
    counts,
    hasConflicts,
    canApply: !hasConflicts && rows.length > 0,
    merged: hasConflicts ? existing.map((a) => ({ ...a })) : merged,
    addCount: hasConflicts ? 0 : addCount,
    updateCount: hasConflicts ? 0 : updateCount,
  }
}

function headerErrorText(error: HeaderError): string {
  switch (error.kind) {
    case 'empty':
      return 'CSV 内容为空：请粘贴包含表头的数据（至少一行表头）'
    case 'missing':
      return `表头缺少必需列：${error.columns.map((c) => COLUMN_LABEL[c]).join('、')}。表头需包含「网段 CIDR、设备名、IPv4、MAC」四列（允许常见别名，如 cidr/名称/ip地址）`
    case 'duplicate':
      return `表头中 ${COLUMN_LABEL[error.column]} 列匹配到多个列名：${error.headers.join('、')}，每列只允许出现一次`
  }
}

/** 面板「填入示例」用的 CSV（对齐 demo 规划的网段） */
export const LEASE_IMPORT_SAMPLE = [
  '网段 CIDR,设备名,IPv4,MAC',
  '192.168.10.16/30,管理设备A,192.168.10.17,aa:bb:cc:00:00:01',
  '192.168.10.16/30,管理设备B,192.168.10.18,aa:bb:cc:00:00:02',
  '192.168.10.32/27,监控网关,192.168.10.33,aa:bb:cc:00:00:03',
].join('\n')
