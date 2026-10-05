'use strict';

const { Readable } = require('stream');
const net = require('net');

// ═══════════════════════════════════════════════
// 配置
// ═══════════════════════════════════════════════

// 白名单开关：true 开启，false 关闭（关闭后仍禁止内网地址）
const WHITELIST_ENABLED = true;

const MAX_BODY_BYTES = 4 * 1024 * 1024;   // 请求体上限 4 MB（平台 4.5 MB，留余量）
const PROBE_TIMEOUT_MS = 15_000;          // 源站探测超时
const CHUNK_TIMEOUT_MS = 120_000;         // 单分片下载超时
const CHUNK_MAX_RETRY = 3;                // 单分片最大重试次数

const CORS_HEADERS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': '*',
  'Access-Control-Allow-Headers': '*',
  'Access-Control-Expose-Headers': '*',
  'Access-Control-Max-Age': '86400'
};

const WHITELIST_DOMAINS = [
  // 微软系
  'microsoft.com',
  'azure.com',
  'windows.net',
  'live.com',
  'office.com',
  'office365.com',
  'sharepoint.com',
  'onedrive.com',
  'msn.com',
  'bing.com',
  'visualstudio.com',
  'vscode.dev',
  'github.com',
  'githubusercontent.com',
  'githubassets.com',
  'github.io',
  'blob.core.windows.net',
  // Google 系
  'google.com',
  'googleapis.com',
  'gstatic.com',
  'googlevideo.com',
  'youtube.com',
  'ytimg.com',
  'ggpht.com',
  'googleusercontent.com',
  'gvt1.com',
  'gvt2.com',
  'gvt3.com',
  'blogspot.com',
  'blogger.com',
  'android.com'
];

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ═══════════════════════════════════════════════
// 入口
// ═══════════════════════════════════════════════

module.exports = async function handler(req, res) {
  if (req.method === 'OPTIONS') {
    res.writeHead(204, CORS_HEADERS);
    return res.end();
  }

  try {
    await handleRequest(req, res);
  } catch (err) {
    const msg = (err && err.message) || 'unknown';
    if (!res.headersSent) {
      sendError(res, 500, `服务器内部错误：${msg}`, `Internal server error: ${msg}`);
    } else {
      try { res.end(); } catch (_) {}
    }
  }
};

async function handleRequest(req, res) {
  const targetUrl = parseTargetUrl(req);
  if (!targetUrl) {
    return sendError(res, 400, '无法解析目标地址', 'Unable to parse target URL');
  }

  let parsed;
  try {
    parsed = new URL(targetUrl);
  } catch (_) {
    return sendError(res, 400, '目标地址格式不正确', 'Invalid target URL format');
  }

  if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') {
    return sendError(res, 400, '仅支持 http/https 协议', 'Only http/https protocols are supported');
  }

  if (isPrivateHost(parsed.hostname)) {
    return sendError(res, 403, '禁止访问内网地址', 'Access to private addresses is forbidden');
  }

  if (WHITELIST_ENABLED && !isWhitelisted(parsed.hostname)) {
    return sendError(res, 403, '目标域名不在白名单内', 'Target domain is not in the whitelist');
  }

  if (req.method === 'GET' || req.method === 'HEAD') {
    return handleDownload(req, res, targetUrl);
  }

  if (req.method === 'POST') {
    return handlePost(req, res, targetUrl);
  }

  return sendError(res, 405, `不支持的请求方法：${req.method}`, `Method not allowed: ${req.method}`);
}

// ═══════════════════════════════════════════════
// 下载代理（多分片 + 流式）
// ═══════════════════════════════════════════════

async function handleDownload(req, res, targetUrl) {
  const headers = buildForwardHeaders(req, { 'accept-encoding': 'identity' });

  let probe;
  try {
    probe = await fetch(targetUrl, {
      method: 'GET',
      headers: { ...headers, Range: 'bytes=0-0' },
      signal: AbortSignal.timeout(PROBE_TIMEOUT_MS),
      redirect: 'follow'
    });
  } catch (err) {
    return sendError(res, 502, `无法连接源站：${err.message}`, `Failed to connect to upstream: ${err.message}`);
  }

  if (probe.status === 206) {
    const contentRange = probe.headers.get('content-range') || '';
    const totalSize = parseContentRangeTotal(contentRange);
    const upstreamHeaders = probe.headers;

    try { probe.body && probe.body.cancel(); } catch (_) {}

    if (totalSize > 1) {
      return streamMultiChunk(req, res, targetUrl, headers, totalSize, upstreamHeaders);
    }
  }

  try { probe.body && probe.body.cancel(); } catch (_) {}

  let response;
  try {
    response = await fetch(targetUrl, {
      method: 'GET',
      headers,
      redirect: 'follow'
    });
  } catch (err) {
    return sendError(res, 502, `无法连接源站：${err.message}`, `Failed to connect to upstream: ${err.message}`);
  }

  return relayResponse(response, res);
}

async function streamMultiChunk(req, res, targetUrl, headers, totalSize, upstreamHeaders) {
  const chunkCount = pickChunkCount(totalSize);
  const ranges = splitRanges(totalSize, chunkCount);

  res.statusCode = 200;
  res.setHeader('Content-Type', upstreamHeaders.get('content-type') || 'application/octet-stream');
  res.setHeader('Content-Length', String(totalSize));
  res.setHeader('Accept-Ranges', 'bytes');
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);

  const buffers = new Array(chunkCount).fill(null);
  let writeIndex = 0;
  let nextIndex = 0;
  let failed = null;

  const worker = async () => {
    while (true) {
      if (failed) return;
      const i = nextIndex++;
      if (i >= chunkCount) return;

      try {
        const buf = await fetchChunkWithRetry(targetUrl, headers, ranges[i]);
        buffers[i] = buf;

        while (writeIndex < chunkCount && buffers[writeIndex] !== null) {
          const chunk = buffers[writeIndex];
          buffers[writeIndex] = null;
          if (!res.write(chunk)) {
            await new Promise((r) => res.once('drain', r));
          }
          writeIndex++;
        }
      } catch (err) {
        failed = err;
        return;
      }
    }
  };

  const concurrency = Math.min(chunkCount, 16);
  const workers = [];
  for (let i = 0; i < concurrency; i++) workers.push(worker());

  await Promise.all(workers.map((p) => p.catch(() => {})));

  if (failed) {
    try { res.end(); } catch (_) {}
    return;
  }

  res.end();
}

async function fetchChunkWithRetry(targetUrl, headers, range) {
  let lastErr;
  for (let attempt = 0; attempt < CHUNK_MAX_RETRY; attempt++) {
    try {
      const response = await fetch(targetUrl, {
        method: 'GET',
        headers: { ...headers, Range: `bytes=${range.start}-${range.end}` },
        signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS),
        redirect: 'follow'
      });

      if (response.status === 429 || response.status >= 500) {
        lastErr = new Error(`HTTP ${response.status}`);
        await sleep(400 * Math.pow(2, attempt) + Math.random() * 200);
        continue;
      }

      if (!response.ok) {
        throw new Error(`HTTP ${response.status}`);
      }

      return Buffer.from(await response.arrayBuffer());
    } catch (err) {
      lastErr = err;
      if (attempt < CHUNK_MAX_RETRY - 1) {
        await sleep(400 * Math.pow(2, attempt) + Math.random() * 200);
      }
    }
  }
  throw lastErr || new Error('chunk download failed');
}

function pickChunkCount(totalSize) {
  if (totalSize < 1 * 1024 * 1024) return 1;
  if (totalSize < 10 * 1024 * 1024) return 4;
  if (totalSize < 50 * 1024 * 1024) return 8;
  if (totalSize < 200 * 1024 * 1024) return 16;
  return 32;
}

function splitRanges(totalSize, count) {
  const chunkSize = Math.ceil(totalSize / count);
  const ranges = [];
  for (let i = 0; i < count; i++) {
    const start = i * chunkSize;
    const end = Math.min(start + chunkSize - 1, totalSize - 1);
    if (start > end) break;
    ranges.push({ start, end });
  }
  return ranges;
}

function parseContentRangeTotal(contentRange) {
  const m = contentRange.match(/\/(\d+)\s*$/);
  return m ? parseInt(m[1], 10) : 0;
}

// ═══════════════════════════════════════════════
// POST 透传（请求体上限 4 MB）
// ═══════════════════════════════════════════════

async function handlePost(req, res, targetUrl) {
  const cl = req.headers['content-length'];
  if (cl && parseInt(cl, 10) > MAX_BODY_BYTES) {
    return sendError(
      res,
      413,
      '请求体过大，超过 4 MB 限制，请先上传成文件再提供链接',
      'Payload too large, exceeds 4 MB limit. Please upload the file first and provide a link.'
    );
  }

  let body;
  try {
    body = await readRequestBody(req);
  } catch (err) {
    if (err.message === 'BODY_TOO_LARGE') {
      return sendError(
        res,
        413,
        '请求体过大，超过 4 MB 限制，请先上传成文件再提供链接',
        'Payload too large, exceeds 4 MB limit. Please upload the file first and provide a link.'
      );
    }
    return sendError(res, 400, `读取请求体失败：${err.message}`, `Failed to read request body: ${err.message}`);
  }

  const headers = buildForwardHeaders(req);
  delete headers['content-length'];

  let response;
  try {
    response = await fetch(targetUrl, {
      method: 'POST',
      headers,
      body,
      redirect: 'follow'
    });
  } catch (err) {
    return sendError(res, 502, `无法连接源站：${err.message}`, `Failed to connect to upstream: ${err.message}`);
  }

  return relayResponse(response, res);
}

async function readRequestBody(req) {
  const chunks = [];
  let total = 0;
  for await (const chunk of req) {
    total += chunk.length;
    if (total > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
    chunks.push(chunk);
  }
  if (chunks.length > 0) return Buffer.concat(chunks);

  if (req.body !== undefined && req.body !== null) {
    if (Buffer.isBuffer(req.body)) {
      if (req.body.length > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
      return req.body;
    }
    if (typeof req.body === 'string') {
      const buf = Buffer.from(req.body);
      if (buf.length > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
      return buf;
    }
    if (typeof req.body === 'object') {
      const buf = Buffer.from(JSON.stringify(req.body));
      if (buf.length > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
      return buf;
    }
  }

  return Buffer.alloc(0);
}

// ═══════════════════════════════════════════════
// 响应中继
// ═══════════════════════════════════════════════

async function relayResponse(response, res) {
  res.statusCode = response.status;

  for (const [key, value] of response.headers) {
    const lower = key.toLowerCase();
    if (lower === 'transfer-encoding') continue;
    res.setHeader(key, value);
  }

  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);

  if (!response.body) {
    return res.end();
  }

  const nodeStream = Readable.fromWeb(response.body);
  await new Promise((resolve) => {
    nodeStream.on('error', () => { try { res.end(); } catch (_) {} resolve(); });
    res.on('error', resolve);
    nodeStream.pipe(res).on('finish', resolve);
  });
}

// ═══════════════════════════════════════════════
// URL 解析与校验
// ═══════════════════════════════════════════════

function parseTargetUrl(req) {
  const raw = req.url || '';
  const queryIdx = raw.indexOf('?');
  let path = queryIdx >= 0 ? raw.slice(0, queryIdx) : raw;
  const query = queryIdx >= 0 ? raw.slice(queryIdx) : '';

  if (path.startsWith('/')) path = path.slice(1);

  try { path = decodeURIComponent(path); } catch (_) {}

  // 修复被平台规范化的双斜杠：https:/example.com → https://example.com
  path = path.replace(/^(https?):\/(?!\/)/i, '$1://');

  if (!/^https?:\/\//i.test(path)) {
    if (/^[a-z0-9.-]+\.[a-z]{2,}/i.test(path)) {
      path = 'https://' + path;
    } else {
      return '';
    }
  }

  return path + query;
}

function buildForwardHeaders(req, override = {}) {
  const headers = {};
  const skip = new Set(['host', 'connection', 'content-length', 'transfer-encoding']);
  for (const [key, value] of Object.entries(req.headers)) {
    if (skip.has(key.toLowerCase())) continue;
    headers[key] = value;
  }
  return Object.assign(headers, override);
}

// ───────────────────────────────────────────────
// 内网地址判断（IPv4 + IPv6 全覆盖）
// ───────────────────────────────────────────────

function isPrivateHost(hostname) {
  if (!hostname) return true;

  let host = String(hostname).toLowerCase().trim();

  // 去掉 IPv6 方括号
  if (host.startsWith('[') && host.endsWith(']')) host = host.slice(1, -1);

  // 去掉 IPv6 作用域 ID，例如 fe80::1%eth0
  const pct = host.indexOf('%');
  if (pct >= 0) host = host.slice(0, pct);

  if (!host) return true;

  if (host === 'localhost' || host.endsWith('.localhost')) return true;
  if (host.endsWith('.local')) return true;

  const version = net.isIP(host);
  if (version === 4) return isPrivateIPv4(host);
  if (version === 6) return isPrivateIPv6(host);

  // 不是 IP 字面量：交给白名单把关
  return false;
}

function isPrivateIPv4(host) {
  const m = /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.exec(host);
  if (!m) return true; // 异常写法，保守拒绝

  const a = Number(m[1]);
  const b = Number(m[2]);

  if (a === 0) return true;                            // 0.0.0.0/8
  if (a === 10) return true;                           // 10.0.0.0/8
  if (a === 127) return true;                          // 127.0.0.0/8
  if (a === 169 && b === 254) return true;             // 169.254.0.0/16
  if (a === 172 && b >= 16 && b <= 31) return true;    // 172.16.0.0/12
  if (a === 192 && b === 168) return true;             // 192.168.0.0/16
  if (a === 100 && b >= 64 && b <= 127) return true;   // 100.64.0.0/10 CGNAT
  if (a >= 224) return true;                           // 组播 + 保留
  return false;
}

function isPrivateIPv6(host) {
  const groups = expandIPv6(host);
  if (!groups) return true; // 解析失败，保守拒绝

  const [g0, g1, g2, g3, g4, g5, g6, g7] = groups;

  // ::/96 —— 环回、未指定、IPv4 兼容，全部拒绝
  if (g0 === 0 && g1 === 0 && g2 === 0 && g3 === 0 && g4 === 0 && g5 === 0) {
    return true;
  }

  // ::ffff:0:0/96 —— IPv4-mapped，取后 32 位按 IPv4 判定
  if (g0 === 0 && g1 === 0 && g2 === 0 && g3 === 0 && g4 === 0 && g5 === 0xffff) {
    return isPrivateIPv4(`${g6 >> 8}.${g6 & 0xff}.${g7 >> 8}.${g7 & 0xff}`);
  }

  // fc00::/7 —— ULA
  if ((g0 & 0xfe00) === 0xfc00) return true;

  // fe80::/10 —— 链路本地
  if ((g0 & 0xffc0) === 0xfe80) return true;

  // ff00::/8 —— 组播
  if ((g0 & 0xff00) === 0xff00) return true;

  // 2002::/16 —— 6to4，内嵌 IPv4
  if (g0 === 0x2002) {
    return isPrivateIPv4(`${g1 >> 8}.${g1 & 0xff}.${g2 >> 8}.${g2 & 0xff}`);
  }

  // 64:ff9b::/96 —— NAT64，内嵌 IPv4
  if (g0 === 0x0064 && g1 === 0xff9b && g2 === 0 && g3 === 0 && g4 === 0 && g5 === 0) {
    return isPrivateIPv4(`${g6 >> 8}.${g6 & 0xff}.${g7 >> 8}.${g7 & 0xff}`);
  }

  // 64:ff9b:1::/48 —— 本地 NAT64
  if (g0 === 0x0064 && g1 === 0xff9b && g2 === 0x0001) return true;

  // 2001:db8::/32 —— 文档地址
  if (g0 === 0x2001 && g1 === 0x0db8) return true;

  // 2001::/32 —— Teredo（内嵌 IPv4 易被混淆，直接拒绝）
  if (g0 === 0x2001 && g1 === 0x0000) return true;

  // 2001:10::/28、2001:20::/28 —— ORCHID
  if (g0 === 0x2001 && (g1 & 0xfff0) === 0x0010) return true;
  if (g0 === 0x2001 && (g1 & 0xfff0) === 0x0020) return true;

  // 5f00::/8 —— 保留段
  if ((g0 & 0xff00) === 0x5f00) return true;

  return false;
}

/**
 * 将 IPv6 字符串展开为 8 个 16 位整数数组。
 * 支持压缩写法（::）、内嵌 IPv4 尾部。解析失败返回 null。
 */
function expandIPv6(host) {
  if (net.isIP(host) !== 6) return null;

  let h = host;
  let v4Tail = null;

  // 处理内嵌 IPv4 尾部
  const lastColon = h.lastIndexOf(':');
  if (lastColon >= 0) {
    const tail = h.slice(lastColon + 1);
    if (tail.includes('.')) {
      const parts = tail.split('.');
      if (parts.length !== 4) return null;
      const nums = parts.map((p) => Number(p));
      if (nums.some((n) => !Number.isInteger(n) || n < 0 || n > 255)) return null;
      v4Tail = [(nums[0] << 8) | nums[1], (nums[2] << 8) | nums[3]];
      h = h.slice(0, lastColon + 1) + '0:0';
    }
  }

  const dbl = h.indexOf('::');
  let left;
  let right;

  if (dbl >= 0) {
    if (h.indexOf('::', dbl + 2) >= 0) return null;
    const l = h.slice(0, dbl);
    const r = h.slice(dbl + 2);
    left = l ? l.split(':') : [];
    right = r ? r.split(':') : [];
    if (left.length + right.length > 7) return null;
  } else {
    left = h.split(':');
    right = [];
    if (left.length !== 8) return null;
  }

  const parseGroup = (s) => {
    if (!/^[0-9a-f]{1,4}$/i.test(s)) return -1;
    return parseInt(s, 16);
  };

  const groups = [];
  for (const g of left) {
    const n = parseGroup(g);
    if (n < 0) return null;
    groups.push(n);
  }
  if (dbl >= 0) {
    const missing = 8 - left.length - right.length;
    if (missing < 1) return null;
    for (let i = 0; i < missing; i++) groups.push(0);
  }
  for (const g of right) {
    const n = parseGroup(g);
    if (n < 0) return null;
    groups.push(n);
  }

  if (groups.length !== 8) return null;

  if (v4Tail) {
    groups[6] = v4Tail[0];
    groups[7] = v4Tail[1];
  }

  return groups;
}

function isWhitelisted(hostname) {
  const host = hostname.toLowerCase();
  for (const domain of WHITELIST_DOMAINS) {
    if (host === domain) return true;
    if (host.endsWith('.' + domain)) return true;
  }
  return false;
}

// ═══════════════════════════════════════════════
// 错误响应
// ═══════════════════════════════════════════════

function sendError(res, statusCode, zhMsg, enMsg) {
  if (res.headersSent) {
    try { res.end(); } catch (_) {}
    return;
  }
  res.statusCode = statusCode;
  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
  res.end(`${zhMsg}\n${enMsg}\n`);
}