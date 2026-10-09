'use strict';

const { Readable } = require('stream');
const dns = require('dns');
const net = require('net');
const { Agent, fetch: undiciFetch } = require('undici');
const ipaddr = require('ipaddr.js');
const contentType = require('content-type');
const iconv = require('iconv-lite');
const parse5 = require('parse5');
const acorn = require('acorn');
const walk = require('acorn-walk');

// ═══════════════════════════════════════════════
// 日志
// ═══════════════════════════════════════════════
const LOG_ENABLED = process.env.PROXY_LOG !== 'off';
let __reqSeq = 0;

function newTag() {
  return 'r' + (++__reqSeq).toString(36);
}

function log(tag, stage, msg, meta) {
  if (!LOG_ENABLED) return;
  const line = ['[proxy]', tag, stage, msg];
  if (meta !== undefined) {
    try { line.push(JSON.stringify(meta)); }
    catch { line.push(String(meta)); }
  }
  console.log(line.join(' '));
}

function logErr(tag, stage, msg, err) {
  const meta = {};
  if (err) {
    meta.message = err.message;
    if (err.code) meta.code = err.code;
    if (err.name) meta.name = err.name;
    if (err.stack) meta.stack = String(err.stack).split('\n').slice(0, 3).join(' | ');
  }
  console.error(['[proxy]', tag, stage, msg, JSON.stringify(meta)].join(' '));
}

function briefUrl(u, max = 120) {
  if (typeof u !== 'string') return String(u);
  return u.length > max ? u.slice(0, max) + '...' : u;
}

// ═══════════════════════════════════════════════
// 配置
// ═══════════════════════════════════════════════
const WHITELIST_ENABLED = true;
const MAX_BODY_BYTES = 4 * 1024 * 1024;
const HTML_MAX_BYTES = 8 * 1024 * 1024;
const PROBE_TIMEOUT_MS = 15_000;
const CHUNK_TIMEOUT_MS = 120_000;
const CHUNK_MAX_RETRY = 3;
const MAX_INFLIGHT = 4;
const MAX_CONCURRENCY = 4;
const MAX_REDIRECTS = 5;
const REWRITE_SCRIPT = true;
const VIDEO_PREVIEW_BYTES = 512 * 1024;

const CORS_HEADERS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': '*',
  'Access-Control-Allow-Headers': '*',
  'Access-Control-Expose-Headers': '*',
  'Access-Control-Max-Age': '86400'
};

// ═══════════════════════════════════════════════
// 白名单
// ═══════════════════════════════════════════════
const WHITELIST_DOMAINS = [
  'microsoft.com', 'azure.com', 'windows.net', 'live.com', 'office.com',
  'office365.com', 'sharepoint.com', 'onedrive.com', 'msn.com', 'bing.com',
  'visualstudio.com', 'vscode.dev', 'blob.core.windows.net',

  'google.com', 'googleapis.com', 'gstatic.com', 'googlevideo.com',
  'youtube.com', 'ytimg.com', 'ggpht.com', 'googleusercontent.com',
  'gvt1.com', 'gvt2.com', 'gvt3.com', 'blogspot.com', 'blogger.com', 'android.com',

  'github.com', 'githubusercontent.com', 'githubassets.com', 'github.io',

  'netlify.com', 'netlify.app', 'netlify.dev', 'netlify-cdn.com',

  'vercel.com', 'vercel.app', 'vercel.dev', 'now.sh', 'vercel-dns.com',

  'openai.com', 'chatgpt.com', 'oaistatic.com', 'oaiusercontent.com',
  'openai.azure.com', 'sora.com',

  'cloudflare.com', 'cloudflare.net', 'cloudflareinsights.com',
  'cdnjs.com', 'workers.dev', 'pages.dev', 'cloudflarestream.com',
  'r2.dev', 'cfdata.org', 'cloudflareclient.com',

  '344977.xyz',

  'discord.com', 'discordapp.com', 'discordapp.net', 'discord.gg',
  'telegram.org', 't.me', 'telegram.me',
  'slack.com', 'slack-edge.com', 'slack-files.com', 'slack-imgs.com',
  'line.me', 'line-scdn.net',
  'wechat.com', 'weixin.qq.com', 'qpic.cn', 'qlogo.cn',
  'meta.com', 'facebook.com', 'fbcdn.net', 'whatsapp.com', 'whatsapp.net',
  'twitter.com', 'x.com', 'twimg.com',
  'reddit.com', 'redd.it', 'redditstatic.com',

  'npmjs.org', 'npmjs.com', 'registry.npmjs.org', 'pypi.org', 'pythonhosted.org'
];

const HOP_BY_HOP = new Set([
  'connection', 'keep-alive', 'proxy-authenticate', 'proxy-authorization',
  'te', 'trailer', 'transfer-encoding', 'upgrade'
]);

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ═══════════════════════════════════════════════
// SSRF 防护
// ═══════════════════════════════════════════════
function isPrivateAddress(ip) {
  let addr;
  try { addr = ipaddr.parse(ip); } catch { return true; }

  if (addr.kind() === 'ipv4') return addr.range() !== 'unicast';

  const range = addr.range();
  try {
    if (range === 'ipv4Mapped' || range === 'rfc6052' || range === 'rfc6145') {
      return isPrivateAddress(addr.toIPv4Address().toString());
    }
    if (range === '6to4') {
      const b = addr.toByteArray();
      return isPrivateAddress(`${b[2]}.${b[3]}.${b[4]}.${b[5]}`);
    }
    if (range === 'teredo') return true;
  } catch (_) { return true; }

  return range !== 'unicast';
}

function isWhitelisted(hostname, list) {
  const host = String(hostname).toLowerCase().replace(/\.$/, '');
  for (const d of list) {
    if (host === d) return true;
    if (host.endsWith('.' + d)) return true;
  }
  return false;
}

async function resolveSafe(hostname, tag) {
  let host = String(hostname);
  if (host.startsWith('[') && host.endsWith(']')) host = host.slice(1, -1);

  const v = net.isIP(host);
  if (v > 0) {
    if (isPrivateAddress(host)) {
      if (tag) log(tag, 'dns', 'ip literal blocked', { host });
      throw Object.assign(new Error('SSRF_BLOCKED'), { code: 'SSRF_BLOCKED' });
    }
    return [{ address: host, family: v }];
  }

  let addrs;
  try {
    addrs = await dns.promises.lookup(host, { all: true, verbatim: true });
  } catch (e) {
    if (tag) log(tag, 'dns', 'lookup failed', { host, err: e.message });
    throw Object.assign(new Error('DNS_FAILED'), { code: 'DNS_FAILED' });
  }
  if (!addrs || addrs.length === 0) {
    if (tag) log(tag, 'dns', 'empty result', { host });
    throw Object.assign(new Error('DNS_EMPTY'), { code: 'DNS_EMPTY' });
  }

  const safe = addrs.filter((a) => !isPrivateAddress(a.address));
  if (safe.length === 0) {
    if (tag) log(tag, 'dns', 'all private', { host, resolved: addrs.map((a) => a.address) });
    throw Object.assign(new Error('SSRF_BLOCKED'), { code: 'SSRF_BLOCKED' });
  }
  if (tag) log(tag, 'dns', 'ok', { host, addrs: safe.map((a) => a.address) });
  return safe;
}

// ═══════════════════════════════════════════════
// 安全 Agent
// undici 调用 lookup 时始终传 { all: true }，要求回调返回记录数组
// ═══════════════════════════════════════════════
const SECURE_AGENT = new Agent({
  connect: {
    lookup(hostname, options, callback) {
      const wantAll = !options || options.all === true;
      const wantFamily =
        options && (options.family === 4 || options.family === 6)
          ? options.family
          : 0;

      resolveSafe(hostname).then((addrs) => {
        let list = addrs;
        if (wantFamily) {
          list = addrs.filter((a) => a.family === wantFamily);
          if (list.length === 0) {
            return callback(new Error('NO_MATCHING_FAMILY'));
          }
        }
        if (wantAll) {
          callback(null, list.map((a) => ({ address: a.address, family: a.family })));
        } else {
          callback(null, list[0].address, list[0].family);
        }
      }).catch((err) => callback(err));
    }
  },
  connectTimeout: 10_000,
  headersTimeout: 30_000,
  bodyTimeout: CHUNK_TIMEOUT_MS,
  keepAliveTimeout: 10_000,
  keepAliveMaxTimeout: 60_000,
  pipelining: 1
});

// ═══════════════════════════════════════════════
// MIME
// ═══════════════════════════════════════════════
function getMimeType(ct) {
  if (!ct) return '';
  try { return contentType.parse(ct).type.toLowerCase(); } catch {
    const m = /^\s*([a-z0-9!#$&\-^_.+]+\/[a-z0-9!#$&\-^_.+]+)/i.exec(ct);
    return m ? m[1].toLowerCase() : '';
  }
}

function isHtmlMime(m) {
  return m === 'text/html' || m === 'application/xhtml+xml';
}

function isVideoMime(m) {
  return m.startsWith('video/');
}

function isUnrestrictedMime(m) {
  if (m.startsWith('image/')) return true;
  if (m.startsWith('audio/')) return true;
  if (m.startsWith('font/')) return true;
  if (m === 'text/css') return true;
  if (m === 'text/javascript' || m === 'application/javascript'
      || m === 'application/x-javascript' || m === 'application/ecmascript') return true;
  if (m === 'application/json' || m === 'text/plain') return true;
  return false;
}

// ═══════════════════════════════════════════════
// 主入口
// ═══════════════════════════════════════════════
module.exports = async function handler(req, res) {
  const tag = newTag();
  const startedAt = Date.now();

  if (req.url === '/__health__') {
    res.statusCode = 200;
    res.setHeader('Content-Type', 'text/plain');
    return res.end('ok');
  }

  if (req.method === 'OPTIONS') {
    log(tag, 'entry', 'preflight', { method: req.method, url: briefUrl(req.url) });
    res.writeHead(204, CORS_HEADERS);
    return res.end();
  }

  log(tag, 'entry', 'request', {
    method: req.method,
    url: briefUrl(req.url),
    ua: req.headers && req.headers['user-agent'] ? briefUrl(req.headers['user-agent'], 60) : undefined
  });

  let parsed;
  try {
    parsed = parseRequest(req);
  } catch (e) {
    logErr(tag, 'parse', 'failed', e);
    return sendError(res, 400, `请求解析失败：${e.message}`);
  }
  if (!parsed) {
    log(tag, 'parse', 'unresolvable', { url: briefUrl(req.url) });
    return sendError(res, 400, '无法解析目标地址');
  }

  log(tag, 'parse', 'ok', {
    target: briefUrl(parsed.targetUrl),
    host: parsed.parsedUrl.hostname,
    white: !!parsed.options.white
  });

  try {
    await handleRequest(req, res, parsed, tag);
    log(tag, 'done', 'completed', {
      status: res.statusCode,
      ms: Date.now() - startedAt
    });
  } catch (err) {
    const code = err && err.code;
    const msg = (err && err.message) || 'unknown';
    logErr(tag, 'handler', 'threw', err);

    if (res.headersSent) {
      try { res.destroy(); } catch (_) {}
      return;
    }
    if (code === 'SSRF_BLOCKED') return sendError(res, 403, '禁止访问内网地址', tag);
    if (code === 'NOT_WHITELISTED') return sendError(res, 403, '目标域名不在白名单内', tag);
    if (code === 'DNS_FAILED') return sendError(res, 502, '域名解析失败', tag);
    sendError(res, 502, `上游错误：${msg}`, tag);
  }
};

async function handleRequest(req, res, { targetUrl, parsedUrl, options }, tag) {
  if (!options.white && WHITELIST_ENABLED) {
    if (!isWhitelisted(parsedUrl.hostname, WHITELIST_DOMAINS)) {
      log(tag, 'whitelist', 'rejected', { host: parsedUrl.hostname });
      return sendError(res, 403, '目标域名不在白名单内', tag);
    }
    log(tag, 'whitelist', 'passed', { host: parsedUrl.hostname });
  } else if (options.white) {
    log(tag, 'whitelist', 'bypassed by white=Y', { host: parsedUrl.hostname });
  }

  if (req.method === 'GET' || req.method === 'HEAD') {
    return handleDownload(req, res, targetUrl, options, tag);
  }
  if (['POST', 'PUT', 'PATCH', 'DELETE'].includes(req.method)) {
    return handleForward(req, res, targetUrl, options, tag);
  }
  log(tag, 'method', 'not allowed', { method: req.method });
  return sendError(res, 405, `不支持的请求方法：${req.method}`, tag);
}

// ═══════════════════════════════════════════════
// safeFetch
// ═══════════════════════════════════════════════
async function safeFetch(rawUrl, init, options, tag) {
  let current = rawUrl;
  let redirects = 0;
  let method = (init.method || 'GET').toUpperCase();
  let body = init.body;
  const baseHeaders = { ...init.headers };

  while (true) {
    const u = new URL(current);

    if (!options.white && WHITELIST_ENABLED) {
      if (!isWhitelisted(u.hostname, WHITELIST_DOMAINS)) {
        throw Object.assign(new Error('NOT_WHITELISTED'), { code: 'NOT_WHITELISTED' });
      }
    }

    const t0 = Date.now();
    let res;
    try {
      res = await undiciFetch(current, {
        method, body,
        headers: baseHeaders,
        redirect: 'manual',
        signal: init.signal,
        dispatcher: SECURE_AGENT
      });
    } catch (e) {
      if (tag) logErr(tag, 'fetch', 'network error', e);
      throw e;
    }

    if (tag) log(tag, 'fetch', 'response', {
      url: briefUrl(current),
      status: res.status,
      ct: res.headers.get('content-type'),
      cl: res.headers.get('content-length'),
      ms: Date.now() - t0
    });

    if ([301, 302, 303, 307, 308].includes(res.status)) {
      const loc = res.headers.get('location');
      if (!loc) return res;
      cancelBody(res);
      if (++redirects > MAX_REDIRECTS) {
        if (tag) log(tag, 'redirect', 'too many', { count: redirects });
        throw new Error('重定向次数过多');
      }

      if (res.status === 303 ||
          ((res.status === 301 || res.status === 302) && method !== 'GET' && method !== 'HEAD')) {
        method = 'GET';
        body = undefined;
        delete baseHeaders['content-type'];
      }
      const next = new URL(loc, current).href;
      if (tag) log(tag, 'redirect', 'follow', {
        from: briefUrl(current),
        to: briefUrl(next),
        status: res.status,
        method
      });
      current = next;
      continue;
    }
    return res;
  }
}

// ═══════════════════════════════════════════════
// GET / HEAD 分发
// ═══════════════════════════════════════════════
async function handleDownload(req, res, targetUrl, options, tag) {
  const headers = buildForwardHeaders(req);
  const isHead = req.method === 'HEAD';

  let probe;
  try {
    probe = await safeFetch(targetUrl, {
      method: 'GET',
      headers: { ...headers, Range: 'bytes=0-0' },
      signal: AbortSignal.timeout(PROBE_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    logErr(tag, 'probe', 'failed', err);
    return sendError(res, 502, `无法连接源站：${err.message}`, tag);
  }

  const probeCT = probe.headers.get('content-type') || '';
  const probeCR = probe.headers.get('content-range') || '';
  const probeStatus = probe.status;
  const mime = getMimeType(probeCT);
  cancelBody(probe);

  log(tag, 'probe', 'result', {
    status: probeStatus,
    mime,
    cr: probeCR || undefined,
    head: isHead
  });

  if (isHead) {
    log(tag, 'route', 'head');
    return handleHead(req, res, targetUrl, headers, options, tag);
  }

  if (isHtmlMime(mime)) {
    log(tag, 'route', 'html');
    return handleHtml(req, res, targetUrl, headers, options, tag);
  }

  if (isVideoMime(mime)) {
    log(tag, 'route', 'video-preview');
    return handleVideoPreview(req, res, targetUrl, headers, options, tag);
  }

  if (isUnrestrictedMime(mime)) {
    if (probeStatus === 206) {
      const totalSize = parseContentRangeTotal(probeCR);
      if (totalSize > 1) {
        log(tag, 'route', 'chunked-unrestricted', { totalSize });
        return streamMultiChunk(req, res, targetUrl, headers, totalSize, probe.headers, options, tag);
      }
    }
    log(tag, 'route', 'stream-unrestricted');
    return streamFallback(req, res, targetUrl, headers, options, tag);
  }

  if (probeStatus === 206) {
    const totalSize = parseContentRangeTotal(probeCR);
    if (totalSize > 1) {
      log(tag, 'route', 'chunked-default', { totalSize });
      return streamMultiChunk(req, res, targetUrl, headers, totalSize, probe.headers, options, tag);
    }
  }
  log(tag, 'route', 'stream-default');
  return streamFallback(req, res, targetUrl, headers, options, tag);
}

// ── HEAD ──
async function handleHead(req, res, targetUrl, headers, options, tag) {
  let response;
  try {
    response = await safeFetch(targetUrl, {
      method: 'HEAD',
      headers,
      signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    // HEAD 405/501 时降级为 GET + Range 0-0
    if (/40[15]|50[15]/.test(String(err && err.message))) {
      log(tag, 'head', 'fallback to GET Range');
      try {
        response = await safeFetch(targetUrl, {
          method: 'GET',
          headers: { ...headers, Range: 'bytes=0-0' },
          signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
        }, options, tag);
      } catch (err2) {
        logErr(tag, 'head', 'fallback failed', err2);
        return sendError(res, 502, `无法连接源站：${err2.message}`, tag);
      }
    } else {
      logErr(tag, 'head', 'failed', err);
      return sendError(res, 502, `无法连接源站：${err.message}`, tag);
    }
  }

  res.statusCode = response.status;
  for (const [k, v] of response.headers) {
    const lk = k.toLowerCase();
    if (HOP_BY_HOP.has(lk)) continue;
    if (lk === 'content-length' && response.headers.get('content-range')) {
      // Range 0-0 时不要暴露 1 字节长度给 HEAD 客户端
      const total = parseContentRangeTotal(response.headers.get('content-range'));
      if (total > 0) res.setHeader('Content-Length', String(total));
      continue;
    }
    res.setHeader(k, v);
  }
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);

  cancelBody(response);
  res.end();
}

// ═══════════════════════════════════════════════
// 视频预览
// ═══════════════════════════════════════════════
async function handleVideoPreview(req, res, targetUrl, headers, options, tag) {
  const previewLimit = VIDEO_PREVIEW_BYTES;

  let start = 0;
  let end = previewLimit - 1;

  const clientRange = req.headers['range'];
  if (clientRange) {
    const m = /^bytes=(\d+)-(\d*)/.exec(clientRange);
    if (m) {
      const s = parseInt(m[1], 10);
      if (Number.isFinite(s)) {
        if (s >= previewLimit) {
          log(tag, 'video', 'range beyond preview', { start: s, limit: previewLimit });
          res.statusCode = 416;
          res.setHeader('Content-Range', `bytes */${previewLimit}`);
          res.setHeader('Accept-Ranges', 'bytes');
          for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
          return res.end();
        }
        start = s;
        if (m[2]) {
          const e = parseInt(m[2], 10);
          if (Number.isFinite(e)) end = Math.min(end, e);
        }
      }
    }
  }

  let response;
  try {
    response = await safeFetch(targetUrl, {
      method: 'GET',
      headers: { ...headers, Range: `bytes=${start}-${end}` },
      signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    logErr(tag, 'video', 'fetch failed', err);
    return sendError(res, 502, `无法连接源站：${err.message}`, tag);
  }

  if (response.status !== 200 && response.status !== 206) {
    log(tag, 'video', 'upstream non-2xx, relay', { status: response.status });
    return relayResponse(response, res, tag);
  }

  const limit = end - start + 1;
  let bodyBuf;
  try {
    bodyBuf = await readLimitedBody(response, limit);
  } catch (err) {
    logErr(tag, 'video', 'read failed', err);
    return sendError(res, 502, `读取视频失败：${err.message}`, tag);
  }

  if (bodyBuf.length === 0) {
    log(tag, 'video', 'empty body');
    return sendError(res, 502, '视频源站返回空响应', tag);
  }

  const totalSize = parseContentRangeTotal(response.headers.get('content-range') || '');
  const realEnd = start + bodyBuf.length - 1;

  log(tag, 'video', 'preview served', {
    bytes: bodyBuf.length,
    range: `${start}-${realEnd}`,
    total: totalSize || 'unknown',
    upstreamStatus: response.status
  });

  res.statusCode = 206;
  res.setHeader('Content-Type', response.headers.get('content-type') || 'video/mp4');
  res.setHeader('Content-Length', String(bodyBuf.length));
  res.setHeader('Accept-Ranges', 'bytes');
  res.setHeader(
    'Content-Range',
    totalSize > 0
      ? `bytes ${start}-${realEnd}/${totalSize}`
      : `bytes ${start}-${realEnd}/*`
  );
  res.setHeader('X-Preview-Only', 'first-frame');
  res.setHeader('X-Preview-Bytes', String(VIDEO_PREVIEW_BYTES));
  res.setHeader('Cache-Control', 'public, max-age=3600');
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
  res.end(bodyBuf);
}

async function readLimitedBody(response, limit) {
  if (!response.body) return Buffer.alloc(0);

  const reader = response.body.getReader();
  const chunks = [];
  let total = 0;

  try {
    while (total < limit) {
      const { done, value } = await reader.read();
      if (done) break;
      if (value && value.length) {
        chunks.push(Buffer.from(value));
        total += value.length;
      }
    }
  } finally {
    try { await reader.cancel(); } catch (_) {}
    try { reader.releaseLock(); } catch (_) {}
  }

  const full = Buffer.concat(chunks, Math.min(total, limit));
  return full.length > limit ? full.subarray(0, limit) : full;
}

// ═══════════════════════════════════════════════
// 通用流式回源
// ═══════════════════════════════════════════════
async function streamFallback(req, res, targetUrl, headers, options, tag) {
  let response;
  try {
    response = await safeFetch(targetUrl, {
      method: req.method,
      headers,
      signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    logErr(tag, 'stream', 'fetch failed', err);
    return sendError(res, 502, `无法连接源站：${err.message}`, tag);
  }
  return relayResponse(response, res, tag);
}

// ═══════════════════════════════════════════════
// HTML
// ═══════════════════════════════════════════════
async function handleHtml(req, res, targetUrl, headers, options, tag) {
  let response;
  try {
    response = await safeFetch(targetUrl, {
      method: 'GET',
      headers: { ...headers, 'accept-encoding': 'identity' },
      signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    logErr(tag, 'html', 'fetch failed', err);
    return sendError(res, 502, `无法连接源站：${err.message}`, tag);
  }

  const ctRaw = response.headers.get('content-type') || '';
  if (!isHtmlMime(getMimeType(ctRaw))) {
    log(tag, 'html', 'content-type not html, relay', { ct: ctRaw });
    return relayResponse(response, res, tag);
  }

  const enc = response.headers.get('content-encoding');
  if (enc && enc !== 'identity') {
    log(tag, 'html', 'compressed, relay', { enc });
    return relayResponse(response, res, tag);
  }

  const declaredLen = parseInt(response.headers.get('content-length') || '0', 10);
  if (declaredLen > HTML_MAX_BYTES) {
    log(tag, 'html', 'too large (declared), relay', { declaredLen });
    return relayResponse(response, res, tag);
  }

  let rawBuf;
  try {
    rawBuf = Buffer.from(await response.arrayBuffer());
  } catch (err) {
    logErr(tag, 'html', 'read failed', err);
    return sendError(res, 502, `读取 HTML 失败：${err.message}`, tag);
  }

  if (rawBuf.length > HTML_MAX_BYTES) {
    log(tag, 'html', 'too large (actual), passthrough', { size: rawBuf.length });
    return sendBufferedResponse(res, response, rawBuf);
  }

  const finalUrl = response.url || targetUrl;
  const t0 = Date.now();
  const outBuf = rewriteHtmlBody(rawBuf, ctRaw, finalUrl, options);
  if (!outBuf) {
    log(tag, 'html', 'rewrite failed, passthrough', {
      size: rawBuf.length,
      ms: Date.now() - t0
    });
    return sendBufferedResponse(res, response, rawBuf);
  }

  log(tag, 'html', 'rewritten', {
    in: rawBuf.length,
    out: outBuf.length,
    ms: Date.now() - t0
  });

  res.statusCode = response.status;
  for (const [k, v] of response.headers) {
    const lk = k.toLowerCase();
    if (HOP_BY_HOP.has(lk)) continue;
    if (lk === 'content-length' || lk === 'content-encoding') continue;
    res.setHeader(k, v);
  }

  let outCT = ctRaw;
  try {
    const parsed = contentType.parse(ctRaw);
    parsed.parameters.charset = 'utf-8';
    outCT = contentType.format(parsed);
  } catch { outCT = 'text/html; charset=utf-8'; }

  res.setHeader('Content-Type', outCT);
  res.setHeader('Content-Length', String(outBuf.length));
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
  res.end(outBuf);
}

function sendBufferedResponse(res, response, buf) {
  res.statusCode = response.status;
  for (const [k, v] of response.headers) {
    const lk = k.toLowerCase();
    if (HOP_BY_HOP.has(lk)) continue;
    if (lk === 'content-length') continue;
    res.setHeader(k, v);
  }
  res.setHeader('Content-Length', String(buf.length));
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
  res.end(buf);
}

// ═══════════════════════════════════════════════
// 多分片
// ═══════════════════════════════════════════════
async function streamMultiChunk(req, res, targetUrl, headers, totalSize, upstreamHeaders, options, tag) {
  const chunkCount = pickChunkCount(totalSize);
  const ranges = splitRanges(totalSize, chunkCount);

  log(tag, 'chunk', 'start', {
    totalSize,
    chunks: chunkCount,
    concurrency: Math.min(chunkCount, MAX_CONCURRENCY)
  });

  res.statusCode = 200;
  res.setHeader('Content-Type', upstreamHeaders.get('content-type') || 'application/octet-stream');
  res.setHeader('Content-Length', String(totalSize));
  res.setHeader('Accept-Ranges', 'bytes');

  for (const [k, v] of upstreamHeaders) {
    const lk = k.toLowerCase();
    if (HOP_BY_HOP.has(lk)) continue;
    if (lk === 'content-length' || lk === 'content-type'
        || lk === 'content-range' || lk === 'accept-ranges') continue;
    res.setHeader(k, v);
  }
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);

  const buffers = new Array(chunkCount).fill(null);
  let writeIndex = 0, nextIndex = 0, failed = null, aborted = false;
  let doneCount = 0;

  res.on('close', () => {
    if (!res.writableEnded) {
      aborted = true;
      log(tag, 'chunk', 'client closed', { writeIndex, doneCount, total: chunkCount });
    }
  });

  const worker = async () => {
    while (true) {
      if (failed || aborted) return;
      while (!failed && !aborted && (nextIndex - writeIndex) >= MAX_INFLIGHT) {
        await sleep(20);
      }
      if (failed || aborted) return;
      const i = nextIndex++;
      if (i >= chunkCount) return;

      try {
        const buf = await fetchChunkWithRetry(targetUrl, headers, ranges[i], options, tag, i, chunkCount);
        if (failed || aborted) return;
        buffers[i] = buf;
        doneCount++;

        while (writeIndex < chunkCount && buffers[writeIndex] !== null) {
          const chunk = buffers[writeIndex];
          buffers[writeIndex] = null;
          try {
            await writeWithBackpressure(res, chunk);
          } catch (e) { failed = e; return; }
          writeIndex++;
        }
      } catch (err) { failed = err; return; }
    }
  };

  const concurrency = Math.min(chunkCount, MAX_CONCURRENCY);
  await Promise.all(Array.from({ length: concurrency }, () => worker().catch(() => {})));

  if (failed && !aborted) {
    logErr(tag, 'chunk', 'failed', failed);
    try { res.destroy(); } catch (_) {}
    return;
  }
  if (!aborted) {
    log(tag, 'chunk', 'completed', { total: chunkCount, ms: 0 });
    try { res.end(); } catch (_) {}
  }
}

function writeWithBackpressure(res, chunk) {
  if (res.write(chunk)) return Promise.resolve();

  return new Promise((resolve, reject) => {
    const onDrain = () => { cleanup(); resolve(); };
    const onClose = () => { cleanup(); reject(new Error('client closed')); };
    const onError = (err) => { cleanup(); reject(err); };
    const cleanup = () => {
      res.off('drain', onDrain);
      res.off('close', onClose);
      res.off('error', onError);
    };
    res.once('drain', onDrain);
    res.once('close', onClose);
    res.once('error', onError);
  });
}

async function fetchChunkWithRetry(targetUrl, headers, range, options, tag, idx, total) {
  let lastErr;
  for (let attempt = 0; attempt < CHUNK_MAX_RETRY; attempt++) {
    let response;
    try {
      response = await safeFetch(targetUrl, {
        method: 'GET',
        headers: { ...headers, Range: `bytes=${range.start}-${range.end}` },
        signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
      }, options, tag);
    } catch (err) {
      lastErr = err;
      if (tag) log(tag, 'chunk', 'retry', { idx, attempt, err: err.message });
      if (attempt < CHUNK_MAX_RETRY - 1) {
        await sleep(400 * Math.pow(2, attempt) + Math.random() * 200);
      }
      continue;
    }

    if (response.status === 429 || response.status >= 500) {
      lastErr = new Error(`HTTP ${response.status}`);
      cancelBody(response);
      if (tag) log(tag, 'chunk', 'retryable status', { idx, attempt, status: response.status });
      await sleep(400 * Math.pow(2, attempt) + Math.random() * 200);
      continue;
    }
    if (response.status !== 206) {
      cancelBody(response);
      throw new Error(`源站不支持分片：HTTP ${response.status}`);
    }
    try {
      const buf = Buffer.from(await response.arrayBuffer());
      if (tag && (attempt > 0 || idx < 3 || idx >= total - 3)) {
        log(tag, 'chunk', 'ok', { idx, attempt, bytes: buf.length });
      }
      return buf;
    } catch (err) { lastErr = err; }
  }
  throw lastErr || new Error('chunk download failed');
}

function pickChunkCount(totalSize) {
  const TARGET = 2 * 1024 * 1024;
  const MAX = 256;
  if (totalSize <= TARGET) return 1;
  return Math.min(MAX, Math.ceil(totalSize / TARGET));
}

function splitRanges(totalSize, count) {
  const cs = Math.ceil(totalSize / count);
  const ranges = [];
  for (let i = 0; i < count; i++) {
    const start = i * cs;
    const end = Math.min(start + cs - 1, totalSize - 1);
    if (start > end) break;
    ranges.push({ start, end });
  }
  return ranges;
}

function parseContentRangeTotal(cr) {
  const m = cr.match(/\/(\d+)\s*$/);
  return m ? parseInt(m[1], 10) : 0;
}

// ═══════════════════════════════════════════════
// POST / PUT / PATCH / DELETE
// ═══════════════════════════════════════════════
async function handleForward(req, res, targetUrl, options, tag) {
  const cl = req.headers['content-length'];
  if (cl && parseInt(cl, 10) > MAX_BODY_BYTES) {
    log(tag, 'forward', 'body too large (declared)', { cl });
    return sendError(res, 413, '请求体过大，超过 4 MB 限制', tag);
  }

  let body;
  try {
    body = await readRequestBody(req);
  } catch (err) {
    if (err.message === 'BODY_TOO_LARGE') {
      log(tag, 'forward', 'body too large (actual)');
      return sendError(res, 413, '请求体过大', tag);
    }
    logErr(tag, 'forward', 'read body failed', err);
    return sendError(res, 400, `读取请求体失败：${err.message}`, tag);
  }

  log(tag, 'forward', 'sending', { method: req.method, bodyBytes: body.length });

  const headers = buildForwardHeaders(req);

  let response;
  try {
    response = await safeFetch(targetUrl, {
      method: req.method,
      headers,
      body: body.length > 0 ? body : undefined,
      signal: AbortSignal.timeout(CHUNK_TIMEOUT_MS)
    }, options, tag);
  } catch (err) {
    logErr(tag, 'forward', 'fetch failed', err);
    return sendError(res, 502, `无法连接源站：${err.message}`, tag);
  }
  return relayResponse(response, res, tag);
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

  if (req.body != null) {
    if (Buffer.isBuffer(req.body)) {
      if (req.body.length > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
      return req.body;
    }
    if (typeof req.body === 'string') {
      const b = Buffer.from(req.body);
      if (b.length > MAX_BODY_BYTES) throw new Error('BODY_TOO_LARGE');
      return b;
    }
  }
  return Buffer.alloc(0);
}

// ═══════════════════════════════════════════════
// 响应中继
// ═══════════════════════════════════════════════
async function relayResponse(response, res, tag) {
  res.statusCode = response.status;

  const contentEnc = response.headers.get('content-encoding');
  const skipLength = contentEnc && contentEnc !== 'identity';

  for (const [key, value] of response.headers) {
    const lower = key.toLowerCase();
    if (HOP_BY_HOP.has(lower)) continue;
    if (lower === 'content-length' && skipLength) continue;
    res.setHeader(key, value);
  }
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);

  if (!response.body) {
    if (tag) log(tag, 'relay', 'no body', { status: response.status });
    return res.end();
  }

  if (tag) log(tag, 'relay', 'streaming', {
    status: response.status,
    ct: response.headers.get('content-type'),
    cl: response.headers.get('content-length')
  });

  const nodeStream = Readable.fromWeb(response.body);
  const t0 = Date.now();
  let bytes = 0;

  nodeStream.on('data', (c) => { bytes += c.length; });

  await new Promise((resolve) => {
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      try { nodeStream.destroy(); } catch (_) {}
      if (tag) log(tag, 'relay', 'done', { bytes, ms: Date.now() - t0 });
      resolve();
    };
    res.on('close', finish);
    nodeStream.on('error', (e) => {
      if (tag) logErr(tag, 'relay', 'stream error', e);
      try { res.end(); } catch (_) {}
      finish();
    });
    nodeStream.pipe(res).on('finish', finish);
  });
}

function cancelBody(response) {
  try {
    if (response && response.body && typeof response.body.cancel === 'function') {
      response.body.cancel().catch(() => {});
    }
  } catch (_) {}
}

// ═══════════════════════════════════════════════
// URL 解析
// ═══════════════════════════════════════════════
function parseRequest(req) {
  const raw = req.url || '';

  // 标准代理模式：GET http://example.com/path HTTP/1.1
  if (/^https?:\/\//i.test(raw)) {
    try {
      const u = new URL(raw);
      const { query, white } = extractWhite(u.search.slice(1));
      u.search = query ? '?' + query : '';
      return { targetUrl: u.href, parsedUrl: u, options: { white } };
    } catch { return null; }
  }

  // 路径模式：/https://example.com/path?x=1
  const qIdx = raw.indexOf('?');
  let path = qIdx >= 0 ? raw.slice(0, qIdx) : raw;
  let queryStr = qIdx >= 0 ? raw.slice(qIdx + 1) : '';

  if (path.startsWith('/')) path = path.slice(1);
  try { path = decodeURIComponent(path); } catch (_) {}
  path = path.replace(/^(https?):\/(?!\/)/i, '$1://');

  if (!/^https?:\/\//i.test(path)) {
    if (/^[a-z0-9.-]+\.[a-z]{2,}/i.test(path)) path = 'https://' + path;
    else return null;
  }

  const { query, white } = extractWhite(queryStr);
  const targetUrl = path + (query ? '?' + query : '');

  let parsedUrl;
  try { parsedUrl = new URL(targetUrl); } catch { return null; }
  if (parsedUrl.protocol !== 'http:' && parsedUrl.protocol !== 'https:') return null;

  return { targetUrl, parsedUrl, options: { white } };
}

function extractWhite(query) {
  if (!query) return { query: '', white: false };
  const parts = query.split('&');
  const kept = [];
  let white = false;

  for (const part of parts) {
    if (!part) continue;
    const eq = part.indexOf('=');
    const rawKey = eq >= 0 ? part.slice(0, eq) : part;
    const rawVal = eq >= 0 ? part.slice(eq + 1) : '';

    let key = rawKey;
    try { key = decodeURIComponent(rawKey); } catch (_) {}

    if (key === 'white') {
      let val = rawVal;
      try { val = decodeURIComponent(rawVal); } catch (_) {}
      if (val.toUpperCase() === 'Y') white = true;
      continue;
    }
    kept.push(part);
  }
  return { query: kept.join('&'), white };
}

// ═══════════════════════════════════════════════
// HTML 重写
// ═══════════════════════════════════════════════
function detectCharset(buf, httpCT) {
  if (buf.length >= 3 && buf[0] === 0xEF && buf[1] === 0xBB && buf[2] === 0xBF) return 'utf-8';
  if (buf.length >= 2 && buf[0] === 0xFE && buf[1] === 0xFF) return 'utf-16be';
  if (buf.length >= 2 && buf[0] === 0xFF && buf[1] === 0xFE) return 'utf-16le';

  if (httpCT) {
    try {
      const p = contentType.parse(httpCT);
      if (p.parameters.charset) return normalizeCharset(p.parameters.charset);
    } catch {}
  }

  const head = buf.slice(0, 4096).toString('latin1');
  let m = head.match(/<meta[^>]+charset\s*=\s*["']?\s*([a-z0-9_\-]+)/i);
  if (m) return normalizeCharset(m[1]);
  m = head.match(/<meta[^>]+content\s*=\s*["'][^"']*charset\s*=\s*([a-z0-9_\-]+)/i);
  if (m) return normalizeCharset(m[1]);
  return 'utf-8';
}

function normalizeCharset(cs) {
  const s = String(cs).trim().toLowerCase().replace(/^["']|["']$/g, '');
  if (!s) return 'utf-8';
  if (s === 'gb2312' || s === 'gb_2312-80') return 'gbk';
  return s;
}

function rewriteHtmlBody(rawBuf, ctRaw, baseUrl, options) {
  const charset = detectCharset(rawBuf, ctRaw);
  let html;
  try { html = iconv.decode(rawBuf, charset); }
  catch { html = rawBuf.toString('utf8'); }

  let doc;
  try { doc = parse5.parse(html); } catch { return null; }

  const ctx = buildContext(doc, baseUrl, options);
  rewriteDom(doc, ctx);

  let out;
  try { out = parse5.serialize(doc); } catch { return null; }
  return Buffer.from(out, 'utf8');
}

function buildContext(doc, baseUrl, options) {
  let base;
  try { base = new URL(baseUrl); } catch { base = null; }

  let hasBase = false;
  walkNode(doc, (node) => {
    if (hasBase) return;
    if (node.tagName === 'base' && node.attrs) {
      const href = getAttr(node, 'href');
      if (href) {
        try { base = new URL(href, base || baseUrl); hasBase = true; } catch (_) {}
      }
    }
  });

  return { base, white: !!options.white, whiteQS: options.white ? 'white=Y' : '' };
}

const URL_ATTRS = new Set([
  'src', 'href', 'action', 'poster', 'formaction', 'background',
  'cite', 'longdesc', 'usemap', 'manifest', 'ping'
]);

function tuneVideoTag(node, ctx) {
  if (!node.attrs) return;
  node.attrs = node.attrs.filter((a) => a.name.toLowerCase() !== 'autoplay');

  const has = node.attrs.find((a) => a.name.toLowerCase() === 'preload');
  if (has) has.value = 'metadata';
  else node.attrs.push({ name: 'preload', value: 'metadata' });

  const poster = node.attrs.find((a) => a.name.toLowerCase() === 'poster');
  if (poster) {
    poster.value = toProxyUrl(poster.value, ctx, { keepHash: false });
  }
}

function rewriteDom(doc, ctx) {
  walkNode(doc, (node) => {
    if (!node.tagName || !node.attrs) return;

    if (node.tagName === 'video') tuneVideoTag(node, ctx);

    for (const attr of node.attrs) {
      const n = attr.name.toLowerCase();

      if (URL_ATTRS.has(n)) {
        attr.value = toProxyUrl(attr.value, ctx, { keepHash: true });
        continue;
      }
      if (n === 'srcset' || n === 'imagesrcset') {
        attr.value = rewriteSrcset(attr.value, ctx);
        continue;
      }
      if (n === 'style') {
        attr.value = rewriteCssUrls(attr.value, ctx);
        continue;
      }
      if (n === 'content' && node.tagName === 'meta') {
        const he = (getAttr(node, 'http-equiv') || '').toLowerCase();
        if (he === 'refresh') attr.value = rewriteMetaRefresh(attr.value, ctx);
      }
      if (n === 'data-src' || n === 'data-original' || n === 'data-href' || n === 'data-url') {
        attr.value = toProxyUrl(attr.value, ctx, { keepHash: true });
      }
    }

    if (node.tagName === 'style' && node.childNodes) {
      for (const child of node.childNodes) {
        if (child.nodeName === '#text' && typeof child.value === 'string') {
          child.value = rewriteCssUrls(child.value, ctx);
        }
      }
    }

    if (REWRITE_SCRIPT && node.tagName === 'script' && node.childNodes) {
      const type = (getAttr(node, 'type') || '').toLowerCase();
      const isJs = !type || /javascript|ecmascript|module/.test(type);
      if (isJs) {
        for (const child of node.childNodes) {
          if (child.nodeName === '#text' && typeof child.value === 'string') {
            const r = rewriteInlineScript(child.value, ctx);
            if (r !== null) child.value = r;
          }
        }
      }
    }
  });
}

function toProxyUrl(raw, ctx, { keepHash = true } = {}) {
  if (raw == null) return raw;
  const s = String(raw).trim();
  if (!s) return raw;
  if (/^(?:data|javascript|mailto|tel|blob|about|chrome|file|ws|wss):/i.test(s)) return raw;
  if (s.startsWith('#')) return raw;

  let abs;
  try { abs = new URL(s, ctx.base); } catch { return raw; }
  if (abs.protocol !== 'http:' && abs.protocol !== 'https:') return raw;

  let href = abs.href, hash = '';
  if (keepHash) {
    const i = href.indexOf('#');
    if (i >= 0) { hash = href.slice(i); href = href.slice(0, i); }
  } else {
    const i = href.indexOf('#');
    if (i >= 0) href = href.slice(0, i);
  }

  if (ctx.whiteQS) href += (href.includes('?') ? '&' : '?') + ctx.whiteQS;
  return '/' + href + hash;
}

function rewriteSrcset(value, ctx) {
  if (!value) return value;
  return value.split(',').map((seg) => {
    const t = seg.trim();
    if (!t) return t;
    const sp = t.split(/\s+/);
    sp[0] = toProxyUrl(sp[0], ctx, { keepHash: false });
    return sp.join(' ');
  }).join(', ');
}

function rewriteCssUrls(css, ctx) {
  if (!css) return css;
  css = css.replace(
    /url\(\s*(?:(['"])([^'"]*)\1|([^)'"\s]+))\s*\)/gi,
    (m, q, u1, u2) => {
      const u = u1 != null ? u1 : u2;
      const nu = toProxyUrl(u, ctx, { keepHash: false });
      return q ? `url(${q}${nu}${q})` : `url(${nu})`;
    }
  );
  css = css.replace(
    /(@import\s+)(['"])([^'"]+)\2/gi,
    (m, pre, q, u) => pre + q + toProxyUrl(u, ctx, { keepHash: false }) + q
  );
  return css;
}

function rewriteMetaRefresh(value, ctx) {
  if (!value) return value;
  return value.replace(
    /(;\s*url\s*=\s*)(['"]?)([^'";]+)\2/i,
    (m, pre, q, u) => pre + q + toProxyUrl(u, ctx, { keepHash: false }) + q
  );
}

function rewriteInlineScript(src, ctx) {
  if (!src || src.length > 2 * 1024 * 1024) return null;

  let ast;
  try {
    ast = acorn.parse(src, {
      ecmaVersion: 'latest', sourceType: 'script',
      allowReturnOutsideFunction: true, allowHashBang: true
    });
  } catch {
    try { ast = acorn.parse(src, { ecmaVersion: 'latest', sourceType: 'module' }); }
    catch { return null; }
  }

  const edits = [];
  const visitLiteral = (node) => {
    if (typeof node.value !== 'string') return;
    if (!isLikelyUrl(node.value)) return;
    const rewritten = toProxyUrl(node.value, ctx, { keepHash: true });
    if (rewritten === node.value) return;
    const q = src[node.start] === '"' ? '"' : "'";
    edits.push({ start: node.start, end: node.end, value: q + escapeJsString(rewritten, q) + q });
  };

  try {
    walk.simple(ast, {
      Literal: visitLiteral,
      TemplateLiteral(node) {
        if (node.expressions.length === 0 && node.quasis.length === 1) {
          const raw = node.quasis[0].value.cooked;
          if (typeof raw === 'string' && isLikelyUrl(raw)) {
            const rewritten = toProxyUrl(raw, ctx, { keepHash: true });
            if (rewritten !== raw) {
              edits.push({
                start: node.start, end: node.end,
                value: '`' + escapeTemplateString(rewritten) + '`'
              });
            }
          }
        }
      }
    });
  } catch { return null; }

  if (edits.length === 0) return null;
  edits.sort((a, b) => b.start - a.start);
  let out = src;
  for (const e of edits) out = out.slice(0, e.start) + e.value + out.slice(e.end);
  return out;
}

function isLikelyUrl(s) {
  if (!s || s.length < 4) return false;
  if (/^https?:\/\//i.test(s)) return true;
  if (/^\/\//.test(s)) return true;
  if (/^\/[^/*]/.test(s)) return true;
  if (/^\.\.?\//.test(s)) return true;
  return false;
}

function escapeJsString(s, quote) {
  return s.replace(/\\/g, '\\\\')
    .replace(new RegExp(quote, 'g'), '\\' + quote)
    .replace(/\n/g, '\\n').replace(/\r/g, '\\r')
    .replace(/\u2028/g, '\\u2028').replace(/\u2029/g, '\\u2029');
}

function escapeTemplateString(s) {
  return s.replace(/\\/g, '\\\\').replace(/`/g, '\\`')
    .replace(/\$\{/g, '\\${')
    .replace(/\u2028/g, '\\u2028').replace(/\u2029/g, '\\u2029');
}

function walkNode(node, fn) {
  fn(node);
  if (node.childNodes) for (const c of node.childNodes) walkNode(c, fn);
  if (node.content) walkNode(node.content, fn);
}

function getAttr(node, name) {
  if (!node.attrs) return null;
  for (const a of node.attrs) if (a.name === name) return a.value;
  return null;
}

// ═══════════════════════════════════════════════
// 工具
// ═══════════════════════════════════════════════
function buildForwardHeaders(req, override = {}) {
  const headers = {};
  const skip = new Set([
    'host', 'connection', 'content-length',
    'transfer-encoding', 'proxy-authorization',
    'range', 'if-range'
  ]);
  for (const [k, v] of Object.entries(req.headers)) {
    if (skip.has(k.toLowerCase())) continue;
    headers[k] = v;
  }
  headers['accept-encoding'] = 'identity';
  return Object.assign(headers, override);
}

function sendError(res, statusCode, msg, tag) {
  if (res.headersSent) { try { res.destroy(); } catch (_) {} return; }
  const body = Buffer.from(msg + '\n', 'utf8');
  res.statusCode = statusCode;
  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  res.setHeader('Content-Length', String(body.length));
  for (const [k, v] of Object.entries(CORS_HEADERS)) res.setHeader(k, v);
  res.end(body);
  if (tag) log(tag, 'error', 'sent', { status: statusCode, msg });
}