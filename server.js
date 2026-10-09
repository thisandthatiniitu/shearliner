#!/usr/bin/env node
'use strict';
/*
  Shearline multiplayer server
  ----------------------------
  One file, no dependencies: it only needs Node.js 16 or newer (https://nodejs.org).

  It does two jobs:
    1. Serves the game page, so every player simply opens this server's address in a browser.
    2. Relays messages between the players in a lobby (create a lobby, share the 4-letter code, others join).

  Run it:           node server.js
  Other port:       PORT=3000 node server.js          (Windows PowerShell:  $env:PORT=3000; node server.js)

  SAME WI-FI:       run it on one computer. It prints a "Same Wi-Fi" address such as http://192.168.1.23:8080.
                    Everyone on that Wi-Fi opens that address. If your firewall asks, allow Node.js on private networks.
  FROM ANYWHERE:    the server has to be reachable from the internet. Either
                      - put server.js and shearline.html on any Node host (Render, Railway, Fly.io, a VPS, ...).
                        Start command: node server.js   (it reads the PORT variable that hosts provide), or
                      - run it on your computer and expose it with a tunnel (for example: cloudflared tunnel --url http://localhost:8080
                        or ngrok http 8080) or by forwarding the port on your router.
                    Then send your friends the public address and your lobby code.

  Keep server.js and shearline.html in the same folder (or set GAME_FILE to the game's path).
  There are no accounts and no anti-cheat: it is meant for playing with friends.
*/
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const os = require('os');

const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const MAX_FRAME = 16 * 1024;                  // biggest message accepted from a player
const MAX_PLAYERS = 8;
const MAX_CLIENTS = 400;
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const RELAY_ALL = new Set(['s', 'kill', 'chat', 'slam']);            // sent to everyone else in the lobby
const RELAY_TO = new Set(['hit', 'parried', 'deflect']);     // sent to one player (field "to")

function createServer(opts) {
  opts = opts || {};
  const gameFile = opts.gameFile || process.env.GAME_FILE || path.join(__dirname, 'shearline.html');
  const heartbeatMs = opts.heartbeatMs || 15000;
  const log = opts.quiet ? () => {} : (...a) => console.log(new Date().toISOString().slice(11, 19), ...a);
  const lobbies = new Map();
  const clients = new Set();
  let nextId = 1;

  /* ---------- WebSocket framing (RFC 6455) ---------- */
  function encodeFrame(opcode, payload) {
    const len = payload.length; let header;
    if (len < 126) { header = Buffer.alloc(2); header[1] = len; }
    else if (len < 65536) { header = Buffer.alloc(4); header[1] = 126; header.writeUInt16BE(len, 2); }
    else { header = Buffer.alloc(10); header[1] = 127; header.writeBigUInt64BE(BigInt(len), 2); }
    header[0] = 0x80 | opcode;
    return Buffer.concat([header, payload]);
  }
  function rawSend(c, buf) { if (!c.closed && c.socket.writable) { try { c.socket.write(buf); } catch (e) { /* socket is going away */ } } }
  function send(c, obj) { rawSend(c, encodeFrame(0x1, Buffer.from(JSON.stringify(obj), 'utf8'))); }
  function closeWith(c, code) {
    if (c.closed) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code, 0);
    rawSend(c, encodeFrame(0x8, p));
    try { c.socket.end(); } catch (e) { /* already closed */ }
    setTimeout(() => { try { c.socket.destroy(); } catch (e) { /* ignore */ } }, 500).unref();
    cleanup(c);
  }
  function parse(c) {
    for (;;) {
      const b = c.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0, rsv = b[0] & 0x70, op = b[0] & 0x0f, masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f, off = 2;
      if (rsv) return closeWith(c, 1002);
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) {
        if (b.length < 10) return;
        const big = b.readBigUInt64BE(2);
        if (big > BigInt(MAX_FRAME)) return closeWith(c, 1009);
        len = Number(big); off = 10;
      }
      if (!masked) return closeWith(c, 1002);                       // clients must mask their frames
      if (len > MAX_FRAME) return closeWith(c, 1009);
      if (op >= 8 && (!fin || len > 125)) return closeWith(c, 1002); // control frames are short and unfragmented
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) data[i] ^= mask[i & 3];
      c.buf = b.subarray(off + 4 + len);
      onFrame(c, fin, op, data);
      if (c.closed) return;
    }
  }
  function onFrame(c, fin, op, data) {
    c.alive = true;
    if (op === 0x8) { closeWith(c, 1000); return; }
    if (op === 0x9) { rawSend(c, encodeFrame(0xA, data)); return; }
    if (op === 0xA) return;
    if (op === 0x1 || op === 0x2) {
      if (c.frag) return closeWith(c, 1002);
      c.frag = { op, chunks: [data], size: data.length };
    } else if (op === 0x0) {
      if (!c.frag) return closeWith(c, 1002);
      c.frag.chunks.push(data); c.frag.size += data.length;
      if (c.frag.size > MAX_FRAME) return closeWith(c, 1009);
    } else return closeWith(c, 1002);
    if (!fin) return;
    const frag = c.frag; c.frag = null;
    if (frag.op === 0x1) onMessage(c, Buffer.concat(frag.chunks).toString('utf8'));
  }

  /* ---------- lobbies ---------- */
  function cleanName(n) { return String(n == null ? '' : n).replace(/[^\w .\-]/g, '').trim().slice(0, 16) || 'Player'; }
  function uniqueName(lobby, n) {
    const taken = new Set([...lobby.members.values()].map(m => m.name.toLowerCase()));
    if (!taken.has(n.toLowerCase())) return n;
    for (let i = 2; i < 99; i++) { const t = (n.slice(0, 13) + ' ' + i); if (!taken.has(t.toLowerCase())) return t; }
    return n;
  }
  function newCode() {
    for (let tries = 0; tries < 1000; tries++) {
      let code = ''; for (let i = 0; i < 4; i++) code += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
      if (!lobbies.has(code)) return code;
    }
    return null;
  }
  function snapshot(lobby) {
    return { code: lobby.code, host: lobby.hostId, target: lobby.target, state: lobby.state,
      players: [...lobby.members.values()].map(m => ({ id: m.id, name: m.name, col: m.col })) };
  }
  function broadcast(lobby, obj, exceptId) { for (const m of lobby.members.values()) if (m.id !== exceptId) send(m, obj); }
  function pushPlayers(lobby) { broadcast(lobby, Object.assign({ t: 'players' }, snapshot(lobby))); }
  function freeColor(lobby) {
    const used = new Set([...lobby.members.values()].map(m => m.col));
    for (let i = 0; i < MAX_PLAYERS; i++) if (!used.has(i)) return i;
    return 0;
  }
  function leaveLobby(c) {
    const lobby = c.lobby; if (!lobby) return;
    c.lobby = null; lobby.members.delete(c.id);
    if (lobby.members.size === 0) { lobbies.delete(lobby.code); log('lobby', lobby.code, 'closed'); return; }
    if (lobby.hostId === c.id) lobby.hostId = lobby.members.keys().next().value;
    broadcast(lobby, { t: 'left', id: c.id });
    if (lobby.state === 'playing' && lobby.members.size < 2) { lobby.state = 'waiting'; broadcast(lobby, { t: 'end', winner: null, reason: 'Not enough players left.' }); }
    pushPlayers(lobby);
  }
  function cleanup(c) {
    if (c.closed) return;
    c.closed = true; clients.delete(c);
    leaveLobby(c);
  }
  function err(c, msg) { send(c, { t: 'err', msg }); }
  function onMessage(c, text) {
    // light rate limit: 150 messages/second sustained, short bursts allowed
    const now = Date.now(); c.tokens = Math.min(250, c.tokens + (now - c.lastTok) * 0.15); c.lastTok = now;
    if (c.tokens < 1) { if (++c.drops > 600) closeWith(c, 1008); return; }
    c.tokens -= 1;
    let m; try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m !== 'object' || typeof m.t !== 'string') return;
    switch (m.t) {
      case 'host': {
        if (c.lobby) return err(c, 'Leave your current lobby first.');
        const code = newCode(); if (!code) return err(c, 'Server is busy. Try again.');
        const target = Math.max(5, Math.min(50, parseInt(m.target, 10) || 20));
        const lobby = { code, hostId: c.id, target, state: 'waiting', members: new Map() };
        c.name = cleanName(m.name); c.col = 0; c.lobby = lobby; lobby.members.set(c.id, c); lobbies.set(code, lobby);
        log('lobby', code, 'created by', c.name);
        send(c, Object.assign({ t: 'joined', id: c.id }, snapshot(lobby)));
        break;
      }
      case 'join': {
        if (c.lobby) return err(c, 'Leave your current lobby first.');
        const lobby = lobbies.get(String(m.code || '').toUpperCase().trim());
        if (!lobby) return err(c, 'No lobby with that code.');
        if (lobby.state === 'playing') return err(c, 'That match is already in progress.');
        if (lobby.members.size >= MAX_PLAYERS) return err(c, 'That lobby is full (' + MAX_PLAYERS + ' players).');
        c.name = uniqueName(lobby, cleanName(m.name)); c.col = freeColor(lobby); c.lobby = lobby; lobby.members.set(c.id, c);
        log(c.name, 'joined', lobby.code, '(' + lobby.members.size + ')');
        send(c, Object.assign({ t: 'joined', id: c.id }, snapshot(lobby)));
        broadcast(lobby, Object.assign({ t: 'players' }, snapshot(lobby)), c.id);
        break;
      }
      case 'leave': leaveLobby(c); send(c, { t: 'left', id: c.id, you: true }); break;
      case 'target': {
        const lobby = c.lobby; if (!lobby || lobby.hostId !== c.id || lobby.state !== 'waiting') return;
        lobby.target = Math.max(5, Math.min(50, parseInt(m.target, 10) || 20)); pushPlayers(lobby);
        break;
      }
      case 'start': {
        const lobby = c.lobby; if (!lobby) return;
        if (lobby.hostId !== c.id) return err(c, 'Only the host can start the match.');
        if (lobby.state === 'playing') return;
        if (lobby.members.size < 2) return err(c, 'You need at least 2 players to start.');
        lobby.state = 'playing'; log('lobby', lobby.code, 'match started');
        broadcast(lobby, { t: 'start', target: lobby.target });
        break;
      }
      case 'end': {
        const lobby = c.lobby; if (!lobby || lobby.hostId !== c.id || lobby.state !== 'playing') return;
        lobby.state = 'waiting';
        const winner = typeof m.winner === 'number' && lobby.members.has(m.winner) ? m.winner : null;
        broadcast(lobby, { t: 'end', winner }); pushPlayers(lobby);
        break;
      }
      default: {
        const lobby = c.lobby; if (!lobby) return;
        if (RELAY_ALL.has(m.t)) {
          if (m.t === 'chat') {                                  // tidy the text and stop spam: one message per half second
            const now = Date.now(); if (now - (c.lastChat || 0) < 500) return; c.lastChat = now;
            m.text = String(m.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 120); if (!m.text) return;
          }
          m.from = c.id; broadcast(lobby, m, c.id);
        } else if (RELAY_TO.has(m.t)) {
          const target = lobby.members.get(m.to); if (!target || target.id === c.id) return;
          m.from = c.id; send(target, m);
        }
      }
    }
  }

  /* ---------- HTTP + upgrade ---------- */
  const server = http.createServer((req, res) => {
    const url = req.url.split('?')[0];
    if (url === '/' || url === '/index.html' || url === '/shearline.html') {
      fs.readFile(gameFile, (e, data) => {
        if (e) { res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' }); res.end('Could not read ' + gameFile + '. Keep server.js and shearline.html in the same folder.'); return; }
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }); res.end(data);
      });
    } else if (url === '/health') {
      res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok ' + lobbies.size + ' lobbies ' + clients.size + ' players');
    } else { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('Not found'); }
  });
  server.on('upgrade', (req, socket, head) => {
    const key = req.headers['sec-websocket-key'];
    if (String(req.headers.upgrade || '').toLowerCase() !== 'websocket' || !key || req.headers['sec-websocket-version'] !== '13' || clients.size >= MAX_CLIENTS) {
      socket.end('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n'); return;
    }
    const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
    socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
    socket.setNoDelay(true);
    const c = { id: nextId++, socket, buf: head && head.length ? Buffer.from(head) : Buffer.alloc(0), alive: true, closed: false, frag: null, lobby: null, name: 'Player', col: 0, tokens: 250, lastTok: Date.now(), drops: 0 };
    clients.add(c);
    socket.on('data', chunk => {
      if (c.closed) return;
      c.buf = Buffer.concat([c.buf, chunk]);
      parse(c);                                                       // read every complete message in this chunk first...
      if (!c.closed && c.buf.length > MAX_FRAME + 16) closeWith(c, 1009); // ...then refuse anything that is still an oversized unfinished frame
    });
    socket.on('close', () => cleanup(c));
    socket.on('error', () => cleanup(c));
    if (c.buf.length) parse(c);
  });
  const beat = setInterval(() => {
    for (const c of [...clients]) {
      if (!c.alive) { try { c.socket.destroy(); } catch (e) { /* ignore */ } cleanup(c); continue; }
      c.alive = false; rawSend(c, encodeFrame(0x9, Buffer.alloc(0)));
    }
  }, heartbeatMs);
  beat.unref();

  return {
    server, lobbies, clients,
    listen(port, host) { return new Promise((res, rej) => { server.once('error', rej); server.listen(port, host || '0.0.0.0', () => { server.removeListener('error', rej); res(server.address().port); }); }); },
    close() { clearInterval(beat); for (const c of [...clients]) { try { c.socket.destroy(); } catch (e) { /* ignore */ } } return new Promise(r => server.close(() => r())); }
  };
}

function lanUrls(port) {
  const out = [];
  for (const list of Object.values(os.networkInterfaces())) for (const i of list || []) if ((i.family === 'IPv4' || i.family === 4) && !i.internal) out.push('http://' + i.address + ':' + port);
  return out;
}

if (require.main === module) {
  const PORT = parseInt(process.env.PORT || '8080', 10), HOST = process.env.HOST || '0.0.0.0';
  const app = createServer();
  app.listen(PORT, HOST).then(port => {
    console.log('\nShearline server is running.\n');
    console.log('  On this computer:   http://localhost:' + port);
    const lan = lanUrls(port);
    if (lan.length) lan.forEach((u, i) => console.log((i === 0 ? '  Same Wi-Fi:         ' : '                      ') + u));
    console.log('\n  Open an address above, click ONLINE in the menu, then Host a lobby and share the code.');
    console.log('  For friends outside your Wi-Fi, host this on the internet (see the notes at the top of server.js).\n');
    if (!fs.existsSync(process.env.GAME_FILE || path.join(__dirname, 'shearline.html'))) console.log('  WARNING: shearline.html was not found next to server.js, so the game page cannot be served.\n');
  }).catch(e => { console.error(e.code === 'EADDRINUSE' ? 'Port ' + PORT + ' is already in use. Try: PORT=3000 node server.js' : e); process.exit(1); });
  process.on('SIGINT', () => process.exit(0));
}
module.exports = { createServer, lanUrls };
