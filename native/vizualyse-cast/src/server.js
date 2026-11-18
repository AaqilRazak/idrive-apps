// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Yousaf Khan
/**
 * vizualyse-cast: plays a stream URL on the iDrive 7 instrument cluster or HUD,
 * with its sound through the car's speakers, controlled from a phone page; or
 * CarPlay's own cluster screen (the second CarPlay screen, through hook111).
 *
 * - A web page on the uplink's Wi-Fi address (the phone's hotspot), port
 *   8480, behind a token; the cluster shows its link as a QR code while idle.
 * - ffmpeg (bundled, static) reads the stream through proxy.js, which runs as
 *   the tool's internet uid; mgu-uplink routes only that uid through the
 *   phone. ffmpeg writes I420 frames (stdout) and S16LE 48 kHz audio (fd 3).
 * - Frames go to cluster-render as a video layer; audio to pcm_play.py
 *   (mgu-python), which plays it into SmartXbar: into CarLife's source,
 *   claimed while it plays (speakers.js: the car's speakers at the iDrive
 *   volume, no CarPlay phone needed), or CarPlay's input if they can't be had.
 * - The CarPlay second screen: ffmpeg listens on 127.0.0.1:6111 for hook111's
 *   H.264 (carplay_screen.js) and scales it for the cluster map or the HUD;
 *   a small second output feeds the touch screen's live preview.
 * - The touch screen (touch.js, the platform's touch kit): the iDrive app's
 *   controls by touch in the central screen's app area, while the app's
 *   screen state is open ({"cmd":"touch","on":true}); only where mgu-render
 *   is installed, parked or driving (map settings while driving, as the
 *   car's own controls), and never with a stream on this screen (the same mgu-render client name: one at a
 *   time; it comes back when that stream ends).
 *
 *   node server.js     (root: the render socket, ALSA, nftables)
 */
'use strict';

const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const { spawn } = require('child_process');
const { URL } = require('url');
const qrcode = require('./qrcode.js');
const firewall = require('./firewall.js');
const { ClusterRender } = require('./cluster_render_client.js');
const { Speakers, CARPLAY } = require('./speakers.js');
const consoleOut = require('./console_out.js');
const { startControl } = require('./control.js');
const carplay = require('./carplay_screen.js');
const { Bus } = require('./mqtt_bus.js');
const { CastTouch } = require('./touch.js');

const HERE = __dirname;
const STATE_DIR = process.env.CAST_STATE || '/var/opt/vizualyse-cast/state';
const PORT = Number(process.env.CAST_PORT) || 8480;
const PROXY_PORT = PORT + 1;
const INTERNET_UID = 12999;
const IFNAME = 'wlan0';
const FFMPEG = process.env.CAST_FFMPEG || path.join(HERE, 'ffmpeg');
const PYTHON = '/var/opt/mgu-python/current/bin/python3';
const LEASE = process.env.CAST_LEASE || '/run/mgu-uplink/lease.json';
const UPLINK_STATUS = '/run/mgu-uplink/status.json';
/* the touch screen's touches: the reader (touch_reader.py on mgu-python)
 * and the display's PDUs it copies; CAST_TOUCH_CMD: a stand-in, off the car */
const TOUCH_PYTHON = process.env.CAST_PYTHON || PYTHON;
const TOUCH_IFACE = process.env.CAST_TOUCH_IFACE || 'vlan73';
const TOUCH_SRC = process.env.CAST_TOUCH_SRC || '160.48.199.115';
const TOUCH_FILE = process.env.CAST_TOUCH_FILE || '';
/* above this the car moves (the status's moving: the touch screen says so;
 * it stays up while driving, as the car's own controls do) */
const MAX_KMH = 3;
/* The CarPlay preview (carplay_screen.previewArgs): a second ffmpeg output
 * only where the touch screen can show it (mgu-render installed). It shares
 * the cluster's ffmpeg, so CAST_CARPLAY_PREVIEW=0 leaves that ffmpeg exactly
 * as before 0.4.0 should the preview ever trouble the cluster's stream. */
const PREVIEW_ON = process.env.CAST_CARPLAY_PREVIEW !== '0';

function even(n) { return Math.max(0, Math.round(n / 2) * 2); }
/* cluster-render takes a video at most this wide a multiple of 4. */
function four(n) { return Math.max(4, Math.floor(n / 4) * 4); }

/* Each output: the target, the frame size sent and its rate (within the
 * renderer's 5500 KB/s upload ceiling), and the part of the target used. */
const OUTPUTS = {
    map: { target: 'map', W: 1088, H: 480, w: 512, h: 288, fps: 15, band: null, title: 'Cluster map' },
    /* band: the part of the height the HUD shows clear of its clipped top and
     * the speed; xband: the part of the width its optics show. */
    hud: { target: 'hud', W: 800, H: 480, w: 480, h: 270, fps: 15, band: [0.25, 0.65], xband: [0.17, 0.83], title: 'HUD' },
    /* The central display through mgu-render: a frame file, not cluster-render's upload budget. */
    console: { console: true, w: 640, h: 360, fps: 15, title: 'Media console' },
    none: { title: 'Audio only' },
};

const log = (s) => console.log(new Date().toISOString() + ' ' + s);
/* the car's speakers while something plays with sound: CarLife's source
 * (platform tool/speakers) */
const speakers = new Speakers({ log: log });
/* a player's hold on the speakers ends (its sound ended, or it stopped) */
function releaseSpeakers(p) {
    p.down = true;
    if (p.speakers) { p.speakers = false; speakers.release(); }
}

/* ---- small helpers ------------------------------------------------------- */

function mkdirp(d) { if (!fs.existsSync(d)) { mkdirp(path.dirname(d)); fs.mkdirSync(d, 0o700); } }

function readJson(f) { try { return JSON.parse(fs.readFileSync(f, 'utf8')); } catch (e) { return null; } }

/* The token in the QR link: kept across restarts, so a saved link works. */
function token() {
    const f = path.join(STATE_DIR, 'token');
    try { const t = fs.readFileSync(f, 'utf8').trim(); if (/^[0-9a-f]{16}$/.test(t)) return t; } catch (e) { /* new */ }
    const t = crypto.randomBytes(8).toString('hex');
    mkdirp(STATE_DIR);
    fs.writeFileSync(f, t + '\n', { mode: 0o600 });
    return t;
}

/* The head unit's address on the phone's hotspot, or null. */
function uplinkIp() {
    const l = readJson(LEASE);
    if (l && l.ip) return l.ip;
    const ifs = os.networkInterfaces()[IFNAME] || [];
    const v4 = ifs.filter((a) => a.family === 'IPv4' && !a.internal)[0];
    return v4 ? v4.address : null;
}

/* A URL without its query or credentials, for logs and status. */
function redact(u) {
    try { const x = new URL(u); return x.protocol + '//' + x.host + x.pathname + (x.search ? '?…' : ''); } catch (e) { return '(invalid)'; }
}

/* ---- the cluster: QR code and video layer -------------------------------- */

const TOKEN = token();
const cr = new ClusterRender('vizualyse_cast');

/* Settings kept across restarts in STATE_DIR/settings.json: the service on
 * or off, the QR code on the cluster (off by default: with navigation up
 * the cluster draws its direction list over it; the iDrive page shows it),
 * the CarPlay cluster cards (directions, time / distance; both on), whether the phone is
 * asked to centre its view (the target's safe area; on by default), and the
 * HUD's alternate mode (the wide 1056x384 picture, not centred; off),
 * showBadge (off: the car's badge over the map while no route; "The car's
 * badge" below), perfMode (off: "Experimental performance mode" below) and
 * carplayResume (the CarPlay output the user last picked, for perfMode). */
const SETTINGS_FILE = path.join(STATE_DIR, 'settings.json');
const settings = Object.assign({ enabled: true, clusterQr: false, carplayDirections: true, carplayEta: true, carplayCentre: true, carplayHudAlt: false, showBadge: false, perfMode: false, carplayResume: null }, readJson(SETTINGS_FILE) || {});
settings.carplayCentre = settings.carplayCentre !== false;
settings.carplayHudAlt = settings.carplayHudAlt === true;
settings.carplayDirections = settings.carplayDirections !== false;
settings.carplayEta = settings.carplayEta !== false;
settings.showBadge = settings.showBadge === true;
settings.perfMode = settings.perfMode === true;
settings.carplayResume = settings.carplayResume === 'map' || settings.carplayResume === 'hud' ? settings.carplayResume : null;

/* ---- the car's badge --------------------------------------------------------
 * The model badge (M340i, ...) is not in the map's slot (0x100) but in a small
 * one over it, 0x105 (0x103 on some cars), where BMW's HMI also maps its
 * CarPlay turn box (content 0x1000310) for a route. cluster-render's guide
 * hold covers that slot with an empty scene, so the map shows there, while
 * the box is mapped in it, shown or parked (map status 1, 2 or 3), and a
 * layer on the map lets it (guide_hold, default 1). Where the HMI keeps the
 * box mapped without a route, that covers the badge all the time.
 *
 * showBadge off: Cast's layers let the hold work as cluster-render decides
 * (as before 0.4.2). On: Cast decides from the slot table whether a route is
 * up, and lets the hold work only then:
 *  - released (guide_hold 0): the badge shows. The box mapped and visible in
 *    the slot (map status 1 or 2) is a route: held.
 *  - held: the map has the slot (the CarPlay map and its directions card show
 *    there; neither the badge nor BMW's box). Released once no box is mapped
 *    in either slot for BADGE_RELEASE_MS (the route over).
 * BMW's box can show for a moment at a route's start (from its first report
 * to cluster-render's take-over), as with cluster-render's own hold. Without
 * the slot table (no report yet): held, as cluster-render would. */
const BOX = 0x1000310, BADGE_SLOTS = [0x105, 0x103], BADGE_RELEASE_MS = 5000;
const badge = { hold: true, route: null, since: Date.now(), boxGone: null, text: null, why: 'no report from cluster-render yet' };
function guideHold() { return settings.showBadge ? badge.hold : true; }
delete settings.carplayView;   /* 0.3.6's view setting: the two card switches replace it */
delete settings.carplayShape; delete settings.carplayVignette;   /* 0.3.5's, removed */
function saveSettings() {
    try { mkdirp(STATE_DIR); fs.writeFileSync(SETTINGS_FILE, JSON.stringify(settings) + '\n', { mode: 0o600 }); } catch (e) { log('settings: ' + e.message); }
}
let qrLayer = null, qrUrl = null, qrWanted = settings.clusterQr;

function link() { const ip = uplinkIp(); return ip ? 'http://' + ip + ':' + PORT + '/?t=' + TOKEN : null; }

/* RGBA pixels of the QR code of `text`, black on white with a 4-module quiet
 * zone, `px` pixels a module: { px, size }. */
function qrPixels(text, target) {
    const q = qrcode(0, 'M');
    q.addData(text);
    q.make();
    const n = q.getModuleCount(), m = Math.max(2, Math.floor(target / (n + 8))), size = (n + 8) * m;
    const buf = Buffer.alloc(size * size * 4, 255);
    for (let r = 0; r < n; r++) {
        for (let c = 0; c < n; c++) {
            if (!q.isDark(r, c)) continue;
            for (let y = (r + 4) * m; y < (r + 5) * m; y++) {
                const row = y * size * 4;
                for (let x = (c + 4) * m; x < (c + 5) * m; x++) buf.fill(0, row + x * 4, row + x * 4 + 3);
            }
        }
    }
    return { px: buf, size: size };
}

/* The QR code on the cluster's map area while idle and wanted. A content
 * layer: an overlay alone never takes the area from the cluster's own map. */
function updateQr() {
    /* Shown until the video's first frame: the area is never left empty in
     * between, which would hand it back to the cluster's own map. */
    const url = link(), show = settings.enabled && qrWanted && (!player || !player.frames) && !!url;
    if (url && url !== qrUrl) {
        if (qrLayer) cr.drop(qrLayer);
        const q = qrPixels(url, 300), W = 1088, H = 480;
        /* contend: take the centre from the stock map (cluster-render's
         * take-over), as the Waze map does; without it the layer waits for a
         * free slot, which in Map view never comes. */
        qrLayer = cr.image({ target: 'map', contend: true, guide_hold: guideHold(), x: Math.round((W - q.size) / 2), y: Math.round((H - q.size) / 2),
            w: q.size, h: q.size, iw: q.size, ih: q.size, visible: show });
        cr.pixels(qrLayer, null, q.px);
        qrUrl = url;
        log('qr: ' + url.replace(TOKEN, '<token>') + ' (' + q.size + ' px)');
    } else if (qrLayer) {
        cr.set(qrLayer, { visible: show });
    }
}

/* I420 to the renderer's 4:2:0 atlas: the Y plane, then each chroma row as
 * its U half followed by its V half. */
function atlas(i420, w, h, out) {
    const ySize = w * h, cw = w / 2, ch = h / 2, cSize = cw * ch;
    i420.copy(out, 0, 0, ySize);
    for (let y = 0; y < ch; y++) {
        const row = ySize + y * w;
        i420.copy(out, row, ySize + y * cw, ySize + (y + 1) * cw);
        i420.copy(out, row + cw, ySize + cSize + y * cw, ySize + cSize + (y + 1) * cw);
    }
    return out;
}

/* The largest rect of w:h inside the output's area (or band), centred. */
function placement(o) {
    const a = area(o);
    const s = Math.min(a.W / o.w, a.H / o.h), dw = Math.round(o.w * s), dh = Math.round(o.h * s);
    return { x: a.x + Math.round((a.W - dw) / 2), y: a.y + Math.round((a.H - dh) / 2), w: dw, h: dh };
}

/* The part of a target that is shown: its bands, or all of it. */
function area(o) {
    const x = o.xband ? Math.round(o.W * o.xband[0]) : 0, y = o.band ? Math.round(o.H * o.band[0]) : 0;
    return { x: x, y: y, W: o.xband ? Math.round(o.W * (o.xband[1] - o.xband[0])) : o.W,
        H: o.band ? Math.round(o.H * (o.band[1] - o.band[0])) : o.H };
}

/* ---- the proxy ----------------------------------------------------------- */

let proxy = null;
function startProxy() {
    proxy = spawn(process.execPath, [path.join(HERE, 'proxy.js'), String(PROXY_PORT)],
        { uid: INTERNET_UID, gid: INTERNET_UID, stdio: ['ignore', 'pipe', 'pipe'] });
    proxy.stdout.on('data', (d) => process.stdout.write(d));
    proxy.stderr.on('data', (d) => process.stderr.write(d));
    proxy.on('exit', (code, sig) => {
        log('proxy: exited (' + (sig || code) + ')');
        proxy = null;
        if (!stopping) setTimeout(startProxy, 2000);
    });
}

/* ---- playback ------------------------------------------------------------ */

let player = null;      /* { ff, py, opts, video, started, frames, lastErr[] } */
const consoleVideo = new consoleOut.ConsoleVideo(log);
let last = { state: 'idle' };
let lastPlay = null;    /* the last play's options (with its full URL): the app's Play last */
let restartTimer = null; /* the CarPlay second screen's ffmpeg, started again after it ends */
let restartDelay = 500;  /* doubles after each run without a frame, back to 1 s after one with */

function o0(p) { return OUTPUTS[p.opts.output] || {}; }

/* ---- the other tools' asks (platform tool/mqtt_bus, native/vizualyse-bus) ---
 * While another tool asks for the cluster's or the HUD's video off (Steam
 * while a game runs: the CPU this decoding takes, and cluster-render's
 * upload), a play there is paused (ffmpeg stopped, the layer dropped) and
 * started again once no tool asks. A play started meanwhile waits the same
 * way. A stop, or another play, forgets the paused one. */
const bus = new Bus('vizualyse-cast', { log: log });
const ASK_FOR = { map: 'cluster-video', hud: 'hud-video' };
let paused = null;      /* { opts, by: [{ from, why }] }: a play waiting for the asks to go */

function askedOff(output) { return ASK_FOR[output] ? bus.asked(ASK_FOR[output], 'off') : []; }
function who(by) { return by.map((b) => b.from.replace(/^vizualyse-/, '') + (b.why ? ' (' + b.why + ')' : '')).join(', '); }

function pause(opts, by) {
    paused = { opts: opts, by: by };
    last = { state: 'paused', url: opts.shown, output: opts.output, note: 'paused while ' + who(by) + ' asks for it' };
    log('play: paused on ' + opts.output + ': ' + who(by) + ' asks for ' + ASK_FOR[opts.output] + ' off');
    updateQr();
}

function applyAsks() {
    if (stopping) return;
    if (player && !paused) {
        const by = askedOff(player.opts.output);
        if (by.length) { const opts = player.opts; stopPlayer('paused', true); pause(opts, by); }
    } else if (paused) {
        const by = askedOff(paused.opts.output);
        if (by.length) { paused.by = by; last.note = 'paused while ' + who(by) + ' asks for it'; return; }
        const opts = paused.opts;
        paused = null;
        if (settings.enabled && lastPlay === opts) { log('play: no tool asks any more: started again'); play(opts); }
    }
}
bus.on('asks', applyAsks);

/* keepPaused: a pause stops it, to start again; any other stop forgets a paused play */
function stopPlayer(why, keepPaused) {
    clearTimeout(restartTimer); restartTimer = null;
    if (!keepPaused && paused) {
        last = { state: 'idle', note: why, url: paused.opts.shown, output: paused.opts.output, frames: 0 };
        paused = null;
    }
    const p = player;
    if (!p) return;
    player = null;
    p.stopped = why;
    try { p.ff.kill('SIGTERM'); } catch (e) { /* gone */ }
    setTimeout(() => { try { p.ff.kill('SIGKILL'); } catch (e) { /* gone */ } }, 3000);
    if (p.py) try { p.py.kill('SIGTERM'); } catch (e) { /* gone */ }
    releaseSpeakers(p);
    if (p.video) cr.drop(p.video);
    if (o0(p).console) { consoleVideo.stop(); setImmediate(resumeTouch); }
    if (p.opts.source === 'carplay') touch.previewEnd();
    log('play: stopped (' + why + ') after ' + p.frames + ' frames');
    last = { state: 'idle', note: why, url: p.opts.shown, output: p.opts.output, frames: p.frames };
    updateQr();
}

function play(opts) {
    stopPlayer('replaced');
    lastPlay = opts;
    const asked = askedOff(opts.output);
    if (asked.length) { pause(opts, asked); return; }
    const cp = opts.source === 'carplay';
    /* the experimental performance mode: the CarPlay picture only */
    const perf = cp && settings.perfMode;
    let o = OUTPUTS[opts.output];
    if (cp) {
        /* the size the phone should draw at (from its next connection), and
         * what goes on to the renderer */
        const t = carplay.TARGETS[opts.output];
        o = Object.assign({}, o, { w: t.w, h: t.h, fps: perf ? carplay.PERF_FPS[opts.output] || t.fps : t.fps }, t.xband ? { xband: t.xband } : {}, t.band ? { band: t.band } : {});
        try {
            const d = carplay.wantDisplay(opts.output, undefined, settings.carplayCentre, settings.carplayHudAlt);
            if (d) log('carplay: asking for ' + d.wanted + (d.safearea ? ', safe area ' + d.safearea : ', no safe area') +
                (d.pending ? ' (from the phone\'s next connection; until then scaled)' : ''));
        } catch (e) { log('carplay: display: ' + e.message); }
        syncScene();
    }
    if (o.w) o = Object.assign({}, o, { w: four(o.w), h: even(o.h) });
    const wantVideo = opts.output !== 'none';
    const isHttp = !cp && /^https?:/i.test(opts.url);
    /* this screen: the touch screen gives way (one mgu-render client at a
     * time); it comes back when the stream ends (resumeTouch) */
    if (o.console && touch.shown()) touch.hide('a stream on this screen');
    const preview = cp && PREVIEW_ON && touchAvailable;

    const args = ['-nostdin', '-hide_banner', '-loglevel', 'warning', '-threads', '3'];
    if (cp) {
        /* live: no -re; the hook connects to this listener */
        args.push.apply(args, carplay.inputArgs(carplay.state().port));
        args.push.apply(args, perf ? carplay.perfOutputArgs(opts.output) : carplay.outputArgs(opts.output));
        if (preview) args.push.apply(args, carplay.previewArgs());
    } else {
        if (opts.realtime) args.push('-re');
        if (isHttp) args.push('-reconnect', '1', '-reconnect_streamed', '1', '-reconnect_delay_max', '5');
        args.push('-i', opts.url);
        if (wantVideo) {
            args.push('-map', '0:v:0', '-vf',
                'scale=' + o.w + ':' + o.h + ':force_original_aspect_ratio=decrease:flags=bilinear,' +
                'pad=' + o.w + ':' + o.h + ':-1:-1,fps=' + o.fps + (o.look ? ',' + o.look : '') + ',format=yuv420p',
                '-f', 'rawvideo', 'pipe:1');
        }
    }
    if (opts.audio) {
        args.push('-map', '0:a:0', '-af', 'volume=' + (opts.volume / 100).toFixed(2), '-ac', '2', '-ar', '48000',
            '-f', 's16le', 'pipe:3');
    }

    const env = Object.assign({}, process.env, { http_proxy: 'http://127.0.0.1:' + PROXY_PORT, https_proxy: 'http://127.0.0.1:' + PROXY_PORT });
    /* fd 3: the sound; fd 4: the CarPlay preview */
    const ff = spawn(FFMPEG, args, { env: env, stdio: ['ignore', 'pipe', 'pipe', 'pipe', 'pipe'] });
    const p = { ff: ff, py: null, opts: opts, video: null, started: Date.now(), frames: 0, lastErr: [], perf: perf };
    player = p;
    log('play: ' + opts.shown + ' on ' + opts.output + (opts.audio ? ' with audio at ' + opts.volume + '%' : ' without audio') + (preview ? ', a preview for the touch screen' : '') +
        (perf ? ', performance mode (every frame, ' + o.fps + ' fps layer' + (cr.alwaysPacked ? ', always_packed' : '') + ')' : ''));
    ff.on('error', (e) => { p.lastErr.push('ffmpeg: ' + e.message); log('ffmpeg: ' + e.message); });
    /* the preview's pictures: always read (a full pipe would hold the
     * cluster's output back too), kept only while the touch screen draws them */
    if (preview) {
        touch.previewStart();
        ff.stdio[4].on('data', (d) => { if (player === p) touch.previewData(d); });
    } else {
        ff.stdio[4].resume();
    }

    ff.stderr.on('data', (d) => {
        String(d).split('\n').filter((l) => l.trim()).forEach((l) => {
            p.lastErr.push(l.trim());
            if (p.lastErr.length > 6) p.lastErr.shift();
            log('ffmpeg: ' + l.trim());
        });
    });

    if (wantVideo) {
        const size = o.w * o.h * 3 / 2, out = Buffer.alloc(size);
        const r = o.console ? null : placement(o);
        if (o.console) consoleVideo.start(o.w, o.h, o.fps);
        /* prewarm: ask for the slot before the first frame (ffmpeg takes a
         * second or two to start); contend: take it from the stock content. */
        if (!o.console) {
            /* performance mode: every write as cluster-render's packed blocks,
             * only the changed ones (a service that doesn't offer it ignores
             * it and writes the layer exact) */
            p.layerOpts = { target: o.target, z: 1, contend: true, prewarm: true, guide_hold: guideHold(), x: r.x, y: r.y, w: r.w, h: r.h, vw: o.w, vh: o.h, fps: o.fps };
            if (perf && o.h % 4 === 0) p.layerOpts.always_packed = true;
            p.video = cr.video(p.layerOpts);
        }
        let parts = [], have = 0;
        if (perf) {
            /* ffmpeg sends the atlas itself: each frame is copied once, into
             * one buffer kept for the run (cr.frame copies it on) */
            const frame = Buffer.alloc(size);
            ff.stdout.on('data', (d) => {
                let off = 0;
                while (off < d.length) {
                    const n = Math.min(size - have, d.length - off);
                    d.copy(frame, have, off, off + n);
                    have += n; off += n;
                    if (have === size) {
                        have = 0;
                        cr.frame(p.video, frame, ++p.frames);
                        if (p.frames === 1) { log('play: first frame'); updateQr(); }
                    }
                }
            });
        } else ff.stdout.on('data', (d) => {
            parts.push(d);
            have += d.length;
            while (have >= size) {
                const all = parts.length === 1 ? parts[0] : Buffer.concat(parts, have);
                if (o.console) { consoleVideo.frame(all.slice(0, size)); ++p.frames; }
                else cr.frame(p.video, atlas(all.slice(0, size), o.w, o.h, out), ++p.frames);
                if (p.frames === 1) { log('play: first frame'); updateQr(); }
                parts = have > size ? [all.slice(size)] : [];
                have -= size;
            }
        });
    } else {
        ff.stdout.resume();
    }

    if (opts.audio) {
        /* the speakers first, then the player on the device they give (ffmpeg's sound waits in its pipe) */
        p.speakers = true;
        speakers.claimOr(CARPLAY).then((device) => {
            if (p.down) { releaseSpeakers(p); ff.stdio[3].resume(); return; }
            const py = spawn(PYTHON, [path.join(HERE, 'pcm_play.py'), '--device', device, '--file', '-'], { stdio: ['pipe', 'pipe', 'pipe'] });
            p.py = py;
            ff.stdio[3].pipe(py.stdin);
            py.stdin.on('error', () => { /* python gone: ffmpeg's write fails and it ends */ });
            py.stdout.on('data', (d) => log(String(d).trim()));
            py.stderr.on('data', (d) => { const l = String(d).trim(); p.lastErr.push(l); log(l); });
            /* played to the end (stdin ended) or killed */
            py.on('exit', () => releaseSpeakers(p));
        });
    } else {
        ff.stdio[3].resume();
    }

    updateQr();
    ff.on('exit', (code, sig) => {
        if (player !== p) return;     /* stopped or replaced */
        const ok = code === 0;
        log('play: ffmpeg ended (' + (sig || code) + ')');
        if (!ok && opts.audio && !p.frames && p.lastErr.some((l) => /matches no streams|does not contain any stream/i.test(l))) {
            log('play: the stream has no audio; again without it');
            return play(Object.assign({}, opts, { audio: false }));
        }
        player = null;
        if (p.py) try { p.py.stdin.end(); } catch (e) { /* gone */ }
        else releaseSpeakers(p);
        if (p.video) cr.drop(p.video);
        if (o.console) { consoleVideo.stop(); setImmediate(resumeTouch); }
        if (cp) touch.previewEnd();
        last = { state: ok ? 'ended' : 'error', url: opts.shown, output: opts.output, frames: p.frames,
            error: ok ? null : (p.lastErr.slice(-3).join(' | ') || 'ffmpeg exited ' + (sig || code)) };
        /* The second screen has no end: the hook's connection went (it gives
         * up on a reader that stops, then reconnects); listen again. */
        if (cp && !stopping && settings.enabled) {
            /* a run that showed nothing waits longer each time (up to 30 s), so
             * a listener that can't start doesn't spin */
            restartDelay = p.frames ? 1000 : Math.min(30000, restartDelay * 2);
            /* performance mode: while hook111 says the phone streams, the next
             * run can take it at once: at most 3 s between runs, not 30 */
            if (p.perf && !p.frames && carplayStreaming()) restartDelay = Math.min(restartDelay, 3000);
            last = { state: 'waiting', url: opts.shown, output: opts.output, frames: p.frames,
                note: 'listening again for the second screen in ' + Math.round(restartDelay / 1000) + ' s', error: last.error };
            restartTimer = setTimeout(() => { restartTimer = null; if (!player && lastPlay === opts && settings.enabled && !stopping) play(opts); }, restartDelay);
        }
        updateQr();
    });
}

function status() {
    const up = readJson(UPLINK_STATUS) || {};
    const s = player
        ? { state: 'playing', url: player.opts.shown, output: player.opts.output, audio: player.opts.audio, volume: player.opts.volume,
            frames: player.frames, seconds: Math.round((Date.now() - player.started) / 1000) }
        : last;
    const c = carplay.state();
    touchAvailable = consoleOut.available();
    return Object.assign({ enabled: settings.enabled, uplink: up.state || 'unknown', render: cr.ready ? 'connected' : 'not connected', qr: qrWanted,
        link: link(), canReplay: !!lastPlay, bus: bus.state(),
        /* the touch screen: up, wanted by the app (up, or waiting for a
         * stream on this screen to end), possible here (mgu-render) */
        touch: touch.shown(), touchWanted: touchWanted, touchAvailable: touchAvailable, moving: moving(), speed: car.kmh,
        source: player ? player.opts.source || 'url' : (lastPlay && lastPlay.source) || 'url',
        carplay: { armed: c.armed, ready: c.ready, why: c.why, mode: c.mode, streaming: c.streaming, frames: c.frames,
            display: c.display, wanted: c.wanted, size: c.size, switch: carplaySwitch(), cards: carplayCards(c), centre: carplayCentre(c), hudAlt: settings.carplayHudAlt,
            night: { now: c.night, car: c.nightCar, acked: c.nightAcked } },
        badge: { show: settings.showBadge, shown: settings.showBadge && !badge.hold, route: badge.route, why: badge.why, slot: badge.text },
        perf: { on: settings.perfMode, packed: !!cr.alwaysPacked, resume: settings.carplayResume, map: mapTarget.state, note: perfNote },
        outputs: Object.keys(OUTPUTS).filter((k) => k !== 'console' || consoleOut.available()).map((k) => ({ id: k, title: OUTPUTS[k].title })) }, s);
}

/* The last status, for the touch screen: made once a second (the control
 * socket's broadcast, or the touch screen's own tick) and after every
 * action, so a frame never reads a file. */
let lastStatus = null;
function freshStatus() { lastStatus = status(); return lastStatus; }

/* ---- the touch screen ---------------------------------------------------- */

/* the car's speed, from the iDrive app (app/vehicle_speed) about once a
 * second: moving true / false, or null when unknown (none for 10 s) */
const car = { kmh: null, at: 0 };
function moving() { return car.kmh === null || Date.now() - car.at > 10000 ? null : car.kmh > MAX_KMH; }

let touchAvailable = consoleOut.available();
/* the app's screen state is open: the touch screen is up, or waits for a
 * stream on this screen to end */
let touchWanted = false;
const touch = new CastTouch({
    dir: HERE, log: log, clientPath: consoleOut.CLIENT,
    touch: { python: TOUCH_PYTHON, iface: TOUCH_IFACE, src: TOUCH_SRC, file: TOUCH_FILE,
        cmd: process.env.CAST_TOUCH_CMD ? JSON.parse(process.env.CAST_TOUCH_CMD) : null },
    state: () => lastStatus,
    command: (c) => command(c),
});
touch.on('change', () => { freshStatus(); if (control) control.broadcast(); });
/* the List corner: the app goes back to its iDrive list (the touch screen hides) */
touch.on('list', () => { hideTouch('List'); if (control) { control.send({ ev: 'list' }); control.broadcast(); } });
/* the seconds playing and what changed elsewhere, once a second */
const touchTimer = setInterval(() => { if (touch.shown()) { freshStatus(); touch.refresh(); } }, 1000);

function consoleUp() { return !!(player && player.opts.output === 'console'); }
function showTouch() {
    if (!touchAvailable) return 'the touch screen needs mgu-render';
    touchWanted = true;
    if (consoleUp()) { log('touch: after the stream on this screen'); return null; }
    freshStatus();
    return touch.show();
}
function hideTouch(why) { touchWanted = false; touch.hide(why); }
/* a stream on this screen ended: the touch screen again, if the app still wants it */
function resumeTouch() {
    if (!touchWanted || touch.shown() || consoleUp() || !touchAvailable || stopping) return;
    log('touch: back after the stream on this screen');
    freshStatus();
    touch.show();
}

/* ---- the web page -------------------------------------------------------- */

const PAGE = fs.readFileSync(path.join(HERE, 'page.html'), 'utf8');

function send(res, code, type, body) {
    res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff' });
    res.end(body);
}
function json(res, code, obj) { send(res, code, 'application/json', JSON.stringify(obj)); }

function readBody(req, cb) {
    let b = '';
    req.on('data', (d) => { b += d; if (b.length > 16384) req.destroy(); });
    req.on('end', () => { try { cb(null, b ? JSON.parse(b) : {}); } catch (e) { cb(e); } });
}

function authorised(req, u) {
    const t = req.headers['x-cast-token'] || u.searchParams.get('t') || '';
    return t.length === TOKEN.length && crypto.timingSafeEqual(Buffer.from(t), Buffer.from(TOKEN));
}

const web = http.createServer((req, res) => {
    const u = new URL(req.url, 'http://x');
    if (!authorised(req, u)) return send(res, 403, 'text/plain', 'Scan the QR code on the iDrive Cast page to open this page.\n');
    if (!settings.enabled) return send(res, 503, 'text/plain', 'Cast to cluster is off: turn it on on the iDrive Cast page.\n');
    if (req.method === 'GET' && u.pathname === '/') return send(res, 200, 'text/html; charset=utf-8', PAGE);
    if (req.method === 'GET' && u.pathname === '/api/status') return json(res, 200, status());
    if (req.method !== 'POST') return json(res, 404, { error: 'not found' });

    readBody(req, (err, b) => {
        if (err) return json(res, 400, { error: 'bad JSON' });
        if (u.pathname === '/api/play' && b.source === 'carplay') {
            const why = playCarplay(b.output);
            return why ? json(res, 400, { error: why }) : json(res, 200, status());
        }
        if (u.pathname === '/api/play') {
            let url;
            try { url = new URL(String(b.url || '')); } catch (e) { return json(res, 400, { error: 'not a URL' }); }
            if (!/^(https?|rtsp|rtmp):$/.test(url.protocol)) return json(res, 400, { error: 'http(s), rtsp or rtmp only' });
            const output = OUTPUTS[b.output] ? b.output : 'map';
            const audio = b.audio !== false;
            if (output === 'none' && !audio) return json(res, 400, { error: 'nothing to play: no video output and no audio' });
            const volume = Math.max(0, Math.min(150, Math.round(Number(b.volume) || 60)));
            forgetResume('a stream from the phone');
            play({ url: url.href, shown: redact(url.href), output: output, audio: audio, volume: volume, realtime: b.realtime !== false });
            return json(res, 200, status());
        }
        if (u.pathname === '/api/carplay-centre') {
            setCarplayCentre(b.on === true);
            return json(res, 200, status());
        }
        if (u.pathname === '/api/perf-mode') {
            setPerfMode(b.on === true);
            return json(res, 200, status());
        }
        if (u.pathname === '/api/show-badge') {
            setShowBadge(b.on === true);
            return json(res, 200, status());
        }
        if (u.pathname === '/api/carplay-hud-alt') {
            setCarplayHudAlt(b.on === true);
            return json(res, 200, status());
        }
        if (u.pathname === '/api/carplay-cards') {
            setCarplayCards(b);
            return json(res, 200, status());
        }
        if (u.pathname === '/api/carplay-zoom') {
            const why = carplayZoom(b.dir);
            return why ? json(res, 400, { error: why }) : json(res, 200, status());
        }
        if (u.pathname === '/api/hook111') {
            const why = setCarplayMode(b.mode);
            return why ? json(res, 400, { error: why }) : json(res, 200, status());
        }
        if (u.pathname === '/api/stop') { forgetResume('stopped from the phone'); stopPlayer('stopped from the phone'); return json(res, 200, status()); }
        if (u.pathname === '/api/qr') { setQr(!!b.show); return json(res, 200, status()); }
        json(res, 404, { error: 'not found' });
    });
});

/* ---- start and stop ------------------------------------------------------ */

/* The CarPlay second screen on the cluster map or the HUD: null, or why not. */
function carplayOpts(output) {
    return { source: 'carplay', shown: 'CarPlay second screen', output: output, audio: false, volume: 0, realtime: false };
}
function playCarplay(output) {
    const c = carplay.state();
    if (!c.ready) return 'the CarPlay second screen is not available: ' + c.why;
    const out = output === 'hud' ? 'hud' : 'map';
    if (settings.carplayResume !== out) { settings.carplayResume = out; saveSettings(); }
    play(carplayOpts(out));
    return null;
}

/* The second screen's switch: hook111's mode, off or alt, now and for later
 * starts (carplay_screen.setMode). Off also stops a second screen playing.
 * null, or why not. */
function carplaySwitch() {
    try { return carplay.switchState(); } catch (e) { return { installed: false, on: false, pending: null, error: e.message }; }
}
function setCarplayMode(mode) {
    let r;
    try { r = carplay.setMode(mode); } catch (e) { log('hook111: mode ' + mode + ': ' + e.message); return e.message; }
    log('hook111: mode ' + r.mode + ' saved; ' + r.note);
    if (r.mode === 'off') forgetResume('the CarPlay second screen turned off');
    if (r.mode === 'off' && player && player.opts.source === 'carplay') stopPlayer('the CarPlay second screen turned off');
    return null;
}

/* The CarPlay output playing, or last played, or the cluster map. */
function carplayOutput() {
    return (player && player.opts.source === 'carplay' && player.opts.output) || (lastPlay && lastPlay.source === 'carplay' && lastPlay.output) || 'map';
}
const hudAltOn = (out) => out === 'hud' && settings.carplayHudAlt;

/* The cluster scene: the directions card and the time / distance card,
 * written for hook111 (carplay_screen.sceneUrl), now and every 5 s (its run
 * directory is new at each start). hook111 0.1.5 sends a change to the phone
 * at once; 0.1.6 sends it again 1, 4 and 10 s later and says when the phone
 * answered (pending until then). The HUD's alternate mode shows the time /
 * distance card only. */
function sceneOpts(out) {
    const alt = hudAltOn(out);
    return { directions: alt ? false : settings.carplayDirections, eta: settings.carplayEta, wide: alt || !settings.carplayCentre };
}
function syncScene() {
    try { return carplay.wantScene(sceneOpts(carplayOutput())); } catch (e) { log('carplay: scene: ' + e.message); return null; }
}
function carplayCards(c) {
    const url = carplay.sceneUrl(sceneOpts(carplayOutput()));
    return { directions: settings.carplayDirections, eta: settings.carplayEta, url: url,
        pending: c.streaming && !carplay.sceneTaken(c, url) ? 'in a moment' : null };
}
function setCarplayCards(b) {
    if (typeof b.directions === 'boolean') settings.carplayDirections = b.directions;
    if (typeof b.eta === 'boolean') settings.carplayEta = b.eta;
    saveSettings();
    const r = syncScene();
    log('carplay: directions card ' + (settings.carplayDirections ? 'on' : 'off') + ', time / distance card ' + (settings.carplayEta ? 'on' : 'off') +
        (r ? ': ' + r.url : ', from the next start (hook111 is not armed this start)'));
    return null;
}
/* Zoom the cluster map in or out (hook111 sends it while the stream runs). */
function carplayZoom(dir) {
    let ok;
    try { ok = carplay.requestZoom(dir); } catch (e) { return e.message; }
    if (!ok) return 'hook111 is not armed this start';
    log('carplay: zoom ' + dir);
    return null;
}

/* Centre the map: view area 0, the phone's view centred on the target's safe
 * area (carplay_screen TARGETS[].safe): the directions card at the top, the
 * car, the time / distance card at the bottom. Off: view area 1, Maps' own
 * layout. hook111 0.1.5 switches it at once (updateViewArea). */
function carplayCentre(c) {
    const out = carplayOutput();
    return { on: settings.carplayCentre, safearea: carplay.safeText(carplay.safeAreaFor(out, hudAltOn(out))),
        pending: c.streaming && c.viewarea !== null && c.viewarea !== (settings.carplayCentre ? 0 : 1) ? 'in a moment' : null };
}
function setCarplayCentre(on) {
    settings.carplayCentre = !!on;
    saveSettings();
    const out = carplayOutput();
    try { carplay.wantDisplay(out, undefined, settings.carplayCentre, hudAltOn(out)); } catch (e) { log('carplay: centre: ' + e.message); }
    syncScene();
    log('carplay: centre ' + (on ? 'on' : 'off') + ' saved');
    return null;
}
/* The HUD's alternate mode: the phone draws the HUD band's own wide shape
 * (1056x384), no safe area, the time / distance card only. Off (the default):
 * the cluster's picture and cards, centred, fitted into the band. Written now
 * when the CarPlay picture is on the HUD (the size from the phone's next
 * connection). */
function setCarplayHudAlt(on) {
    settings.carplayHudAlt = !!on;
    saveSettings();
    const onHud = player && player.opts.source === 'carplay' && player.opts.output === 'hud';
    let d = null;
    if (onHud) { try { d = carplay.wantDisplay('hud', undefined, settings.carplayCentre, settings.carplayHudAlt); } catch (e) { log('carplay: hud: ' + e.message); } }
    syncScene();
    log('carplay: HUD alternate mode ' + (on ? 'on' : 'off') + ' saved' + (d ? ', asking for ' + d.wanted + ', from the phone\'s next connection' : ', from the next play on the HUD'));
    return null;
}

/* Cast's layers on the map take the hold Cast wants now (guideHold()). */
function applyGuideHold() {
    const hold = guideHold();
    if (player && player.video && o0(player).target === 'map') cr.set(player.video, { guide_hold: hold });
    if (qrLayer) cr.set(qrLayer, { guide_hold: hold });
}
function setShowBadge(on) {
    settings.showBadge = !!on;
    saveSettings();
    applyGuideHold();
    if (cr.ready) cr.status();
    log('badge: ' + (on ? 'shown while no route (the map over it during a route)' : 'as cluster-render decides (its guide hold)'));
    return null;
}

/* ---- the experimental performance mode -------------------------------------
 * settings.perfMode, off by default; on: the CarPlay picture (not a stream
 * URL) and its recovery, each audited for the car's safety first (README.md
 * "Experimental performance mode"):
 *  - every decoded frame to the renderer, which writes the newest at up to
 *    PERF_FPS (no ffmpeg fps filter dropping frames on made-up timestamps);
 *  - ffmpeg makes the renderer's atlas (no row copies in the tool);
 *  - cluster-render's always_packed, where it offers it;
 *  - the CarPlay output the user last picked starts again by itself once
 *    hook111 is ready (a car start, a restart of the tool) until a Stop, a
 *    stream URL or the second screen turned off (carplayResume);
 *  - at most 3 s between listener runs while the phone streams (not 30);
 *  - a stalled ffmpeg (the phone's frames reach hook111, none reach the
 *    tool for STALL_MS) is started again;
 *  - the cluster map taken back by the stock map: after RETAKE_AFTER_MS
 *    parked behind it (or waiting while it holds the slot), the layer is made
 *    again, as a Cluster tap does, at most once a RETAKE_GAP_MS and
 *    RETAKE_MAX times before the map is shown again; never for a slot lock
 *    (a warning, a door), a refusal, or the HUD (which gives way to calls). */
const STALL_MS = 5000, STALL_GAP_MS = 20000;
const RETAKE_AFTER_MS = 20000, RETAKE_GAP_MS = 60000, RETAKE_MAX = 3, RETAKE_SHOWN_MS = 10000;
let perfNote = null;   /* the last thing the mode did, for the status */
const mapTarget = { state: null, holder: null, reason: '', since: Date.now(), retakes: 0, lastRetake: -Infinity };
let lastStallKill = -Infinity, lastResumeTry = -Infinity;

function setPerfMode(on) {
    settings.perfMode = !!on;
    saveSettings();
    perfNote = null;
    log('perf: experimental performance mode ' + (on ? 'on' : 'off') + (player && player.opts.source === 'carplay' ? ': the CarPlay picture starts again with it' : ''));
    /* the picture playing takes it now: ffmpeg's arguments and the layer change */
    if (player && player.opts.source === 'carplay' && settings.enabled) play(carplayOpts(player.opts.output));
    return null;
}
function forgetResume(why) {
    if (settings.carplayResume === null) return;
    settings.carplayResume = null;
    saveSettings();
    log('perf: the CarPlay output is not started again by itself any more (' + why + ')');
}
function carplayStreaming() { try { return carplay.state().streaming; } catch (e) { return false; } }
function perfNoteSet(t) { perfNote = t; log('perf: ' + t); }

/* Once a second while the mode is on. */
function perfTick(now) {
    if (!settings.perfMode || stopping) return;
    let c = null;
    try { c = carplay.state(); } catch (e) { return; }
    /* the CarPlay output the user picked, again by itself */
    if (settings.enabled && settings.carplayResume && !player && !paused && !restartTimer && c.ready && now - lastResumeTry >= 5000) {
        lastResumeTry = now;
        perfNoteSet('starting the CarPlay picture on ' + settings.carplayResume + ' again by itself');
        play(carplayOpts(settings.carplayResume));
        return;
    }
    const p = player;
    if (!p || !p.perf) return;
    /* a stalled ffmpeg: the phone's frames come, ours don't */
    if (!p.wd) p.wd = { at: now, hook: c.frames, ours: p.frames };
    else if (now - p.wd.at >= STALL_MS) {
        const hookMoved = c.frames - p.wd.hook >= 10, oursMoved = p.frames > p.wd.ours;
        if (hookMoved && !oursMoved && now - p.started > 8000 && now - lastStallKill > STALL_GAP_MS) {
            lastStallKill = now;
            perfNoteSet('no frame for ' + Math.round((now - p.wd.at) / 1000) + ' s while the phone streams: ffmpeg started again');
            try { p.ff.kill('SIGKILL'); } catch (e) { /* gone */ }   /* its exit starts it again */
        }
        p.wd = { at: now, hook: c.frames, ours: p.frames };
    }
    /* the cluster map taken back by the stock map */
    if (p.video && p.layerOpts && p.layerOpts.target === 'map') {
        const t = mapTarget;
        if (t.state === 'shown' && now - t.since >= RETAKE_SHOWN_MS) t.retakes = 0;
        const behind = t.holder === 'stock' && !/lock|refused/i.test(t.reason || '') &&
            (t.state === 'parked' || (t.state === 'waiting' && /slot in use/.test(t.reason || '')));
        if (behind && now - t.since >= RETAKE_AFTER_MS && now - t.lastRetake >= RETAKE_GAP_MS && t.retakes < RETAKE_MAX) {
            t.retakes++; t.lastRetake = now;
            perfNoteSet('the cluster map behind the stock map for ' + Math.round((now - t.since) / 1000) + ' s: asked for again (' + t.retakes + ' of ' + RETAKE_MAX + ')');
            const old = p.video;
            cr.drop(old);
            p.layerOpts.guide_hold = guideHold();
            p.video = cr.video(p.layerOpts);
            t.since = now;
        }
    }
}

/* The slot table's rows for a slot: [{ content, klass, map }] (cluster-render's
 * status: "slot 0x105 status 2: 0x1000310 class 0 map 1, ..."). */
function slotRows(lines, slot) {
    const want = 'slot 0x' + slot.toString(16) + ' ';
    const l = lines.find((x) => x.indexOf(want) === 0);
    if (!l) return null;
    const out = [], re = /0x([0-9a-f]+) class (\d+) map (\d+)/g;
    let m;
    while ((m = re.exec(l))) out.push({ content: parseInt(m[1], 16), klass: Number(m[2]), map: Number(m[3]) });
    return out;
}

/* A status from cluster-render (asked for every 2 s, BADGE_POLL_MS): the
 * badge's slots, the route decision, and the map target's line for the
 * Info tab. */
function onRenderStatus(text) {
    const lines = String(text || '').split('\n').map((l) => l.trim());
    const now = Date.now();
    let boxMapped = false, boxVisible = false, any = false;
    BADGE_SLOTS.forEach((slot) => {
        const rows = slotRows(lines, slot);
        if (!rows) return;
        any = true;
        rows.forEach((r) => {
            if (r.content !== BOX) return;
            if (r.map >= 1) boxMapped = true;
            if (r.map === 1 || r.map === 2) boxVisible = true;
        });
    });
    const shown = lines.filter((l) => /^target guide/.test(l) || /^slot 0x10[35] /.test(l))
        .sort((x, y) => (x[0] === 's' ? 0 : 1) - (y[0] === 's' ? 0 : 1));   /* the KOMBI's rows first */
    const t = shown.length ? shown.join('\n') : null;
    if (t !== badge.text) log('badge: ' + (t ? t.replace(/\n/g, ' | ') : 'cluster-render names no guide target or badge slot'));
    badge.text = t;
    const was = badge.hold;
    if (!any) {
        /* the KOMBI hasn't reported either slot: as cluster-render would */
        badge.hold = true; badge.route = null; badge.why = 'the badge slot is not reported yet';
    } else if (!badge.hold || badge.route === null) {
        badge.route = boxVisible;
        badge.hold = boxVisible;
        badge.boxGone = null;
        badge.why = boxVisible ? 'BMW\'s turn box is up: a route' : boxMapped ? 'BMW\'s turn box parked: no route' : 'no turn box: no route';
    } else {
        /* held: the box is parked behind ours whatever the route does; the
         * route is over once it is gone from both slots for a while */
        if (boxMapped) badge.boxGone = null;
        else if (badge.boxGone === null) badge.boxGone = now;
        if (badge.boxGone !== null && now - badge.boxGone >= BADGE_RELEASE_MS) {
            badge.hold = false; badge.route = false; badge.boxGone = null; badge.why = 'the turn box is gone: the route is over';
        } else badge.why = 'a route: the map over the badge';
    }
    if (badge.hold !== was) {
        badge.since = now;
        log('badge: ' + (badge.hold ? 'map over the badge slot' : 'badge shown') + ' (' + badge.why + ')');
        if (settings.showBadge) applyGuideHold();
    }
}

/* The iDrive app's commands over the control socket: null, or why not. */
function setQr(show) { qrWanted = show; settings.clusterQr = show; saveSettings(); updateQr(); }

/* On: the phone page reachable (its firewall rule), the QR code as set.
 * Off: nothing plays, no QR code, the page closed. */
function setEnabled(on) {
    settings.enabled = on;
    saveSettings();
    if (on) {
        try { log('firewall: ' + firewall.add(PORT, IFNAME) + ' rule for ' + IFNAME + ' tcp ' + PORT); } catch (e) { log('firewall: ' + e.message); }
    } else {
        stopPlayer('turned off');
        try { log('firewall: removed ' + firewall.remove() + ' rule(s)'); } catch (e) { log('firewall: ' + e.message); }
    }
    log('cast: ' + (on ? 'on' : 'off'));
    updateQr();
}

function command(c) {
    if (c.cmd === 'speed') {
        const kmh = Number(c.kmh);
        if (!isFinite(kmh) || kmh < 0) return 'speed: a number of km/h';
        car.kmh = kmh; car.at = Date.now();
        return null;
    }
    if (c.cmd === 'touch') {
        if (!c.on) { if (touch.shown() || touchWanted) hideTouch('the app hid it'); return null; }
        return showTouch();
    }
    if (c.cmd === 'enable') { setEnabled(true); return null; }
    if (c.cmd === 'disable') { setEnabled(false); return null; }
    if (c.cmd === 'hook111') return setCarplayMode(c.mode);
    if (c.cmd === 'carplayCards') return setCarplayCards(c);
    if (c.cmd === 'carplayZoom') return carplayZoom(c.dir);
    if (c.cmd === 'carplayCentre') return setCarplayCentre(c.on === true);
    if (c.cmd === 'carplayHudAlt') return setCarplayHudAlt(c.on === true);
    if (c.cmd === 'showBadge') return setShowBadge(c.on === true);
    if (c.cmd === 'perfMode') return setPerfMode(c.on === true);
    if (!settings.enabled) return 'Cast to cluster is off';
    if (c.cmd === 'carplay') return playCarplay(c.output);
    if (c.cmd === 'stop') { forgetResume('stopped on the iDrive page'); stopPlayer('stopped on the iDrive page'); return null; }
    if (c.cmd === 'qr') { setQr(!!c.show); return null; }
    if (c.cmd === 'replay') {
        if (!lastPlay) return 'nothing played yet: start a stream from the phone first';
        const output = OUTPUTS[c.output] ? c.output : lastPlay.output;
        if (output === 'console' && !consoleOut.available()) return 'the media console needs mgu-render';
        if (lastPlay.source === 'carplay') {
            if (output === 'console' || output === 'none') return 'the CarPlay second screen goes to the cluster map or the HUD';
            return playCarplay(output);
        }
        forgetResume('the last stream again');
        play(Object.assign({}, lastPlay, { output: output, audio: lastPlay.audio || output === 'none' }));
        return null;
    }
    return 'unknown command';
}

let control = null;
let stopping = false;
function shutdown(sig) {
    if (stopping) return;
    stopping = true;
    log('stopping (' + sig + ')');
    stopPlayer('shutting down');
    clearInterval(touchTimer);
    hideTouch('the tool stops');
    bus.close();
    consoleVideo.stop();
    try { log('firewall: removed ' + firewall.remove() + ' rule(s)'); } catch (e) { log('firewall: ' + e.message); }
    if (proxy) proxy.kill('SIGTERM');
    if (control) control.close();
    cr.close();
    web.close();
    setTimeout(() => process.exit(0), 500);
}
process.on('SIGTERM', () => shutdown('SIGTERM'));
process.on('SIGINT', () => shutdown('SIGINT'));

cr.on('ready', () => { log('render: connected (' + cr.backend + (cr.alwaysPacked ? ', always_packed offered' : '') + ')'); updateQr(); });
cr.on('disconnected', () => log('render: disconnected'));
cr.on('status', onRenderStatus);
cr.on('layer', (ref, state, reason) => log('render: layer ' + ref + (ref === qrLayer ? ' (qr)' : player && ref === player.video ? ' (video)' : '') +
    ' ' + state + (reason ? ': ' + reason : '')));
cr.on('target', (t, state, holder, reason) => {
    /* the map's state, for the performance mode's retake */
    if (t === 'map' && (state !== mapTarget.state || holder !== mapTarget.holder || (reason || '') !== mapTarget.reason)) {
        Object.assign(mapTarget, { state: state, holder: holder, reason: reason || '', since: Date.now() });
    }
    log('render: target ' + t + ' ' + state + (holder && holder !== 'none' ? ' (holder ' + holder + ')' : '') + (reason ? ': ' + reason : ''));
});
cr.on('refused', (op, ref, reason) => log('render: refused ' + op + ' ' + ref + (reason ? ': ' + reason : '')));

if (settings.enabled) {
    try { log('firewall: ' + firewall.add(PORT, IFNAME) + ' rule for ' + IFNAME + ' tcp ' + PORT); } catch (e) { log('firewall: ' + e.message); }
} else {
    log('cast: off (turn it on on the iDrive Cast page)');
}
startProxy();
web.listen(PORT, '0.0.0.0', () => log('web: listening on port ' + PORT));
/* speakers a previous run (or a head unit restart) left claimed: given back */
speakers.recover();
control = startControl({ app: 'vizualyse_cast', status: freshStatus, command: command, log: log });
cr.connect();
/* The address changes with the hotspot: keep the QR code current. hook111's
 * run directory can appear after this tool starts: keep its view current. */
syncScene();
setInterval(() => { updateQr(); syncScene(); }, 5000);
/* cluster-render's status: every 2 s while the badge is wanted (its route
 * decision), else every 10 s (the Info tab's badge slot) */
let statusTick = 0;
setInterval(() => {
    const now = Date.now();
    statusTick++;
    if (cr.ready && (settings.showBadge ? statusTick % 2 === 0 : statusTick % 10 === 0)) cr.status();
    perfTick(now);
}, 1000);
