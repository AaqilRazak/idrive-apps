// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Yousaf Khan
/* Steam's DRM wrapper (SteamStub) taken off a game's program, on the car.
 * Our own code, written from the format's public description (not from any
 * other unpacker's source).
 *
 * A wrapped program has a .bind section holding the stub; its entry point
 * is in .bind, and just before it lies the stub's header, each dword XORed
 * with the one before it (the first is the key). Variant 3 headers start
 * with the key, then the signature 0xC0DEC0DF; they carry the original entry
 * point, the code section's address and size, and (unless the flags say
 * NoEncryption, 0x4) an AES-256 key and IV: the code section was encrypted
 * AES-256-CBC with the IV that AES-256-ECB-decrypting the header's IV gives,
 * and its first 16 encrypted bytes were moved into the header.
 *
 * Unwrapping: decrypt the code section (the 16 bytes put back in front),
 * restore the entry point, drop .bind when nothing else points into it and
 * it is the last section, fix the sizes, file offsets and the checksum.
 * Variant 3.1 (x86, x64) and 3.0 (x86) are the layouts we know; 3.0 x64 is
 * tried with 3.1's field layout (marked guessed); variant 1 and 2 are found
 * (a .bind without a variant 3 header) but not unwrapped yet.
 *
 * Every layout is checked against the program before anything is written:
 * the code section at the header's address, the entry point inside the
 * image, the AES block size. Node 8 (the unit's): no BigInt.
 *
 *   detect(file)          null (no .bind), or { variant, arch, appId,
 *                         flags, encrypted, supported, why, guessed }
 *   unpack(in, out)       writes the unwrapped program; returns detect()'s
 *   unwrapExe(file, on)   on: the program unwrapped in place, Steam's kept
 *                         as <file>.vzs-orig; off: Steam's put back */
'use strict';
const fs = require('fs');
const crypto = require('crypto');

const SIG = 0xc0dec0df;
const NO_ENCRYPTION = 0x4;
const ORIG = '.vzs-orig';

/* the variant 3 headers: [offset, bytes] of the fields we use */
const WIDE = { imageBase: [0x08, 8], oep: [0x20, 8], appId: [0x38, 4], flags: [0x3c, 4], bindVs: [0x40, 4],
    codeVa: [0x48, 8], codeRaw: [0x50, 8], key: 0x58, iv: 0x78, stolen: 0x88 };
const NARROW = { imageBase: [0x08, 4], oep: [0x18, 4], appId: [0x2c, 4], flags: [0x30, 4], bindVs: [0x34, 4],
    codeVa: [0x3c, 4], codeRaw: [0x40, 4], key: 0x44, iv: 0x64, stolen: 0x74 };
const LAYOUTS = [
    { variant: '3.1', size: 0xf0, f: WIDE },
    { variant: '3.0', size: 0xb0, arch: 'x86', f: NARROW },
    { variant: '3.0', size: 0xd0, arch: 'x64', f: WIDE, guessed: true },
];

class StubError extends Error {}
function fail(msg) { throw new StubError(msg); }

function u64(b, o) { return b.readUInt32LE(o) + b.readUInt32LE(o + 4) * 0x100000000; }
function field(b, f) { return f[1] === 8 ? u64(b, f[0]) : b.readUInt32LE(f[0]); }
function align(v, a) { return a ? Math.ceil(v / a) * a : v; }

/* ---- the PE ------------------------------------------------------------------ */

/* the headers we need, from a Buffer holding at least the file's headers */
function parsePe(b) {
    if (b.length < 0x40 || b.readUInt16LE(0) !== 0x5a4d) fail('not a Windows program (no MZ)');
    const pe = b.readUInt32LE(0x3c);
    if (pe + 24 > b.length || b.readUInt32LE(pe) !== 0x00004550) fail('not a Windows program (no PE header)');
    const machine = b.readUInt16LE(pe + 4), count = b.readUInt16LE(pe + 6), optSize = b.readUInt16LE(pe + 20);
    const opt = pe + 24;
    if (opt + optSize > b.length || optSize < 96) fail('a truncated PE header');
    const magic = b.readUInt16LE(opt), wide = magic === 0x20b;
    if (magic !== 0x10b && !wide) fail('an unknown optional header (0x' + magic.toString(16) + ')');
    const dirAt = opt + (wide ? 112 : 96), dirCount = Math.min(b.readUInt32LE(opt + (wide ? 108 : 92)), 16);
    const dirs = [];
    for (let i = 0; i < dirCount && dirAt + i * 8 + 8 <= opt + optSize; i++) dirs.push({ rva: b.readUInt32LE(dirAt + i * 8), size: b.readUInt32LE(dirAt + i * 8 + 4) });
    const table = opt + optSize;
    if (table + count * 40 > b.length) fail('a truncated section table');
    const sections = [];
    for (let i = 0; i < count; i++) {
        const at = table + i * 40;
        sections.push({ index: i, at: at, name: b.toString('latin1', at, at + 8).replace(/\0+$/, ''),
            vs: b.readUInt32LE(at + 8), va: b.readUInt32LE(at + 12), raw: b.readUInt32LE(at + 16), ptr: b.readUInt32LE(at + 20) });
    }
    return { pe: pe, opt: opt, optSize: optSize, wide: wide, table: table, dirAt: dirAt, dirs: dirs, sections: sections,
        arch: machine === 0x8664 ? 'x64' : machine === 0x14c ? 'x86' : null,
        ep: b.readUInt32LE(opt + 16), imageBase: wide ? u64(b, opt + 24) : b.readUInt32LE(opt + 28),
        sectAlign: b.readUInt32LE(opt + 32), fileAlign: b.readUInt32LE(opt + 36), sizeOfImage: b.readUInt32LE(opt + 56),
        sizeOfHeaders: b.readUInt32LE(opt + 60), checksumAt: opt + 64 };
}

function sectionAt(p, rva) {
    return p.sections.filter((s) => rva >= s.va && rva < s.va + Math.max(s.vs, s.raw))[0] || null;
}
function rvaToOff(p, rva) {
    const s = sectionAt(p, rva);
    if (!s || rva - s.va >= s.raw) return null;
    return s.ptr + (rva - s.va);
}

/* the header's dwords, each XORed with the one before it in the file */
function xorDecode(enc) {
    const out = Buffer.from(enc);
    let key = enc.readUInt32LE(0);
    for (let i = 4; i + 4 <= enc.length; i += 4) {
        const v = enc.readUInt32LE(i);
        out.writeUInt32LE((v ^ key) >>> 0, i);
        key = v;
    }
    return out;
}

/* an address the header gives: an RVA, or a VA (the image base added) */
function toRva(v, p, base) {
    if (v < p.sizeOfImage) return v;
    if (base && v >= base && v - base < p.sizeOfImage) return v - base;
    if (v >= p.imageBase && v - p.imageBase < p.sizeOfImage) return v - p.imageBase;
    return null;
}

/* the variant 3 header at the entry point, checked against the program:
 * read(off, len) gives the file's bytes */
function findHeader(p, read) {
    const epOff = rvaToOff(p, p.ep);
    if (epOff === null) return null;
    for (const L of LAYOUTS) {
        if (L.arch && L.arch !== p.arch) continue;
        if (epOff < L.size) continue;
        const enc = read(epOff - L.size, L.size);
        if (enc.length < L.size) continue;
        const h = xorDecode(enc);
        if (h.readUInt32LE(4) !== SIG) continue;
        const f = L.f, base = field(h, f.imageBase);
        const oep = toRva(field(h, f.oep), p, base), codeVa = toRva(field(h, f.codeVa), p, base);
        const code = codeVa === null ? null : p.sections.filter((s) => s.va === codeVa)[0];
        const codeRaw = field(h, f.codeRaw), flags = h.readUInt32LE(f.flags[0]);
        const encrypted = !(flags & NO_ENCRYPTION);
        if (oep === null || !sectionAt(p, oep) || sectionAt(p, oep).name === '.bind') continue;
        if (encrypted && (!code || codeRaw === 0 || codeRaw % 16 !== 0 || codeRaw > code.raw)) continue;
        return { layout: L, variant: L.variant, guessed: !!L.guessed, oep: oep, code: code, codeRaw: codeRaw, flags: flags, encrypted: encrypted,
            appId: h.readUInt32LE(f.appId[0]), key: h.slice(f.key, f.key + 32), iv: h.slice(f.iv, f.iv + 16), stolen: h.slice(f.stolen, f.stolen + 16) };
    }
    return null;
}

function describe(p, h) {
    if (!h) {
        return { variant: null, arch: p.arch, appId: null, flags: null, encrypted: null, supported: false, guessed: false,
            why: 'Steam\'s DRM wrapper of a kind we can\'t take off yet (variant 1 or 2, or an unknown one)' };
    }
    return { variant: h.variant, arch: p.arch, appId: h.appId, flags: h.flags, encrypted: h.encrypted, supported: true, guessed: h.guessed, why: null };
}

function wrapErr(e) {
    if (e instanceof StubError) return e;
    if (e instanceof RangeError) return new StubError('a truncated or damaged program (' + e.message + ')');
    return e;
}

/* ---- detect ------------------------------------------------------------------ */

function detectBuffer(b) {
    try {
        const p = parsePe(b);
        if (!p.sections.some((s) => s.name === '.bind')) return null;
        return describe(p, findHeader(p, (off, len) => b.slice(off, off + len)));
    } catch (e) { throw wrapErr(e); }
}

function detect(file) {
    const fd = fs.openSync(file, 'r');
    try {
        const read = (off, len) => { const b = Buffer.alloc(len); const n = fs.readSync(fd, b, 0, len, off); return b.slice(0, n); };
        const head = read(0, 65536);
        try {
            const p = parsePe(head);
            if (!p.sections.some((s) => s.name === '.bind')) return null;
            return describe(p, findHeader(p, read));
        } catch (e) { throw wrapErr(e); }
    } finally { fs.closeSync(fd); }
}

/* ---- unpack ------------------------------------------------------------------ */

function aes(mode, key, iv, data) {
    const d = crypto.createDecipheriv(mode, key, iv);
    d.setAutoPadding(false);
    return Buffer.concat([d.update(data), d.final()]);
}

/* the standard PE checksum (the field itself counted as zero) */
function peChecksum(b, at) {
    let sum = 0;
    for (let i = 0; i < b.length; i += 2) {
        if (i === at || i === at + 2) continue;
        sum += i + 1 < b.length ? b.readUInt16LE(i) : b[i];
        sum = (sum & 0xffff) + (sum >>> 16);
    }
    sum = (sum & 0xffff) + (sum >>> 16);
    return (sum + b.length) >>> 0;
}

/* the unwrapped program as a new Buffer */
function unpackBuffer(b) {
    try { return unpackInner(b); } catch (e) { throw wrapErr(e); }
}

function unpackInner(b) {
    const p = parsePe(b);
    const bind = p.sections.filter((s) => s.name === '.bind')[0];
    if (!bind) fail('no .bind section: not wrapped by Steam\'s DRM');
    const h = findHeader(p, (off, len) => b.slice(off, off + len));
    if (!h) fail(describe(p, null).why);

    /* the code section's bytes as they were */
    let code = null;
    if (h.encrypted) {
        if (h.code.ptr + h.codeRaw > b.length) fail('the code section runs past the end of the file');
        const iv = aes('aes-256-ecb', h.key, Buffer.alloc(0), h.iv);
        code = aes('aes-256-cbc', h.key, iv, Buffer.concat([h.stolen, b.slice(h.code.ptr, h.code.ptr + h.codeRaw)]));
        const next = p.sections.filter((s) => s.va > h.code.va).sort((x, y) => x.va - y.va)[0];
        if (next && h.code.va + code.length > next.va) fail('the decrypted code section would run into ' + next.name);
    }

    /* .bind goes when it is the last section (in the table, in memory and in
     * the file) and no directory nor the entry point points into it */
    const inBind = (rva) => rva >= bind.va && rva < bind.va + Math.max(bind.vs, bind.raw);
    const last = p.sections[p.sections.length - 1] === bind &&
        p.sections.every((s) => s === bind || (s.va < bind.va && (!s.raw || s.ptr < bind.ptr || !bind.raw)));
    const dropBind = last && !p.dirs.some((d) => d.size && inBind(d.rva)) && !inBind(h.oep);

    /* new file offsets: the code section may grow, .bind's bytes may go */
    const withRaw = p.sections.filter((s) => s.raw).sort((x, y) => x.ptr - y.ptr);
    const rawEnd = withRaw.reduce((m, s) => Math.max(m, s.ptr + s.raw), p.sizeOfHeaders);
    const plan = [];
    let shift = 0;
    withRaw.forEach((s) => {
        const ptr = s.ptr + shift;
        let size = s.raw;
        if (s === bind && dropBind) { size = 0; } else if (code && s === h.code && code.length > s.raw) size = align(code.length, p.fileAlign);
        plan.push({ s: s, ptr: s === bind && dropBind ? 0 : ptr, size: size });
        shift += size - s.raw;
    });
    const mapOff = (off) => {
        for (const x of plan) if (off >= x.s.ptr && off < x.s.ptr + x.s.raw) return x.size ? x.ptr + (off - x.s.ptr) : null;
        return off >= rawEnd ? off + shift : off;
    };

    const out = Buffer.alloc(b.length + shift);
    b.copy(out, 0, 0, Math.min(b.length, withRaw.length ? withRaw[0].ptr : p.sizeOfHeaders));
    plan.forEach((x) => {
        if (!x.size) return;
        b.copy(out, x.ptr, x.s.ptr, x.s.ptr + Math.min(x.s.raw, x.size));
        if (code && x.s === h.code) code.copy(out, x.ptr);
    });
    if (rawEnd < b.length) b.copy(out, rawEnd + shift, rawEnd);

    /* the headers */
    out.writeUInt32LE(h.oep, p.opt + 16);
    plan.forEach((x) => {
        out.writeUInt32LE(x.size, x.s.at + 16);
        out.writeUInt32LE(x.size ? x.ptr : 0, x.s.at + 20);
    });
    if (code && code.length > h.code.vs) out.writeUInt32LE(code.length, h.code.at + 8);
    if (dropBind) {
        out.fill(0, bind.at, bind.at + 40);
        out.writeUInt16LE(p.sections.length - 1, p.pe + 6);
        const kept = p.sections.filter((s) => s !== bind);
        out.writeUInt32LE(kept.reduce((m, s) => Math.max(m, s.va + align(Math.max(code && s === h.code ? code.length : 0, s.vs || s.raw), p.sectAlign)), align(p.sizeOfHeaders, p.sectAlign)), p.opt + 56);
    }
    /* file offsets in the directories: the certificates (4), the debug data (6) */
    const sec = p.dirs[4];
    if (sec && sec.size && sec.rva) out.writeUInt32LE(mapOff(sec.rva) || 0, p.dirAt + 4 * 8);
    const dbg = p.dirs[6];
    if (dbg && dbg.size) {
        const at = rvaToOff(p, dbg.rva);
        if (at !== null) {
            const nat = mapOff(at);
            for (let i = 0; nat !== null && i + 28 <= dbg.size; i += 28) {
                const old = out.readUInt32LE(nat + i + 24);
                if (old) out.writeUInt32LE(mapOff(old) || 0, nat + i + 24);
            }
        }
    }
    /* a checksum that was there is made right again; none stays none */
    if (out.readUInt32LE(p.checksumAt)) out.writeUInt32LE(peChecksum(out, p.checksumAt), p.checksumAt);
    return { buffer: out, info: Object.assign(describe(p, h), { bindRemoved: dropBind }) };
}

function unpack(input, output) {
    const r = unpackBuffer(fs.readFileSync(input));
    fs.writeFileSync(output, r.buffer);
    return r.info;
}

/* ---- in place, for the tool ------------------------------------------------- */

/* on: the program unwrapped where it is, Steam's kept as <file>.vzs-orig (a
 * new wrapped one, from an update, replaces the kept one); off: Steam's put
 * back. Returns what happened: 'unwrapped' (with info), 'already',
 * 'restored', 'nothing'. Throws (StubError) when it can't. */
function unwrapExe(file, on) {
    const orig = file + ORIG, tmp = file + '.vzs-tmp';
    if (!on) {
        if (!fs.existsSync(orig)) return { done: 'nothing' };
        fs.unlinkSync(file);
        fs.renameSync(orig, file);
        return { done: 'restored' };
    }
    const now = detect(file);
    if (now && now.supported) {
        const info = unpack(file, tmp);
        try {
            if (fs.existsSync(orig)) fs.unlinkSync(orig);
            fs.renameSync(file, orig);
            fs.renameSync(tmp, file);
        } catch (e) {
            try { fs.unlinkSync(tmp); } catch (e2) { /* gone */ }
            throw e;
        }
        return { done: 'unwrapped', info: info };
    }
    if (fs.existsSync(orig)) return { done: 'already' };
    if (now) fail(now.why);
    fail('Steam\'s DRM wrapper isn\'t on this program');
}

module.exports = { detect, detectBuffer, unpack, unpackBuffer, unwrapExe, peChecksum, xorDecode, StubError, SIG, NO_ENCRYPTION, ORIG };
