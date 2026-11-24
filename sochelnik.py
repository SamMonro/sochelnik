#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Сочельник 2026 — розыгрыш с интернет-туннелем и fallback на Wi-Fi."""
from __future__ import annotations
import argparse
import collections
import ipaddress
import itertools
import json
import platform
import random
import re
import secrets
import shutil
import socket
import stat
import subprocess
import tarfile
import threading
import time
import unicodedata
import urllib.request
import webbrowser
from http import cookies
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

# --- QR (упрощённый порт Nayuki; kanji-режим не нужен — имена кириллицей) ---

class QrCode:
    @staticmethod
    def encode_text(text, ecl):
        return QrCode.encode_segments(QrSegment.make_segments(text), ecl)

    @staticmethod
    def encode_segments(segs, ecl, minversion=1, maxversion=40, mask=-1, boostecl=True):
        if not (1 <= minversion <= maxversion <= 40) or not (-1 <= mask <= 7):
            raise ValueError("Invalid value")
        for version in range(minversion, maxversion + 1):
            cap = QrCode._get_num_data_codewords(version, ecl) * 8
            used = QrSegment.get_total_bits(segs, version)
            if used is not None and used <= cap:
                break
            if version >= maxversion:
                raise DataTooLongError("Segment too long")
        for newecl in (QrCode.Ecc.MEDIUM, QrCode.Ecc.QUARTILE, QrCode.Ecc.HIGH):
            if boostecl and used <= QrCode._get_num_data_codewords(version, newecl) * 8:
                ecl = newecl
        bb = _BitBuffer()
        for seg in segs:
            bb.append_bits(seg.get_mode().get_mode_bits(), 4)
            bb.append_bits(seg.get_num_chars(), seg.get_mode().num_char_count_bits(version))
            bb.extend(seg._bitdata)
        cap = QrCode._get_num_data_codewords(version, ecl) * 8
        bb.append_bits(0, min(4, cap - len(bb)))
        bb.append_bits(0, -len(bb) % 8)
        for padbyte in itertools.cycle((0xEC, 0x11)):
            if len(bb) >= cap:
                break
            bb.append_bits(padbyte, 8)
        datacodewords = bytearray([0] * (len(bb) // 8))
        for i, bit in enumerate(bb):
            datacodewords[i >> 3] |= bit << (7 - (i & 7))
        return QrCode(version, ecl, datacodewords, mask)

    def __init__(self, version, errcorlvl, datacodewords, msk):
        self._version = version
        self._size = version * 4 + 17
        self._errcorlvl = errcorlvl
        self._modules = [[False] * self._size for _ in range(self._size)]
        self._isfunction = [[False] * self._size for _ in range(self._size)]
        self._draw_function_patterns()
        allcw = self._add_ecc_and_interleave(bytearray(datacodewords))
        self._draw_codewords(allcw)
        if msk == -1:
            best, minp = 0, 1 << 32
            for i in range(8):
                self._apply_mask(i); self._draw_format_bits(i)
                p = self._get_penalty_score()
                if p < minp:
                    best, minp = i, p
                self._apply_mask(i)
            msk = best
        self._mask = msk
        self._apply_mask(msk)
        self._draw_format_bits(msk)
        del self._isfunction

    def get_size(self): return self._size
    def get_module(self, x, y):
        return 0 <= x < self._size and 0 <= y < self._size and self._modules[y][x]

    def _draw_function_patterns(self):
        for i in range(self._size):
            self._set_function_module(6, i, i % 2 == 0)
            self._set_function_module(i, 6, i % 2 == 0)
        self._draw_finder_pattern(3, 3)
        self._draw_finder_pattern(self._size - 4, 3)
        self._draw_finder_pattern(3, self._size - 4)
        pos = self._get_alignment_pattern_positions()
        skips = ((0, 0), (0, len(pos) - 1), (len(pos) - 1, 0))
        for i, x in enumerate(pos):
            for j, y in enumerate(pos):
                if (i, j) not in skips:
                    self._draw_alignment_pattern(x, y)
        self._draw_format_bits(0)
        self._draw_version()

    def _draw_format_bits(self, mask):
        data = self._errcorlvl.formatbits << 3 | mask
        rem = data
        for _ in range(10):
            rem = (rem << 1) ^ ((rem >> 9) * 0x537)
        bits = (data << 10 | rem) ^ 0x5412
        for i in range(6): self._set_function_module(8, i, _get_bit(bits, i))
        self._set_function_module(8, 7, _get_bit(bits, 6))
        self._set_function_module(8, 8, _get_bit(bits, 7))
        self._set_function_module(7, 8, _get_bit(bits, 8))
        for i in range(9, 15): self._set_function_module(14 - i, 8, _get_bit(bits, i))
        for i in range(8): self._set_function_module(self._size - 1 - i, 8, _get_bit(bits, i))
        for i in range(8, 15): self._set_function_module(8, self._size - 15 + i, _get_bit(bits, i))
        self._set_function_module(8, self._size - 8, True)

    def _draw_version(self):
        if self._version < 7: return
        rem = self._version
        for _ in range(12):
            rem = (rem << 1) ^ ((rem >> 11) * 0x1F25)
        bits = self._version << 12 | rem
        for i in range(18):
            bit = _get_bit(bits, i)
            a, b = self._size - 11 + i % 3, i // 3
            self._set_function_module(a, b, bit)
            self._set_function_module(b, a, bit)

    def _draw_finder_pattern(self, x, y):
        for dy in range(-4, 5):
            for dx in range(-4, 5):
                xx, yy = x + dx, y + dy
                if 0 <= xx < self._size and 0 <= yy < self._size:
                    self._set_function_module(xx, yy, max(abs(dx), abs(dy)) not in (2, 4))

    def _draw_alignment_pattern(self, x, y):
        for dy in range(-2, 3):
            for dx in range(-2, 3):
                self._set_function_module(x + dx, y + dy, max(abs(dx), abs(dy)) != 1)

    def _set_function_module(self, x, y, isdark):
        self._modules[y][x] = isdark
        self._isfunction[y][x] = True

    def _add_ecc_and_interleave(self, data):
        v = self._version
        nb = QrCode._NUM_ECC_BLOCKS[self._errcorlvl.ordinal][v]
        bl = QrCode._ECC_PER_BLOCK[self._errcorlvl.ordinal][v]
        raw = QrCode._get_num_raw_data_modules(v) // 8
        nshort = nb - raw % nb
        shortlen = raw // nb
        blocks = []
        rsdiv = QrCode._reed_solomon_compute_divisor(bl)
        k = 0
        for i in range(nb):
            dat = data[k:k + shortlen - bl + (0 if i < nshort else 1)]
            k += len(dat)
            ecc = QrCode._reed_solomon_compute_remainder(dat, rsdiv)
            if i < nshort: dat.append(0)
            blocks.append(dat + ecc)
        result = bytearray()
        for i in range(len(blocks[0])):
            for j, blk in enumerate(blocks):
                if i != shortlen - bl or j >= nshort:
                    result.append(blk[i])
        return result

    def _draw_codewords(self, data):
        i = 0
        for right in range(self._size - 1, 0, -2):
            if right <= 6: right -= 1
            for vert in range(self._size):
                for j in range(2):
                    x = right - j
                    upward = (right + 1) & 2 == 0
                    y = (self._size - 1 - vert) if upward else vert
                    if not self._isfunction[y][x] and i < len(data) * 8:
                        self._modules[y][x] = _get_bit(data[i >> 3], 7 - (i & 7))
                        i += 1

    def _apply_mask(self, mask):
        masker = QrCode._MASK_PATTERNS[mask]
        for y in range(self._size):
            for x in range(self._size):
                self._modules[y][x] ^= (masker(x, y) == 0) and not self._isfunction[y][x]

    def _get_penalty_score(self):
        result, size, mod = 0, self._size, self._modules
        for y in range(size):
            rc, rx, hist = False, 0, collections.deque([0] * 7, 7)
            for x in range(size):
                if mod[y][x] == rc:
                    rx += 1
                    if rx == 5: result += 3
                    elif rx > 5: result += 1
                else:
                    self._finder_penalty_add_history(rx, hist)
                    if not rc: result += self._finder_penalty_count_patterns(hist) * 40
                    rc, rx = mod[y][x], 1
            result += self._finder_penalty_terminate_and_count(rc, rx, hist) * 40
        for x in range(size):
            rc, ry, hist = False, 0, collections.deque([0] * 7, 7)
            for y in range(size):
                if mod[y][x] == rc:
                    ry += 1
                    if ry == 5: result += 3
                    elif ry > 5: result += 1
                else:
                    self._finder_penalty_add_history(ry, hist)
                    if not rc: result += self._finder_penalty_count_patterns(hist) * 40
                    rc, ry = mod[y][x], 1
            result += self._finder_penalty_terminate_and_count(rc, ry, hist) * 40
        for y in range(size - 1):
            for x in range(size - 1):
                if mod[y][x] == mod[y][x + 1] == mod[y + 1][x] == mod[y + 1][x + 1]:
                    result += 3
        dark = sum(1 for row in mod for c in row if c)
        total = size ** 2
        k = (abs(dark * 20 - total * 10) + total - 1) // total - 1
        return result + k * 10

    def _get_alignment_pattern_positions(self):
        if self._version == 1: return []
        n = self._version // 7 + 2
        step = (self._version * 8 + n * 3 + 5) // (n * 4 - 4) * 2
        return list(reversed([self._size - 7 - i * step for i in range(n - 1)] + [6]))

    @staticmethod
    def _get_num_raw_data_modules(v):
        r = (16 * v + 128) * v + 64
        if v >= 2:
            n = v // 7 + 2
            r -= (25 * n - 10) * n - 55
            if v >= 7: r -= 36
        return r

    @staticmethod
    def _get_num_data_codewords(v, ecl):
        return (QrCode._get_num_raw_data_modules(v) // 8
                - QrCode._ECC_PER_BLOCK[ecl.ordinal][v] * QrCode._NUM_ECC_BLOCKS[ecl.ordinal][v])

    @staticmethod
    def _reed_solomon_compute_divisor(degree):
        if not (1 <= degree <= 255): raise ValueError()
        res = bytearray([0] * (degree - 1) + [1])
        root = 1
        for _ in range(degree):
            for j in range(degree):
                res[j] = QrCode._reed_solomon_multiply(res[j], root)
                if j + 1 < degree: res[j] ^= res[j + 1]
            root = QrCode._reed_solomon_multiply(root, 0x02)
        return res

    @staticmethod
    def _reed_solomon_compute_remainder(data, divisor):
        res = bytearray([0] * len(divisor))
        for b in data:
            factor = b ^ res.pop(0)
            res.append(0)
            for i, coef in enumerate(divisor):
                res[i] ^= QrCode._reed_solomon_multiply(coef, factor)
        return res

    @staticmethod
    def _reed_solomon_multiply(x, y):
        z = 0
        for i in reversed(range(8)):
            z = (z << 1) ^ ((z >> 7) * 0x11D)
            z ^= ((y >> i) & 1) * x
        return z

    def _finder_penalty_count_patterns(self, h):
        n = h[1]
        core = n > 0 and h[2] == h[4] == h[5] == n and h[3] == n * 3
        return (1 if (core and h[0] >= n * 4 and h[6] >= n) else 0) + \
               (1 if (core and h[6] >= n * 4 and h[0] >= n) else 0)

    def _finder_penalty_terminate_and_count(self, rc, rl, h):
        if rc:
            self._finder_penalty_add_history(rl, h); rl = 0
        self._finder_penalty_add_history(rl + self._size, h)
        return self._finder_penalty_count_patterns(h)

    def _finder_penalty_add_history(self, rl, h):
        if h[0] == 0: rl += self._size
        h.appendleft(rl)


QrCode._ECC_PER_BLOCK = (
    (-1, 7, 10, 15, 20, 26, 18, 20, 24, 30, 18, 20, 24, 26, 30, 22, 24, 28, 30, 28, 28, 28, 28, 30, 30, 26, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30),
    (-1, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26, 30, 22, 22, 24, 24, 28, 28, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28),
    (-1, 13, 22, 18, 26, 18, 24, 18, 22, 20, 24, 28, 26, 24, 20, 30, 24, 28, 28, 26, 30, 28, 30, 30, 30, 30, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30),
    (-1, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28, 24, 28, 22, 24, 24, 30, 28, 28, 26, 28, 30, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30),
)
QrCode._NUM_ECC_BLOCKS = (
    (-1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4, 4, 6, 6, 6, 6, 7, 8, 8, 9, 9, 10, 12, 12, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 24, 25),
    (-1, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5, 5, 8, 9, 9, 10, 10, 11, 13, 14, 16, 17, 17, 18, 20, 21, 23, 25, 26, 28, 29, 31, 33, 35, 37, 38, 40, 43, 45, 47, 49),
    (-1, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8, 10, 12, 16, 12, 17, 16, 18, 21, 20, 23, 23, 25, 27, 29, 34, 34, 35, 38, 40, 43, 45, 48, 51, 53, 56, 59, 62, 65, 68),
    (-1, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8, 11, 11, 16, 16, 18, 16, 19, 21, 25, 25, 25, 34, 30, 32, 35, 37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 70, 74, 77, 81),
)
QrCode._MASK_PATTERNS = (
    lambda x, y: (x + y) % 2, lambda x, y: y % 2, lambda x, y: x % 3,
    lambda x, y: (x + y) % 3, lambda x, y: (x // 3 + y // 2) % 2,
    lambda x, y: x * y % 2 + x * y % 3, lambda x, y: (x * y % 2 + x * y % 3) % 2,
    lambda x, y: ((x + y) % 2 + x * y % 3) % 2,
)


class _Ecc:
    def __init__(self, i, fb):
        self.ordinal, self.formatbits = i, fb


QrCode.Ecc = type("Ecc", (), {
    "LOW": _Ecc(0, 1), "MEDIUM": _Ecc(1, 0),
    "QUARTILE": _Ecc(2, 3), "HIGH": _Ecc(3, 2),
})


class _Mode:
    def __init__(self, mb, cc):
        self._modebits, self._charcounts = mb, cc
    def get_mode_bits(self): return self._modebits
    def num_char_count_bits(self, v): return self._charcounts[(v + 7) // 17]


class QrSegment:
    @staticmethod
    def make_bytes(data):
        bb = _BitBuffer()
        for b in data: bb.append_bits(b, 8)
        return QrSegment(QrSegment.Mode.BYTE, len(data), bb)

    @staticmethod
    def make_numeric(digits):
        bb = _BitBuffer()
        i = 0
        while i < len(digits):
            n = min(len(digits) - i, 3)
            bb.append_bits(int(digits[i:i + n]), n * 3 + 1); i += n
        return QrSegment(QrSegment.Mode.NUMERIC, len(digits), bb)

    @staticmethod
    def make_alphanumeric(text):
        bb = _BitBuffer()
        for i in range(0, len(text) - 1, 2):
            bb.append_bits(QrSegment._ALNUM[text[i]] * 45 + QrSegment._ALNUM[text[i + 1]], 11)
        if len(text) % 2 > 0:
            bb.append_bits(QrSegment._ALNUM[text[-1]], 6)
        return QrSegment(QrSegment.Mode.ALPHANUMERIC, len(text), bb)

    @staticmethod
    def make_segments(text):
        if text == "": return []
        if QrSegment._NUM_RE.fullmatch(text): return [QrSegment.make_numeric(text)]
        if QrSegment._ALNUM_RE.fullmatch(text): return [QrSegment.make_alphanumeric(text)]
        return [QrSegment.make_bytes(text.encode("UTF-8"))]

    def __init__(self, mode, numch, bitdata):
        self._mode, self._numchars, self._bitdata = mode, numch, list(bitdata)

    def get_mode(self): return self._mode
    def get_num_chars(self): return self._numchars

    @staticmethod
    def get_total_bits(segs, version):
        r = 0
        for seg in segs:
            cb = seg.get_mode().num_char_count_bits(version)
            if seg.get_num_chars() >= (1 << cb): return None
            r += 4 + cb + len(seg._bitdata)
        return r


QrSegment.Mode = type("Mode", (), {
    "NUMERIC": _Mode(0x1, (10, 12, 14)),
    "ALPHANUMERIC": _Mode(0x2, (9, 11, 13)),
    "BYTE": _Mode(0x4, (8, 16, 16)),
})
QrSegment._NUM_RE = re.compile(r"[0-9]*")
QrSegment._ALNUM_RE = re.compile(r"[A-Z0-9 $%+./:\-]*")
QrSegment._ALNUM = {ch: i for i, ch in enumerate("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%+-./:")}


class _BitBuffer(list):
    def append_bits(self, val, n):
        self.extend(((val >> i) & 1) for i in reversed(range(n)))


def _get_bit(x, i): return (x >> i) & 1 != 0


class DataTooLongError(ValueError): pass


# --- HTML / CSS / JS ---

HTML = """<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Сочельник 2026 — Рождественский розыгрыш</title>
<link rel="stylesheet" href="/app.css">
</head>
<body>
<div class="garland" aria-hidden="true"></div>
<div class="snow" aria-hidden="true"><!--SNOW--></div>
<div class="frame" aria-hidden="true"><i></i><i></i><i></i><i></i><i></i><i></i></div>
<header class="masthead"><div class="wordmark">
<svg aria-hidden="true" class="star" viewBox="0 0 48 48"><path d="M24 1l4 16 14-11-10 15 15 3-15 4 10 14-14-10-4 15-4-15L6 42l10-14L1 24l15-3L6 6l14 11z"/></svg>
<span>Сочельник</span><span class="year">2026</span></div></header>
<aside id="notice" role="status" hidden></aside>
<main id="stage"></main>
<div class="fir" aria-hidden="true"></div>
<footer class="base" aria-hidden="true"><i></i><span>Рождественский розыгрыш</span><i></i></footer>
<noscript><p style="text-align:center;padding:1rem">Для участия включи JavaScript в браузере.</p></noscript>
<script src="/app.js"></script>
</body>
</html>"""

CSS = """:root{color-scheme:dark;--bg:#10291f;--ink:#fff8e8;--dim:#dfcfab;--line:#ffffff35;--panel:#19372b;--action:#f8e5b6;--action-ink:#16251d;font-family:system-ui,-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}
*{box-sizing:border-box}
body{margin:0;min-height:100vh;min-height:100dvh;display:flex;flex-direction:column;color:var(--ink);background:radial-gradient(ellipse at 50% 10%,#21463800,transparent 75%),var(--bg);overflow-wrap:anywhere}
body:not(.positive):not(.red){background:radial-gradient(ellipse at 50% 10%,#214638,transparent 75%),var(--bg)}
body.positive{color-scheme:light;--bg:#5dff36;--ink:#102511;--dim:#193c18;--line:#10251150}
body.red{--bg:#da0029;--ink:#fff;--dim:#fff5f0;--line:#ffffff85}
button,input,select{font:inherit}
button,.button{min-height:46px;padding:.7rem 1.15rem;border-radius:9px;background:var(--action);color:var(--action-ink);border:1px solid transparent;font-weight:750;cursor:pointer;text-decoration:none;display:inline-flex;align-items:center;justify-content:center;text-align:center}
button:disabled{opacity:.42;cursor:not-allowed}
button.secondary,.button.secondary{color:var(--ink);background:transparent;border-color:var(--line)}
button:hover:not(:disabled),.button:hover{filter:brightness(1.13)}
:focus-visible{outline:3px solid currentColor;outline-offset:4px}
[hidden]{display:none!important}
.masthead{display:flex;justify-content:center;padding:clamp(1rem,4vh,2.3rem) 1rem .85rem}
.wordmark{display:flex;align-items:center;gap:.65rem;color:var(--ink);letter-spacing:.1em;text-transform:uppercase;font-weight:720;font-size:.87rem;white-space:nowrap}
.star{width:28px;height:28px;fill:currentColor;color:var(--dim)}
.year{border-left:1px solid var(--line);padding-left:.65rem;color:var(--dim);font-variant-numeric:tabular-nums}
#notice{margin:.25rem auto 0;padding:.65rem 1rem;max-width:94%;background:#fff2d4;color:#302318;border-radius:8px;text-align:center}
#stage{display:grid;flex:1;place-items:center;padding:1.1rem clamp(1rem,5vw,3rem)}
.base{margin-top:auto;padding:.8rem 1rem max(1.2rem,env(safe-area-inset-bottom));display:flex;justify-content:center;align-items:center;gap:.8rem;text-transform:uppercase;letter-spacing:.13em;font-size:.64rem;color:var(--dim);text-align:center}
.base i{height:1px;width:clamp(13px,6vw,55px);background:var(--line)}
.center{width:min(100%,60rem);text-align:center}
.eyebrow{font-size:.75rem;font-weight:800;letter-spacing:.15em;text-transform:uppercase;color:var(--dim);margin:0 0 1.1rem}
.tag{display:inline-block;border:1px solid var(--line);border-radius:100px;padding:.55rem .9rem}
.display,h1{font-family:Georgia,'Times New Roman',serif;font-weight:600;letter-spacing:-.045em;text-wrap:balance;line-height:.99;margin:.15em 0 .25em}
.display{font-size:clamp(2.1rem,9vw,6.2rem)}
.guest .display{font-size:clamp(2.1rem,10vw,5.2rem)}
h1{font-size:clamp(2rem,6vw,4rem)}
p{line-height:1.5}
.lead{font-size:clamp(1.04rem,3.1vw,1.45rem);color:var(--dim);max-width:37ch;margin:1rem auto}
.message{font-family:Georgia,'Times New Roman',serif;font-size:clamp(1.47rem,6.3vw,3rem);line-height:1.23;max-width:31ch;margin:1.6rem auto .85rem;text-wrap:balance}
.verse{font-size:.86rem;margin:.65rem 0;color:var(--dim)}
.count{font-size:clamp(1.14rem,3.5vw,2.25rem);font-weight:620;margin:0 0 .45rem}
.count strong{color:var(--action);font-variant-numeric:tabular-nums}
.qr{display:block;width:min(74vw,52vh,510px);height:auto;aspect-ratio:1;margin:.85rem auto;border-radius:12px;box-shadow:0 12px 40px #00150e70}
.url{color:var(--dim);font-size:clamp(.83rem,2vw,1.1rem);margin:.15rem 0;display:inline-block;text-underline-offset:.2em}
.screen-tools{position:fixed;right:.7rem;bottom:.65rem;z-index:2;display:flex;gap:.35rem;opacity:.72}
.screen-tools button{font-size:.75rem;min-height:38px;padding:.3rem .55rem}
.screen-tools:hover{opacity:1}
.roulette{margin:1.45rem auto 0;max-width:48rem;display:grid;gap:.34rem}
.slot{display:grid;place-items:center;border:1px solid var(--line);padding:.9rem 1rem;border-radius:10px;font-family:Georgia,'Times New Roman',serif;font-size:clamp(1.8rem,9vw,5rem);min-height:1.9em;background:#00000025;line-height:1.03}
.ghost{color:var(--dim);opacity:.85;font-size:clamp(.95rem,4vw,1.55rem);min-height:1.5em}
.slot.bump{animation:bump .16s ease-out}
@keyframes bump{from{transform:translateY(5px);opacity:.79}to{transform:none;opacity:1}}
progress{width:min(100%,390px);height:.45rem;accent-color:var(--ink);margin:1.1rem auto .3rem}
.card{width:min(100%,28rem);padding:clamp(1.15rem,5vw,2rem);background:var(--panel);border:1px solid var(--line);border-radius:16px;box-shadow:0 14px 50px #07171060}
.card form{display:grid;gap:.85rem;margin-top:1.4rem}
label{font-size:.95rem;font-weight:620}
input:not([type=checkbox]),select{width:100%;min-height:48px;background:#10251e;color:var(--ink);border:1px solid var(--line);border-radius:8px;padding:.56rem .7rem;font-size:16px}
label>input:not([type=checkbox]){display:block;margin-top:.4rem}
.error{margin:.2rem 0;color:#ffcbbe;font-size:.9rem}
.host #stage{place-items:start center}
.dash{width:min(100%,61rem)}
.dash h1{margin-bottom:.22em}
.dash-grid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.15fr);gap:1rem;margin:1.2rem 0}
.dash .card{width:100%;box-shadow:none}
.dash h2{font-size:1.15rem;margin:.15rem 0 .75rem}
.actions{display:flex;gap:.6rem;flex-wrap:wrap;margin:.65rem 0}
.details{font-size:.87rem;color:var(--dim)}
.people{list-style:none;margin:0;padding:0;max-height:380px;overflow:auto}
.people li{display:flex;align-items:center;justify-content:space-between;gap:.7rem;border-top:1px solid var(--line);padding:.38rem 0}
.people button{min-height:38px;font-size:.75rem;padding:.35rem .6rem}
.winner-label{font-size:.78rem;color:var(--dim);white-space:nowrap}
.stat{font-size:1.3rem;color:var(--action);margin:.4rem 0}
.dash select{margin-top:.35rem}
.result-star{width:clamp(26px,8vw,55px);height:auto;fill:currentColor;color:var(--ink);margin:0 auto .75rem;display:block}
.screen .lead,.screen h1{max-width:30ch;margin-left:auto;margin-right:auto}
@media(max-width:660px){.dash-grid{grid-template-columns:1fr}.screen-tools{position:static;justify-content:center;margin-top:1rem}.screen .qr{width:min(77vw,45vh)}}
@media(prefers-reduced-motion:reduce){.slot.bump{animation:none}.ghost{visibility:hidden}}
.screen .masthead{padding-top:1rem;padding-bottom:.4rem}
.screen #stage{padding-top:.45rem;padding-bottom:.45rem}
.screen .qr{width:min(74vw,47vh,510px);margin:.6rem auto}
.screen .base{padding-bottom:1rem}
.screen .lead{margin-top:.55rem;margin-bottom:.35rem}
.screen h1{font-size:clamp(1.8rem,5.6vw,3.6rem)}"""

# Рождественское оформление. Inline-стили запрещены CSP, поэтому всё — через классы
# и отдельные SVG-файлы (/garland.svg, /fir.svg).
CSS_EXTRA = """
body{position:relative}
.garland,.snow,.frame,.fir{display:none}
body:not(.positive):not(.red) .garland{display:block}
body:not(.positive):not(.red):not(.host) .snow,body:not(.positive):not(.red):not(.host) .fir{display:block}
body.positive .frame,body.red .frame{display:block}
body:not(.positive):not(.red){background:radial-gradient(ellipse at 50% 0%,#7a5a2440,transparent 42%),radial-gradient(ellipse at 50% 12%,#214638,transparent 75%),radial-gradient(ellipse at 50% 100%,#0b1f16,transparent 60%),var(--bg)}
body:not(.positive):not(.red) .display{text-shadow:0 0 32px #ffd37a30}
.garland{position:absolute;top:0;left:0;right:0;height:56px;background:url(/garland.svg) repeat-x center top;background-size:auto 56px;pointer-events:none;z-index:1}
body.screen .garland{height:44px;background-size:auto 44px}
.masthead{position:relative;z-index:2}
body:not(.positive):not(.red) .masthead{padding-top:clamp(2.7rem,9vh,3.7rem)}
body.screen:not(.positive):not(.red) .masthead{padding-top:2.15rem;padding-bottom:.3rem}
#stage,.base{position:relative;z-index:1}
.snow{position:fixed;inset:0;pointer-events:none;overflow:hidden;z-index:0}
.snow i{position:absolute;top:-12px;border-radius:50%;background:#fff;opacity:0;filter:blur(.4px);animation:fall linear infinite}
@keyframes fall{0%{transform:translate3d(0,0,0);opacity:0}8%{opacity:.85}92%{opacity:.85}100%{transform:translate3d(var(--dx,0),108vh,0);opacity:0}}
.fir{position:relative;z-index:1;height:34px;margin-top:auto;background:url(/fir.svg) repeat-x center bottom;background-size:auto 34px;-webkit-mask-image:linear-gradient(90deg,transparent,#000 10%,#000 90%,transparent);mask-image:linear-gradient(90deg,transparent,#000 10%,#000 90%,transparent);pointer-events:none}
body.screen .fir{height:26px;background-size:auto 26px}
body:not(.positive):not(.red):not(.host) .base{margin-top:0}
.frame{position:fixed;inset:12px;border:2px solid var(--ink);border-radius:6px;pointer-events:none;z-index:0}
.frame::before{content:'';position:absolute;inset:6px;border:1px solid var(--ink);border-radius:3px;opacity:.55}
.frame i{position:absolute;width:15px;height:15px;background:var(--bg);border:2px solid var(--ink);transform:rotate(45deg)}
.frame i:nth-child(1){top:-8px;left:-8px}
.frame i:nth-child(2){top:-8px;right:-8px}
.frame i:nth-child(3){bottom:-8px;left:-8px}
.frame i:nth-child(4){bottom:-8px;right:-8px}
.frame i:nth-child(5){top:-6px;left:calc(50% - 5px);width:11px;height:11px}
.frame i:nth-child(6){bottom:-6px;left:calc(50% - 5px);width:11px;height:11px}
body.positive #stage,body.red #stage{padding:2rem clamp(1.9rem,6vw,3.5rem)}
body.positive .masthead,body.red .masthead{padding-top:2.2rem}
body.positive .base,body.red .base{padding-bottom:max(2.1rem,env(safe-area-inset-bottom))}
.quote{--q:var(--ink);position:relative;width:min(100%,36rem);margin:1.7rem auto 1rem;padding:4px;border:2px solid var(--q);border-radius:15px}
body:not(.positive):not(.red) .quote{--q:var(--action)}
.quote::before,.quote::after{content:'';position:absolute;left:50%;width:12px;height:12px;background:var(--q);transform:translateX(-50%) rotate(45deg)}
.quote::before{top:-8px}
.quote::after{bottom:-8px}
.quote-in{border:1px solid var(--q);border-radius:10px;padding:1.5rem 1rem 1.2rem}
.quote .message{margin:0 auto .4rem}
.quote .verse{margin:.5rem 0 0}
.tree{display:block;width:clamp(46px,10vw,78px);height:auto;margin:0 auto .5rem}
.orn{position:relative;width:min(70%,16rem);height:12px;margin:.8rem auto;background:linear-gradient(90deg,transparent,var(--action)) left center/calc(50% - 14px) 1px no-repeat,linear-gradient(270deg,transparent,var(--action)) right center/calc(50% - 14px) 1px no-repeat}
.orn::after{content:'';position:absolute;left:calc(50% - 4px);top:2px;width:8px;height:8px;background:var(--action);transform:rotate(45deg)}
.center .card{margin-left:auto;margin-right:auto}
.card.festive{border-color:#f8e5b680;outline:1px solid #f8e5b645;outline-offset:5px}
.qr-frame{position:relative;width:fit-content;max-width:100%;margin:.9rem auto;padding:.85rem;border:2px solid var(--action);border-radius:18px}
.qr-frame::before,.qr-frame::after{content:'';position:absolute;left:calc(50% - 6px);width:12px;height:12px;background:var(--action);transform:rotate(45deg)}
.qr-frame::before{top:-8px}
.qr-frame::after{bottom:-8px}
.qr-frame .qr{margin:0;box-shadow:none;outline:1px solid #f8e5b680;outline-offset:6px}
.screen .qr-frame .qr{width:min(74vw,42vh,480px)}
@media(prefers-reduced-motion:reduce){.snow{display:none!important}}
"""

_rng = random.Random(24)
CSS += CSS_EXTRA + ''.join(
    '.snow i:nth-child({n}){{left:{x:.1f}%;width:{s}px;height:{s}px;--dx:{dx}vw;'
    'animation-duration:{d:.1f}s;animation-delay:-{dl:.1f}s}}'.format(
        n=n, x=_rng.uniform(1, 98), s=_rng.choice((3, 4, 4, 5, 6, 7)),
        dx=_rng.randint(-7, 7), d=_rng.uniform(9, 19), dl=_rng.uniform(0, 19))
    for n in range(1, 29))
HTML = HTML.replace('<!--SNOW-->', '<i></i>' * 28)


def _garland_svg():
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="140" height="56" viewBox="0 0 140 56">',
           '<path d="M0,8 Q70,40 140,8" fill="none" stroke="#86ab96" stroke-width="1.6"/>']
    colors = ('#ffcf5a', '#e5384a', '#fff1c9', '#6fd08c')
    for i, t in enumerate((0.125, 0.375, 0.625, 0.875)):
        x = 140 * t
        y = 8 * (1 - t) ** 2 + 80 * (1 - t) * t + 8 * t * t
        c = colors[i]
        out.append(
            f'<g><rect x="{x - 2:.1f}" y="{y - 1:.1f}" width="4" height="6" rx="1" fill="#2a3d33"/>'
            f'<circle cx="{x:.1f}" cy="{y + 12:.1f}" r="11" fill="{c}" opacity=".18"/>'
            f'<ellipse cx="{x:.1f}" cy="{y + 12:.1f}" rx="4.8" ry="6.8" fill="{c}"/>'
            f'<animate attributeName="opacity" values="1;.5;1" dur="{2.2 + i * .5:.1f}s" '
            f'begin="-{i * .7:.1f}s" repeatCount="indefinite"/></g>')
    out.append('</svg>')
    return ''.join(out)


def _fir_svg():
    greens = ('#2f7a54', '#3f9a6c', '#276646')
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="160" height="44" viewBox="0 0 160 44">',
           '<path d="M0,22 H160" stroke="#5a3b24" stroke-width="2.2"/>']
    for n, x in enumerate(range(0, 153, 8)):
        up, dn = 9 + (n * 5) % 4 * 2, 9 + (n * 3) % 4 * 2
        out.append(f'<path d="M{x},22 L{x + 6},{22 - up} M{x},22 L{x + 6},{22 + dn}" stroke="{greens[n % 3]}" '
                   f'stroke-width="2.4" stroke-linecap="round" fill="none"/>')
        out.append(f'<path d="M{x + 4},22 L{x + 8},{22 - 6 if n % 2 else 22 + 6}" stroke="{greens[(n + 1) % 3]}" '
                   f'stroke-width="2" stroke-linecap="round" fill="none"/>')
    for cx in (36, 100, 148):
        out.append(f'<circle cx="{cx}" cy="22" r="2.8" fill="#d63a46"/>'
                   f'<circle cx="{cx + 5}" cy="25.5" r="2.8" fill="#d63a46"/>'
                   f'<circle cx="{cx + 4}" cy="18.5" r="2.8" fill="#e5535d"/>')
    out.append('</svg>')
    return ''.join(out)


GARLAND_SVG = _garland_svg()
FIR_SVG = _fir_svg()

JS = r"""(() => {
'use strict';
const $ = (id) => document.getElementById(id);
const stage = $('stage'), notice = $('notice');
const role = location.pathname === '/host' ? 'host' : location.pathname === '/screen' ? 'screen' : 'guest';
document.body.classList.add(role);
let key = '', state = null, signature = '', pollTimer = 0, busy = false, fetching = false;
let spinClock = null, anim = 0;
if (role === 'host') {
  try { key = sessionStorage.getItem('sochelnik-key') || ''; } catch (e) {}
  if (location.hash.slice(1)) {
    key = location.hash.slice(1);
    try { sessionStorage.setItem('sochelnik-key', key); history.replaceState(null, '', '/host'); } catch (e) {}
  }
}
const star = '<svg aria-hidden="true" class="result-star" viewBox="0 0 48 48"><path d="M24 1l4 16 14-11-10 15 15 3-15 4 10 14-14-10-4 15-4-15L6 42l10-14L1 24l15-3L6 6l14 11z"/></svg>';
const bulb = (x, y, r, c, d) => '<circle cx="' + x + '" cy="' + y + '" r="' + r + '" fill="' + c + '"><animate attributeName="opacity" values="1;.35;1" dur="' + d + 's" repeatCount="indefinite"/></circle>';
const tree = '<svg aria-hidden="true" class="tree" viewBox="0 0 64 84">' +
  '<polygon points="32,12 46,36 18,36" fill="#3a8c62"/><polygon points="32,24 53,54 11,54" fill="#2f7a54"/>' +
  '<polygon points="32,38 59,73 5,73" fill="#276646"/><rect x="28" y="73" width="8" height="9" rx="1" fill="#7a4e2d"/>' +
  '<svg x="23" y="0" width="18" height="18" viewBox="0 0 48 48"><path fill="#ffd36b" d="M24 1l4 16 14-11-10 15 15 3-15 4 10 14-14-10-4 15-4-15L6 42l10-14L1 24l15-3L6 6l14 11z"/></svg>' +
  bulb(30, 31, 2.4, '#ffd36b', 2.4) + bulb(37, 44, 2.8, '#e5384a', 3.1) + bulb(24, 49, 2.6, '#fff1c9', 2.8) +
  bulb(35, 60, 2.4, '#ffd36b', 3.4) + bulb(46, 66, 2.8, '#e5384a', 2.6) + bulb(19, 65, 3, '#fff1c9', 3.7) +
  bulb(30, 68, 2.4, '#e5384a', 2.9) + '</svg>';
const orn = '<div class="orn" aria-hidden="true"></div>';
const quote = (inner) => '<div class="quote"><div class="quote-in">' + inner + '</div></div>';
const phaseNames = {open: 'Регистрация открыта', closed: 'Регистрация завершена', spin: 'Выбираем победителя', result: 'Победитель определён'};

async function api(path, data) {
  const headers = role === 'host' ? {'X-Host-Key': key} : {};
  const opts = {headers, cache: 'no-store'};
  const controller = new AbortController();
  opts.signal = controller.signal;
  if (data) { opts.method = 'POST'; opts.body = JSON.stringify(data); headers['Content-Type'] = 'application/json'; }
  const timeout = setTimeout(() => controller.abort(), 4500);
  try {
    const res = await fetch(path, opts);
    const out = await res.json();
    if (!res.ok) throw new Error(out.error || 'Действие не выполнено.');
    return out;
  } finally { clearTimeout(timeout); }
}
function errorText(e) { return e instanceof TypeError || e.name === 'AbortError' ? 'Нет связи с ведущим. Проверь интернет и попробуй ещё раз.' : e.message; }
function text(id, value) { if ($(id)) $(id).textContent = value; }
function setAccent(tone) {
  document.body.classList.toggle('positive', tone === 'positive');
  document.body.classList.toggle('red', tone === 'red');
}
function center(markup) { stage.innerHTML = '<div class="center">' + markup + '</div>'; }
function urlFor(s) { return s.urls[s.network] || s.urls[0]; }
function screenTools() { return '<div class="screen-tools"><button id="fullscreen" class="secondary">На весь экран</button></div>'; }
function spinMarkup(s) {
  return '<p class="eyebrow">Раунд ' + s.round + '</p><h1 class="display">Выбираем победителя</h1>' +
    '<div class="roulette"><div class="ghost" id="prev"></div><div class="slot" id="slot"></div><div class="ghost" id="next"></div></div>' +
    '<progress id="bar" max="1" value="0"></progress>';
}

function guest(s) {
  if (!s.joined) {
    setAccent('');
    if (s.phase !== 'open') return center(tree + '<p class="eyebrow">Рождественский розыгрыш</p><h1 class="display">Регистрация завершена</h1>' + orn + '<p class="lead">Если регистрация уже была, вернись в тот же браузер и на тот же адрес.</p>');
    stage.innerHTML = '<div class="center">' + tree + '<p class="eyebrow">Регистрация открыта</p><h1 class="display">Участвуй в розыгрыше</h1>' + orn + '<p class="lead">Введи имя и фамилию, затем оставь эту вкладку открытой.</p>' +
      '<form id="join-form" class="card festive"><label>Имя<input name="first" required maxlength="20" autocomplete="given-name"></label>' +
      '<label>Фамилия<input name="last" required maxlength="20" autocomplete="family-name"></label>' +
      '<button id="join-btn" type="submit">Участвовать</button><p id="join-error" class="error" hidden></p></form></div>';
    $('join-form').addEventListener('submit', join);
    return;
  }
  if (s.phase === 'open') {
    setAccent('positive');
    center(star + '<p class="eyebrow">Место в списке подтверждено</p><h1 class="display">Ты учавствуешь!</h1>' + quote('<p class="message"><span id="you"></span></p>') + '<p class="lead">Оставь этот экран открытым. Рулетка запустится сама.</p>');
    text('you', s.you);
  } else if (s.phase === 'closed') {
    setAccent('');
    center(tree + '<p class="eyebrow">Ты в списке</p><h1 class="display">Регистрация завершена</h1>' + orn + '<p class="lead">Скоро начнётся розыгрыш. Не закрывай экран.</p>');
  } else if (s.phase === 'spin') {
    setAccent('red');
    center(spinMarkup(s));
  } else if (s.won) {
    setAccent('positive');
    center(star + '<p class="eyebrow">Результат розыгрыша</p><h1 class="display">Приз твой!</h1>' + quote('<p class="message"><span id="you"></span></p>') + '<p class="lead">Подними телефон и покажи зелёный экран ведущему.</p>');
    text('you', s.you);
  } else if (s.prior) {
    setAccent('red');
    center('<p class="eyebrow">Спасибо за участие</p><h1 class="display">У тебя уже есть приз</h1>');
  } else {
    setAccent('red');
    center('<p class="eyebrow">Спасибо за участие</p><h1 class="display">Сегодня без приза</h1>' + quote('<p class="message" id="message"></p><p class="verse" id="verse"></p>') + '');
    text('message', s.message[0]);
    text('verse', 'По мотивам: ' + s.message[1]);
  }
}

function screen(s) {
  setAccent('');
  if (s.phase === 'open') {
    center('<p class="eyebrow">Зарегистрировано человек: <strong id="count">0</strong></p><h1 class="display">Рождественский розыгрыш</h1>' +
      '<p class="lead">Наведи камеру телефона на код</p><div class="qr-frame"><img class="qr" id="qr" alt="QR-код для входа"></div><a class="url" id="address" href="#"></a>' + screenTools());
    $('qr').src = '/qr.svg?i=' + s.network;
    $('address').href = urlFor(s);
    text('address', urlFor(s));
  } else if (s.phase === 'closed') {
    center(tree + '<p class="eyebrow">Все участники в списке</p><h1 class="display">Регистрация завершена</h1>' + orn + '<p class="lead">Оставьте страницу открытой. Скоро на телефонах запустится рулетка.</p>' + screenTools());
  } else if (s.phase === 'spin') {
    center(spinMarkup(s) + screenTools());
  } else {
    center(star + '<p class="eyebrow">Результат розыгрыша</p><h1 class="display">Поздравляем!</h1>' + quote('<p class="message"><span id="winner"></span></p>') + '<p class="lead">Покажи ведущему зелёный экран на телефоне.</p>' + screenTools());
    text('winner', s.winner);
  }
  if ($('fullscreen')) {
    const fs = $('fullscreen');
    fs.hidden = !document.documentElement.requestFullscreen;
    fs.onclick = async () => {
      try { if (document.fullscreenElement) await document.exitFullscreen(); else await document.documentElement.requestFullscreen(); }
      catch (e) { fs.textContent = 'Используй полноэкранный режим браузера'; }
    };
  }
}

function host(s) {
  stage.innerHTML = '<div class="dash"><p class="eyebrow">Рождественский розыгрыш</p><h1>Панель ведущего</h1>' +
    '<div class="dash-grid"><div class="card"><h2>Управление</h2>' +
    '<p class="details"><a href="/screen" target="_blank" rel="noopener" class="button">Открыть экран проектора</a></p>' +
    '<p class="details">Перетащи окно браузера на проектор и включи полноэкранный режим.</p>' +
    '<p class="details">Адрес участников: <a id="host-address" href="#" class="url"></a></p>' +
    '<label>Режим сети<select id="network"></select></label>' +
    '<p class="details">По умолчанию выбран интернет-туннель. Если интернет на ноутбуке пропадёт — переключись на локальный Wi-Fi (гости должны быть в той же сети).</p>' +
    '<p class="stat" id="host-status"></p><p id="host-winner" class="message"></p>' +
    '<div class="actions" id="actions"></div><p class="details" id="note"></p><p id="host-error" class="error" hidden></p></div>' +
    '<div class="card"><h2 id="people-title">Участники: 0</h2><p id="empty" class="details">Пока никого нет. Покажи QR-код участникам.</p><ul class="people" id="people"></ul></div></div></div>';
  const network = $('network');
  s.urls.forEach((url, i) => network.add(new Option(url, i)));
  network.value = s.network;
  network.disabled = s.urls.length < 2 || s.phase !== 'open' || s.count > 0;
  network.onchange = async () => { await control('network', Number(network.value), network); if (network.isConnected) network.value = state.network; };
  $('host-address').href = urlFor(s); text('host-address', urlFor(s));
  function add(op, label, secondary = false, disabled = false) {
    const b = document.createElement('button');
    b.textContent = label; b.disabled = disabled;
    if (secondary) b.className = 'secondary';
    b.onclick = () => {
      if (op === 'reset' && !confirm('Очистить список и начать новый розыгрыш?')) return;
      if (op === 'redraw' && !confirm('Повторить рулетку? Результат этого раунда будет отменён, участники те же.')) return;
      control(op, null, b);
    };
    $('actions').append(b);
  }
  text('host-status', phaseNames[s.phase] + (s.round ? ' · Раунд ' + s.round : ''));
  if (s.phase === 'open') add('close', 'Завершить регистрацию', false, !s.count);
  if (s.phase === 'closed') { add('draw', 'Запустить рулетку', false, !s.eligible); add('open', 'Открыть регистрацию снова', true); }
  if (s.phase === 'result') { add('draw', 'Следующий приз', false, !s.eligible); add('redraw', 'Повторить рулетку', true); }
  if (s.phase !== 'spin') add('reset', 'Очистить список', true, !s.count);
  text('note', s.phase === 'spin' ? 'Рулетка идёт на проекторе и на телефонах.' : s.phase === 'result' ? '«Следующий приз» разыгрывается без прежних победителей. «Повторить рулетку» отменяет этот результат и крутит заново среди тех же участников.' : 'В следующем раунде прежние победители не участвуют.');
  text('host-winner', s.winner ? 'Победитель: ' + s.winner : '');
  text('people-title', 'Участники: ' + s.count);
  $('empty').hidden = !!s.count;
  for (const p of s.people) {
    const li = document.createElement('li'), name = document.createElement('span');
    name.textContent = p.name; li.append(name);
    if (p.won) {
      const label = document.createElement('span'); label.className = 'winner-label'; label.textContent = 'Есть приз'; li.append(label);
    } else if (s.phase === 'open' || s.phase === 'closed') {
      const b = document.createElement('button'); b.className = 'secondary'; b.textContent = 'Убрать';
      b.setAttribute('aria-label', 'Убрать из списка: ' + p.name);
      b.onclick = () => { if (confirm('Убрать из списка: ' + p.name + '?')) control('remove', p.id, b); };
      li.append(b);
    }
    $('people').append(li);
  }
}

function advance(now) {
  if (!spinClock || !$('slot')) return;
  const {tape, anchor, elapsed, duration} = spinClock;
  const progress = Math.min(1, (elapsed + (now - anchor) / 1000) / duration);
  const i = Math.floor(42 * (1 - Math.pow(1 - progress, 1.9)));
  $('bar').value = progress;
  if (i !== spinClock.last && tape.length) {
    const slot = $('slot');
    text('slot', tape[i % tape.length]);
    text('prev', tape.length > 1 ? tape[(i + tape.length - 1) % tape.length] : '');
    text('next', tape.length > 1 ? tape[(i + 1) % tape.length] : '');
    if (spinClock.last != null) { slot.classList.remove('bump'); void slot.offsetWidth; slot.classList.add('bump'); }
    spinClock.last = i;
  }
  anim = requestAnimationFrame(advance);
}

function update(s, delay = 0) {
  if (state && s.revision < state.revision) return;
  state = s;
  const sig = JSON.stringify([s.phase, s.round, s.joined, s.you, s.won, s.prior, s.winner, s.message, s.network, s.urls, role === 'host' ? s.people : null]);
  if (signature !== sig) {
    signature = sig;
    cancelAnimationFrame(anim);
    spinClock = null;
    ({guest, screen, host})[role](s);
  }
  if (role === 'screen') text('count', s.count);
  if (s.phase === 'spin' && $('slot') && s.tape && !spinClock) {
    spinClock = {tape: s.tape, anchor: performance.now(), elapsed: s.elapsed + delay / 2000, duration: s.duration, last: null};
    advance(performance.now());
  }
}

async function poll() {
  if (fetching || busy) return;
  fetching = true;
  const start = performance.now();
  try {
    const s = await api(role === 'host' ? '/host-state' : role === 'screen' ? '/state?screen=1' : '/state');
    if (!busy) { notice.hidden = true; update(s, performance.now() - start); }
  } catch (e) {
    notice.textContent = !state && role === 'host' ? errorText(e) : 'Связь с ведущим прервалась. Восстанавливаем соединение…';
    notice.hidden = false;
  } finally { fetching = false; schedule(); }
}
function schedule() { clearTimeout(pollTimer); pollTimer = setTimeout(poll, (state?.phase === 'spin' ? 350 : 900) + Math.random() * 180); }
async function join(e) {
  e.preventDefault(); if (busy) return;
  busy = true; const b = $('join-btn'), err = $('join-error'), form = new FormData(e.currentTarget);
  b.disabled = true; err.hidden = true;
  try { update(await api('/register', {first: form.get('first'), last: form.get('last')})); }
  catch (e) { err.textContent = errorText(e); err.hidden = false; }
  finally { b.disabled = false; busy = false; schedule(); }
}
async function control(op, id, button) {
  if (busy) return;
  busy = true; button.disabled = true;
  const err = $('host-error'); err.hidden = true;
  try { update(await api('/control', {op, id})); }
  catch (e) { err.textContent = errorText(e); err.hidden = false; }
  finally { if (signature && button.isConnected) button.disabled = false; busy = false; schedule(); }
}
document.addEventListener('visibilitychange', () => { if (!document.hidden) poll(); });
window.addEventListener('online', poll);
poll();
})();"""


# --- Игровая логика ---

DURATION = 10.0  # увеличено с 8.5: задержка туннеля 300–1500 мс
LIMIT = 500
MESSAGES = [
    ('Сегодня приз достался не тебе. Но Божья любовь не зависит от исхода розыгрыша.', 'Римлянам 8:38–39'),
    ('Пусть впереди будет ещё много поводов благодарить Бога за неожиданные дары.', 'Иакова 1:17'),
    ('Даже если сегодня без приза, надежда остаётся. Пусть Бог наполнит сердце миром и радостью.', 'Римлянам 15:13'),
    ('Господь знает тебя по имени. Для этого не нужна рулетка.', 'Исаия 43:1'),
    ('Пусть Рождество напомнит: свет сияет даже там, где его не ждут.', 'Иоанна 1:5'),
    ('Божья любовь не разыгрывается. Для тебя в ней всегда есть место.', 'Иоанна 3:16'),
    ('Пусть сегодняшний вечер оставит тебе не только ожидание подарка, но и тихую радость о Христе.', 'Луки 2:10–11'),
    ('Пусть мир Христа будет с тобой и сегодня, и в те дни, когда сердце тревожится.', 'Иоанна 14:27'),
    ('Пусть Бог укрепит твоё сердце для того доброго, что ещё предстоит.', 'Псалом 26:14'),
    ('Пусть радость другого сегодня станет и твоей радостью.', 'Римлянам 12:15'),
    ('Твоя ценность не измеряется призами. В Божьих глазах ты драгоценность.', 'Исаия 43:4'),
    ('Пусть среди праздничного шума найдётся минутка услышать: Бог рядом.', 'Матфея 1:23'),
    ('Приз бывает один, а Божьи милости обновляются каждое утро.', 'Плач Иеремии 3:22–23'),
    ('Пусть Бог даст тебе заметить маленькую радость, мимо которой легко пройти.', '1 Фессалоникийцам 5:16–18'),
    ('Не всякий подарок можно завернуть. Пусть сегодня тебе подарят внимание, тепло и добрые слова.', 'Колоссянам 3:12–14'),
    ('Когда планы складываются иначе, можно идти дальше с надеждой: Господь направляет шаги.', 'Притчи 16:9'),
    ('Пусть Божий мир хранит твоё сердце крепче, чем любой удачный билет.', 'Филиппийцам 4:6–7'),
    ('Христос пришёл в мир без пышности. Пусть это Рождество поможет разглядеть великое в простом.', 'Луки 2:7'),
    ('Пусть вечером найдётся человек, с кем можно разделить радость. Иногда это и есть лучший подарок.', 'Екклесиаст 4:9–10'),
    ('Пусть Бог благословит тебя и сохранит. И пусть этот вечер запомнится теплом.', 'Числа 6:24–26'),
    ('Пусть вместо огорчения останется светлая мысль: ничто не может отлучить нас от Божьей любви.', 'Римлянам 8:39'),
    ('Даже если сегодня без приза, пусть этот вечер станет добрым воспоминанием о встрече и дружбе.', 'Псалом 132:1'),
    ('Пусть в эти праздничные дни найдётся возможность подарить кому-то ту радость, которой хочется тебе.', 'Деяния 20:35'),
    ('Пусть Господь будет твоим светом и в праздник, и в самый обычный день.', 'Псалом 26:1'),
    ('То, что сегодня прошло мимо, не закрывает дорогу добру. Пусть Бог даст сил не унывать.', 'Галатам 6:9'),
    ('Рождественская весть — о великой радости для всех. Для тебя тоже.', 'Луки 2:10'),
    ('Пусть Бог даст тебе надежду на завтра и благодарность за то доброе, что уже есть сегодня.', 'Псалом 102:2'),
    ('Если сегодня на сердце тяжело, пусть найдётся время доверить Богу то, что тревожит.', '1 Петра 5:7'),
]


def display_name(text):
    if not isinstance(text, str):
        raise ValueError('Введи имя и фамилию.')
    text = ' '.join(unicodedata.normalize('NFC', text).split())
    words = text.split()
    if (not 1 <= len(words) <= 4 or len(text) > 40
            or any(not w[0].isalpha() or not w[-1].isalpha()
                   or any(not (c.isalpha() or unicodedata.category(c).startswith('M') or c in "-’'")
                           for c in w)
                   for w in words)):
        raise ValueError('Проверь имя и фамилию: до 40 символов, только буквы, пробелы, дефисы и апострофы.')
    return text


class Game:
    def __init__(self, urls):
        self.lock = threading.RLock()
        self.urls = urls
        self.people = {}
        self.won = set()
        self.phase = 'open'
        self.round = 0
        self.winner = None
        self.started = 0
        self.tape = []
        self.network = 0
        self.revision = 0
        self.qr_cache = {}  # url -> svg, кэш из локальной версии

    def get_qr(self, url):
        with self.lock:
            if url not in self.qr_cache:
                self.qr_cache[url] = qr_svg(url)
            return self.qr_cache[url]

    def add_tunnel_url(self, url):
        with self.lock:
            if url not in self.urls:
                self.urls.insert(0, url)
                self.network = 0
                self.revision += 1
                return url
        return None

    def tick(self):
        if self.phase == 'spin' and time.monotonic() - self.started >= DURATION:
            self.phase = 'result'
            self.won.add(self.winner)
            self.revision += 1

    def view(self, who=None, role='guest'):
        self.tick()
        person = self.people.get(who)
        out = dict(phase=self.phase, round=self.round, count=len(self.people),
                   joined=bool(person), revision=self.revision,
                   network=self.network, urls=self.urls)
        if person:
            out['you'] = ' '.join(person[:2])
        if self.phase == 'spin':
            out.update(elapsed=max(0, time.monotonic() - self.started), duration=DURATION)
            if person or role != 'guest':
                out['tape'] = self.tape
        if self.phase == 'result':
            out['winner'] = ' '.join(self.people[self.winner][:2])
            if person:
                out['won'] = who == self.winner
                out['prior'] = who in self.won and not out['won']
                if not out['won'] and not out['prior']:
                    out['message'] = MESSAGES[(person[2] + self.round - 1) % len(MESSAGES)]
        if role == 'admin':
            out.update(
                people=[dict(id=k, name=' '.join(v[:2]), won=k in self.won) for k, v in self.people.items()],
                eligible=len(self.people) - len(self.won),
            )
        return out

    def register(self, who, data):
        if who in self.people:
            return who
        if self.phase != 'open':
            raise ValueError('Регистрация уже завершена.')
        if len(self.people) >= LIMIT:
            raise ValueError('Достигнут лимит регистрации.')
        first = display_name(data.get('first'))
        last = display_name(data.get('last'))
        if not who or not re.fullmatch(r'[A-Za-z0-9_-]{32}', who):
            who = secrets.token_urlsafe(24)
        self.people[who] = (first, last, secrets.randbelow(len(MESSAGES)))
        self.revision += 1
        return who

    def _spin(self, pool):
        if not pool:
            raise ValueError('Нет участников для следующего розыгрыша.')
        self.winner = secrets.choice(pool)
        names = list(dict.fromkeys(self.people[k][0] for k in pool))
        secrets.SystemRandom().shuffle(names)
        self.tape = names[:32]
        self.round += 1
        self.started = time.monotonic()
        self.phase = 'spin'

    def control(self, data):
        self.tick()
        op = data.get('op')
        if op == 'network' and self.phase == 'open' and not self.people:
            i = data.get('id')
            if type(i) is not int or not 0 <= i < len(self.urls):
                raise ValueError('Указан неверный сетевой адрес.')
            self.network = i
        elif op == 'close' and self.phase == 'open':
            self.phase = 'closed'
        elif op == 'open' and self.phase == 'closed':
            self.phase = 'open'
        elif op == 'remove' and self.phase in ('open', 'closed'):
            who = data.get('id')
            if isinstance(who, str):
                self.people.pop(who, None)
        elif op == 'draw' and self.phase in ('closed', 'result'):
            self._spin([k for k in self.people if k not in self.won])
        elif op == 'redraw' and self.phase == 'result' and self.winner in self.people:
            # повтор раунда: последний результат отменяется, пул тот же (включая прежнего победителя раунда)
            self.won.discard(self.winner)
            self.round -= 1
            self._spin([k for k in self.people if k not in self.won])
        elif op == 'reset' and self.phase != 'spin':
            self.people.clear()
            self.won.clear()
            self.phase, self.round, self.winner, self.tape = 'open', 0, None, []
        else:
            raise ValueError('Это действие сейчас недоступно. Дождись обновления экрана.')
        self.revision += 1


def qr_svg(text):
    qr = QrCode.encode_text(text, QrCode.Ecc.MEDIUM)
    n = qr.get_size()
    path = ''.join(f'M{x+4},{y+4}h1v1h-1z'
                   for y in range(n) for x in range(n) if qr.get_module(x, y))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {n+8} {n+8}" '
            f'shape-rendering="crispEdges"><rect width="{n+8}" height="{n+8}" fill="#fff"/>'
            f'<path d="{path}" fill="#000"/></svg>')


# --- HTTP ---

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args): pass

    def setup(self):
        super().setup()
        self.connection.settimeout(5)

    def respond(self, status, body, mime='application/json; charset=utf-8', cookie=None):
        if not isinstance(body, (str, bytes)):
            body = json.dumps(body, ensure_ascii=False, separators=(',', ':'))
        if isinstance(body, str):
            body = body.encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', mime)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'no-referrer')
        self.send_header(
            'Content-Security-Policy',
            "default-src 'none'; style-src 'self'; script-src 'self'; "
            "img-src 'self'; connect-src 'self'; form-action 'self'; "
            "frame-ancestors 'none'; base-uri 'none'",
        )
        if cookie:
            # Secure только если запрос пришёл по HTTPS (через туннель);
            # по локальному HTTP браузер Secure-cookie не сохранит.
            secure = '; Secure' if self.headers.get('X-Forwarded-Proto') == 'https' else ''
            self.send_header('Set-Cookie', f'sochelnik={cookie}; Path=/; HttpOnly; SameSite=Strict{secure}')
        self.end_headers()
        self.wfile.write(body)

    def host_ok(self):
        """Защита от DNS rebinding: Host должен быть в белом списке."""
        return self.headers.get('Host', '') in self.server.allowed_hosts

    def is_local_browser(self):
        """True только для запросов с самого ноутбука ведущего."""
        addr = self.client_address[0]
        if addr not in ('127.0.0.1', '::1'):
            return False
        # cloudflared добавляет CF-Connecting-IP / X-Forwarded-For для туннельных запросов
        if self.headers.get('CF-Connecting-IP') or self.headers.get('X-Forwarded-For'):
            return False
        return True

    def admin_ok(self):
        if not self.is_local_browser():
            return False
        key = self.headers.get('X-Host-Key', '').encode('utf-8')
        return secrets.compare_digest(key, self.server.key.encode('ascii'))

    def origin_ok(self):
        origin = self.headers.get('Origin')
        if origin is None:
            return True
        host = self.headers.get('Host', '')
        return origin in (f'http://{host}', f'https://{host}')

    def who(self):
        try:
            v = cookies.SimpleCookie(self.headers.get('Cookie', '')).get('sochelnik')
            return v.value if v else None
        except cookies.CookieError:
            return None

    def do_GET(self):
        if not self.host_ok():
            return self.respond(400, {'error': 'Неверный адрес сервера.'})
        parsed = urlsplit(self.path)
        path = parsed.path

        if path in ('/', '/join', '/screen', '/host'):
            if path == '/host' and not self.is_local_browser():
                return self.respond(403, 'Панель доступна только на компьютере ведущего.',
                                    'text/plain; charset=utf-8')
            return self.respond(200, HTML, 'text/html; charset=utf-8')

        if path == '/app.css':
            return self.respond(200, CSS, 'text/css; charset=utf-8')
        if path == '/app.js':
            return self.respond(200, JS, 'application/javascript; charset=utf-8')
        if path == '/garland.svg':
            return self.respond(200, GARLAND_SVG, 'image/svg+xml')
        if path == '/fir.svg':
            return self.respond(200, FIR_SVG, 'image/svg+xml')

        if path in ('/state', '/host-state'):
            if path == '/host-state' and not self.admin_ok():
                return self.respond(403, {'error': 'Открой панель по ссылке, показанной в окне запуска.'})
            with self.server.game.lock:
                role = 'admin' if path == '/host-state' else ('screen' if parse_qs(parsed.query).get('screen') == ['1'] else 'guest')
                data = self.server.game.view(self.who() if role == 'guest' else None, role)
                new_cookie = None
                if role == 'guest' and not self.who():
                    new_cookie = secrets.token_urlsafe(24)
                return self.respond(200, data, cookie=new_cookie)

        if path == '/qr.svg':
            try:
                i = int(parse_qs(parsed.query).get('i', ['0'])[0])
                url = self.server.game.urls[i]
            except (ValueError, IndexError):
                return self.respond(404, {})
            return self.respond(200, self.server.game.get_qr(url), 'image/svg+xml')

        return self.respond(404, {'error': 'Страница не найдена.'})

    def do_POST(self):
        if not self.host_ok() or not self.origin_ok():
            return self.respond(403, {'error': 'Запрос отклонён.'})
        path = urlsplit(self.path).path
        if path not in ('/register', '/control'):
            return self.respond(404, {})
        if path == '/control' and not self.admin_ok():
            return self.respond(403, {'error': 'Нет доступа к панели ведущего.'})
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if self.headers.get_content_type() != 'application/json' or not 0 < size <= 4096:
                raise ValueError()
            data = json.loads(self.rfile.read(size))
            if not isinstance(data, dict):
                raise ValueError()
        except (ValueError, OSError):
            return self.respond(400, {'error': 'Неверный формат запроса.'})
        key = None
        try:
            with self.server.game.lock:
                if path == '/register':
                    key = self.server.game.register(self.who(), data)
                    payload = self.server.game.view(key)
                else:
                    self.server.game.control(data)
                    payload = self.server.game.view(role='admin')
        except ValueError as err:
            return self.respond(409, {'error': str(err)})
        return self.respond(200, payload, cookie=key)


# --- Сеть и туннель ---

def local_ips(preferred):
    items = [preferred] if preferred else []
    for target in ('1.1.1.1', '192.168.0.1'):
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
            try:
                sock.connect((target, 80))
                items.append(sock.getsockname()[0])
            except OSError:
                pass
    items = list(dict.fromkeys(ip for ip in items if not ipaddress.ip_address(ip).is_loopback))
    return items or ['127.0.0.1']


def get_cloudflared_bin():
    existing = shutil.which('cloudflared')
    if existing:
        return existing
    app_dir = Path.home() / '.sochelnik_bin'
    app_dir.mkdir(parents=True, exist_ok=True)
    system, machine = platform.system().lower(), platform.machine().lower()

    if system == 'windows':
        bin_path = app_dir / 'cloudflared.exe'
        if bin_path.exists(): return str(bin_path)
        url = 'https://github.com/cloudflare/cloudflared/releases/latest/download/cloudflared-windows-amd64.exe'
        print('Первый запуск: скачиваем cloudflared (~35 МБ)...', flush=True)
        urllib.request.urlretrieve(url, bin_path)
        return str(bin_path)

    if system == 'darwin':
        bin_path = app_dir / 'cloudflared'
        if bin_path.exists(): return str(bin_path)
        arch = 'arm64' if machine in ('arm64', 'aarch64') else 'amd64'
        url = f'https://github.com/cloudflare/cloudflared/releases/latest/download/cloudflared-darwin-{arch}.tgz'
        tgz = app_dir / 'cf.tgz'
        print('Первый запуск: скачиваем cloudflared для macOS...', flush=True)
        urllib.request.urlretrieve(url, tgz)
        with tarfile.open(tgz, 'r:gz') as tar:
            tar.extractall(app_dir)
        tgz.unlink(missing_ok=True)
        bin_path.chmod(bin_path.stat().st_mode | stat.S_IEXEC)
        return str(bin_path)

    return None


def start_tunnel(port, server):
    """Поднимает cloudflared и, когда появится URL, добавляет его в игру и в allowed_hosts."""
    try:
        bin_path = get_cloudflared_bin()
        if not bin_path:
            print('cloudflared не найден — работаем в режиме локального Wi-Fi.\n', flush=True)
            return
        proc = subprocess.Popen(
            [bin_path, 'tunnel', '--url', f'http://127.0.0.1:{port}'],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1,
        )
        IGNORED_HOSTS = {'api.trycloudflare.com', 'www.trycloudflare.com', 'trycloudflare.com'}
        for line in proc.stdout:
            match = re.search(r'https://[a-zA-Z0-9-]+\.trycloudflare\.com', line)
            if match:
                candidate = match.group(0)
                host = urlsplit(candidate).hostname or ''
                if host in IGNORED_HOSTS:
                    continue
                public_url = candidate + '/join'
                added = server.game.add_tunnel_url(public_url)
                if added:
                    server.allowed_hosts.add(urlsplit(public_url).netloc)
                    print(f'Интернет-туннель активен! Ссылка для гостей: {public_url}\n', flush=True)
                break
    except Exception as e:
        print(f'Не удалось запустить интернет-туннель (работаем в режиме Wi-Fi): {e}\n', flush=True)

def main():
    parser = argparse.ArgumentParser(description='Сочельник 2026 — розыгрыш с туннелем и Wi-Fi fallback.')
    parser.add_argument('--ip', type=ipaddress.IPv4Address)
    parser.add_argument('--port', type=int, default=8765)
    parser.add_argument('--no-browser', action='store_true')
    parser.add_argument('--no-tunnel', action='store_true', help='Не поднимать туннель, только Wi-Fi')
    args = parser.parse_args()

    try:
        server = ThreadingHTTPServer(('0.0.0.0', args.port), Handler)
    except (OSError, OverflowError) as e:
        raise SystemExit(f'Не удалось запустить сервер: {e}. Попробуй --port 8766.') from e

    port = server.server_address[1]
    ips = local_ips(str(args.ip) if args.ip else None)
    urls = [f'http://{ip}:{port}/join' for ip in ips]
    server.game = Game(urls)
    server.key = secrets.token_urlsafe(24)
    # Белый список Host для host_ok — локальные адреса; при появлении туннеля пополнится
    server.allowed_hosts = {f'{ip}:{port}' for ip in [*ips, '127.0.0.1', 'localhost']}

    host = f'http://127.0.0.1:{port}/host#{server.key}'
    print(f'\nСОЧЕЛЬНИК 2026\n\n'
          f'Панель ведущего: {host}\n'
          f'Экран проектора: http://127.0.0.1:{port}/screen\n'
          f'Локальный адрес:  {urls[0]}\n', flush=True)

    if not args.no_tunnel:
        print('Запускаю интернет-туннель (5–10 сек на первый раз)...', flush=True)
        threading.Thread(target=start_tunnel, args=(port, server), daemon=True).start()
    else:
        print('Туннель отключён флагом --no-tunnel. Гости должны быть в той же Wi-Fi.\n', flush=True)

    if not args.no_browser:
        threading.Timer(0.8, webbrowser.open, args=(host,)).start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
