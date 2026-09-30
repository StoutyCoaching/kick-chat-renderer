#!/usr/bin/env python3
"""
kick_chat_render.py - render a Kick chat JSON export into a video with a
transparent background, for dropping over footage in a video editor.

Requirements: Python 3.9+, Pillow (pip install pillow), ffmpeg on PATH.

Quick start:
    python kick_chat_render.py messages.json                       # QuickTime Animation .mov (alpha)
    python kick_chat_render.py messages.json --start 12:30:00 --end 12:45:00
    python kick_chat_render.py messages.json --preview 12:10:00    # one PNG to check the look
    python kick_chat_render.py messages.json --format webm         # tiny VP9+alpha file
    python kick_chat_render.py messages.json --format prores --start +0 --end +120  # ProRes 4444, short clip
    python kick_chat_render.py messages.json --format h264 --bg 00ff00   # green-screen fallback

Timestamps in --start / --end / --preview are UTC clock times (HH:MM:SS, the
same clock as the "createdAt" fields), a full ISO timestamp, or "+SECONDS"
after the first message. Line up the first frame of the render with the matching
moment of your footage in the editor.
"""
import argparse
import bisect
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from datetime import datetime, timedelta, timezone

from PIL import Image, ImageChops, ImageDraw, ImageFont

EMOTE_RE = re.compile(r"\[emote:(\d+):([^\]]+)\]")
EMOTE_URL = "https://files.kick.com/emotes/{id}/fullsize"

# Kick-ish username palette (the export has no per-user colours, so we hash).
PALETTE = [
    "#FF6B6B", "#FF9F43", "#FECA57", "#1DD1A1", "#48DBFB", "#54A0FF",
    "#5F27CD", "#A29BFE", "#FD79A8", "#E17055", "#00CEC9", "#55E6C1",
    "#B8E994", "#F8A5C2", "#CAD3C8", "#FFC312",
]

REGULAR_FONTS = [
    "C:/Windows/Fonts/tahoma.ttf",
    "C:/Windows/Fonts/segoeui.ttf", "C:/Windows/Fonts/arial.ttf",
    "/System/Library/Fonts/Supplemental/Arial.ttf", "/Library/Fonts/Arial.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
]
BOLD_FONTS = [
    "C:/Windows/Fonts/tahomabd.ttf",
    "C:/Windows/Fonts/segoeuib.ttf", "C:/Windows/Fonts/arialbd.ttf",
    "/System/Library/Fonts/Supplemental/Arial Bold.ttf", "/Library/Fonts/Arial Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
]
EMOJI_FONTS = [
    "C:/Windows/Fonts/seguiemj.ttf",
    "/System/Library/Fonts/Apple Color Emoji.ttc",
    "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",
    "/usr/share/fonts/noto/NotoColorEmoji.ttf",
]

_PICT = ("\U0001F300-\U0001FAFF\u2600-\u27BF\u2B00-\u2BFF\u2300-\u23FF")
_ONE = f"[{_PICT}]\\uFE0F?[\U0001F3FB-\U0001F3FF]?"
# flags | keycaps | pictographs (with skin tones, variation selectors, ZWJ sequences)
EMOJI_RE = re.compile(
    "[\U0001F1E6-\U0001F1FF]{2}"
    "|[0-9#*]\\uFE0F?\\u20E3"
    f"|{_ONE}(?:\\u200D{_ONE})*"
)


# --------------------------------------------------------------------------- utils
def hex_to_rgb(s):
    s = s.lstrip("#")
    return tuple(int(s[i:i + 2], 16) for i in (0, 2, 4))


def parse_ts(s):
    s = s.strip()
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    dt = datetime.fromisoformat(s)
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def find_font(user_path, candidates, what):
    if user_path:
        return user_path
    for c in candidates:
        if os.path.exists(c):
            return c
    sys.exit(f"Could not find a {what} font. Pass one with --font / --font-bold.")


def ease_out(p):
    p = max(0.0, min(1.0, p))
    return 1 - (1 - p) ** 3


def user_color(name, overrides):
    if name in overrides:
        return hex_to_rgb(overrides[name])
    h = int(hashlib.md5(name.encode("utf-8")).hexdigest(), 16)
    return hex_to_rgb(PALETTE[h % len(PALETTE)])


# --------------------------------------------------------------------------- emotes
class EmoteStore:
    def __init__(self, cache_dir, size, font, offline=False):
        self.cache_dir = cache_dir
        self.size = size
        self.font = font
        self.offline = offline
        self.mem = {}
        self.failed = set()
        os.makedirs(cache_dir, exist_ok=True)

    def _download(self, eid):
        path = os.path.join(self.cache_dir, eid)
        if os.path.exists(path) and os.path.getsize(path) > 0:
            return path
        if self.offline:
            return None
        req = urllib.request.Request(
            EMOTE_URL.format(id=eid),
            headers={"User-Agent": "Mozilla/5.0 (kick-chat-render)"},
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as r, open(path, "wb") as f:
                shutil.copyfileobj(r, f)
            return path
        except Exception as e:  # noqa: BLE001
            print(f"  ! emote {eid} download failed: {e}", file=sys.stderr)
            if os.path.exists(path):
                os.remove(path)
            return None

    def _placeholder(self, name):
        s = self.size
        im = Image.new("RGBA", (s, s), (0, 0, 0, 0))
        d = ImageDraw.Draw(im)
        d.rounded_rectangle((0, 0, s - 1, s - 1), radius=s // 5, fill=(90, 90, 100, 200))
        label = re.sub(r"^(collectibles|emoji)", "", name)[:3] or name[:3]
        d.text((s / 2, s / 2), label, font=self.font, fill=(255, 255, 255, 255), anchor="mm")
        return im

    def get(self, eid, name):
        if eid in self.mem:
            return self.mem[eid]
        im = None
        path = self._download(eid)
        if path:
            try:
                src = Image.open(path)
                src.seek(0)  # animated emotes: first frame only
                src = src.convert("RGBA")
                w = max(1, round(src.width * self.size / src.height))
                im = src.resize((w, self.size), Image.LANCZOS)
            except Exception as e:  # noqa: BLE001
                print(f"  ! emote {eid} unreadable: {e}", file=sys.stderr)
        if im is None:
            self.failed.add(f"{eid}:{name}")
            im = self._placeholder(name)
        self.mem[eid] = im
        return im


class EmojiStore:
    """Renders Unicode emoji as colour images using a separate emoji font."""

    def __init__(self, path, height):
        self.height = height
        self.cache = {}
        self.font = None
        self.native = None
        if path is None:
            for c in EMOJI_FONTS:
                if os.path.exists(c):
                    path = c
                    break
        if not path:
            return
        try:  # vector/COLR fonts (Segoe UI Emoji) accept any size
            self.font = ImageFont.truetype(path, height * 4)
            self.native = height * 4
        except Exception:  # noqa: BLE001
            try:  # bitmap-only fonts (Noto Color Emoji) need their one strike size
                self.font = ImageFont.truetype(path, 109)
                self.native = 109
            except Exception as e:  # noqa: BLE001
                print(f"  ! emoji font unusable: {e}", file=sys.stderr)

    def get(self, cluster):
        if self.font is None:
            return None
        if cluster in self.cache:
            return self.cache[cluster]
        im = None
        try:
            asc, desc = self.font.getmetrics()
            w = max(1, int(self.font.getlength(cluster)) + 4)
            cell = Image.new("RGBA", (w, asc + desc + 4), (0, 0, 0, 0))
            ImageDraw.Draw(cell).text((2, 2), cluster, font=self.font, embedded_color=True)
            if cell.getbbox() is None:
                raise ValueError("blank glyph")
            scale = self.height / cell.height
            im = cell.resize((max(1, round(cell.width * scale)), self.height), Image.LANCZOS)
        except Exception as e:  # noqa: BLE001
            print(f"  ! emoji {cluster!r} not rendered: {e}", file=sys.stderr)
        self.cache[cluster] = im
        return im


# --------------------------------------------------------------------------- message layout
def draw_text(img, xy, text, font, color, outline):
    """Draw antialiased text onto a transparent RGBA image without dark fringes."""
    if outline:
        sm = Image.new("L", img.size, 0)
        ImageDraw.Draw(sm).text(xy, text, font=font, fill=255, anchor="lm",
                                stroke_width=outline, stroke_fill=255)
        shadow = Image.new("RGBA", img.size, (0, 0, 0, 0))
        shadow.putalpha(sm.point([int(i * 0.85) for i in range(256)]))
        img.alpha_composite(shadow)
    mask = Image.new("L", img.size, 0)
    ImageDraw.Draw(mask).text(xy, text, font=font, fill=255, anchor="lm")
    layer = Image.new("RGBA", img.size, tuple(color) + (0,))
    layer.putalpha(mask)
    img.alpha_composite(layer)


def rounded_box(size, radius, rgba):
    """Antialiased rounded rectangle (4x supersampled)."""
    ss = 4
    w, h = size
    m = Image.new("L", (w * ss, h * ss), 0)
    ImageDraw.Draw(m).rounded_rectangle((0, 0, w * ss - 1, h * ss - 1), radius=radius * ss, fill=rgba[3])
    m = m.resize((w, h), Image.LANCZOS)
    layer = Image.new("RGBA", size, tuple(rgba[:3]) + (0,))
    layer.putalpha(m)
    return layer


class Layout:
    def __init__(self, a):
        self.a = a
        self.font = ImageFont.truetype(find_font(a.font, REGULAR_FONTS, "regular"), a.font_size)
        self.bold = ImageFont.truetype(find_font(a.font_bold, BOLD_FONTS, "bold"), a.font_size)
        self.emote_size = round(a.font_size * 1.5)
        self.emoji = EmojiStore(a.emoji_font, round(a.font_size * 1.3))
        self.emotes = EmoteStore(a.emote_cache, self.emote_size, self.font, a.offline)
        self.line_h = round(a.font_size * 1.45)
        self.space = self.font.getlength(" ")
        self.colors = {}
        if a.user_colors:
            with open(a.user_colors, encoding="utf-8") as f:
                self.colors = json.load(f)

    def word_tokens(self, word):
        out, pos = [], 0

        def text(sv):
            return {"k": "text", "s": sv, "f": self.font, "c": (255, 255, 255), "gap": 0}

        for mt in EMOJI_RE.finditer(word):
            if mt.start() > pos:
                out.append(text(word[pos:mt.start()]))
            img = self.emoji.get(mt.group())
            out.append({"k": "emoji", "img": img, "gap": 0} if img else text(mt.group()))
            pos = mt.end()
        if pos < len(word):
            out.append(text(word[pos:]))
        out[-1]["gap"] = self.space
        return out

    def tokens(self, m):
        name_col = user_color(m["username"], self.colors)
        toks = [
            {"k": "text", "s": m["username"], "f": self.bold, "c": name_col, "gap": 0},
            {"k": "text", "s": ":", "f": self.font, "c": (255, 255, 255), "gap": self.space},
        ]
        parts = EMOTE_RE.split(m["content"])
        # split() with 2 groups -> [text, id, name, text, id, name, ..., text]
        for i in range(0, len(parts), 3):
            for word in parts[i].split():
                toks.extend(self.word_tokens(word))
            if i + 2 < len(parts):
                toks.append({"k": "emote", "id": parts[i + 1], "name": parts[i + 2], "gap": self.space / 2})
        return toks

    def render(self, m):
        a = self.a
        pad = a.padding
        avail = a.width - 2 * a.margin - 2 * pad
        lines = [[]]
        x = 0.0
        for t in self.tokens(m):
            if t["k"] in ("emote", "emoji"):
                if t["k"] == "emote":
                    t["img"] = self.emotes.get(t["id"], t["name"])
                pieces = [t]
                t["w"] = t["img"].width
            else:
                w = t["f"].getlength(t["s"])
                pieces = []
                if w > avail:  # very long word: hard-break it
                    chunk = ""
                    for ch in t["s"]:
                        if t["f"].getlength(chunk + ch) > avail and chunk:
                            pieces.append(dict(t, s=chunk, w=t["f"].getlength(chunk), gap=0))
                            chunk = ""
                        chunk += ch
                    pieces.append(dict(t, s=chunk, w=t["f"].getlength(chunk)))
                else:
                    t["w"] = w
                    pieces = [t]
            for p in pieces:
                if x > 0 and x + p["w"] > avail:
                    lines.append([])
                    x = 0.0
                p["x"] = x
                lines[-1].append(p)
                x += p["w"] + p["gap"]
        heights = []
        for ln in lines:
            has_emote = any(p["k"] == "emote" for p in ln)
            heights.append(max(self.line_h, self.emote_size + 4) if has_emote else self.line_h)
        h = sum(heights) + 2 * pad
        box_w = a.width - 2 * a.margin
        img = Image.new("RGBA", (a.width, h), (0, 0, 0, 0))
        if a.bg_opacity > 0:
            img.alpha_composite(rounded_box((box_w, h), a.radius, (0, 0, 0, int(255 * a.bg_opacity))),
                                dest=(a.margin, 0))
        y = pad
        for ln, lh in zip(lines, heights):
            cy = y + lh / 2
            for p in ln:
                px = a.margin + pad + p["x"]
                if p["k"] in ("emote", "emoji"):
                    img.alpha_composite(p["img"], dest=(int(px), int(cy - p["img"].height / 2)))
                else:
                    draw_text(img, (px, cy), p["s"], p["f"], p["c"], a.outline)
            y += lh
        return img


# --------------------------------------------------------------------------- frame composition
def scale_alpha(img, p):
    if p >= 0.999:
        return img
    out = img.copy()
    out.putalpha(img.getchannel("A").point([int(i * p) for i in range(256)]))
    return out


def blit(canvas, img, y):
    H = canvas.height
    y = int(round(y))
    top = 0
    if y < 0:
        top = -y
        y = 0
    bottom = img.height
    if y + (bottom - top) > H:
        bottom = top + (H - y)
    if bottom <= top:
        return
    src = img.crop((0, top, img.width, bottom)) if (top or bottom < img.height) else img
    canvas.alpha_composite(src, dest=(0, y))


class FrameMaker:
    def __init__(self, a, msgs, images, t0):
        self.a = a
        self.imgs = images
        self.times = [(m["_dt"] - t0).total_seconds() for m in msgs]
        self.hs = [im.height for im in images]
        self.bg = None
        if a.bg:
            self.bg = Image.new("RGBA", (a.width, a.height), hex_to_rgb(a.bg) + (255,))
        self.fade = None
        if a.top_fade > 0:
            g = Image.new("L", (a.width, a.height), 255)
            px = g.load()
            for yy in range(min(a.top_fade, a.height)):
                v = int(255 * yy / a.top_fade)
                for xx in range(a.width):
                    px[xx, yy] = v
            self.fade = g
        self._cache_key = None
        self._cache_bytes = None

    def frame(self, t):
        a = self.a
        idx = bisect.bisect_right(self.times, t) - 1
        animating = idx >= 0 and (t - self.times[idx]) < a.anim + 1e-6
        key = None if animating else idx
        if key is not None and key == self._cache_key:
            return self._cache_bytes
        canvas = Image.new("RGBA", (a.width, a.height), (0, 0, 0, 0))
        bottom = a.height - a.margin
        j = idx
        while j >= 0 and bottom > -2000:
            p = ease_out((t - self.times[j]) / a.anim) if a.anim > 0 else 1.0
            h = self.hs[j]
            slide = (1 - p) * a.slide
            if p > 0:
                blit(canvas, scale_alpha(self.imgs[j], p), bottom - h + slide)
            bottom -= (h + a.gap) * p
            if bottom < -h:  # everything above is off-screen
                break
            j -= 1
        if self.fade is not None:
            canvas.putalpha(ImageChops.multiply(canvas.getchannel("A"), self.fade))
        if self.bg is not None:
            canvas = Image.alpha_composite(self.bg, canvas)
        data = canvas.tobytes()
        if key is not None:
            self._cache_key, self._cache_bytes = key, data
        return data

    def image(self, t):
        a = self.a
        return Image.frombytes("RGBA", (a.width, a.height), self.frame(t))


# --------------------------------------------------------------------------- ffmpeg
def find_ffmpeg():
    """Look for ffmpeg bundled inside the exe, next to it/the script, then on PATH."""
    here = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))
    dirs = [d for d in (getattr(sys, "_MEIPASS", None), here) if d]
    for d in dirs:
        for n in ("ffmpeg.exe", "ffmpeg"):
            p = os.path.join(d, n)
            if os.path.isfile(p):
                return p
    return shutil.which("ffmpeg")


def ffmpeg_cmd(a, out, ffmpeg="ffmpeg"):
    base = [ffmpeg, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgba",
            "-s", f"{a.width}x{a.height}", "-r", str(a.fps), "-i", "-"]
    f = a.format
    if f == "prores":
        return base + ["-c:v", "prores_ks", "-profile:v", "4444", "-pix_fmt", "yuva444p10le",
                       "-alpha_bits", "8", "-vendor", "apl0", "-qscale:v", str(a.quality), out]
    if f == "qtrle":
        return base + ["-c:v", "qtrle", "-pix_fmt", "argb", "-g", str(a.keyint), out]
    if f == "webm":
        return base + ["-c:v", "libvpx-vp9", "-pix_fmt", "yuva420p", "-b:v", "0", "-crf", "28",
                       "-auto-alt-ref", "0", "-deadline", "realtime", "-cpu-used", "8",
                       "-row-mt", "1", "-g", str(a.keyint), out]
    if f == "h264":
        return base + ["-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "16", "-preset", "medium", out]
    if f == "png":
        os.makedirs(out, exist_ok=True)
        return base + [os.path.join(out, "chat_%06d.png")]
    raise SystemExit(f"unknown format {f}")


DEFAULT_EXT = {"prores": ".mov", "qtrle": ".mov", "webm": ".webm", "h264": ".mp4", "png": "_frames"}


# --------------------------------------------------------------------------- core
DEFAULT_CACHE = os.path.join(os.path.expanduser("~"), ".kick_chat_render", "emotes")


class Cancelled(Exception):
    pass


def build_parser():
    ap = argparse.ArgumentParser(description="Render Kick chat JSON to a transparent video overlay. "
                                             "Run with no arguments to open the GUI.")
    ap.add_argument("input", help="Kick chat export (.json list of messages)")
    ap.add_argument("-o", "--output", help="output path (default: chat.<ext>)")
    ap.add_argument("--format", choices=["qtrle", "prores", "webm", "h264", "png"], default="qtrle",
                    help="qtrle=QuickTime Animation .mov, alpha, compact (default); "
                         "prores=ProRes 4444 .mov, alpha, most compatible but HUGE (~6 MB/s) - short clips only; "
                         "webm=VP9 alpha, tiny; png=PNG sequence (alpha); h264=mp4, no alpha (use with --bg)")
    ap.add_argument("--keyint", type=int, default=60, help="keyframe interval in frames (qtrle/webm)")
    ap.add_argument("--width", type=int, default=420)
    ap.add_argument("--height", type=int, default=1080)
    ap.add_argument("--fps", type=float, default=30)
    ap.add_argument("--start", help="UTC HH:MM:SS, ISO timestamp, or +SECONDS after first message")
    ap.add_argument("--end", help="same formats as --start (default: last message + 5s)")
    ap.add_argument("--preview", metavar="TIME", help="write preview.png at this time and exit")
    ap.add_argument("--bg", metavar="HEX", help="solid background colour, e.g. 00ff00 (default: transparent)")
    ap.add_argument("--bg-opacity", type=float, default=0.45, help="per-message dark box opacity 0-1 (0 = none)")
    ap.add_argument("--font", help="regular .ttf path")
    ap.add_argument("--font-bold", help="bold .ttf path")
    ap.add_argument("--emoji-font", help="colour emoji font path (default: Segoe UI Emoji on Windows)")
    ap.add_argument("--font-size", type=int, default=22)
    ap.add_argument("--outline", type=int, default=2, help="text outline px (0 = off)")
    ap.add_argument("--margin", type=int, default=10)
    ap.add_argument("--padding", type=int, default=8)
    ap.add_argument("--radius", type=int, default=10)
    ap.add_argument("--gap", type=int, default=6, help="px between messages")
    ap.add_argument("--anim", type=float, default=0.3, help="new-message animation seconds (0 = instant)")
    ap.add_argument("--slide", type=int, default=16, help="px a new message slides up from")
    ap.add_argument("--top-fade", type=int, default=140, help="px fade-out at top edge (0 = off)")
    ap.add_argument("--quality", type=int, default=11, help="ProRes qscale (lower = bigger/better, 4-16)")
    ap.add_argument("--hide-users", nargs="*", default=[], help="usernames to leave out (e.g. bots)")
    ap.add_argument("--user-colors", help="JSON file {username: '#rrggbb'} to override name colours")
    ap.add_argument("--emote-cache", default=DEFAULT_CACHE)
    ap.add_argument("--offline", action="store_true", help="don't download emotes (use cache/placeholders)")
    return ap


def run(a, log=print, progress=None, cancel=None):
    """Do the work. Raises RuntimeError with a readable message on failure."""
    try:
        with open(a.input, encoding="utf-8") as f:
            msgs = json.load(f)
    except Exception as e:  # noqa: BLE001
        raise RuntimeError(f"Couldn't read {a.input}: {e}")
    hide = {u.lower() for u in a.hide_users}
    msgs = [m for m in msgs if m.get("content") and m["username"].lower() not in hide]
    for m in msgs:
        m["_dt"] = parse_ts(m["createdAt"])
    msgs.sort(key=lambda m: m["_dt"])
    if not msgs:
        raise RuntimeError("No messages found.")
    first, last = msgs[0]["_dt"], msgs[-1]["_dt"]

    def when(s):
        s = s.strip()
        try:
            if s.startswith("+"):
                return first + timedelta(seconds=float(s[1:]))
            if "T" in s or "-" in s:
                return parse_ts(s)
            parts = [int(x) for x in s.split(":")] + [0, 0]
            return first.replace(hour=parts[0], minute=parts[1], second=parts[2], microsecond=0)
        except Exception:  # noqa: BLE001
            raise RuntimeError(f"Couldn't understand time '{s}'. Use HH:MM:SS (UTC), an ISO timestamp, or +SECONDS.")

    t0 = when(a.start) if a.start else first
    t_end = when(a.end) if a.end else last + timedelta(seconds=5)
    if a.preview:
        t0 = when(a.preview)
        t_end = t0

    # Only lay out messages that can ever be visible in this window (plus history above).
    first_idx = max(0, bisect.bisect_right([m["_dt"] for m in msgs], t0) - 60)
    use = [m for m in msgs[first_idx:] if m["_dt"] <= t_end]
    log(f"{len(use)} messages in range; laying out (downloading emotes on first run)...")
    try:
        layout = Layout(a)
    except SystemExit as e:
        raise RuntimeError(str(e))
    images = []
    for m in use:
        if cancel and cancel.is_set():
            raise Cancelled()
        images.append(layout.render(m))
    if layout.emotes.failed:
        log(f"Note: {len(layout.emotes.failed)} emote(s) could not be fetched and show as grey placeholders "
            f"(check your internet connection and run again).")

    maker = FrameMaker(a, use, images, t0)

    if a.preview:
        im = maker.image(a.anim + 0.01)  # just past t0 so any fresh message has finished animating
        check = Image.new("RGBA", im.size, (40, 40, 40, 255))
        d = ImageDraw.Draw(check)
        for yy in range(0, im.height, 20):
            for xx in range(0, im.width, 20):
                if (xx // 20 + yy // 20) % 2:
                    d.rectangle((xx, yy, xx + 19, yy + 19), fill=(70, 70, 70, 255))
        path = os.path.join(os.path.dirname(os.path.abspath(a.output or a.input)), "preview.png")
        Image.alpha_composite(check, im).save(path)
        log(f"Wrote {path} (checkerboard = transparent)")
        return path

    out = a.output or ("chat" + DEFAULT_EXT[a.format])
    if a.format == "h264" and not a.bg:
        log("Note: h264 has no alpha; rendering over black. Use a green background for chroma keying.")
    total = max(1, int((t_end - t0).total_seconds() * a.fps))
    log(f"Rendering {total} frames ({total / a.fps:.0f}s) at {a.width}x{a.height} -> {out}")
    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("ffmpeg not found. Put ffmpeg.exe next to this program, or install it and add it to PATH.")
    errf = tempfile.TemporaryFile()
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    proc = subprocess.Popen(ffmpeg_cmd(a, out, ff), stdin=subprocess.PIPE, stdout=subprocess.DEVNULL,
                            stderr=errf, creationflags=flags)
    start = time.time()
    try:
        for i in range(total):
            if cancel and cancel.is_set():
                proc.kill()
                raise Cancelled()
            proc.stdin.write(maker.frame(i / a.fps))
            if i % 150 == 0 and progress:
                el = time.time() - start
                progress(i, total, (el / i * (total - i)) if i else None)
        proc.stdin.close()
    except BrokenPipeError:
        pass
    proc.wait()
    if proc.returncode != 0:
        errf.seek(0)
        raise RuntimeError("ffmpeg failed: " + errf.read().decode("utf-8", "replace")[-500:])
    if progress:
        progress(total, total, 0)
    log(f"Done: {out}")
    return out


def cli(argv):
    a = build_parser().parse_args(argv)

    def prog(i, total, eta):
        print(f"  {i}/{total} frames ({100 * i / total:.0f}%)" + (f"  ETA {eta / 60:.1f} min" if eta else ""),
              end="\r", flush=True)

    try:
        run(a, log=lambda s: print(s), progress=prog)
    except RuntimeError as e:
        sys.exit(str(e))
    print()


# --------------------------------------------------------------------------- GUI
def gui():
    import queue
    import threading
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

    root = tk.Tk()
    root.title("Kick Chat Renderer")
    root.geometry("660x680")
    q = queue.Queue()
    cancel = threading.Event()
    busy = {"on": False}

    v = {k: tk.StringVar(value=val) for k, val in dict(
        input="", output="", fmt="qtrle", start="", end="", width="420", height="1080",
        opacity="0.45", hide="", green="0", font="", bold="", fsize="22").items()}

    frm = ttk.Frame(root, padding=12)
    frm.pack(fill="both", expand=True)
    frm.columnconfigure(1, weight=1)

    def row(r, label, widget, span=1):
        ttk.Label(frm, text=label).grid(row=r, column=0, sticky="w", pady=3)
        widget.grid(row=r, column=1, columnspan=span, sticky="ew", pady=3, padx=(8, 0))

    def pick_in():
        p = filedialog.askopenfilename(title="Kick chat export", filetypes=[("JSON", "*.json"), ("All", "*.*")])
        if p:
            v["input"].set(p)
            if not v["output"].get():
                v["output"].set(os.path.splitext(p)[0] + "_chat.mov")

    def pick_out():
        p = filedialog.asksaveasfilename(title="Save video as", defaultextension=".mov")
        if p:
            v["output"].set(p)

    f1 = ttk.Frame(frm); f1.columnconfigure(0, weight=1)
    ttk.Entry(f1, textvariable=v["input"]).grid(row=0, column=0, sticky="ew")
    ttk.Button(f1, text="Browse...", command=pick_in).grid(row=0, column=1, padx=(6, 0))
    row(0, "Chat JSON", f1)
    f2 = ttk.Frame(frm); f2.columnconfigure(0, weight=1)
    ttk.Entry(f2, textvariable=v["output"]).grid(row=0, column=0, sticky="ew")
    ttk.Button(f2, text="Browse...", command=pick_out).grid(row=0, column=1, padx=(6, 0))
    row(1, "Output file", f2)

    fmt = ttk.Combobox(frm, textvariable=v["fmt"], state="readonly",
                       values=["qtrle", "webm", "prores", "png", "h264"])
    row(2, "Format", fmt)
    ttk.Label(frm, text="qtrle = .mov with transparency (default) | prores = huge, short clips only | "
                        "png = image sequence folder", foreground="#666").grid(row=3, column=1, sticky="w", padx=8)
    row(4, "Start (UTC HH:MM:SS)", ttk.Entry(frm, textvariable=v["start"]))
    row(5, "End (UTC HH:MM:SS)", ttk.Entry(frm, textvariable=v["end"]))
    ttk.Label(frm, text="Leave blank to render the whole file. Also accepts +SECONDS from first message.",
              foreground="#666").grid(row=6, column=1, sticky="w", padx=8)
    sz = ttk.Frame(frm)
    ttk.Entry(sz, textvariable=v["width"], width=7).pack(side="left")
    ttk.Label(sz, text=" x ").pack(side="left")
    ttk.Entry(sz, textvariable=v["height"], width=7).pack(side="left")
    ttk.Label(sz, text="   Box opacity 0-1 ").pack(side="left")
    ttk.Entry(sz, textvariable=v["opacity"], width=6).pack(side="left")
    row(7, "Size (px)", sz)
    row(8, "Hide users (spaces)", ttk.Entry(frm, textvariable=v["hide"]))
    row(9, "Font size", ttk.Entry(frm, textvariable=v["fsize"], width=7))

    def pick_font(key):
        p = filedialog.askopenfilename(title="Choose a font file", initialdir="C:/Windows/Fonts",
                                       filetypes=[("Fonts", "*.ttf *.otf *.ttc"), ("All", "*.*")])
        if p:
            v[key].set(p)

    for r, (label, key) in enumerate([("Font (regular)", "font"), ("Font (bold names)", "bold")], start=10):
        ff = ttk.Frame(frm); ff.columnconfigure(0, weight=1)
        ttk.Entry(ff, textvariable=v[key]).grid(row=0, column=0, sticky="ew")
        ttk.Button(ff, text="Browse...", command=lambda k=key: pick_font(k)).grid(row=0, column=1, padx=(6, 0))
        row(r, label, ff)
    ttk.Label(frm, text="Leave fonts blank for the default (Segoe UI). Pick the bold version of the same "
                        "family for usernames.", foreground="#666").grid(row=12, column=1, sticky="w", padx=8)
    ttk.Checkbutton(frm, text="Solid green background instead of transparent (fallback)",
                    variable=v["green"], onvalue="1", offvalue="0").grid(row=13, column=1, sticky="w", padx=8)

    bar = ttk.Progressbar(frm, maximum=100)
    bar.grid(row=14, column=0, columnspan=2, sticky="ew", pady=(10, 4))
    btns = ttk.Frame(frm)
    btns.grid(row=15, column=0, columnspan=2, sticky="ew")
    logbox = tk.Text(frm, height=9, state="disabled", wrap="word")
    logbox.grid(row=16, column=0, columnspan=2, sticky="nsew", pady=(8, 0))
    frm.rowconfigure(16, weight=1)

    def log(s):
        logbox.config(state="normal")
        logbox.insert("end", s + "\n")
        logbox.see("end")
        logbox.config(state="disabled")

    def argv(preview=None):
        if not v["input"].get():
            raise ValueError("Choose a chat JSON file first.")
        out = v["output"].get() or os.path.splitext(v["input"].get())[0] + "_chat.mov"
        x = [v["input"].get(), "-o", out, "--format", v["fmt"].get(), "--width", v["width"].get(),
             "--height", v["height"].get(), "--bg-opacity", v["opacity"].get()]
        if v["start"].get().strip():
            x += ["--start", v["start"].get().strip()]
        if v["end"].get().strip():
            x += ["--end", v["end"].get().strip()]
        if v["hide"].get().strip():
            x += ["--hide-users"] + v["hide"].get().split()
        if v["green"].get() == "1":
            x += ["--bg", "00ff00"]
        if v["fsize"].get().strip():
            x += ["--font-size", v["fsize"].get().strip()]
        if v["font"].get().strip():
            x += ["--font", v["font"].get().strip()]
        if v["bold"].get().strip():
            x += ["--font-bold", v["bold"].get().strip()]
        if preview:
            x += ["--preview", preview]
        return build_parser().parse_args(x)

    def worker(a):
        try:
            res = run(a, log=lambda s: q.put(("log", s)),
                      progress=lambda i, t, e: q.put(("prog", 100 * i / t)), cancel=cancel)
            q.put(("done", res))
        except Cancelled:
            q.put(("log", "Cancelled."))
            q.put(("done", None))
        except Exception as e:  # noqa: BLE001
            q.put(("err", str(e)))

    def start(preview=None):
        if busy["on"]:
            return
        try:
            a = argv(preview)
        except Exception as e:  # noqa: BLE001
            messagebox.showerror("Kick Chat Renderer", str(e))
            return
        cancel.clear()
        busy["on"] = True
        bar["value"] = 0
        threading.Thread(target=worker, args=(a,), daemon=True).start()

    def do_preview():
        t = v["start"].get().strip() or "+60"
        start(preview=t)

    ttk.Button(btns, text="Preview frame", command=do_preview).pack(side="left")
    ttk.Button(btns, text="Render video", command=lambda: start()).pack(side="left", padx=6)
    ttk.Button(btns, text="Cancel", command=cancel.set).pack(side="left")

    def poll():
        try:
            while True:
                kind, val = q.get_nowait()
                if kind == "log":
                    log(val)
                elif kind == "prog":
                    bar["value"] = val
                elif kind == "err":
                    busy["on"] = False
                    log("ERROR: " + val)
                    messagebox.showerror("Kick Chat Renderer", val)
                elif kind == "done":
                    busy["on"] = False
                    if val and val.endswith(".png") and os.name == "nt":
                        os.startfile(val)  # noqa: S606
        except queue.Empty:
            pass
        root.after(100, poll)

    poll()
    root.mainloop()


def main():
    if len(sys.argv) == 1:
        try:
            gui()
        except Exception as e:  # noqa: BLE001  (e.g. no display on a headless box)
            print(f"GUI unavailable ({e}). Run with --help for command-line use.")
        return
    cli(sys.argv[1:])


if __name__ == "__main__":
    main()
