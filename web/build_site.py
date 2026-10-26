#!/usr/bin/env python3
"""Builds the web version of the document into web/site/index.html.

Runs Typst's HTML export on main.typ: template.typ switches to the web layout in web.typ, which
has Typst draw every equation as an SVG, and the page is styled by web.css. Figures are written to
web/site/figures/ and fonts are loaded from web/site/fonts/. Usage: python3 web/build_site.py
"""

import base64
import hashlib
import os
import re
import shutil
import subprocess
from pathlib import Path
from urllib.parse import urlparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # Where main.typ is.
OUT = HERE / "site" / "index.html"
FIGURES = OUT.parent / "figures"
PREVIEW = OUT.parent / "hero.png"  # Made by hero.typ (see the top of it).
SITE_URL = os.environ.get("SITE_URL")  # Where it's deployed, set by .github/workflows/pages.yml.

SYMBOL = re.compile(r'<symbol id="([^"]+)"[^>]*>.*?</symbol>', re.S)


def share_glyphs(html):
    """Each equation's SVG carries its own copy of every glyph it uses, so the same few hundred
    glyphs are repeated thousands of times. Typst names glyphs by a hash of their shape, so keep one
    copy of each in a hidden SVG at the top of the page, which every equation's <use> can point to."""
    glyphs = {}
    for m in SYMBOL.finditer(html):
        if glyphs.setdefault(m.group(1), m.group(0)) != m.group(0):
            raise ValueError(f"two different glyphs named {m.group(1)}")
    html = SYMBOL.sub("", html).replace("<defs></defs>", "")
    shared = '<svg class="glyphs" aria-hidden="true"><defs>' + "".join(glyphs.values()) + "</defs></svg>"
    return re.sub(r"(<body[^>]*>)", lambda m: m.group(1) + shared, html, count=1)


INLINE_EQ = re.compile(r'([(\[“‘]*)(<span class="im"[^>]*><svg [^>]*>.*?</svg><span class="math-text">[^<]*</span></span>)([.,;:!?)\]”’]*)', re.S)


def keep_punctuation_with_maths(html):
    """Browsers may break a line between an inline equation's SVG and the punctuation touching it,
    leaving e.g. a lone full stop on the next line; Typst never does. Glue them together."""
    def glue(m):
        if not (m.group(1) or m.group(3)):
            return m.group(0)
        return f'<span class="nobr">{m.group(0)}</span>'
    return INLINE_EQ.sub(glue, html)


def sidenote_spans(html):
    """(start, end) of the inside of each sidenote's <span>."""
    for m in re.finditer(r'<span class="sidenote[^"]*">', html):
        depth = 1
        for t in re.finditer(r"<(/?)span\b[^>]*>", html[m.end() :]):
            depth += -1 if t.group(1) else 1
            if depth == 0:
                yield m.end(), m.end() + t.start()
                break


def unwrap_note_paragraphs(html):
    """Typst wraps the text around a display equation in <p>s, even inside a sidenote; turn those
    into spans (laid out the same by web.css), since a <p> can't sit inside a paragraph."""
    out, last = [], 0
    for start, end in sidenote_spans(html):
        inner = html[start:end].replace("<p>", '<span class="sn-p">').replace("</p>", "</span>")
        out += [html[last:start], inner]
        last = end
    return "".join(out) + html[last:]


def hide_maths_pictures(html):
    """Screen readers read an equation's plain-text version, hidden beside its picture (see web.typ's
    math_text), so they should skip the picture itself."""
    html, n = re.subn(r'(<(?:span|div) class="(?:im|eq-scroll)"[^>]*>)<svg ', r'\1<svg aria-hidden="true" ', html)
    assert n == html.count('class="math-text"'), "an equation's picture isn't where it was expected"
    return html


def name_maths_refs(html):
    """A reference inside an equation comes out of web.typ's math_text as @label, as it can't be
    laid out there; swap in what references to the same thing show elsewhere (e.g. Theorem 2.3.1)."""
    shown = dict(re.findall(r'<a href="#([^"]+)">([^<]+)</a>', html))

    def swap(r):
        if r[2] not in shown:
            return r[0]
        text, opened, closed = shown[r[2]], r[1] or "", r[3] or ""
        if opened and closed and text.startswith("(") and text.endswith(")"):  # Not ⇓^((4.4.3)).
            return text
        return opened + text + closed

    def name(m):
        return re.sub(r"(\()?@([\w.:-]+)(\))?", swap, m[0])

    return re.sub(r'class="math-text">.*?</(?:span|div)>', name, html, flags=re.S)


BLOCK_TAG = re.compile(r"<(div|p|ul|ol|li|figure|table|h[1-6]|blockquote|pre|hr)\b")


def check_sidenotes(html):
    """Sidenotes sit inside paragraphs, where block elements aren't allowed: the browser would end
    the paragraph there and spill the rest of the note into the text. web.typ builds notes from
    spans; fail loudly if some new kind of content in a note slips through as a block."""
    bad = []
    for start, end in sidenote_spans(html):
        inner = html[start:end]
        if found := BLOCK_TAG.search(re.sub(r"<svg .*?</svg>", "", inner, flags=re.S)):
            num = re.search(r'class="sn-num">(\d+)<', inner)
            bad.append(f"sidenote {num.group(1) if num else '(unnumbered)'} contains <{found.group(1)}>")
    if bad:
        raise SystemExit("Block elements inside sidenotes (see web.typ's sidenote):\n  " + "\n  ".join(bad))


DATA_IMAGE = re.compile(r'<img src="data:([^;"]+);base64,([^"]*)"([^>]*)>')
EXTENSIONS = {"image/svg+xml": "svg", "image/png": "png", "image/jpeg": "jpg"}
SVG_SIZE = re.compile(rb'<svg [^>]*?viewBox="[\d.-]+ [\d.-]+ ([\d.]+) ([\d.]+)"')


def extract_figures(html):
    """Typst embeds each image in the page as a base64 data URI, which made the figures about two
    thirds of the download, all before the end of the page (where web.js lays out the margin
    notes). Write each to its own file instead, named by its contents, and load it lazily. Its space
    is set aside before it loads: Typst's width and height stay on the <img>, but they're rounded to
    whole pixels, which would leave notes further down a pixel or so off their lines once figures
    above them load, so SVGs also get their exact aspect ratio."""
    shutil.rmtree(FIGURES, ignore_errors=True)
    FIGURES.mkdir()

    def extract(m):
        data = base64.b64decode(m.group(2))
        name = f"{hashlib.sha256(data).hexdigest()[:12]}.{EXTENSIONS[m.group(1)]}"
        (FIGURES / name).write_bytes(data)
        attrs = m.group(3)
        if size := SVG_SIZE.search(data):
            ratio = f"aspect-ratio: {size[1].decode()} / {size[2].decode()}"
            if 'style="' in attrs:
                attrs = re.sub(r'style="([^"]*)"', lambda s: f'style="{s[1]}; {ratio}"', attrs, count=1)
            else:
                attrs += f' style="{ratio}"'
        return f'<img loading="lazy" decoding="async" src="figures/{name}"{attrs}>'

    return DATA_IMAGE.sub(extract, html)


def add_share_tags(html):
    """What a link to the page shows when shared (X, Slack, iMessage, ...): the site's name, and
    the preview image, which has to be given as an absolute URL, so these are added here rather
    than by Typst. Skipped when SITE_URL isn't set (e.g. local builds)."""
    if not SITE_URL:
        return html
    site_name = urlparse(SITE_URL).hostname.encode().decode("idna")  # E.g. 2λ.com, not xn--2-kmb.com.
    tags = f'<meta property="og:site_name" content="{site_name}">'
    if PREVIEW.exists():
        tags += (
            f'<meta property="og:image" content="{SITE_URL}{PREVIEW.name}">'
            '<meta name="twitter:card" content="summary_large_image">'
        )
    return html.replace("</head>", tags + "</head>", 1)


def repo_url():
    """The repo on GitHub: GitHub Actions says which when deploying, and local builds use the origin
    remote. None if neither says."""
    if repo := os.environ.get("GITHUB_REPOSITORY"):
        return f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/{repo}"
    remote = subprocess.run(["git", "remote", "get-url", "origin"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    m = re.fullmatch(r"(?:https://github\.com/|git@github\.com:)(.+?)(?:\.git)?", remote)
    return f"https://github.com/{m[1]}" if m else None


def add_feedback_link(html):
    """Point readers who spot a mistake at the repo, beside the author's name in the footer."""
    if not (url := repo_url()):
        return html
    note = f'<span class="pagefoot-note">Spot an issue? Open an issue or pull request on <a href="{url}">GitHub</a>!</span>'
    html, n = re.subn(r'(<footer class="pagefoot">.*?)(</footer>)', lambda m: m[1] + note + m[2], html, count=1, flags=re.S)
    assert n == 1, "no footer to add the note to"
    return html


def open_links_in_new_tabs(html):
    """Links out of the page open in a new tab, so the reader keeps their place in it. Links within
    the page (sections, equations, notes) don't."""
    return re.sub(r'<a href="(https?://[^"]*)"', r'<a href="\1" target="_blank" rel="noopener"', html)


def main():
    OUT.parent.mkdir(exist_ok=True)
    subprocess.run(
        ["typst", "compile", "--features", "html", "--format", "html", "main.typ", str(OUT)],
        cwd=ROOT,
        check=True,
    )
    html = unwrap_note_paragraphs(keep_punctuation_with_maths(name_maths_refs(hide_maths_pictures(share_glyphs(OUT.read_text())))))
    check_sidenotes(html)
    OUT.write_text(open_links_in_new_tabs(add_feedback_link(add_share_tags(extract_figures(html)))))
    figures = list(FIGURES.iterdir())
    print(
        f"Wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size / 1e6:.1f} MB) and {len(figures)} figures "
        f"to {FIGURES.relative_to(ROOT)}/ ({sum(f.stat().st_size for f in figures) / 1e6:.1f} MB)"
    )


if __name__ == "__main__":
    main()
