#!/usr/bin/env python3
"""Builds the web version of the document into web/site/index.html.

Runs Typst's HTML export on main.typ: template.typ switches to the web layout in web.typ, which
has Typst draw every equation as an SVG, and the page is styled by web.css. Images are embedded in
the page; fonts are loaded from web/site/fonts/. Usage: python3 web/build_site.py
"""

import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # Where main.typ is.
OUT = HERE / "site" / "index.html"

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


INLINE_EQ = re.compile(r'([(\[“‘]*)(<span class="im"[^>]*><svg [^>]*>.*?</svg></span>)([.,;:!?)\]”’]*)', re.S)


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


def main():
    OUT.parent.mkdir(exist_ok=True)
    subprocess.run(
        ["typst", "compile", "--features", "html", "--format", "html", "main.typ", str(OUT)],
        cwd=ROOT,
        check=True,
    )
    html = unwrap_note_paragraphs(keep_punctuation_with_maths(share_glyphs(OUT.read_text())))
    check_sidenotes(html)
    OUT.write_text(html)
    print(f"Wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size / 1e6:.1f} MB)")


if __name__ == "__main__":
    main()
