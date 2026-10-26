// The web version of the document (Typst's HTML export): what template.typ uses in place of its
// PDF layout when `target() == "html"`. Styled by web.css and driven by web.js, both inlined into
// the page; build_site.py builds it into site/. Imported by template.typ as `web`.

// Everything here is a function: `html` only exists in HTML builds, so nothing may use it while
// the PDF build imports this file.
#let el(tag, class: none, ..args) = html.elem(tag, attrs: if class == none { (:) } else { (class: class) }, ..args)

#let qed() = el("span", class: "qed", $#sym.qed$)
#let divider() = html.elem("hr")

// A sidenote is an inline span next to its marker; web.js moves it into the right margin. It sits
// inside the paragraph it annotates, where HTML allows no block elements (a <ul> or <div> there
// ends the paragraph early and spills the rest of the note into the text), so paragraph breaks,
// lists and display equations inside it are made of spans instead. build_site.py checks this.
#let in_note = state("web-in-sidenote", false)
#let note_list(markers, items, numbered: false) = el("span", class: if numbered { "sn-list sn-enum" } else { "sn-list" }, markers.zip(items).map(((m, item)) => {
  el("span", class: "sn-li", { el("span", class: "sn-marker", m); item })
}).join())
// Typst only gathers list items into a list after show rules run, and sidenote's parbreak rule
// turns the blank line between a loose list's items into an element, which would split it into
// one list per item (each numbered 1.). So gather each run of items into its list beforehand.
#let gather_lists(body) = {
  if body.func() != [].func() { return body }
  let parts = () // Content, and runs of items: (kind, items, gap), gap being what follows the last.
  for c in body.children {
    let f = c.func()
    let run = parts.len() > 0 and type(parts.last()) == dictionary
    if f in (enum.item, list.item) {
      if run and parts.last().kind == f {
        parts.at(-1).items.push(c)
        parts.at(-1).gap = ()
      } else { parts.push((kind: f, items: (c,), gap: ())) }
    } else if run and f in (parbreak, [ ].func()) {
      parts.at(-1).gap.push(c)
    } else { parts.push(c) }
  }
  parts.map(p => if type(p) == dictionary {
    if p.kind == enum.item { enum(tight: false, ..p.items) } else { list(tight: false, ..p.items) }
    p.gap.join()
  } else { p }).join()
}
#let sidenote(numbered, body) = {
  if numbered { counter(footnote).step() }
  context {
    let n = str(counter(footnote).get().first())
    el("span", class: "sn-wrap", {
      if numbered {
        [#metadata(n)<_web_sidenote>]
        html.elem("sup", attrs: (class: "sn-ref", id: "sn-" + n), n)
      }
      el("span", class: if numbered { "sidenote" } else { "sidenote marginnote" }, {
        show parbreak: el("span", class: "sn-br")
        show list: it => note_list(it.children.map(_ => "•"), it.children.map(c => c.body))
        show enum: it => {
          let start = if it.start == auto { 1 } else { it.start }
          let nums = it.children.enumerate().map(((i, c)) => {
            if c.at("number", default: none) in (none, auto) { start + i } else { c.number }
          })
          note_list(nums.map(k => numbering(it.numbering, k)), it.children.map(c => c.body), numbered: true)
        }
        in_note.update(true)
        if numbered { el("sup", class: "sn-num", n) }
        gather_lists(body)
        in_note.update(false)
      })
      // A word joiner, so a note ending a paragraph doesn't end its last line: Chrome then thinks
      // there's another line after it and stretches the real last one to the full width.
      el("span", class: "sn-end", "\u{2060}")
    })
  }
}

// A reference to a labelled sidenote: its number, linking to its marker.
#let sidenote_ref(note) = {
  let n = query(selector(<_web_sidenote>).after(note.location())).first().value
  el("sup", class: "sn-ref", html.elem("a", attrs: (href: "#sn-" + n), n))
}

#let wideblock(body) = el("div", class: "wide", body)

// Page rules aren't allowed in HTML, so a page background becomes a tinted full-width band.
#let page_fill(fill, rest) = html.elem("div", attrs: (class: "page-fill", style: "--fill: " + fill.to-hex()), rest)

#let heading(it, number) = html.elem("h" + str(calc.min(it.level + 1, 6)), {
  if it.numbering != none { el("span", class: "secnum", number) }
  it.body
})

// A theorem-style box (ctheorems' format function), as a classed <div>: fills, strokes and
// placement don't exist in HTML, so web.css draws the box.
#let thm(identifier, head, bodyfmt, name, number, body, title: auto, ..rest) = {
  if title == auto { title = head }
  if not number == none { title += " " + number }
  el("div", class: "thm thm-" + identifier, {
    if number == none {
      // Unnumbered (proofs): title runs into the body text.
      [#el("span", class: "thm-kind", title)#if name != none [ #el("span", class: "thm-name", name)]: #bodyfmt(body)]
    } else {
      el("div", class: "thm-head", {
        el("span", class: "thm-name", name)
        el("span", class: "thm-kind", title)
      })
      el("div", class: "thm-body", bodyfmt(body))
    }
  })
}
#let proof_body(body) = [#body#qed()]

// Equations: Typst draws each one itself (as an SVG), so it looks exactly like the PDF. Frames are
// sized in ems, so they scale with the text.

// An equation as plain text, like a_i^2 or (a + b)/c. A picture has no text in it, so each one
// carries this as visually hidden text after it (math_label): it's what screen readers and
// anything reading the page as text (an LLM fetching it, search engines) get instead, and what
// web.js uses when copying or quoting a passage. build_site.py hides the picture itself from
// screen readers.
#let math_text(c) = {
  if c == none { return "" }
  if type(c) == str { return c }
  let f = c.func()
  // A script or fraction part longer than one character needs brackets: a^(n+1), not a^n+1.
  let group(x) = {
    let s = math_text(x).trim()
    if s.clusters().len() > 1 and not (s.starts-with("(") and s.ends-with(")")) { "(" + s + ")" } else { s }
  }
  // A combining accent goes on a single letter, even one with scripts or primes (ã, G̃_i, ã′); over
  // anything longer it would land on its last character, so that's written out: tilde(f ⋅ h).
  let accented(base, mark, name) = {
    let s = math_text(base)
    let letter = math_text(if base.func() == math.attach { base.base } else { base })
    if letter.clusters().len() == 1 and s.starts-with(letter) {
      letter + mark + s.slice(letter.len())
    } else {
      let bracketed = s.starts-with("(") and s.ends-with(")") // As (f ⋅ h).
      name + if bracketed { s } else { "(" + s + ")" }
    }
  }
  let list(xs, sep) = xs.map(x => math_text(x).trim()).join(sep, default: "")
  if f == [ ].func() or f == h { " " }
  else if f == linebreak { "\n" }
  else if c.has("text") { math_text(c.text) }
  else if f == [].func() { c.children.map(math_text).join(default: "") }
  else if f == math.attach {
    let base = math_text(c.base)
    // Primes (r') are a top-right script, but are written straight after the base: r′, r′_i.
    let tr = c.at("tr", default: none)
    if tr != none and tr.func() == math.primes {
      base += math_text(tr)
      tr = none
    }
    for (script, mark) in ((c.at("b", default: none), "_"), (c.at("br", default: none), "_"), (c.at("t", default: none), "^"), (tr, "^")) {
      let s = group(script)
      if s != "" { base += mark + s }
    }
    base
  }
  else if f == math.frac { group(c.num) + "/" + group(c.denom) }
  else if f == math.binom { "binom(" + math_text(c.upper) + ", " + list(c.lower, ", ") + ")" }
  else if f == math.root { math_text(c.at("index", default: none)) + "√" + group(c.radicand) }
  else if f == math.accent {
    let names = ("\u{300}": "grave", "\u{301}": "acute", "\u{302}": "hat", "\u{303}": "tilde", "\u{304}": "macron",
      "\u{305}": "overline", "\u{306}": "breve", "\u{307}": "dot", "\u{308}": "dot.double", "\u{30C}": "caron", "\u{20D7}": "arrow")
    accented(c.base, c.accent, names.at(c.accent, default: "accent"))
  }
  else if f == math.overline { accented(c.body, "\u{305}", "overline") }
  else if f == math.underline { accented(c.body, "\u{332}", "underline") }
  // Braces and the like with a label (underbrace(x + y, W)): written out, so the label isn't lost.
  else if c.has("annotation") and c.annotation != none {
    repr(f) + "(" + math_text(c.body).trim() + ", " + math_text(c.annotation).trim() + ")"
  }
  // A reference can't be laid out here, so it's written @label, and build_site.py swaps in what
  // the reference shows elsewhere in the page (Theorem 2.3.1).
  else if f == ref { "@" + str(c.target) }
  else if f == math.primes { "′" * c.count }
  else if f == math.vec { "(" + list(c.children, ", ") + ")" }
  else if f == math.mat { "[" + c.rows.map(r => list(r, ", ")).join("; ") + "]" }
  else if f == math.cases { "{ " + list(c.children, "; ") + " }" }
  else if c.has("body") { math_text(c.body) }
  else if c.has("child") { math_text(c.child) }
  else if c.has("children") { c.children.map(math_text).join(default: "") }
  else { "" }
}
// A <div> beside a display equation, as Typst would wrap a <span> there in a paragraph.
#let math_label(body, tag: "span") = el(tag, class: "math-text",
  math_text(body).replace(regex("[ \t]+"), " ").replace(regex(" ?\n ?"), "\n").trim())

// Inline equations sit on the text baseline. One picture can't wrap, but Typst may break a line
// after a relation or binary operator (even inside brackets), so split inline equations there
// into separate pictures the browser can wrap between.
#let break_after = (
  "=", "≠", "<", ">", "≤", "≥", "≈", "≡", "∼", "≃", "≅", "∝", "∈", "∉", "⊂", "⊃", "⊆", "⊇", ":",
  "→", "←", "↔", "↦", "⇒", "⇐", "⇔", "⟹", "⟸", "⟺", "≔",
  "+", "−", "-", "±", "∓", "⋅", "·", "×", "∘", "⊕", "⊗", "∪", "∩", "∧", "∨", "∖",
)
#let is_op(c) = c.has("text") and c.text in break_after
#let is_blank(c) = c.func() == [ ].func()
// The equation as a flat list of atoms, opening up brackets that contain a break point.
#let atoms(c) = {
  if c.func() == [].func() { return c.children.map(atoms).flatten() }
  if c.func() == math.lr {
    let inner = atoms(c.body)
    if inner.any(is_op) { return inner }
  }
  (c,)
}
// Pieces of an inline equation, each ending just after an operator Typst could break at. An
// operator is only a break point between two operands (not a leading minus, or one after "(").
#let pieces(body) = {
  let atoms = atoms(body)
  let pieces = ()
  let cur = ()
  let prev = none // Last non-blank atom.
  for (i, a) in atoms.enumerate() {
    cur.push(a)
    if is_blank(a) { continue }
    let operand_before = prev != none and not is_op(prev) and not (prev.has("text") and prev.text in ("(", "[", "{", "⟨", ","))
    if is_op(a) and operand_before and atoms.slice(i + 1).any(x => not is_blank(x)) {
      pieces.push(cur)
      cur = ()
      prev = none
    } else { prev = a }
  }
  pieces + (cur,)
}
// A zero-width box after a piece's trailing operator keeps it a binary operator, so the space
// after it is kept and the pieces line up exactly as in one equation.
//
// A picture's height runs from its top to however deep its lowest part goes, so where its
// baseline sits varies (limits under "Pr" go deeper than a subscript). An invisible strut makes
// every picture reach exactly 1em below its baseline, and web.css lines that point up with the
// text's baseline. Typst spreads a line apart by however far its maths hangs below the usual text
// depth; that amount is measured here and passed on as --d, so web.css can do the same.
#let inline_math(it) = context {
  let strut = box(width: 0pt, height: 1em, baseline: 1em)
  let pieces = pieces(it.body)
  for (i, piece) in pieces.enumerate() {
    // A zero-width space between pieces gives a justified line somewhere else to put its extra
    // room than the spaces between words (often only one, beside a long equation).
    if i > 0 { el("span", class: "mj", " ") }
    let body = piece.join() + if i < pieces.len() - 1 { box(width: 0pt) }
    let eq = math.equation(body, block: false)
    let extra = measure(eq).height - (measure([#strut#eq]).height - text.size)
    let attrs = (class: "im")
    if extra > 0.01pt { attrs.style = "--d: " + str(calc.round(extra / text.size, digits: 4)) + "em" }
    html.elem("span", attrs: attrs, { box(html.frame[#strut#eq]); math_label(body) })
  }
}

// Display equations scroll sideways if too wide. A sidenote written inside one (wrapped in a
// #block) can't go in the picture, so it's pulled out and placed beside it. The number, which
// HTML export drops, goes beside too.
#let display_math(it) = {
  let parts = if it.body.func() == [].func() { it.body.children } else { (it.body,) }
  let notes = parts.filter(c => c.func() == block).map(c => c.body)
  let body = parts.filter(c => c.func() != block).join()
  let tag = if in_note.get() { "span" } else { "div" } // Spans inside a sidenote (see above).
  el(tag, class: "eqn", {
    el(tag, class: "eq-scroll", {
      html.frame(math.equation(body, block: true, numbering: none))
      math_label(body, tag: tag)
      notes.join()
    })
    if it.numbering != none {
      el(tag, class: "eqnum", numbering(it.numbering, ..counter(math.equation).get()))
    }
  })
}

// The page: a top bar, a contents sidebar, then the body. Sidenotes and figure captions sit in a
// right-hand margin column, as in the PDF.
#let page(title: none, author: none, date: none, description: none, toc: false, heading_numberings: (), body) = {
  let contents = context el("ol", class: "toc-list", for h in query(std.heading.where(outlined: true)) {
    if h.level > 2 { continue }
    let n = if h.numbering != none {
      numbering(heading_numberings.at(calc.min(h.level, heading_numberings.len()) - 1), ..counter(std.heading).at(h.location()))
    }
    el("li", class: "toc-l" + str(h.level), link(h.location(), [#el("span", class: "secnum", n)#h.body]))
  })

  html.elem("html", attrs: (lang: "en"), {
    html.elem("head", {
      html.elem("meta", attrs: (charset: "utf-8"))
      html.elem("meta", attrs: (name: "viewport", content: "width=device-width, initial-scale=1"))
      html.elem("title", title)
      if description != none { html.elem("meta", attrs: (name: "description", content: description)) }
      // What a link to the page shows when shared (X, Slack, iMessage, ...).
      html.elem("meta", attrs: (property: "og:title", content: title))
      if description != none { html.elem("meta", attrs: (property: "og:description", content: description)) }
      html.elem("link", attrs: (rel: "icon", type: "image/svg+xml", href: "favicon.svg"))
      // Fetch the fonts straight away, so text doesn't first render in a fallback font.
      for font in ("LibertinusSans-Regular.woff2", "LibertinusSans-Bold.woff2", "LibertinusSans-Italic.woff2") {
        html.elem("link", attrs: (rel: "preload", href: "fonts/" + font, "as": "font", type: "font/woff2", crossorigin: ""))
      }
      html.elem("style", read("web.css"))
    })
    // Starts with the top bar hidden (.at-top), as the title is on screen; web.js keeps it updated.
    html.elem("body", attrs: (class: "at-top"), {
      // Margin notes stay hidden until web.js has laid them out (only when scripts run).
      html.elem("script", "document.body.classList.add('margin-pending')")
      el("header", class: "topbar", {
        if toc { html.elem("button", attrs: (class: "toc-toggle", "aria-label": "Contents"), "☰") }
        html.elem("a", attrs: (class: "topbar-title", href: "#"), title)
        el("span", class: "topbar-read") // How far through the page, filled in by web.js.
      })
      if toc { html.elem("nav", attrs: (class: "toc", "aria-labelledby": "toc-title"), {
        html.elem("div", attrs: (class: "toc-title", id: "toc-title"), "Contents") // As in the PDF.
        contents
      }) }
      el("main", class: "page", {
        el("header", class: "titleblock", {
          el("h1", title)
          el("p", class: "byline", if author == none { el("span", class: "date", date) } else [
            #author (#el("span", class: "date", date))
          ])
        })
        el("article", body)
        el("footer", class: "pagefoot", author)
      })
      html.elem("script", read("web.js"))
    })
  })
}
