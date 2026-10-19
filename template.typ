#import "@preview/ctheorems:1.1.3": *
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/marginalia:0.3.1" as marginalia
#import "web/web.typ" // The web version's layout, used wherever `target() == "html"` below.

// Macros for common snippets:
#let def = $:=$
#let st = $"s.t."$
#let iff = $<==>$
#let bij = $<->$
#let inj = $arrow.r.hook$
#let surj = $arrow.r.twohead$
#let QED = context if target() == "html" { web.qed() } else [#h(1fr)$qed$]
#let section = sym.section
#let divider = context if target() == "html" { web.divider() } else [#line(length: 100%)]
#let note(body) = [*#smallcaps("Note"):*~#body]
#let case(title, body) = [+ #block[*#title*#parbreak()#body]]
#let todo(body) = [#block(fill: orange, inset: 4pt, text(size: 2em)[*TODO:* #body])]
#let bar(x) = $overline(#x)$
#let card(x) = $\#(#x)$
#let inv(x) = $#x^(-1)$
#let cmath(color, body) = text(fill: color)[$#body$]
#let mics = $upright(mu s)$
// Sidenotes share one sequence with footnotes so numbers never collide.
#let pdf_sidenote = marginalia.note.with(
  counter: counter(footnote),
  // block-style: (width: 100%, fill: luma(99%), inset: 5pt, radius: 3pt),
  numbering: (..n) => super(numbering("1", ..n)),
  flush-numbering: true, // Number inline at the start of the note, not hanging into the gap.
  // Force size/weight/style so notes don't pick up formatting from where their marker sits.
  text-style: (size: 9pt, weight: "regular", style: "normal"),
)
// The leading metadata keeps a labelled sidenote referenceable (marginalia looks for it).
#let sidenote(..args) = [#metadata("_marginalia_note")#context if target() == "html" {
  web.sidenote(args.named().at("counter", default: auto) != none, args.pos().last())
} else { pdf_sidenote(..args) }]
#let sn = sidenote
#let s = sidenote
#let fn = footnote
// Block spanning the text and sidenote columns; notes shift to avoid it. Normal width without sidenotes.
#let wideblock(..args) = context if target() == "html" { web.wideblock(args.pos().last()) } else {
  marginalia.wideblock(..args)
}
// Use as `#show: page_per_h1` to start every following level-1 heading on a fresh page.
#let page_per_h1(rest) = { show heading.where(level: 1): it => pagebreak(weak: true) + it; rest }

// Use as `#show: page_fill.with(color)` to give the rest of the document a page background.
#let page_fill(fill, rest) = context if target() == "html" { web.page_fill(fill, rest) } else {
  set page(fill: fill)
  rest
}

// How many heading levels prefix theorem and equation numbers, e.g. 2 gives Theorem 1.4.3.
#let numbering_depth = 2

// Theme style config:
#let margin_presets = (
  default: (left: 2.5cm, right: 2.5cm, top: 2.5cm, bottom: 2.5cm), // Typst's default for A4.
  compact: (left: 1.5cm, right: 1.5cm, top: 2cm, bottom: 2cm),
)

#let colors = (
  cherry_red: rgb("#ba0017"),
  powder_pink: rgb("#FEF2F4"),
  salmon_pink: rgb("#EE6983"),
  cream: rgb("#FFF4E0"),
  peach: rgb("#F4B183"),
  pale_blue: rgb("#F7FBFC"),
  light_blue: rgb("#769FCD"),
  pale_sage: rgb("#F3F7ED"),
  sage: rgb("#98B475"),
)

#let thmbox_args = (
  titlefmt: title => [
    #place(top + right)[#text(12pt)[#smallcaps[#title]]]
    #sym.wj
    #h(0pt, weak: true)
  ],
  namefmt: name => [#text(12pt, weight: "bold")[#name]],
  separator: none,
  bodyfmt: body => [#v(-1pt)#body],
  padding: (top: 0em, bottom: 0em),
  inset: (top: 0.7em, rest: 8pt),
  base_level: numbering_depth, // Truncate the heading prefix of theorem numbers.
)

// ctheorems' `thmbox`, plus a web version of the box (`web_bodyfmt` formats the body there). The
// PDF branch is ctheorems' own box format, unchanged.
#let thmbox(
  identifier,
  head,
  ..blockargs,
  supplement: auto,
  padding: (top: 0.5em, bottom: 0.5em),
  namefmt: x => [(#x)],
  titlefmt: strong,
  bodyfmt: x => x,
  separator: [#h(0.1em):#h(0.2em)],
  base: "heading",
  base_level: none,
  web_bodyfmt: x => x,
) = {
  if supplement == auto { supplement = head }
  let pdf_fmt(name, number, body, title: auto, ..blockargs_individual) = {
    if not name == none { name = [ #namefmt(name)] } else { name = [] }
    if title == auto { title = head }
    if not number == none { title += " " + number }
    title = titlefmt(title)
    body = bodyfmt(body)
    pad(
      ..padding,
      block(
        width: 100%,
        inset: 1.2em,
        radius: 0.3em,
        breakable: false,
        ..blockargs.named(),
        ..blockargs_individual.named(),
        [#title#name#separator#body]
      )
    )
  }
  let fmt(..args) = context if target() == "html" { web.thm(identifier, head, web_bodyfmt, ..args) } else {
    pdf_fmt(..args)
  }
  thmenv(identifier, base, base_level, fmt).with(supplement: supplement)
}

// Boxes from ctheorems:
#let theorem = thmbox(
  "theorem",
  "Theorem",
  fill: colors.powder_pink,
  stroke: colors.salmon_pink,
  ..thmbox_args,
)

#let lemma = thmbox(
  "lemma",
  "Lemma",
  fill: colors.cream,
  stroke: colors.peach,
  ..thmbox_args,
)

#let corollary = thmbox(
  "corollary",
  "Corollary",
  fill: colors.pale_blue,
  stroke: colors.light_blue,
  ..thmbox_args,
)

#let example = thmbox(
  "example",
  "Example",
  fill: colors.pale_blue,
  stroke: colors.light_blue,
  ..thmbox_args,
)

#let definition = thmbox(
  "definition",
  "Definition",
  fill: colors.pale_sage,
  stroke: colors.sage,
  ..thmbox_args,
)

// Equivalent to ctheorems' `thmproof` (via `thmplain`), built on the `thmbox` above.
#let proof = thmbox(
  "proof",
  "Proof",
  padding: (top: 0em, bottom: 0em),
  breakable: true,
  inset: 0pt,
  namefmt: emph,
  titlefmt: title => [*#smallcaps(title)*],
  bodyfmt: proof-bodyfmt,
  web_bodyfmt: web.proof_body,
).with(numbering: none)

// Theme loader:
#let themed_document(
  // ----------------------------------------------------------------------------------- //
  // Title:
  title: "An Untitled Note",
  author: "Anonymous",
  date: datetime.today().display("[month repr:long] [day], [year]"),
  title_align: center, // May prefer left for more casual documents.
  toc: false,
  margins: none, // none for the Typst default, or a preset name from `margin_presets`.
  sidenotes: false, // Reserves extra right margin for #sidenote[...] and moves the TOC there.
  sidenote_width: 5cm, // Added to the right margin when sidenotes are enabled.
  // Headings:
  heading_font: "Libertinus Sans", // Others: New Computer Modern Sans, Libertinus Serif.
  heading_numberings: (sym.section + "1.1.",), // Per-level numbering; falls back to last.
  // Numbering:
  // Equations are numbered by section, e.g. (1.4.2), restarting at each heading up to
  // `numbering_depth`. These patterns receive the truncated heading number followed by
  // the equation count.
  eqn_numbering: "(1.1)",
  eqn_ref_numbering: "(1.1)", // May prefer something like Eq. (1.1) for clarity.
  // ----------------------------------------------------------------------------------- //
  body,
) = {
  // Shorthands for math equations.
  show: shorthands.with(
    ($,,$, $thin$),
  )

  show: thmrules.with(qed-symbol: $qed$) // Must do this or theorems will format weirdly!
  set document(title: title, author: if author == none { "Unknown" } else { author }) // Metadata.
  set par(justify: true) // Make paragraphs pretty.

  // Keep only the first `numbering_depth` heading numbers.
  let truncate(h) = h.slice(0, calc.min(numbering_depth, h.len()))

  // Colored links.
  show link: it => {
    set text(if (type(it.dest) == str) { blue } else { colors.cherry_red })
    it
  }

  // Make theorem, equation, etc references links.
  show ref: it => {
    if it.element == none { return it }

    if it.element.func() == figure and it.element.kind == "thmenv" {
      // From: https://github.com/sahasatvik/typst-theorems/theorems.typ
      let supplement = it.element.supplement
      if it.citation.supplement != none { supplement = it.citation.supplement }
      let thms = query(selector(<meta:thmenvcounter>).after(it.element.location()))
      let number = thmcounters.at(thms.first().location()).latest

      link(it.target, [#supplement~#numbering(it.element.numbering, ..number)])
    } else if (
      it.element.func() == [].func() and it.element.children.len() > 1
        and it.element.children.first() == metadata("_marginalia_note")
    ) {
      context if target() == "html" { web.sidenote_ref(it.element) } else { it }
    } else if it.element.func() == math.equation {
      // Read both counters at the equation itself, not at the reference.
      let loc = it.element.location()
      let h = counter(heading).at(loc)
      let n = counter(math.equation).at(loc)
      link(it.target, [#numbering(eqn_ref_numbering, ..truncate(h), ..n)])
    } else { it }
  }

  // Number equations by section, but only number equations with labels attached.
  set math.equation(numbering: (..n) => numbering(eqn_numbering, ..truncate(counter(heading).get()), ..n))
  show math.equation: it => {
    // Idea from: https://forum.typst.app/t/how-to-conditionally-enable-equation-numbering-for-labeled-equations
    if it.block and it.numbering != none and not it.has("label") [
      #counter(math.equation).update(v => v - 1)
      #math.equation(it.body, block: true, numbering: none)
    ] else if target() == "html" {
      if it.block { web.display_math(it) } else { web.inline_math(it) }
    } else { it } // Only show equation numbers when they are labeled and have numbering.
  }

  // Seperate and color heading numbers differently from heading text.
  set heading(numbering: heading_numberings.first())
  let heading_number(level) = counter(heading).display(heading_numberings.at(
    calc.min(level, heading_numberings.len()) - 1,
  ))
  show heading: it => context {
    // Restart equation numbering only at headings that appear in the number prefix.
    if it.level <= numbering_depth { counter(math.equation).update(0) }
    if target() == "html" { web.heading(it, heading_number(it.level)) } else { block([
      #set text(font: heading_font, size: 21pt - (it.level * 2.5pt))
      #if (it.numbering != none) [
        #text(colors.cherry_red)[#counter(heading).display(heading_numberings.at(
          calc.min(it.level, heading_numberings.len()) - 1,
        ))]
        #h(3pt) // Space between numbering and heading text.
      ]
      #it.body
      #v(0.4em) // Space below headings.
    ]) }
  }

  // On the web the document is a site rather than pages; everything below this is the PDF layout.
  context if target() == "html" {
    set figure.caption(position: top) if sidenotes // web.js puts it in the margin, as in the PDF.
    web.page(title: title, author: author, date: date, toc: toc, heading_numberings: heading_numberings, body)
  } else {
    // Page margins, widened on the right if sidenotes are enabled.
    let margin = margin_presets.at(if margins == none { "default" } else { margins })
    if sidenotes { margin.right += sidenote_width }
    let full_width = 100% + (margin.right - margin.left) // Text width plus the sidenote area.

    // Sidenote column in the right margin, with outer padding mirroring the left page margin.
    // Marginalia sets the page margins from this, so it must agree with `margin` above.
    let note_sep = 1.5em // Gap between the text and the sidenote column.
    show: marginalia.setup.with(
      inner: (far: margin.left, width: 0pt, sep: 0pt),
      outer: if sidenotes {
        (far: margin.left, width: margin.right - margin.left - note_sep, sep: note_sep)
      } else { (far: margin.right, width: 0pt, sep: 0pt) },
      top: margin.top,
      bottom: margin.bottom,
    )

    // Figure captions go in the sidenote column, top-aligned with the figure (from marginalia's README).
    set figure(gap: 0pt) if sidenotes // Caption is in the margin, so no gap below the figure.
    set figure.caption(position: top) if sidenotes
    show figure.caption.where(position: top): it => if sidenotes {
      sidenote(
        alignment: "top", counter: none, shift: "avoid", keep-order: true,
        dy: -0.01pt, // So the caption is placed above wide figures rather than pushed below them.
        it,
      )
    } else { it }

    set page(
      // Pretty header on each non-cover page with title & dots for page num.
      header: context {
        let page_num = here().page()
        if page_num > 1 { block(width: full_width)[
          *#smallcaps[#title]*
          #h(1fr)
          #box(
            inset: (bottom: 1pt),
            (
              calc.min(page_num, 50) // Too many dots is bad for long docs.
                * (
                  box(
                    circle(
                      radius: 2pt,
                      fill: black,
                    ),
                  ),
                )
            ).join(h(2pt)),
          )
        ] }
      },
      // Pretty footer with author & page num.
      footer: context {
        let page_counter = counter(page)
        if (page_counter.final().at(0) == 1) { return none }
        block(width: full_width)[
          #text(weight: "bold", smallcaps[#if here().page() > 1 [#author] else [#sym.arrow.b]])
          #h(1fr)
          #page_counter.display("1 of 1", both: true)
        ]
      },
    )

    // Title, author, date (centered on the page even if the margins are asymmetric).
    block(width: full_width, align(title_align)[
      #set text(font: heading_font)
      #block(spacing: 1.3em)[#text(25pt, weight: "bold")[#title]]
      #text(15pt)[
        #if author == none [
          #text(colors.cherry_red)[#date]
        ] else [
          #author (#text(colors.cherry_red)[#date])
        ]
      ]
    ])

    v(1em) // Some vertical space.

    // Pretty table of contents if enabled.
    if toc {
      let contents = {
        show outline: it => {
          show heading: it => {
            set text(font: heading_font)
            set par(first-line-indent: 0em)
            it.body
            v(0.75em)
          }
          show outline.entry.where(level: 1): it => {
            text(colors.cherry_red)[#strong[#it]]
          }
          show outline.entry: it => {
            v(0.1em)
            text(font: heading_font, colors.cherry_red)[#it]
          }
          it
        }

        outline(indent: if sidenotes { 0.6em } else { auto }, depth: 2) // Narrow notes can't afford auto indents.
      }

      if sidenotes {
        place(sidenote(counter: none, alignment: "top", box(width: 100%, align(left, contents))))
      } else { contents }
    }

    v(1em) // Some more vertical space.

    body
  }
}