// The image shown when the site is shared (X, Slack, iMessage, ...): 1200×630, the usual size for
// link previews, rendered at 2× so it stays sharp. It's rendered locally and committed:
//   typst compile --root . web/hero.typ web/site/hero.png --ppi 144
//
// A drawing in the style of the Reed-Solomon figures: two polynomials (green and red) evaluated at
// a row of columns, agreeing at two of them, and the die (the favicon) picking a column to check.

#let (W, H) = (1200, 630)
#set page(width: W * 1pt, height: H * 1pt, margin: 0pt, fill: white)

// The figures' colours.
#let green = rgb(18.04%, 61.96%, 30.98%)
#let red = rgb(76.08%, 27.06%, 23.92%)
#let purple = rgb(48.24%, 30.98%, 72.16%)

// The polynomials, in t = x / W (y down), coefficients from the constant up. Red is green plus a
// multiple of (t - 80/W)(t - 560/W), so they agree at the columns x = 80 and 560.
#let poly(cs) = x => cs.rev().fold(0, (acc, c) => acc * x / W + c)
#let green_y = poly((270.86, 612.709, -2005.569, 3432.711, -1873.749))
#let red_y = poly((113.03, 3442.137, -9160.579, 6725.281, -587.373))
#let cols = range(7).map(k => 80 + 160 * k)
#let die_col = 400

// Zoomed in a little (8%) about the middle column, which goes in the middle of the image, so the
// outer columns are the same distance from either edge, and mirrored left to right.
#let zoom = 1.08
#let to_x(x) = W / 2 - zoom * (x - 560)
#let to_y(y) = 340 + zoom * (y - 340)
#let from_x(x) = 560 - (x - W / 2) / zoom
#let green_at(x) = to_y(green_y(from_x(x)))
#let red_at(x) = to_y(red_y(from_x(x)))

#let line_of(f, colour) = curve(
  stroke: (paint: colour.transparentize(15%), thickness: 9pt, cap: "round"),
  curve.move((-40pt, f(-40) * 1pt)),
  ..range(-40, W + 41, step: 6).map(x => curve.line((x * 1pt, f(x) * 1pt))),
)
#let dot(x, y, colour) = place(top + left, dx: x * 1pt - 15pt, dy: y * 1pt - 15pt, circle(radius: 15pt, fill: colour))

// The die over its column, its dotted line running off the bottom. In the SVG's 19-unit view, the
// die's square spans 16 units, from 1.5 units down, centred 10 units across. As in the figure (in
// its units, where the die is 16 wide), the line starts 2 below the die, dashed 2.5 on, 2 off; a
// little thicker than the figure's 1.2, to read at preview sizes.
#let (die, die_top) = (64, 104) // Width and top edge of the die's square.
#let die_svg = die * 19 / 16 // The whole SVG, so its square comes out `die` wide.
#let u = die / 16
#let die_x = to_x(die_col)
#place(top + left, dx: die_x * 1pt, dy: (die_top + die + 2 * u) * 1pt, line(start: (0pt, 0pt),
  end: (0pt, H * 1pt), stroke: (paint: purple, thickness: 1.6 * u * 1pt, dash: (2.5 * u * 1pt, 2 * u * 1pt))))
#place(top + left, dx: (die_x - die_svg * 10 / 19) * 1pt, dy: (die_top - die_svg * 1.5 / 19) * 1pt,
  image("/web/site/favicon.svg", width: die_svg * 1pt))

// Green on top, so where the two agree it's green that shows. There, the red dot is left out, as
// one exactly under the green one would show as a dark fringe round its anti-aliased edge.
#place(top + left, line_of(red_at, red))
#place(top + left, line_of(green_at, green))
#for x in cols.map(to_x) {
  if calc.abs(red_at(x) - green_at(x)) > 1 { dot(x, red_at(x), red) }
  dot(x, green_at(x), green)
}
