#import "@preview/curryst:0.6.0": prooftree, rule

// Colors
#let coeffectColor = rgb("0750d0")
#let uniqueColor = rgb("c20232")
#let borrowColor = rgb("0750d0")
#let highlightPropColor = rgb("005900")
#let darkGreen = rgb("008059")
#let bangcol = coeffectColor
#let starcol = uniqueColor

// Domain Math Macros
#let lolli = $⊸$
#let tensor = $⊗$
#let unitT = $sans("unit")$
#let sqle = $⊑$
#let comprel = $bowtie$
#let circ = $compose$
#let le = $<=$
#let squig = $arrow.squiggly$
#let ucol(x) = text(fill: starcol)[#x]
#let lcol(x) = text(fill: bangcol)[#x]
#let bang = lcol($!$)
#let star = ucol($*$)
#let withB = math.op("&")
#let mapsto = $scripts(|->)$
#let dom = math.op("dom")
#let refs = math.op("refs")
#let arrRefs = math.op("arrRefs")
#let copyop = math.op("copy")
#let over(x) = $overline(#x)$
#let propName(x) = text(fill: highlightPropColor)[#x]
#let goal(x) = text(fill: darkGreen)[#x]
#let rustin(x) = raw(x, lang: "rust")
#let grstep = $arrow.squiggly$
#let GrBox(r, a) = $[#a]_(#lcol(r))$

// Angle bracket helpers
#let langle = $chevron.l$
#let rangle = $chevron.r$

// Math aliases for LaTeX / Ott compatibility
#let Box = $square$
#let Rightarrow = $arrow.double$
#let vdash = $⊢$
#let cdot = $dot.op$
#let notin = $in.not$
#let implies = $arrow.r.double$
#let vee = $or$
#let wedge = $and$
#let neg = $not$
#let subseteq = $subset.eq$
#let dfrac(a, b) = $(#a) / (#b)$
#let ldots = $...$
#let qquad = $quad quad$
#let textiff = "iff"
#let textwhere = "where"
#let textand = "and"
#let setlengtharraycolsep(x) = []
#let vspace(x) = []
#let hspace(x) = []
#let footnotesize = math.op("size")
#let Res = math.op("Res")
#let ref = math.op("ref")
#let mathbfref = math.op("ref")
#let share = math.op("share")
#let clone = math.op("clone")
#let bb(x) = math.bold(x)
#let subst(a, b) = $[#a \/ #b]$

// Clean theorem environment
#let thm(title, kind: "Theorem", body) = block(
  breakable: true,
  width: 100%,
  stroke: (left: 2.5pt + rgb("0750d0")),
  inset: (left: 0.8em, y: 0.4em),
  above: 0.8em,
  below: 0.8em,
  [
    #text(weight: "bold")[#kind#if title != none [ (#title)].] #body
  ]
)
// Codebox helper with badge
#let codebox(title: none, body) = {
  block(
    breakable: false,
    width: 100%,
    stroke: rgb("cbd5e1"),
    radius: 3pt,
    inset: 0.8em,
    fill: rgb("f8fafc"),
    above: 0.8em,
    below: 0.8em,
    stack(
      if title != none {
        align(right, text(size: 8pt, weight: "bold", title))
      },
      v(if title != none { 0.3em } else { 0em }),
      body
    )
  )
}
