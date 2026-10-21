#import "@preview/curryst:0.6.0": prooftree, rule
#import "common.typ": *

// Document setup
#set document(
  title: "Functional Ownership through Fractional Uniqueness",
  author: ("Danielle Marshall", "Dominic Orchard"),
)

#set page(
  paper: "a4",
  margin: (x: 2.2cm, top: 2.5cm, bottom: 2.5cm),
  header: context {
    if here().page() > 1 {
      smallcaps[Functional Ownership through Fractional Uniqueness]
      h(1fr)
      str(here().page())
    }
  },
)

#set text(font: "Libertinus Serif", size: 10pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")

// Title and Author block
#align(center)[
  #v(0.5em)
  #text(1.6em, weight: "bold")[Functional Ownership through Fractional Uniqueness]  #v(0.8em)
  #text(1.1em)[Danielle Marshall#super[1] and Dominic Orchard#super[1,2]]  #v(0.4em)
  #text(0.9em)[
    #super[1] School of Computing, University of Kent, UK     `{dm635, D.A.Orchard}@kent.ac.uk`     #super[2] Department of Computer Science and Technology, University of Cambridge, UK     `dao29@cam.ac.uk`
  ]  #v(1.2em)
]

#align(center)[#text(weight: "bold")[Abstract]]
#block(inset: (x: 1.5cm))[
  #set text(size: 9pt)
  Ownership and borrowing systems, designed to enforce safe memory management without the need for garbage collection, have been brought to the fore by the Rust programming language. Rust also aims to bring some guarantees offered by functional programming into the realm of performant systems code, but the type system is largely separate from the ownership model, with type and borrow checking happening in separate compilation phases. Recent models such as RustBelt and Oxide aim to formalise Rust in depth, but there is less focus on integrating the basic ideas into more traditional type systems. An approach designed to expose an essential core for ownership and borrowing would open the door for functional languages to borrow concepts found in Rust and other ownership frameworks, so that more programmers can enjoy their benefits.

  One strategy for managing memory in a functional setting is through _uniqueness types_, but these offer a coarse-grained view: either a value has exactly one reference, and can be mutated safely, or it cannot, since other references may exist. Recent work demonstrates that _linear_ and _uniqueness_ types can be combined in a single system to offer restrictions on program behaviour and guarantees about memory usage. We develop this connection further, showing that just as _graded_ type systems like those of Granule and Idris generalise linearity, Rust's _ownership_ model arises as a graded generalisation of uniqueness. We combine fractional permissions with grading to give the first account of ownership and borrowing that smoothly integrates into a standard type system alongside linearity and graded types, and extend Granule accordingly with these ideas.
]

#v(1em)

= Introduction <sec:introduction>
#include "intro.typ"

= Key Concepts in Ownership and Borrowing <sec:key>
#include "key.typ"

= Core Calculus <sec:core>
#include "core-ottput.typ"

= One of a Kind: Uniqueness and Sharing <sec:uniqueness>
#include "uniqueness-ottput.typ"

= Immutably Borrowed is Fractionally Unique <sec:fractional>
#include "fractional-ottput.typ"

= Semantics and Meta-theory <sec:semantics>
#include "semantics-ottput.typ"

== Theorems <sec:theorems>
#include "theorems-ottput.typ"

= Related Work <sec:related>
#include "related.typ"

= Conclusions and Future Work <sec:conclusion>
#include "conclusion.typ"

#heading(level: 1, numbering: none)[Data-Availability Statement]

All of the examples presented throughout this work, as well as an installation of Granule with the ownership and borrowing extensions that we describe, are included in the artefact for this paper. The artefact will be available on Zenodo following the conclusion of the artefact evaluation process.

#v(1em)

#bibliography("references.bib", title: "References", style: "chicago-author-date")
