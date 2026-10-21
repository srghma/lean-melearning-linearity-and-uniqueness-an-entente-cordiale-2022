#import "common.typ": *

We define an operational semantics here for the calculus which serves to further explain the details of arrays, mutation, copying, and borrowing. We adapt the approach of @choudhury2021graded and @marshall2022linearity for giving an operational semantics to a graded system, with some degree of accounting for grades and references in order to relate the dynamic semantics back to the static semantics of typing (@sec:theorems). With the exception of Granule and Multi-Graded Featherweight Java @bianchini2023multi, much of the preceding work on operational models for graded systems is based on call-by-name. Here we opted for call-by-value for the purpose of describing real-world practical functional languages; call-by-name is prohibitively expensive with unpredictable performance and poor interaction with side effects.

== Preliminary definitions
<preliminary-definitions>

=== Values
<values>

We first define the subset of terms that are _values_ in the semantics, i.e., normal forms (terms that have no further reduction), via the grammar:

$
  v ::= (v_1, v_2) | () | [v] | lambda x. t | n | p | bold("pack") langle id, v rangle
$

including pairs of values, the unit value, boxed values, abstractions, natural numbers $n$, or primitives $p$ which may also be partially applied to other values: $bold("newArray")$, $bold("readArray")$, $bold("readArray") v$, etc.

=== Runtime terms and typing
<runtime-terms-and-typing>

We extend the syntax of terms (and values) with several runtime representations which appear only in the semantics:

$
  t &::= ldots | * t | bold("unborrow") t | ref | [t]_(lcol(r)) \
  v &::= ldots | * v | bold("unborrow") v | ref
$

where $* t$ represents unique and borrowed terms, $bold("unborrow") t$ is the inverse to borrowed terms (used to implement $bold("withBorrow")$), and $ref$ are references to resources bound in the heap. Furthermore, the syntax for promotion is augmented with an annotation $[t]_(lcol(r))$ of the grade at which the term $t$ is promoted, i.e., Church-style with respect to grades, and thus typing this grade-annotated version produces $r dot.op Gamma ⊢ [t]_(lcol(r)) : Box_(lcol(r)) A$.

In order to type runtime terms with references, the syntax of contexts is extended to include assumptions $ref : Res_id A$ which are treated as a different syntactic category of variables. A _runtime context_ $gamma$ is a context containing only references, i.e.: $gamma ::= emptyset | gamma, ref : Res_id A$.

Context scalar multiplication and addition extend as follows:

$
  (Gamma, ref : Res_id A) + (Gamma', ref : Res_id A) &= (Gamma + Gamma'), ref : Res_id A \
  (Gamma, ref : Res_id A) + Gamma' &= (Gamma + Gamma'), ref : Res_id A quad ("where" ref in.not Gamma') \
  r dot.op (Gamma, ref : Res_id A) &= (r dot.op Gamma), ref : Res_id A
$

Runtime terms are typed by the following rules:

#v(0.5em)
#grid(
  columns: (1fr, 1.2fr, 1.2fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [nec],
      $gamma ⊢ t : A$,
      $0 dot.op Gamma, gamma ⊢ * t : withB_p A$
    )
  ),
  prooftree(
    rule(
      name: [unborrow],
      $Gamma ⊢ t : withB_1 A$,
      $Gamma ⊢ bold("unborrow") t : ucol(*) A$
    )
  ),
  prooftree(
    rule(
      name: [ref],
      $0 dot.op Gamma, ref : Res_id A ⊢ ref : Res_id A$
    )
  )
)
#v(0.5em)

=== Heaps and configurations
<heaps-and-configurations>

Heaps map program variables to values, and map references to identifiers $id$:

$
  H &::= emptyset | H, x mapsto_(lcol(r)) v | H, ref mapsto_(ucol(p)) id | H, id mapsto v_r \
  v_r &::= bold("arr") | mathbfref(v) \
  bold("arr") &::= sans("init") | bold("arr")[n] = v
$

A _configuration_ comprises a pair of a heap $H$ and a term $t$, written $H ⊢ t$, where $sans("fv")(t) subset.eq sans("dom")(H)$ and $sans("refs")(t) subset.eq sans("dom")(H)$.

== Single-step reduction
<single-step-reduction>

Single-step reductions map source configurations to target configurations, with the judgment: $H_1 ⊢ t_1 squig_s H_2 ⊢ t_2$, where $s$ denotes the usage context. Throughout, $x \# overline(t)$ means that $x$ is a fresh name with respect to terms $overline(t)$.

=== Lambda calculus
<lambda-calculus>

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [$squig_("var")$],
      $exists r'. med s + r' sqle r$,
      $H, x mapsto_(lcol(r)) v ⊢ x squig_s H, x mapsto_(lcol(r)) v ⊢ v$
    )
  ),
  prooftree(
    rule(
      name: [$squig_beta$],
      $y \# {H, v, t}$,
      $H ⊢ (lambda x. t) v squig_s H, y mapsto_(lcol(s)) v ⊢ t [y \/ x]$
    )
  )
)

#v(0.5em)
#grid(
  columns: (1fr, 1fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [$squig_("appL")$],
      $H ⊢ t_1 squig_s H' ⊢ t_1'$,
      $H ⊢ t_1 t_2 squig_s H' ⊢ t_1' t_2$
    )
  ),
  prooftree(
    rule(
      name: [$squig_("appR")$],
      $H ⊢ t_2 squig_s H' ⊢ t_2'$,
      $H ⊢ v t_2 squig_s H' ⊢ v t_2'$
    )
  )
)
#v(0.5em)

=== Existential types and names
<existential-types-and-names>

#v(0.5em)
#align(center)[
#prooftree(
  rule(
    name: [$squig_(exists beta)$],
    $y \# {H, v, t}$,
    $H ⊢ bold("unpack") langle id, x rangle = bold("pack") langle id', v rangle bold("in") t squig_s H, y mapsto_(lcol(s)) v ⊢ t [y \/ x]$
  )
)
]
#v(0.5em)

=== Tensors and units
<tensors-and-units>

#v(0.5em)
#align(center)[
#prooftree(
  rule(
    name: [$squig_(tensor beta)$],
    $x' \# {H, v_1, v_2, t}$,
    $y' \# {H, v_1, v_2, t}$,
    $H ⊢ bold("let") (x, y) = (v_1, v_2) bold("in") t squig_s H, x' mapsto_(lcol(s)) v_1, y' mapsto_(lcol(s)) v_2 ⊢ t [y' \/ y] [x' \/ x]$
  )
)
]
#v(0.5em)

=== Graded modalities
<graded-modalities>

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [$squig_square$],
      $H ⊢ t squig_(s * r) H' ⊢ t'$,
      $H ⊢ [t]_r squig_s H' ⊢ [t']_r$
    )
  ),
  prooftree(
    rule(
      name: [$squig_(square beta)$],
      $y \# {H, v, t}$,
      $H ⊢ bold("let") [x] = [v]_r bold("in") t squig_s H, y mapsto_(lcol(s * r)) v ⊢ t [y \/ x]$
    )
  )
)
#v(0.5em)

=== Arrays
<arrays>

#v(0.5em)
#align(center)[
#prooftree(
  rule(
    name: [$squig_("newArray")$],
    $ref \# H$,
    $id \# H$,
    $H ⊢ bold("newArray") n squig_s H, ref mapsto_(ucol(1)) id, id mapsto sans("init") ⊢ bold("pack") langle id, * ref rangle$
  )
)
]

$
  H, ref mapsto_(ucol(p)) id, id mapsto bold("arr")[i] = v ⊢ bold("readArray") (* ref) i &squig_s H, ref mapsto_(ucol(p)) id, id mapsto bold("arr")[i] = v ⊢ (v, * ref) \
  H, ref mapsto_(ucol(p)) id, id mapsto bold("arr") ⊢ bold("writeArray") (* ref) i v &squig_s H, ref mapsto_(ucol(p)) id, id mapsto bold("arr")[i] = v ⊢ * ref \
  H, ref mapsto_(ucol(p)) id, id mapsto bold("arr") ⊢ bold("deleteArray") (* ref) &squig_s H ⊢ ()
$

=== Sharing and cloning
<sharing-and-cloning>

#v(0.5em)
#grid(
  columns: (1fr, 1.4fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [$squig_("share"beta)$],
      $sans("dom")(H) equiv sans("refs")(v)$,
      $H, H' ⊢ bold("share") (* v) squig_s ([H]_0), H' ⊢ [v]$
    )
  ),
  prooftree(
    rule(
      name: [$squig_("clone"beta)$],
      $sans("dom")(H') equiv sans("refs")(v)$,
      $(H'', theta, id) = sans("copy")(H')$,
      $y \# {H, v, t}$,
      $H, H' ⊢ bold("clone") [v]_r bold("as") x bold("in") t_2 squig_s H, H', H'', y mapsto_(lcol(s)) bold("pack") langle id, *(theta(v)) rangle ⊢ t_2 [y \/ x]$
    )
  )
)
#v(0.5em)

=== Borrowing
<borrowing>

#v(0.5em)
#grid(
  columns: (1.2fr, 1fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [$squig_("with"withB)$],
      $y \# {H, v, t}$,
      $H ⊢ bold("withBorrow") (lambda x. t) (* v) squig_s H, y mapsto_(lcol(s)) (* v) ⊢ bold("unborrow") t [y \/ x]$
    )
  ),
  prooftree(
    rule(
      name: [$squig_("un"withB)$],
      $H ⊢ bold("unborrow") (* v) squig_s H ⊢ * v$
    )
  )
)
#v(0.5em)

=== Push and pull
<push-and-pull>

$
  H ⊢ bold("push") (* (v_1, v_2)) &squig_s H ⊢ (* v_1, * v_2) \
  H ⊢ bold("pull") (* v_1, * v_2) &squig_s H ⊢ * (v_1, v_2)
$

=== Split and join
<split-and-join>

#v(0.5em)
#align(center)[
#scale(82%)[
#prooftree(
  rule(
    name: [$squig_("splitRef")$],
    $ref_1 \# H$,
    $ref_2 \# H$,
    $H, ref mapsto_(ucol(p)) id, id mapsto v ⊢ bold("split") (* ref) squig_s H, ref_1 mapsto_(ucol(p / 2)) id, ref_2 mapsto_(ucol(p / 2)) id, id mapsto v ⊢ (* ref_1, * ref_2)$
  )
)
]
]
#v(0.5em)
#align(center)[
#scale(82%)[
#prooftree(
  rule(
    name: [$squig_("joinRef")$],
    $ref \# H$,
    $H, ref_1 mapsto_(ucol(p)) id, ref_2 mapsto_(ucol(q)) id, id mapsto v ⊢ bold("join") (* ref_1) (* ref_2) squig_s H, ref mapsto_(ucol(p + q)) id, id mapsto v ⊢ * ref$
  )
)
]
]
#v(0.5em)

=== Multi-step reductions
<multi-step-reductions>

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [refl],
      $H ⊢ t =>_s H ⊢ t$
    )
  ),
  prooftree(
    rule(
      name: [ext],
      $H ⊢ t_1 squig_s H' ⊢ t_2$,
      $H' ⊢ t_2 =>_s H'' ⊢ t_3$,
      $H ⊢ t_1 =>_s H'' ⊢ t_3$
    )
  )
)
#v(0.5em)
