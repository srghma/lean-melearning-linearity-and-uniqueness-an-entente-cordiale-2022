#import "common.typ": *

#thm("Multi-reduction borrow safety", kind: "Theorem 6.9")[
For a well-typed term $Gamma ⊢ t : A$ and all $Gamma_0$ and $H$ such that $H comprel (Gamma_0 + s dot.op Gamma)$, and multi-step reduction $H ⊢ t =>_s H' ⊢ v$, then for all $id in sans("dom")(H)$:

$
  sum_(ref in sans("refs")(t), \ ref mapsto_p id in H) p = 1 quad implies quad exists! ref' . ref' mapsto_(ucol(1)) id in H'
$

Furthermore, any new references in the final term uniquely point to an identifier with permission $1$:

$
  forall id' in sans("dom")(H') \\ sans("dom")(H) . forall ref in sans("refs")(v) . exists! ref' . ref' mapsto_(ucol(1)) id' in H'
$
] <thm:single-step-uniqueness-multi>
