#import "common.typ": *

#thm("Uniqueness", kind: "Corollary 6.10")[
For a well-typed term $Gamma ⊢ t : ucol(*) A$ and all $Gamma_0$ and $H$ such that $H comprel (Gamma_0 + s dot.op Gamma)$ and multi-reduction to a value $H ⊢ t =>_s H' ⊢ * v$, for all $id in sans("dom")(H)$:

$
  &(forall ref in sans("refs")(t) . ref mapsto_(ucol(1)) id in H implies ref mapsto_(ucol(1)) id in H') \
  &quad and (forall id' in sans("dom")(H') \\ sans("dom")(H) . forall ref in sans("refs")(v) . exists! ref' . ref' mapsto_(ucol(1)) id' in H')
$
] <thm:uniqueness>
