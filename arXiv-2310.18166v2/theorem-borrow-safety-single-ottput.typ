#import "common.typ": *

#thm("Borrow safety", kind: "Lemma 6.8")[
For a well-typed term $Gamma ⊢ t : A$ and all $Gamma_0$ and heaps $H$ such that $H comprel (Gamma_0 + s dot.op Gamma)$, and given a single-step reduction $H ⊢ t squig_s H' ⊢ t'$, then for all $id in sans("dom")(H)$:

$
  sum_(ref in sans("refs")(t), \ ref mapsto_p id in H) p = 1 quad implies quad sum_(ref in sans("refs")(t'), \ ref mapsto_(p') id in H') p' in {0, 1}
$

Furthermore, any resources in the outgoing heap that did not appear in the initial heap have permissions summing to $1$:

$
  forall id' in sans("dom")(H') \\ sans("dom")(H) . quad sum_(ref' in sans("refs")(t'), \ ref' mapsto_q id' in H') q = 1
$
] <thm:single-step-uniqueness>
