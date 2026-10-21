#import "common.typ": *

#thm("Type Preservation", kind: "Theorem 6.7")[
For a well-typed term $Gamma ⊢ t : A$, under a restriction that reference resources are restricted to non-function types, and all $s$, $Gamma_0$, and $H$ such that $H comprel (Gamma_0 + s dot.op Gamma)$ and a reduction $H ⊢ t squig_s H' ⊢ t'$, we have:

$ exists Gamma', H' . quad Gamma' ⊢ t' : A quad and quad H' comprel (Gamma_0 + s dot.op Gamma') $

Note the caveat to preservation: references $sans("Ref")_id A$ are restricted such that $A$ cannot be of function type, or some other composite type involving functions. The restriction is needed for preservation since it works at the granularity of a single reduction, and so cannot rule out the possibility that a reference is storing a $lambda$ term with free variables. This does not affect any of the examples discussed in the paper.
] <thm:type-preservation>
