#import "common.typ": *

#thm("Progress", kind: "Theorem 6.6")[
Given $Gamma ⊢ t : A$, then $t$ is either a value, or for all grades $s$ and contexts $Gamma_0$, if $H comprel (Gamma_0 + s dot.op Gamma)$ there exists a heap $H'$ and term $t'$ such that $H ⊢ t squig_s H' ⊢ t'$.
] <lemma:progress>
