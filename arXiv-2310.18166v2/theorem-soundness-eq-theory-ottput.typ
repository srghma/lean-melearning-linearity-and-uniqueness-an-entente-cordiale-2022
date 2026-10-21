#import "common.typ": *

#thm("Soundness with respect to the equational theory", kind: "Theorem 6.11")[
For all $t_1, t_2$ such that $Gamma ⊢ t_1 : A$, $Gamma ⊢ t_2 : A$, and $t_1 equiv t_2$, and given $H$ such that $H comprel Gamma$, there exist multi-reductions to values that are equal under full $beta$-reduction:

$ H ⊢ t_1 =>_1 H' ⊢ v_1 quad and quad H ⊢ t_2 =>_1 H'' ⊢ v_2 quad and quad H'(v_1) equiv H''(v_2) $
] <thm:soundness-eq-theory>
