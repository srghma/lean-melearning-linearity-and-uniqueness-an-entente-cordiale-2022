#import "common.typ": *

#thm([Graded substitution is admissible, extending @orchard2019quantitative], kind: "Lemma 6.3")[
If $lcol([Gamma_1]) ⊢ t_1 : A$ and $Gamma_2, lcol(x : [A]_r) ⊢ t_2 : B$ (where $lcol([Gamma_1])$ represents a context $Gamma_1$ containing only graded assumptions) and $neg sans("resourceAllocator")(t_1)$, then $Gamma_2 + r dot.op Gamma_1 ⊢ t_2 [t_1 \/ x] : B$.
] <lemma:graded-subst>
