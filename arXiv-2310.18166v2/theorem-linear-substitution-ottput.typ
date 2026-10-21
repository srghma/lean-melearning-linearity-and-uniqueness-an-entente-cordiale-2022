#import "common.typ": *

#thm([Linear substitution is admissible, extending @orchard2019quantitative], kind: "Lemma 6.2")[
If $Gamma_1 ⊢ t_1 : A$ and $Gamma_2, x : A ⊢ t_2 : B$, then $Gamma_2 + Gamma_1 ⊢ t_2 [t_1 \/ x] : B$.
] <lemma:linear-subst>
