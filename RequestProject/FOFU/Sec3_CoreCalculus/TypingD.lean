module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD.Basic
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD.Equiv

/-!
# A dereliction-free presentation of the typing judgment

`HasTypeD` has the same rules as `HasType` except that the dereliction rule `der` is
replaced by the derived rule `(var')` of §3 (`varG`: `0 · Γ, x : [A]_1 ⊢ x : A`).
The two judgments are equivalent (`hasType_iff_hasTypeD`): dereliction is admissible
for `HasTypeD` (`HasTypeD.der`), because a linear variable is used at exactly one
occurrence of `var`, which dereliction turns into `varG`.

Working with `HasTypeD` makes the substitution lemmas provable by induction: with an
explicit dereliction rule, the context of the substituted term may overlap with a
variable that is derelicted later, which breaks the induction.

The same idea is used for *Linearity and Uniqueness* in
`RequestProject/LCU/Sec3_1_Calculus/TypingD.lean` (reused here as a technique; the rule
sets differ, so the code is not shared).

We also prove that approximation extends to whole contexts (`HasTypeD.approxCtx`): if
`Γ ⊢ t : A` and `Γ'` is `Γ` with some grades approximated upwards, then `Γ' ⊢ t : A`.

## Files

* `TypingD/Basic.lean`: the rules of `HasTypeD` and context lemmas about `setVar`;
* `TypingD/Equiv.lean`: approximation of contexts, admissibility of dereliction, and the
  equivalence with `HasType`.
-/
