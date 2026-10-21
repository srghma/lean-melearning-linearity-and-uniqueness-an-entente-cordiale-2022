module
public import RequestProject.LCU.Sec3_4_HeapModel.Heap

/-!
# Metatheory of the heap model: the statements of Theorems 4–7 (Section 3.5)

We state Theorems 4 (Conservation), 5 (Uniqueness), 6 (Progress) and 7 (Soundness
with respect to the equational theory) exactly as they are formulated in the paper,
as propositions about our formalisation of the heap model.

Read literally against the rules in the provided text, all four statements are false.
The disproofs are in the other files of this directory:

| Statement | Disproof | File |
| --- | --- | --- |
| `Conservation` (Theorem 4) | `not_conservation` | `CounterConservation.lean` |
| `Uniqueness` (Theorem 5) | `not_uniqueness` | `CounterUniqueness.lean` |
| `Progress` (Theorem 6) | `not_progress` | `CounterProgress.lean` |
| `EqSoundness` (Theorem 7) | `not_eqSoundness` | `CounterEqSoundness.lean` |

Notation used below: `H ⋈ Γ` is `Compat H Γ` (Definition 3), `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`
is `Step H t H' t' Γ Δ`, `⇒` is its reflexive-transitive closure `Steps`, and `⇒_β` is
full β-reduction `FullSteps`.  Because a step may open binders, the scope can grow
from `n` to `m`; contexts over the old scope are lifted with `liftTo m`.
-/

@[expose] public section

namespace LCU

open Term

/-- **Theorem 4 (Conservation)**, as stated in the paper: for a well-typed term
`Γ ⊢ t : A` and all `Γ₀` and `H` such that `H ⋈ (Γ₀ + Γ)` and a reduction
`H ⊢ t ⇝ H' ⊢ t' | Γ₁ | Δ` we have `∃ Γ'. Γ' ⊢ t' : A ∧ H' ⋈ (Γ₀ + Γ') ∧
(H̄' + Δ) ⊑ (H̄, Γ̄₁)`. -/
def Conservation : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx n) (t : Term n) (A : Ty), HasType Γ t A →
  ∀ (Γ₀ Γs : Ctx n) (H : Heap n), Γ₀.Add Γ Γs → Compat H Γs →
  ∀ (H' : Heap m) (t' : Term m) (Γ₁ : BCtx m) (Δ : UCtx m), Step H t H' t' Γ₁ Δ →
  ∃ Γ' Γs' : Ctx m, HasType Γ' t' A ∧ (Γ₀.liftTo m).Add Γ' Γs' ∧ Compat H' Γs' ∧
    UCtx.Le (UCtx.add H'.usage Δ) (optUnion (liftTo m H.usage) Γ₁.usage)

/-- **Theorem 5 (Uniqueness)**, as stated in the paper: for a well-typed term
`Γ ⊢ t : *A` and all `Γ₀` and `H` such that `H ⋈ (Γ₀ + Γ)` and given a multi-reduction
to a value `H ⊢ t ⇒ H' ⊢ *v | Γ' | Δ`, for all `a ∈ arrRefs(v)` we have
`a ↦₁ t' ∈ H ⟹ ∃ t''. a ↦₁ t'' ∈ H'` and `a ∉ dom(H) ⟹ ∃ t''. a ↦₁ t'' ∈ H'`. -/
def Uniqueness : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx n) (t : Term n) (A : Ty), HasType Γ t (.star A) →
  ∀ (Γ₀ Γs : Ctx n) (H : Heap n), Γ₀.Add Γ Γs → Compat H Γs →
  ∀ (H' : Heap m) (v : Term m) (Γ' : BCtx m) (Δ : UCtx m), Steps H t H' (.star v) Γ' Δ →
  ∀ a, RefIn a v →
    ((∃ e, H.arrs a = some e ∧ e.r = .one) → ∃ e', H'.arrs a = some e' ∧ e'.r = .one) ∧
    (H.arrs a = none → ∃ e', H'.arrs a = some e' ∧ e'.r = .one)

/-- **Theorem 6 (Progress)**, as stated in the paper: given `Γ ⊢ t : A`, `t` is either
a value, or if `H ⋈ Γ₀ + Γ` there exist `H'`, `t'`, `Δ`, `Γ'` with
`H ⊢ t ⇝ H' ⊢ t' | Γ' | Δ`. -/
def Progress : Prop :=
  ∀ {n : ℕ} (Γ : Ctx n) (t : Term n) (A : Ty), HasType Γ t A →
  IsValue t ∨ ∀ (Γ₀ Γs : Ctx n) (H : Heap n), Γ₀.Add Γ Γs → Compat H Γs →
    ∃ (m : ℕ) (H' : Heap m) (t' : Term m) (Γ' : BCtx m) (Δ : UCtx m), Step H t H' t' Γ' Δ

/-- **Theorem 7 (Soundness with respect to the equational theory)**, as stated in
the paper: for all `t₁, t₂` such that `Γ ⊢ t₁ : A`, `Γ ⊢ t₂ : A` and `t₁ ≡ t₂`, and
given `H` such that `H ⋈ Γ`, there exist a value (irreducible term) `v` and
`Γ₁, Γ₂, Δ₁, Δ₂` such that there are full β-reductions to the same value:
`H ⊢ t₁ ⇒_β H' ⊢ v | Γ₁ | Δ₁` and `H ⊢ t₂ ⇒_β H' ⊢ v | Γ₂ | Δ₂`. -/
def EqSoundness : Prop :=
  ∀ {n : ℕ} (Γ : Ctx n) (t₁ t₂ : Term n) (A : Ty), HasType Γ t₁ A → HasType Γ t₂ A →
  t₁ ≡ₗ t₂ → ∀ H : Heap n, Compat H Γ →
  ∃ (m : ℕ) (H' : Heap m) (v : Term m) (Γ₁ Γ₂ : BCtx m) (Δ₁ Δ₂ : UCtx m),
    Irreducible H' v ∧ FullSteps H t₁ H' v Γ₁ Δ₁ ∧ FullSteps H t₂ H' v Γ₂ Δ₂

end LCU
