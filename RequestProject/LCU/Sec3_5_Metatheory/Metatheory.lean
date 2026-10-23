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
full β-reduction `FullSteps`.  A step `Step H t d e H' t' Γ₁ Δ` opens `d` binders and
allocates `e` arrays; contexts over the old scope are padded with `TCtx.lift d e` (and
`UCtx.lift d`).  A multi-step reduction records the embedding `κ` of the old array
references into the final scope, so that statements can compare the reference `κ a` of the
final heap with the reference `a` of the initial heap.
-/

@[expose] public section

namespace LCU

open Term

/-- **Theorem 4 (Conservation)**, as stated in the paper: for a well-typed term
`Γ ⊢ t : A` and all `Γ₀` and `H` such that `H ⋈ (Γ₀ + Γ)` and a reduction
`H ⊢ t ⇝ H' ⊢ t' | Γ₁ | Δ` we have `∃ Γ'. Γ' ⊢ t' : A ∧ H' ⋈ (Γ₀ + Γ') ∧
(H̄' + Δ) ⊑ (H̄, Γ̄₁)`. -/
def Conservation : Prop :=
  ∀ {n ρ : ℕ} (Γ : TCtx n ρ) (t : Term n ρ) (A : Ty), HasType Γ t A →
  ∀ (Γ₀ Γs : TCtx n ρ) (H : Heap n ρ), Γ₀.Add Γ Γs → Compat H Γs →
  ∀ (d e : ℕ) (H' : Heap (n + d) (ρ + e)) (t' : Term (n + d) (ρ + e)) (Γ₁ : BCtx (n + d))
    (Δ : UCtx (n + d)), Step H t d e H' t' Γ₁ Δ →
  ∃ Γ' Γs' : TCtx (n + d) (ρ + e), HasType Γ' t' A ∧ (Γ₀.lift d e).Add Γ' Γs' ∧
    Compat H' Γs' ∧ UCtx.Le (UCtx.add H'.usage Δ) (optUnion (H.usage.lift d) Γ₁.usage)

/-- **Theorem 5 (Uniqueness)**, as stated in the paper: for a well-typed term
`Γ ⊢ t : *A` and all `Γ₀` and `H` such that `H ⋈ (Γ₀ + Γ)` and given a multi-reduction
to a value `H ⊢ t ⇒ H' ⊢ *v | Γ' | Δ`, for all `a ∈ arrRefs(v)` we have
`a ↦₁ t' ∈ H ⟹ ∃ t''. a ↦₁ t'' ∈ H'` and `a ∉ dom(H) ⟹ ∃ t''. a ↦₁ t'' ∈ H'`.
A reference `a` of the final configuration is in `dom(H)` if it is `κ b` for a reference
`b` allocated in `H`. -/
def Uniqueness : Prop :=
  ∀ {n ρ : ℕ} (Γ : TCtx n ρ) (t : Term n ρ) (A : Ty), HasType Γ t (.star A) →
  ∀ (Γ₀ Γs : TCtx n ρ) (H : Heap n ρ), Γ₀.Add Γ Γs → Compat H Γs →
  ∀ {m ρ' : ℕ} (H' : Heap m ρ') (v : Term m ρ') (κ : Var ρ → Var ρ') (Γ' : BCtx m)
    (Δ : UCtx m), Steps H t H' (.star v) κ Γ' Δ →
  ∀ a, RefIn a v →
    ((∃ b e, κ b = a ∧ H.arrs.get b = some e ∧ e.r = .one) →
      ∃ e', H'.arrs.get a = some e' ∧ e'.r = .one) ∧
    ((∀ b, κ b = a → H.arrs.get b = none) → ∃ e', H'.arrs.get a = some e' ∧ e'.r = .one)

/-- **Theorem 6 (Progress)**, as stated in the paper: given `Γ ⊢ t : A`, `t` is either
a value, or if `H ⋈ Γ₀ + Γ` there exist `H'`, `t'`, `Δ`, `Γ'` with
`H ⊢ t ⇝ H' ⊢ t' | Γ' | Δ`. -/
def Progress : Prop :=
  ∀ {n ρ : ℕ} (Γ : TCtx n ρ) (t : Term n ρ) (A : Ty), HasType Γ t A →
  IsValue t ∨ ∀ (Γ₀ Γs : TCtx n ρ) (H : Heap n ρ), Γ₀.Add Γ Γs → Compat H Γs →
    ∃ (d e : ℕ) (H' : Heap (n + d) (ρ + e)) (t' : Term (n + d) (ρ + e)) (Γ' : BCtx (n + d))
      (Δ : UCtx (n + d)), Step H t d e H' t' Γ' Δ

/-- **Theorem 7 (Soundness with respect to the equational theory)**, as stated in
the paper: for all `t₁, t₂` such that `Γ ⊢ t₁ : A`, `Γ ⊢ t₂ : A` and `t₁ ≡ t₂`, and
given `H` such that `H ⋈ Γ`, there exist a value (irreducible term) `v` and
`Γ₁, Γ₂, Δ₁, Δ₂` such that there are full β-reductions to the same value:
`H ⊢ t₁ ⇒_β H' ⊢ v | Γ₁ | Δ₁` and `H ⊢ t₂ ⇒_β H' ⊢ v | Γ₂ | Δ₂`. -/
def EqSoundness : Prop :=
  ∀ {n ρ : ℕ} (Γ : TCtx n ρ) (t₁ t₂ : Term n ρ) (A : Ty), HasType Γ t₁ A → HasType Γ t₂ A →
  t₁ ≡ₗ t₂ → ∀ H : Heap n ρ, Compat H Γ →
  ∃ (m ρ' : ℕ) (H' : Heap m ρ') (v : Term m ρ') (κ₁ κ₂ : Var ρ → Var ρ') (Γ₁ Γ₂ : BCtx m)
    (Δ₁ Δ₂ : UCtx m),
    Irreducible H' v ∧ FullSteps H t₁ H' v κ₁ Γ₁ Δ₁ ∧ FullSteps H t₂ H' v κ₂ Γ₂ Δ₂

end LCU
