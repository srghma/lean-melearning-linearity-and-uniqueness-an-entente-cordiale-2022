module
public import RequestProject.LCU.Sec3_5_Metatheory.Metatheory

/-!
# Theorem 7 (Soundness w.r.t. the equational theory) does not hold as stated

Counterexample: the `η!` instance `let! x = !unit in !x ≡ !unit` (both sides have type
`!1` in the empty context).  The right-hand side `!unit` is irreducible, so its only
full β-reduction sequence is the empty one, ending in the empty heap.  The left-hand
side is reducible, and its only possible first step is `!β`, which allocates the
binding `x ↦_ω unit`; configurations only grow, so the left-hand side can never reach
the same final heap (indeed not even the same scope) as the right-hand side.
-/

@[expose] public section

namespace LCU

open Term

/-! ## General facts about heap reductions -/

/-- No single-step heap rule (`Step`) applies to a term `!t`; only full β-reduction
(`FullStep.bang`) reduces under `!`. -/
lemma Step.not_bang {n ρ d e : ℕ} {H : Heap n ρ} {t : Term n ρ} {H' : Heap (n + d) (ρ + e)}
    {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)}
    (h : Step H (bang t) d e H' t' Γ Δ) : False := by
  cases h

/-- `unit` is irreducible. -/
lemma FullStep.not_unit {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)}
    {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)}
    (h : FullStep H unit d e H' t' Γ Δ) : False := by
  cases h with
  | base h => cases h

/-- `!unit` is irreducible. -/
lemma FullStep.not_bang_unit {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)}
    {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)}
    (h : FullStep H (Term.bang Term.unit) d e H' t' Γ Δ) : False := by
  cases h with
  | base h => exact h.not_bang
  | bang h => exact h.not_unit

/-- Any full β-reduction sequence from `!unit` is empty: it ends in `!unit`, in the same
scope. -/
lemma FullSteps.bang_unit {n ρ m ρ' : ℕ} {H : Heap n ρ} {H' : Heap m ρ'} {v : Term m ρ'}
    {κ : Var ρ → Var ρ'} {Γ : BCtx m} {Δ : UCtx m} (h : FullSteps H (Term.bang Term.unit) H' v κ Γ Δ) :
    v = Term.bang Term.unit ∧ m = n := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih => obtain ⟨rfl, -⟩ := ih; exact hs.not_bang_unit.elim

/-! ## The counterexample -/

namespace EqSoundnessCounterexample

/-- `let! x = !unit in !x` (in any scope) -/
def lhs {n ρ : ℕ} : Term n ρ := letBang (bang unit) (bang (var 0))

/-- `!unit` -/
def rhs : Term 0 0 := bang unit

/-- Both sides have type `!1` in the empty context. -/
lemma lhs_typed : HasType TCtx.empty (lhs : Term 0 0) (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  exact .bangE (.bangI TCtx.AllNonLin.empty (.unitI TCtx.AllNonLin.empty))
    (.bangI (TCtx.AllNonLin.cons TCtx.AllNonLin.empty (nonLin_nonlin _))
      (HasTypeD.var_zero_single (.nonlin .unit))) (TCtx.Add.empty_right _)

lemma rhs_typed : HasType TCtx.empty rhs (.bang .unit) :=
  .bangI TCtx.AllNonLin.empty (.unitI TCtx.AllNonLin.empty)

/-- The two sides are equal by the `η!` axiom. -/
lemma lhs_equiv_rhs : (lhs : Term 0 0) ≡ₗ rhs := .ax (.etaBang _)

/-- Every step of the left-hand side opens a binder. -/
lemma lhs_step_scope {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)}
    {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)}
    (h : FullStep H lhs d e H' t' Γ Δ) : d = 1 := by
  cases h with
  | base h =>
    cases h with
    | letBang h => exact h.not_bang.elim
    | betaBang _ _ => rfl
  | letBang h => exact h.not_bang_unit.elim

/-- A full β-reduction sequence from the left-hand side is empty, or it grows the scope. -/
lemma lhs_steps {n ρ m ρ' : ℕ} {H : Heap n ρ} {H' : Heap m ρ'} {v : Term m ρ'}
    {κ : Var ρ → Var ρ'} {Γ : BCtx m} {Δ : UCtx m} (h : FullSteps H lhs H' v κ Γ Δ) :
    (v = lhs ∧ m = n) ∨ n < m := by
  induction h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | tail _ hs ih =>
    rcases ih with ⟨rfl, rfl⟩ | ih
    · have := lhs_step_scope hs; subst this; right; omega
    · right; omega

/-- The left-hand side is reducible in every heap. -/
lemma lhs_reducible {n ρ : ℕ} (H : Heap n ρ) : ¬ Irreducible H lhs := by
  intro hirr
  exact hirr ⟨1, 0, _, _, _, _, FullStep.base (Step.betaBang (Γ := TCtx.empty) (A := .unit)
    TCtx.AllNonLin.empty (HasType.unitI TCtx.AllNonLin.empty))⟩

end EqSoundnessCounterexample

/-! ## The disproof -/

open EqSoundnessCounterexample in
/-- **Theorem 7 (Soundness with respect to the equational theory) is false as stated.** -/
theorem not_eqSoundness : ¬ EqSoundness := by
  intro hS
  obtain ⟨m, ρ', H', v, κ₁, κ₂, Γ₁, Γ₂, Δ₁, Δ₂, hirr, h₁, h₂⟩ :=
    hS TCtx.empty lhs rhs _ lhs_typed rhs_typed lhs_equiv_rhs Heap.empty Compat.empty
  obtain ⟨-, rfl⟩ := h₂.bang_unit
  rcases lhs_steps h₁ with ⟨rfl, -⟩ | h
  · exact lhs_reducible _ hirr
  · omega

end LCU
