module
public import RequestProject.LCU.CounterConservation

/-!
# Theorem 7 (Soundness w.r.t. the equational theory) does not hold as stated

Counterexample: the `η!` instance `let! x = !unit in !x ≡ !unit` (both sides have type
`!1` in the empty context).  The right-hand side `!unit` is irreducible, so its only
full β-reduction sequence is the empty one, ending in the empty heap.  The left-hand
side is reducible, and its only possible first step is `!β`, which allocates the
binding `x ↦_ω unit`; heaps only grow in scope, so the left-hand side can never reach
the same final heap (indeed not even the same scope) as the right-hand side.
-/

@[expose] public section

namespace LCU

open Term

/-- Reductions never shrink the scope. -/
lemma Step.le {n m : ℕ} {H : Heap n} {t : Term n} {H' : Heap m} {t' : Term m} {Γ : BCtx m}
    {Δ : UCtx m} (h : Step H t H' t' Γ Δ) : n ≤ m := by
  induction h <;> omega

lemma FullStep.le {n m : ℕ} {H : Heap n} {t : Term n} {H' : Heap m} {t' : Term m} {Γ : BCtx m}
    {Δ : UCtx m} (h : FullStep H t H' t' Γ Δ) : n ≤ m := by
  induction h with
  | base h => exact h.le
  | _ => omega

lemma FullSteps.le {n m : ℕ} {H : Heap n} {t : Term n} {H' : Heap m} {t' : Term m} {Γ : BCtx m}
    {Δ : UCtx m} (h : FullSteps H t H' t' Γ Δ) : n ≤ m := by
  induction h with
  | refl => exact le_refl _
  | ext h _ ih => exact h.le.trans ih

lemma Step.not_bang {n m : ℕ} {H : Heap n} {t : Term n} {H' : Heap m} {t' : Term m}
    {Γ : BCtx m} {Δ : UCtx m} (h : Step H (bang t) H' t' Γ Δ) : False := by
  cases h

lemma FullStep.not_unit {n m : ℕ} {H : Heap n} {H' : Heap m} {t' : Term m}
    {Γ : BCtx m} {Δ : UCtx m} (h : FullStep H unit H' t' Γ Δ) : False := by
  cases h with
  | base h => cases h

lemma FullStep.not_bang_unit {n m : ℕ} {H : Heap n} {H' : Heap m} {t' : Term m}
    {Γ : BCtx m} {Δ : UCtx m} (h : FullStep H (Term.bang Term.unit) H' t' Γ Δ) : False := by
  cases h with
  | base h => exact h.not_bang
  | bang h => exact h.not_unit

lemma FullSteps.bang_unit_scope {n m : ℕ} {H : Heap n} {H' : Heap m} {v : Term m}
    {Γ : BCtx m} {Δ : UCtx m} (h : FullSteps H (bang unit) H' v Γ Δ) : n = m := by
  cases h with
  | refl => rfl
  | ext h _ => exact h.not_bang_unit.elim

namespace EqSoundnessCounterexample

/-- `let! x = !unit in !x` -/
def lhs : Term 0 := letBang (bang unit) (bang (var 0))

/-- `!unit` -/
def rhs : Term 0 := bang unit

lemma lhs_typed : HasType Ctx.empty lhs (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  exact .bangE (.bangI Ctx.AllNonLin.empty (.unitI Ctx.AllNonLin.empty))
    (.bangI (Ctx.AllNonLin.cons Ctx.AllNonLin.empty (nonLin_nonlin _))
      (HasTypeD.var_zero_single (.nonlin .unit))) (Ctx.Add.empty_right _)

lemma rhs_typed : HasType Ctx.empty rhs (.bang .unit) :=
  .bangI Ctx.AllNonLin.empty (.unitI Ctx.AllNonLin.empty)

lemma lhs_equiv_rhs : lhs ≡ₗ rhs := .ax (.etaBang _)

lemma lhs_step_scope {m : ℕ} {H : Heap 0} {H' : Heap m} {t' : Term m} {Γ : BCtx m}
    {Δ : UCtx m} (h : FullStep H lhs H' t' Γ Δ) : m = 1 := by
  cases h with
  | base h =>
    cases h with
    | letBang _ h => exact h.not_bang.elim
    | betaBang _ _ => rfl
  | letBang _ h => exact h.not_bang_unit.elim

lemma lhs_reducible (H : Heap 0) : ¬ Irreducible H lhs := by
  intro hirr
  exact hirr ⟨_, _, _, _, _, FullStep.base (Step.betaBang (Γ := Ctx.empty) (A := .unit)
    Ctx.AllNonLin.empty (HasType.unitI Ctx.AllNonLin.empty))⟩

end EqSoundnessCounterexample

open EqSoundnessCounterexample in
/-- **Theorem 7 (Soundness with respect to the equational theory) is false as stated.** -/
theorem not_eqSoundness : ¬ EqSoundness := by
  intro hS
  obtain ⟨m, H', v, Γ₁, Γ₂, Δ₁, Δ₂, hirr, h₁, h₂⟩ :=
    hS Ctx.empty lhs rhs _ lhs_typed rhs_typed lhs_equiv_rhs Heap.empty Compat.empty
  have hm := h₂.bang_unit_scope
  subst hm
  cases h₁ with
  | refl => exact lhs_reducible _ hirr
  | ext h hs =>
    have := lhs_step_scope h
    subst this
    exact absurd hs.le (by omega)

end LCU
