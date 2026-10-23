module
public import RequestProject.FOFU.Sec6_3_Theorems.CounterProgress

/-!
# Theorem 6.11 (Soundness with respect to the equational theory) is false

Take `t₁ = t₂ = split (*())` (equal by reflexivity of `≡`), of type
`&_(1/2) unit ⊗ &_(1/2) unit` in the empty context, with the empty heap.  The term is
stuck (see `CounterProgress.lean`), so the only multi-step reduction from it is the
trivial one, which does not end in a value.  Hence no multi-reductions to values exist,
whatever the relation `heapEq` used for "`H'(v₁) ≡ H''(v₂)`", and for both variants of
heap compatibility.  Since the term contains no redex at all, extending the semantics to
full β-reduction does not change this.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- A multi-step reduction from `split (*())` never ends in a value. -/
theorem stuckSplit_steps_not_value {n ρ ι n' ρ' ι' : ℕ} {H : Heap R n ρ ι} {t : Term R n ρ}
    {s : R} {H' : Heap R n' ρ' ι'} {t' : Term R n' ρ'} {θr : Var ρ → Var ρ'}
    {θi : Var ι → Var ι'} (h : Steps H t s H' t' θr θi) (ht : t = stuckSplit) :
    ¬ IsValue t' := by
  induction h with
  | refl => subst ht; exact stuckSplit_not_value
  | ext h₁ _ _ => subst ht; exact absurd h₁ (stuckSplit_no_step _ _ _ _)

/-- **Theorem 6.11 is false** (for both variants of Definition 6.4 and every choice of
the relation `H'(v₁) ≡ H''(v₂)`). -/
theorem not_eqSoundness (gc : Bool)
    (heapEq : ∀ {n₁ ρ₁ ι₁ n₂ ρ₂ ι₂ : ℕ}, Heap R n₁ ρ₁ ι₁ → Term R n₁ ρ₁ →
      Heap R n₂ ρ₂ ι₂ → Term R n₂ ρ₂ → Prop) :
    ¬ EqSoundness gc heapEq := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, hv, -⟩ :=
    h TCtx.empty stuckSplit stuckSplit stuckSplitTy Heap.empty stuckSplit_typed
      stuckSplit_typed (Equiv.refl _) Compat.empty
  exact stuckSplit_steps_not_value hs rfl hv

end FOFU
