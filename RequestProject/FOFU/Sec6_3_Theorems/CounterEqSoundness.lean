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

/-- Every multi-step reduction from `split (*())` is trivial. -/
theorem stuckSplit_steps {n m : ℕ} {H : Heap R n} {s : R} {H' : Heap R m} {t' : Term R m}
    (h : Steps H stuckSplit s H' t') : ∃ e : n = m, t' = e ▸ stuckSplit := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | ext h₁ _ => exact absurd h₁ (stuckSplit_no_step _ _ _ _)

/-- **Theorem 6.11 is false** (for both variants of Definition 6.4 and every choice of
the relation `H'(v₁) ≡ H''(v₂)`). -/
theorem not_eqSoundness (gc : Bool)
    (heapEq : ∀ {m₁ m₂ : ℕ}, Heap R m₁ → Term R m₁ → Heap R m₂ → Term R m₂ → Prop) :
    ¬ EqSoundness gc heapEq := by
  intro h
  obtain ⟨m₁, H₁, v₁, -, -, -, hs, hv, -⟩ :=
    h Ctx.empty stuckSplit stuckSplit stuckSplitTy Heap.empty stuckSplit_typed stuckSplit_typed
      (Equiv.refl _) Compat.empty
  obtain ⟨rfl, rfl⟩ := stuckSplit_steps hs
  exact stuckSplit_not_value hv

end FOFU
