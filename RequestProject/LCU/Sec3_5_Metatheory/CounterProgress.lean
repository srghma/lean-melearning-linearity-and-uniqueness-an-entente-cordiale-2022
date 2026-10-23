module
public import RequestProject.LCU.Sec3_5_Metatheory.Metatheory

/-!
# Theorem 6 (Progress) does not hold as stated

Counterexample: the closed, well-typed term
```
&(*((λz. z) unit))   :   !1
```
is not a value, but no reduction applies to it in the empty heap: the text gives
exactly two rules for borrowing — the congruence `&`, which would need `*((λz. z) unit)`
to reduce (but `*t` is a value and there is no rule reducing under `*`), and `&β`,
which requires the borrowed term to be of the form `*v` for a *value* `v`, whereas
`(λz. z) unit` is not a value.
-/

@[expose] public section

namespace LCU

open Term

namespace ProgressCounterexample

/-! ## The stuck program -/

/-- `&(*((λz. z) unit))` -/
def prog : Term 0 0 := borrow (star (app (lam (var 0)) unit))

/-- The program has type `!1` in the empty context. -/
lemma prog_typed : HasType TCtx.empty prog (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  exact .borrow (.nec (.app (.abs (HasTypeD.var_zero_single (.lin .unit)))
    (.unitI TCtx.AllNonLin.empty) (TCtx.Add.empty_left _)) (TCtx.allNonLin_replicate _))

/-- The program is not a value: `&t` is never a value. -/
lemma prog_not_value : ¬ IsValue prog := not_isValue_borrow _

/-- No heap rule applies to the program, in any heap. -/
lemma prog_stuck {d e : ℕ} (H : Heap 0 0) (H' : Heap (0 + d) (0 + e))
    (t' : Term (0 + d) (0 + e)) (Γ : BCtx (0 + d)) (Δ : UCtx (0 + d)) :
    ¬ Step H prog d e H' t' Γ Δ := by
  intro h
  cases h with
  | borrow h => cases h
  | betaBorrow hv _ => exact not_isValue_app_lam _ _ hv

end ProgressCounterexample

/-! ## The disproof -/

open ProgressCounterexample in
/-- **Theorem 6 (Progress) is false as stated.** -/
theorem not_progress : ¬ Progress := by
  intro hP
  rcases hP TCtx.empty prog _ prog_typed with hv | hstep
  · exact prog_not_value hv
  · obtain ⟨d, e, H', t', Γ', Δ, h⟩ := hstep TCtx.empty TCtx.empty Heap.empty
      (TCtx.Add.empty_left _) Compat.empty
    exact prog_stuck _ _ _ _ _ h

end LCU
