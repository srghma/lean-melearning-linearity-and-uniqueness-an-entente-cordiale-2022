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
def prog : Term 0 := borrow (star (app (lam (var 0)) unit))

/-- The program has type `!1` in the empty context. -/
lemma prog_typed : HasType Ctx.empty prog (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  refine .borrow (.nec ?_ (fun i => i.elim0))
  have e : (Ctx.empty : Ctx 0).refsOnly = Ctx.empty := by
    funext x; rcases x with i | a <;> rfl
  rw [e]
  exact .app (.abs (HasTypeD.var_zero_single (.lin .unit))) (.unitI Ctx.AllNonLin.empty)
    (Ctx.Add.empty_left _)

/-- The program is not a value: `&t` is never a value. -/
lemma prog_not_value : ¬ IsValue prog := not_isValue_borrow _

/-- No heap rule applies to the program, in any heap. -/
lemma prog_stuck {m : ℕ} (H : Heap 0) (H' : Heap m) (t' : Term m) (Γ : BCtx m) (Δ : UCtx m) :
    ¬ Step H prog H' t' Γ Δ := by
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
  rcases hP Ctx.empty prog _ prog_typed with hv | hstep
  · exact prog_not_value hv
  · obtain ⟨m, H', t', Γ', Δ, h⟩ := hstep Ctx.empty Ctx.empty Heap.empty
      (Ctx.Add.empty_left _) Compat.empty
    exact prog_stuck _ _ _ _ _ h

end LCU
