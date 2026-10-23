module
public import RequestProject.LCU.Sec3_5_Metatheory.Metatheory

/-!
# Theorem 4 (Conservation) does not hold as stated

Counterexample: the closed, well-typed term
```
copy !((λz. z) unit) as x in &x   :   !1
```
in the empty heap.  By `copy_!` (evaluation under `!`) and `β`, it reduces to
```
z ↦₁ (∅ ⊢ unit : 1)  ⊢  copy !z as x in &x
```
The new heap binding `z ↦₁ unit` forces `z` to be a *linear* assumption in any
context compatible with the heap, but the reduct `copy !z as x in &x` can only be
typed if `z` is non-linear (`!z` requires all assumptions to be non-linear).  Hence
there is no `Γ'` as demanded by Theorem 4.
-/

@[expose] public section

namespace LCU

open Term

namespace ConservationCounterexample

/-! ## The program, its type and its first step -/

/-- `copy !((λz. z) unit) as x in &x` -/
def prog : Term 0 0 := copy (bang (app (lam (var 0)) unit)) (borrow (var 0))

/-- The reduct `copy !z as x in &x` (with `z` the new variable `0`). -/
def prog' : Term 1 0 := copy (bang (var 0)) (borrow (var 0))

/-- The program has type `!1` in the empty context. -/
lemma prog_typed : HasType TCtx.empty prog (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  have hid : HasTypeD (TCtx.empty : TCtx 0 0) (app (lam (var 0)) unit) .unit :=
    .app (.abs (HasTypeD.var_zero_single (.lin .unit))) (.unitI TCtx.AllNonLin.empty)
      (TCtx.Add.empty_left _)
  exact .copy (.bangI TCtx.AllNonLin.empty hid)
    (.borrow (HasTypeD.var_zero_single (.lin (.star .unit)))) (TCtx.Add.empty_left _)

/-- The heap entry `z ↦₁ (∅ ⊢ unit : 1)`. -/
def e₀ : VarEntry 0 0 := ⟨.one, TCtx.empty, unit, .unit, HasType.unitI TCtx.AllNonLin.empty⟩

/-- The heap after the reduction. -/
def H₁ : Heap 1 0 := (Heap.empty : Heap 0 0).push e₀

/-- The first step: `β` under `!` (rule `copy_!`) binds `z ↦₁ unit`. -/
lemma step : Step (Heap.empty : Heap 0 0) prog 1 0 H₁ prog' (BCtx.new1 (.lin .unit))
    UCtx.empty :=
  Step.copyBang (t₂ := borrow (var 0))
    (Step.beta (H := (Heap.empty : Heap 0 0)) (t := var 0) (Γ := TCtx.empty) (A := .unit)
      (HasType.unitI TCtx.AllNonLin.empty))

/-! ## Compatibility with the new heap forces `z` to be linear -/

/-- A heap with a single linear-use binding `x ↦₁ t` is compatible only with contexts
in which `x` is a linear assumption. -/
lemma compat_single {n ρ : ℕ} {H : Heap n ρ} {Γ : TCtx n ρ} (hc : Compat H Γ) {x : Var n}
    {e : VarEntry n ρ} (hx : H.vars.get x = some e) (hr : e.r = .one)
    (hv : ∀ y, y ≠ x → H.vars.get y = none) (ha : ∀ a, H.arrs.get a = none) :
    Γ.vars.get x = some (.lin e.ty) := by
  cases hc with
  | empty => simp at hx
  | @ref _ _ a _ _ _ _ => have := ha a; simp at this
  | @lin _ _ _ x' e' _ _ _ =>
    by_cases hxx : x' = x
    · subst hxx
      simp only [Heap.setVar_vars, Ctx.get_set_same, Option.some.injEq] at hx
      subst hx
      simp
    · have := hv x' hxx; simp at this
  | @omega _ _ _ _ x' _ _ _ _ _ _ _ =>
    by_cases hxx : x' = x
    · subst hxx
      simp only [Heap.setVar_vars, Ctx.get_set_same, Option.some.injEq] at hx
      subst hx
      cases hr
    · have := hv x' hxx; simp at this

/-- Any typing of the reduct uses only non-linear assumptions. -/
lemma prog'_typing_nonLin {Γ : TCtx 1 0} {A : Ty} (ht : HasType Γ prog' A) :
    NonLin (Γ.vars.get .zero) := by
  rw [hasType_iff_hasTypeD] at ht
  cases ht with
  | copy h₁ h₂ hadd =>
    cases h₁ with
    | bangI hΓa _ =>
      cases h₂ with
      | borrow h₂ =>
        obtain ⟨_, hpick, _, _⟩ := h₂.var_inv
        have := hpick.other (j := .succ .zero) (Var.succ_ne_zero _)
        exact (hadd.vars.get .zero).nonLin_of (hΓa.vars.get _) this

end ConservationCounterexample

/-! ## The disproof -/

open ConservationCounterexample in
/-- **Theorem 4 (Conservation) is false as stated.** -/
theorem not_conservation : ¬ Conservation := by
  intro hC
  obtain ⟨Γ', Γs', ht, hadd, hc, -⟩ := hC TCtx.empty prog (.bang .unit) prog_typed TCtx.empty
    TCtx.empty Heap.empty (TCtx.Add.empty_left _) Compat.empty _ _ _ _ _ _ step
  have h1 : Γs'.vars.get .zero = some (.lin .unit) :=
    compat_single hc (x := .zero) (e := e₀.lift 1 0) rfl rfl
      (fun y hy => by cases y with | zero => exact absurd rfl hy | succ y => exact y.elim0)
      (fun a => a.elim0)
  have h2 : Γ'.vars.get .zero = Γs'.vars.get .zero := (hadd.vars.get .zero).left_none
  have h3 := prog'_typing_nonLin ht
  rw [h2, h1] at h3
  exact h3.elim

end LCU
