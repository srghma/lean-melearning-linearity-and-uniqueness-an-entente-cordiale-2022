module
public import RequestProject.LCU.CounterUniqueness

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

/-- `copy !((λz. z) unit) as x in &x` -/
def prog : Term 0 := copy (bang (app (lam (var 0)) unit)) (borrow (var 0))

/-- The reduct `copy !z as x in &x` (with `z` the new variable `0`). -/
def prog' : Term 1 := copy (bang (var 0)) (borrow (var 0))

lemma prog_typed : HasType Ctx.empty prog (.bang .unit) := by
  rw [hasType_iff_hasTypeD]
  have hid : HasTypeD (Ctx.empty : Ctx 0) (app (lam (var 0)) unit) .unit :=
    .app (.abs (HasTypeD.var_zero_single (.lin .unit))) (.unitI Ctx.AllNonLin.empty)
      (Ctx.Add.empty_left _)
  exact .copy (.bangI Ctx.AllNonLin.empty hid)
    (.borrow (HasTypeD.var_zero_single (.lin (.star .unit)))) (Ctx.Add.empty_left _)

/-- The heap after the reduction. -/
def H₁ : Heap 1 := (Heap.empty : Heap 0).push ⟨.one, Ctx.empty, unit, .unit⟩

lemma step : Step (Heap.empty : Heap 0) prog H₁ prog' (BCtx.single (Fin.last 0) (.lin .unit))
    UCtx.empty := by
  have := Step.copyBang (t₂ := borrow (var 0)) (Nat.zero_le 1)
    (Step.beta (H := (Heap.empty : Heap 0)) (t := var 0) (Γ := Ctx.empty) (A := .unit)
      (HasType.unitI Ctx.AllNonLin.empty))
  exact this

/-- A heap without any bindings is only compatible with the empty context. -/
lemma compat_empty_heap {n : ℕ} {H : Heap n} {Γ : Ctx n} (hc : Compat H Γ)
    (hv : ∀ y, H.vars y = none) (ha : ∀ a, H.arrs a = none) : Γ = Ctx.empty := by
  cases hc with
  | empty => rfl
  | @ref _ _ a _ _ _ _ => have := ha a; simp [Heap.setArr] at this
  | @lin _ _ _ _ x' _ _ _ _ _ _ _ => have := hv x'; simp [Heap.setVar] at this
  | @omega _ _ _ _ x' _ _ _ _ _ _ _ => have := hv x'; simp [Heap.setVar] at this

/-- A heap with a single linear-use binding `x ↦₁ t` is compatible only with contexts
in which `x` is a linear assumption. -/
lemma compat_single {n : ℕ} {H : Heap n} {Γ : Ctx n} (hc : Compat H Γ) {x : Fin n}
    {e : VarEntry n} (hx : H.vars x = some e) (he : e.r = .one)
    (hv : ∀ y, y ≠ x → H.vars y = none) (ha : ∀ a, H.arrs a = none) :
    Γ (.inl x) = some (.lin e.ty) := by
  cases hc with
  | empty => simp [Heap.empty] at hx
  | @ref _ _ a _ _ _ _ => have := ha a; simp [Heap.setArr] at this
  | @lin Hp Γ₁ Γ₂ Γ₁₂ x' r t A hc' hadd _ hx' =>
    by_cases hxx : x' = x
    · subst hxx
      simp only [Heap.setVar, Function.update_self, Option.some.injEq] at hx
      subst hx
      simp
    · have := hv x' hxx; simp [Heap.setVar] at this
  | @omega Hp Γ₁ Γ₂ Γ₁₂ x' t A hc' hadd _ _ hx' =>
    by_cases hxx : x' = x
    · subst hxx
      simp only [Heap.setVar, Function.update_self, Option.some.injEq] at hx
      subst hx
      cases he
    · have := hv x' hxx; simp [Heap.setVar] at this

/-- Any typing of the reduct uses only non-linear assumptions. -/
lemma prog'_typing_nonLin {Γ : Ctx 1} {A : Ty} (ht : HasType Γ prog' A) :
    NonLin (Γ (.inl 0)) := by
  rw [hasType_iff_hasTypeD] at ht
  cases ht with
  | copy h₁ h₂ hadd =>
    cases h₁ with
    | bangI hΓa _ =>
      cases h₂ with
      | borrow h₂ =>
        obtain ⟨_, _, _, hrest⟩ := h₂.var_inv
        have := hrest (.inl (Fin.succ 0))
        rw [Ctx.set_ne _ _ (fun e => Fin.succ_ne_zero _ (Sum.inl_injective e))] at this
        exact (hadd (.inl 0)).nonLin_of (hΓa _) this

end ConservationCounterexample

open ConservationCounterexample in
/-- **Theorem 4 (Conservation) is false as stated.** -/
theorem not_conservation : ¬ Conservation := by
  intro hC
  obtain ⟨Γ', Γs', ht, hadd, hc, -⟩ := hC Ctx.empty prog (.bang .unit) prog_typed Ctx.empty
    Ctx.empty Heap.empty (Ctx.Add.empty_left _) Compat.empty _ _ _ _ step
  have h1 : Γs' (.inl 0) = some (.lin .unit) := by
    refine compat_single hc (x := 0) (e := ⟨.one, (Ctx.empty : Ctx 0).liftTo 1, unit, .unit⟩) ?_ rfl ?_ ?_
    · simp [H₁, Heap.push, Heap.setVar]; rfl
    · intro y hy; exact absurd (Subsingleton.elim y 0) hy
    · intro a; rfl
  have h2 : Γs' (.inl 0) = Γ' (.inl 0) := ((hadd (.inl 0)).left_none).symm
  have h3 := prog'_typing_nonLin ht
  rw [← h2, h1] at h3
  exact h3

end LCU
