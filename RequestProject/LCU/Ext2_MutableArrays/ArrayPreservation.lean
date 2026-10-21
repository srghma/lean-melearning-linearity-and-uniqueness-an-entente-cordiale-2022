module
public import RequestProject.LCU.Ext2_MutableArrays.ArraySemantics

/-!
# Subject reduction for the store-based array semantics

This file proves that `AStep` (defined in `ArraySemantics.lean`) preserves typing of
configurations.  A step may extend the typing context (for example with the fresh
reference allocated by `newArray`, or with the fresh copies made by `copy_β`); this is
expressed with the context inclusion `Ctx.Sub` of `RefShift.lean`.

## Main results

* `AStep.preserves`: if `ConfOK σ Γ`, `Γ ⊢ t : A` and `σ ⊢ t ⟶ σ' ⊢ t'`, then there
  is `Γ' ⊇ Γ` with `ConfOK σ' Γ'` and `Γ' ⊢ t' : A`.

## Proof outline

1. Inversion lemmas for applications, primitives, `*t` and references in contexts
   whose assumptions are all non-linear (`HasTypeD.inv_app`, ...).
2. Allocation only grows along a step (`AStep.alloc_mono`), so a compatible context
   stays compatible with the new store (`ConfOK.mono_store`).
3. The main induction on the step: the rules shared with `CbnStep` reuse the
   call-by-name subject reduction (`preserves_cbn`); the array rules are checked
   one by one.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Inversion lemmas in non-linear contexts -/

section Inversion

variable {n : ℕ} {Γ : Ctx n}

/-- Inversion for applications in a non-linear context: the function and the
argument are typed in the same context. -/
lemma HasTypeD.inv_app (hΓ : Γ.AllNonLin) {f x : Term n} {B : Ty}
    (ht : HasTypeD Γ (Term.app f x) B) : ∃ A, HasTypeD Γ f (A ⊸ B) ∧ HasTypeD Γ x A := by
  cases ht with
  | app h₁ h₂ hadd =>
    exact ⟨_, h₁.mono (Ctx.Sub.of_add_left hadd) hΓ, h₂.mono (Ctx.Sub.of_add_right hadd) hΓ⟩

/-- Typing an application in a non-linear context (both parts share the context). -/
lemma HasTypeD.app_of (hΓ : Γ.AllNonLin) {f x : Term n} {A B : Ty}
    (h₁ : HasTypeD Γ f (A ⊸ B)) (h₂ : HasTypeD Γ x A) : HasTypeD Γ (Term.app f x) B :=
  .app h₁ h₂ (Ctx.Add.idem hΓ)

/-- A primitive has its declared type. -/
lemma HasTypeD.inv_prim {p : Prim} {T : Ty} (ht : HasTypeD Γ (Term.prim p) T) : T = p.ty := by
  cases ht; rfl

/-- Inversion for `*s` in a context without variables. -/
lemma HasTypeD.inv_star (hΓ : Γ.NoVars) {s : Term n} {T : Ty} (ht : HasTypeD Γ (Term.star s) T) :
    ∃ A, T = .star A ∧ HasTypeD Γ s A := by
  cases ht with
  | nec h _ => rw [hΓ.refsOnly_eq] at h; exact ⟨_, rfl, h⟩

/-- Typing `*s` in a context without variables. -/
lemma HasTypeD.star_of (hΓ : Γ.NoVars) {s : Term n} {A : Ty} (ht : HasTypeD Γ s A) :
    HasTypeD Γ (Term.star s) (.star A) :=
  .nec (by rw [hΓ.refsOnly_eq]; exact ht) (fun i => by rw [hΓ i]; trivial)

/-- Inversion for array references. -/
lemma HasTypeD.inv_ref {a : ℕ} {T : Ty} (ht : HasTypeD Γ (Term.ref a) T) :
    ∃ h, Γ (.inr a) = some h ∧ T = .array h.ty := by
  cases ht with
  | ref ha _ => exact ⟨_, ha, rfl⟩

end Inversion

/-! ## Subject reduction -/

/-- After copying all references `< N` to `N + ·`, everything from `2N` is fresh. -/
lemma Store.FreshFrom.copyShift {σ : Store} {N : ℕ} (h : σ.FreshFrom N) :
    (σ.copyShift N).FreshFrom (N + N) := by
  intro b hb
  simp only [Store.copyShift_apply, show N ≤ b by omega, if_true]
  exact h _ (by omega)

/-- Reduction never deallocates arrays. -/
lemma AStep.alloc_mono {n : ℕ} {σ σ' : Store} {t t' : Term n} (hs : AStep σ t σ' t') :
    ∀ a, σ a ≠ none → σ' a ≠ none := by
  induction hs with
  | betaCopy N u t hN =>
    intro a ha
    simp only [Store.copyShift_apply]
    split_ifs with h
    · exact absurd (hN a h) ha
    · exact ha
  | newArray k b hb =>
    intro a ha
    by_cases hab : a = b
    · subst hab; simp
    · rw [Store.set_apply, Function.update_of_ne hab]; exact ha
  | writeArray b k x arr hb =>
    intro a ha
    by_cases hab : a = b
    · subst hab; simp
    · rw [Store.set_apply, Function.update_of_ne hab]; exact ha
  | app _ _ ih | letPair _ _ ih | letUnit _ _ ih | letBang _ _ ih | borrow _ ih | copy _ _ ih
  | primArg _ _ ih | primStar _ _ ih => exact ih
  | _ => exact fun _ h => h

/-- Compatibility is preserved when the store allocates more references. -/
lemma ConfOK.mono_store {n : ℕ} {σ σ' : Store} {Γ : Ctx n} (h : ConfOK σ Γ)
    (hm : ∀ a, σ a ≠ none → σ' a ≠ none) : ConfOK σ' Γ :=
  ⟨h.noVars, h.refsNonLin, fun a h' ha => hm a (h.alloc a h' ha)⟩

/-- Typing a primitive-free reduct of a `CbnStep`-rule in the same context. -/
private lemma preserves_cbn {n : ℕ} {σ : Store} {Γ : Ctx n} {t t' : Term n} {A : Ty}
    (hc : CbnStep t t') (hΓ : ConfOK σ Γ) (ht : HasTypeD Γ t A) :
    ∃ Γ', Γ.Sub Γ' ∧ ConfOK σ Γ' ∧ HasTypeD Γ' t' A :=
  ⟨Γ, Ctx.Sub.refl Γ, hΓ, hasType_iff_hasTypeD.1
    (hc.preserves hΓ.noVars hΓ.refsNonLin (hasType_iff_hasTypeD.2 ht))⟩

/-- The context extension for a freshly allocated array. -/
private lemma newArray_ctx {n : ℕ} {σ : Store} {Γ : Ctx n} (hΓ : ConfOK σ Γ) {a : ℕ}
    (ha : σ a = none) (arr : ℕ → Float) :
    Γ.Sub (Γ.set (.inr a) (some (.nonlin .float))) ∧
    ConfOK (σ.set a (some arr)) (Γ.set (.inr a) (some (.nonlin .float))) ∧
    HasTypeD (Γ.set (.inr a) (some (.nonlin .float))) (Term.star (Term.ref a))
      (.star (.array .float)) := by
  have hfresh := hΓ.not_alloc ha
  have hsub : Γ.Sub (Γ.set (.inr a) (some (.nonlin .float))) := by
    intro x h e
    by_cases hx : x = .inr a
    · subst hx; rw [hfresh] at e; cases e
    · rw [Ctx.set_ne _ _ hx]; exact e
  have hΓ' : ConfOK (σ.set a (some arr)) (Γ.set (.inr a) (some (.nonlin .float))) := by
    refine ⟨fun i => by rw [Ctx.set_ne _ _ (by simp)]; exact hΓ.noVars i, fun b => ?_,
      fun b h e => ?_⟩
    · by_cases hb : b = a
      · subst hb; simp
      · rw [Ctx.set_ne _ _ (by simpa using hb)]; exact hΓ.refsNonLin b
    · by_cases hb : b = a
      · subst hb; simp
      · rw [Store.set_apply, Function.update_of_ne hb]
        rw [Ctx.set_ne _ _ (by simpa using hb)] at e
        exact hΓ.alloc b h e
  refine ⟨hsub, hΓ', HasTypeD.star_of hΓ'.noVars ?_⟩
  refine HasTypeD.ref (h := .nonlin .float) (by simp) ?_
  rw [Ctx.set_set]
  exact hΓ.allNonLin.set _ trivial

/-- **Subject reduction** for the store-based semantics: a reduction step of a term that
is well-typed in a context compatible with the store yields a term of the same type, in
a (possibly larger) context compatible with the new store. -/
theorem AStep.preserves {n : ℕ} {σ σ' : Store} {t t' : Term n} (hs : AStep σ t σ' t')
    {Γ : Ctx n} {A : Ty} (hΓ : ConfOK σ Γ) (ht : HasTypeD Γ t A) :
    ∃ Γ', Γ.Sub Γ' ∧ ConfOK σ' Γ' ∧ HasTypeD Γ' t' A := by
  induction hs generalizing Γ A with
  | betaLolli | betaTensor | betaUnit | betaBang | betaBorrow =>
    exact preserves_cbn (by constructor) hΓ ht
  | betaCopy N u t hN =>
    cases ht with
    | copy h₁ h₂ hadd =>
      cases h₁ with
      | bangI _ hu =>
        -- the new context: copies of all references at `N + a`
        let Γ' : Ctx n := Sum.elim (fun i => Γ (.inl i))
          (fun b => if N ≤ b then Γ (.inr (b - N)) else Γ (.inr b))
        have hfresh : ∀ b, N ≤ b → Γ (.inr b) = none := fun b hb => hΓ.not_alloc (hN b hb)
        have hsub : Γ.Sub Γ' := by
          rintro (i | b) h e
          · exact e
          · simp only [Γ', Sum.elim_inr]
            split_ifs with hb
            · rw [hfresh b hb] at e; cases e
            · exact e
        have hΓ' : ConfOK (σ.copyShift N) Γ' := by
          refine ⟨fun i => hΓ.noVars i, fun b => ?_, fun b h e => ?_⟩
          · simp only [Γ', Sum.elim_inr]; split_ifs <;> exact hΓ.refsNonLin _
          · simp only [Γ', Sum.elim_inr] at e
            simp only [Store.copyShift_apply]
            split_ifs at e ⊢ <;> exact hΓ.alloc _ _ e
        have hall := hΓ'.allNonLin
        have hshift : Ctx.RefShift N Γ Γ' :=
          { vars := fun i => rfl
            map := fun a => by simp [Γ']
            low := fun b hb => by
              simp only [Γ', Sum.elim_inr, not_le.2 hb, if_false]; exact hΓ.refsNonLin b }
        have hu' : HasTypeD Γ' (u.shiftRefs N) _ :=
          (hu.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin).shiftRefs hshift
        have hb := h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hall
        refine ⟨Γ', hsub, hΓ', ?_⟩
        exact hasType_iff_hasTypeD.1 (HasType.subst_lin
          (hasType_iff_hasTypeD.2 (HasTypeD.star_of hΓ'.noVars hu'))
          (hasType_iff_hasTypeD.2 hb) (Ctx.Add.idem hall))
  | app u _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ h₁
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin h₁' (h₂.mono hsub hΓ'.allNonLin)⟩
  | letPair u _ ih =>
    cases ht with
    | tensorE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .tensorE h₁'
        (h₂.mono_cons₂ ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | letUnit u _ ih =>
    cases ht with
    | unitE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .unitE h₁'
        (h₂.mono ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | letBang u _ ih =>
    cases ht with
    | bangE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .bangE h₁'
        (h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | borrow _ ih =>
    cases ht with
    | borrow h =>
      obtain ⟨Γ', hsub, hΓ', h'⟩ := ih hΓ h
      exact ⟨Γ', hsub, hΓ', .borrow h'⟩
  | copy u _ ih =>
    cases ht with
    | copy h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .copy h₁'
        (h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | primArg _ _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hsub, hΓ', h₂'⟩ := ih hΓ h₂
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin (h₁.mono hsub hΓ'.allNonLin) h₂'⟩
  | primStar p _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, rfl, hs⟩ := h₂.inv_star hΓ.noVars
    obtain ⟨Γ', hsub, hΓ', hs'⟩ := ih hΓ hs
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin (h₁.mono hsub hΓ'.allNonLin)
      (.star_of hΓ'.noVars hs')⟩
  | newArray k a ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h₁, h₂, h₃⟩ := newArray_ctx hΓ ha (fun _ => 0)
    exact ⟨_, h₁, h₂, h₃⟩
  | readArray a k arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, h₄⟩ := h₁.inv_app hΓ.allNonLin
    have e := h₃.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ, .tensorI (.floatI hΓ.allNonLin) h₄
      (Ctx.Add.idem hΓ.allNonLin)⟩
  | writeArray a k x arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ.allNonLin
    obtain ⟨D, h₅, h₆⟩ := h₃.inv_app hΓ.allNonLin
    have e := h₅.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ.mono_store (AStep.writeArray (n := n) σ a k x arr ha).alloc_mono,
      h₆⟩
  | deleteArray a =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ, .unitI hΓ.allNonLin⟩

end LCU
