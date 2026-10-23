module
public import RequestProject.LCU.Ext2_MutableArrays.ArraySemantics

/-!
# Subject reduction for the store-based array semantics

This file proves that `AStep` (defined in `ArraySemantics.lean`) preserves typing of
configurations.  A step allocating `e` new references (the reference allocated by
`newArray`, or the copies made by `copy_β`) extends the typing context accordingly: the
new context is a renaming `TCtx.RenRefs (Var.shiftN e)` of the old one.

## Main results

* `AStep.preserves`: if `ConfOK σ Γ`, `Γ ⊢ t : A` and `σ ⊢ t ⟶ σ' ⊢ t'`, then there
  is `Γ'` extending `Γ` with `ConfOK σ' Γ'` and `Γ' ⊢ t' : A`.

## Proof outline

1. Inversion lemmas for applications, primitives, `*t` and references in contexts
   whose assumptions are all non-linear (`HasTypeD.inv_app`, ...).
2. The main induction on the step: the rules shared with `CbnStep` reuse the
   call-by-name subject reduction (`preserves_cbn`); in the congruence rules the other
   subterms are transported along the renaming of references (`HasTypeD.renameRefs`);
   the array rules are checked one by one.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Inversion lemmas in non-linear contexts -/

section Inversion

variable {n ρ : ℕ} {Γ : TCtx n ρ}

/-- Inversion for applications in a non-linear context: the function and the
argument are typed in the same context. -/
lemma HasTypeD.inv_app (hΓ : Γ.AllNonLin) {f x : Term n ρ} {B : Ty}
    (ht : HasTypeD Γ (Term.app f x) B) : ∃ A, HasTypeD Γ f (A ⊸ B) ∧ HasTypeD Γ x A := by
  cases ht with
  | app h₁ h₂ hadd => exact ⟨_, h₁.weaken_left hΓ hadd, h₂.weaken_right hΓ hadd⟩

/-- Typing an application in a non-linear context (both parts share the context). -/
lemma HasTypeD.app_of (hΓ : Γ.AllNonLin) {f x : Term n ρ} {A B : Ty}
    (h₁ : HasTypeD Γ f (A ⊸ B)) (h₂ : HasTypeD Γ x A) : HasTypeD Γ (Term.app f x) B :=
  .app h₁ h₂ (TCtx.Add.idem hΓ)

/-- A primitive has its declared type. -/
lemma HasTypeD.inv_prim {p : Prim} {T : Ty} (ht : HasTypeD Γ (Term.prim p) T) : T = p.ty := by
  cases ht; rfl

/-- Inversion for `*s` in a context without variables. -/
lemma HasTypeD.inv_star (hΓ : Γ.NoVars) {s : Term n ρ} {T : Ty}
    (ht : HasTypeD Γ (Term.star s) T) : ∃ A, T = .star A ∧ HasTypeD Γ s A := by
  cases ht with
  | nec h _ => rw [hΓ.refsOnly_eq] at h; exact ⟨_, rfl, h⟩

/-- Typing `*s` in a context without variables. -/
lemma HasTypeD.star_of (hΓ : Γ.NoVars) {s : Term n ρ} {A : Ty} (ht : HasTypeD Γ s A) :
    HasTypeD Γ (Term.star s) (.star A) :=
  .nec (by rw [hΓ.refsOnly_eq]; exact ht)
    (show Ctx.All _ _ by rw [show Γ.vars = _ from hΓ]; exact TCtx.allNonLin_replicate _)

/-- Inversion for array references. -/
lemma HasTypeD.inv_ref {a : Var ρ} {T : Ty} (ht : HasTypeD Γ (Term.ref a) T) :
    ∃ h, Γ.refs.get a = some h ∧ T = h.ty.toTy := by
  cases ht with
  | ref ha _ => exact ⟨_, ha.get, rfl⟩

end Inversion

/-! ## Subject reduction -/

/-- Typing a reduct of a `CbnStep`-rule in the same context. -/
private lemma preserves_cbn {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} {t t' : Term n ρ} {A : Ty}
    (hc : CbnStep t t') (hΓ : ConfOK σ Γ) (ht : HasTypeD Γ t A) :
    ∃ Γ' : TCtx n (ρ + 0), Γ.RenRefs (Var.shiftN 0) Γ' ∧ ConfOK σ Γ' ∧ HasTypeD Γ' t' A :=
  ⟨Γ, TCtx.renRefs_shiftN_zero Γ, hΓ, hasType_iff_hasTypeD.1
    (hc.preserves hΓ.noVars hΓ.refsNonLin (hasType_iff_hasTypeD.2 ht))⟩

/-- **Subject reduction** for the store-based semantics: a reduction step of a term that
is well-typed in a context compatible with the store yields a term of the same type, in
an extended context (with hypotheses for the new references) compatible with the new
store. -/
theorem AStep.preserves {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ}
    {t' : Term n (ρ + e)} (hs : AStep σ t e σ' t') {Γ : TCtx n ρ} {A : Ty} (hΓ : ConfOK σ Γ)
    (ht : HasTypeD Γ t A) :
    ∃ Γ' : TCtx n (ρ + e), Γ.RenRefs (Var.shiftN e) Γ' ∧ ConfOK σ' Γ' ∧ HasTypeD Γ' t' A := by
  induction hs generalizing Γ A with
  | betaLolli | betaTensor | betaUnit | betaBang | betaBorrow =>
    exact preserves_cbn (by constructor) hΓ ht
  | betaCopy σ u t =>
    cases ht with
    | copy h₁ h₂ hadd =>
      cases h₁ with
      | bangI _ hu =>
        have hall := hΓ.allNonLin
        have hold := TCtx.renRefs_copyAll_old hΓ.refsNonLin
        have hnew := TCtx.renRefs_copyAll_new hΓ.refsNonLin
        have hΓ' : ConfOK σ.copyAll Γ.copyAll := by
          refine ⟨hΓ.noVars, hΓ.refsNonLin.append hΓ.refsNonLin, fun x h e => ?_⟩
          rcases Var.lowAdd_or_shiftN x with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · simp only [TCtx.copyAll_refs, Ctx.get_append_lowAdd] at e
            simpa [Store.copyAll] using hΓ.alloc i h e
          · simp only [TCtx.copyAll_refs, Ctx.get_append_shiftN] at e
            simpa [Store.copyAll] using hΓ.alloc i h e
        have hu' := (hu.weaken_left hall hadd).renameRefs hnew
        have hb := (h₂.weaken_right_cons hall hadd).renameRefs (hold.cons _)
        refine ⟨Γ.copyAll, hold, hΓ', ?_⟩
        exact hasType_iff_hasTypeD.1 (HasType.subst_lin
          (hasType_iff_hasTypeD.2 (HasTypeD.star_of hΓ'.noVars hu'))
          (hasType_iff_hasTypeD.2 hb) (TCtx.Add.idem hΓ'.allNonLin))
  | app u _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hren, hΓ', h₁'⟩ := ih hΓ h₁
    exact ⟨Γ', hren, hΓ', .app_of hΓ'.allNonLin h₁' (h₂.renameRefs hren)⟩
  | letPair u _ ih =>
    cases ht with
    | tensorE h₁ h₂ hadd =>
      obtain ⟨Γ', hren, hΓ', h₁'⟩ := ih hΓ (h₁.weaken_left hΓ.allNonLin hadd)
      exact ⟨Γ', hren, hΓ', .tensorE h₁'
        ((h₂.weaken_right_cons₂ hΓ.allNonLin hadd).renameRefs ((hren.cons _).cons _))
        (TCtx.Add.idem hΓ'.allNonLin)⟩
  | letUnit u _ ih =>
    cases ht with
    | unitE h₁ h₂ hadd =>
      obtain ⟨Γ', hren, hΓ', h₁'⟩ := ih hΓ (h₁.weaken_left hΓ.allNonLin hadd)
      exact ⟨Γ', hren, hΓ', .unitE h₁' ((h₂.weaken_right hΓ.allNonLin hadd).renameRefs hren)
        (TCtx.Add.idem hΓ'.allNonLin)⟩
  | letBang u _ ih =>
    cases ht with
    | bangE h₁ h₂ hadd =>
      obtain ⟨Γ', hren, hΓ', h₁'⟩ := ih hΓ (h₁.weaken_left hΓ.allNonLin hadd)
      exact ⟨Γ', hren, hΓ', .bangE h₁'
        ((h₂.weaken_right_cons hΓ.allNonLin hadd).renameRefs (hren.cons _))
        (TCtx.Add.idem hΓ'.allNonLin)⟩
  | borrow _ ih =>
    cases ht with
    | borrow h =>
      obtain ⟨Γ', hren, hΓ', h'⟩ := ih hΓ h
      exact ⟨Γ', hren, hΓ', .borrow h'⟩
  | copy u _ ih =>
    cases ht with
    | copy h₁ h₂ hadd =>
      obtain ⟨Γ', hren, hΓ', h₁'⟩ := ih hΓ (h₁.weaken_left hΓ.allNonLin hadd)
      exact ⟨Γ', hren, hΓ', .copy h₁'
        ((h₂.weaken_right_cons hΓ.allNonLin hadd).renameRefs (hren.cons _))
        (TCtx.Add.idem hΓ'.allNonLin)⟩
  | primArg _ _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hren, hΓ', h₂'⟩ := ih hΓ h₂
    exact ⟨Γ', hren, hΓ', .app_of hΓ'.allNonLin (h₁.renameRefs hren) h₂'⟩
  | primStar p _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, rfl, hs⟩ := h₂.inv_star hΓ.noVars
    obtain ⟨Γ', hren, hΓ', hs'⟩ := ih hΓ hs
    exact ⟨Γ', hren, hΓ', .app_of hΓ'.allNonLin (h₁.renameRefs hren)
      (.star_of hΓ'.noVars hs')⟩
  | newArray σ k =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨⟨Γ.refs ,, some (.nonlin (.array .float)), Γ.vars⟩,
      TCtx.renRefs_succ Γ (.nonlin _), ⟨hΓ.noVars, .snoc hΓ.refsNonLin (.nonlin _), ?_⟩, ?_⟩
    · intro x h e
      cases x with
      | zero => simp
      | succ x => exact hΓ.alloc x h e
    · exact .nec (.ref (h := .nonlin (.array .float)) (.here hΓ.refsNonLin)
        (TCtx.allNonLin_replicate _))
        (show Ctx.All _ _ by rw [show Γ.vars = _ from hΓ.noVars]; exact TCtx.allNonLin_replicate _)
  | readArray σ a k arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, h₄⟩ := h₁.inv_app hΓ.allNonLin
    have e := h₃.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨Γ, TCtx.renRefs_shiftN_zero Γ, hΓ, .tensorI (.floatI hΓ.allNonLin) h₄
      (TCtx.Add.idem hΓ.allNonLin)⟩
  | writeArray σ a k x arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ.allNonLin
    obtain ⟨D, h₅, h₆⟩ := h₃.inv_app hΓ.allNonLin
    have e := h₅.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    refine ⟨Γ, TCtx.renRefs_shiftN_zero Γ, ⟨hΓ.noVars, hΓ.refsNonLin, fun b h e => ?_⟩, h₆⟩
    by_cases hb : b = a
    · subst hb; simp
    · rw [Ctx.get_set_ne _ _ hb]; exact hΓ.alloc b h e
  | deleteArray σ a =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨Γ, TCtx.renRefs_shiftN_zero Γ, hΓ, .unitI hΓ.allNonLin⟩

end LCU
