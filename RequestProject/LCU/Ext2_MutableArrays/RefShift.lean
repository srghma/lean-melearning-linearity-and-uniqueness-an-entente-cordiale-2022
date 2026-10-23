module
public import RequestProject.LCU.Ext1_CallByName.CbnSemantics
public import RequestProject.LCU.Sec3_1_Calculus.RefRenaming

/-!
# Copying all arrays, and weakening into non-linear contexts

Auxiliary results for the store-based semantics of `ArraySemantics.lean`:

* `TCtx.copyAll Γ`: the context for a store in which every array of `Γ` has been copied.
  The references of the scope `ρ + ρ` are the copies (`Var.lowAdd a`, the most recent
  ones) and the originals (`Var.shiftN ρ a`).  The renamings to the originals and to the
  copies are renamings of contexts (`TCtx.renRefs_copyAll_old`, `TCtx.renRefs_copyAll_new`);
  the second one is the renaming `θ` of the paper's `copy_β` rule.
* `HasTypeD.weaken_left`, … : a summand of a non-linear context can be weakened to the
  whole context.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Copying all arrays -/

namespace TCtx

variable {n ρ : ℕ}

/-- The context after copying every array reference: the copy of `a` is `Var.lowAdd a`,
the original is `Var.shiftN ρ a`; both carry the hypothesis of `a`. -/
def copyAll (Γ : TCtx n ρ) : TCtx n (ρ + ρ) := ⟨Γ.refs.append Γ.refs, Γ.vars⟩

@[simp] lemma copyAll_vars (Γ : TCtx n ρ) : Γ.copyAll.vars = Γ.vars := rfl
@[simp] lemma copyAll_refs (Γ : TCtx n ρ) : Γ.copyAll.refs = Γ.refs.append Γ.refs := rfl

/-- The originals are a renaming of contexts. -/
lemma renRefs_copyAll_old {Γ : TCtx n ρ} (hΓ : Γ.refs.All NonLin) :
    Γ.RenRefs (Var.shiftN ρ) Γ.copyAll where
  refs :=
    { inj := Var.shiftN_injective ρ
      map := Ctx.get_append_shiftN _ _
      off := fun j hj => by
        rcases Var.lowAdd_or_shiftN j with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · rw [copyAll_refs, Ctx.get_append_lowAdd]; exact hΓ.get i
        · exact absurd rfl (hj i) }
  vars := rfl

/-- The copies are a renaming of contexts. -/
lemma renRefs_copyAll_new {Γ : TCtx n ρ} (hΓ : Γ.refs.All NonLin) :
    Γ.RenRefs Var.lowAdd Γ.copyAll where
  refs :=
    { inj := Var.lowAdd_injective
      map := Ctx.get_append_lowAdd _ _
      off := fun j hj => by
        rcases Var.lowAdd_or_shiftN j with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact absurd rfl (hj i)
        · rw [copyAll_refs, Ctx.get_append_shiftN]; exact hΓ.get i }
  vars := rfl

/-- Renaming along `Var.shiftN 0` (no new references) is the identity renaming. -/
lemma renRefs_shiftN_zero (Γ : TCtx n ρ) : Γ.RenRefs (Var.shiftN 0) Γ :=
  ⟨Ctx.Ren.pad Γ.refs .none 0, rfl⟩

/-- Adding a new reference with a non-linear (or absent) hypothesis. -/
lemma renRefs_succ (Γ : TCtx n ρ) {h : Option (Hyp ArrTy)} (hh : NonLin h) :
    Γ.RenRefs (Var.shiftN 1) ⟨Γ.refs ,, h, Γ.vars⟩ :=
  ⟨Ctx.Ren.succ Γ.refs hh, rfl⟩

end TCtx

/-! ## Weakening into non-linear contexts -/

section Weaken

variable {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ}

/-- The left summand of a non-linear context can be weakened to the whole context. -/
lemma HasTypeD.weaken_left (hΓ : Γ.AllNonLin) (hadd : Γ₁.Add Γ₂ Γ) {t : Term n ρ} {A : Ty}
    (h : HasTypeD Γ₁ t A) : HasTypeD Γ t A :=
  h.weaken (TCtx.AllNonLin.right hadd hΓ) hadd

/-- The right summand of a non-linear context can be weakened to the whole context. -/
lemma HasTypeD.weaken_right (hΓ : Γ.AllNonLin) (hadd : Γ₁.Add Γ₂ Γ) {t : Term n ρ} {A : Ty}
    (h : HasTypeD Γ₂ t A) : HasTypeD Γ t A :=
  h.weaken (TCtx.AllNonLin.left hadd hΓ) hadd.comm

/-- The same under a binder. -/
lemma HasTypeD.weaken_right_cons (hΓ : Γ.AllNonLin) (hadd : Γ₁.Add Γ₂ Γ) {a : Option (Hyp Ty)}
    {t : Term (n + 1) ρ} {A : Ty} (h : HasTypeD (Γ₂.cons a) t A) : HasTypeD (Γ.cons a) t A :=
  h.weaken (TCtx.AllNonLin.left hadd hΓ).cons_none (hadd.comm.cons_none a)

/-- The same under two binders. -/
lemma HasTypeD.weaken_right_cons₂ (hΓ : Γ.AllNonLin) (hadd : Γ₁.Add Γ₂ Γ)
    {a b : Option (Hyp Ty)} {t : Term (n + 2) ρ} {A : Ty}
    (h : HasTypeD ((Γ₂.cons a).cons b) t A) : HasTypeD ((Γ.cons a).cons b) t A :=
  h.weaken (TCtx.AllNonLin.left hadd hΓ).cons_none.cons_none
    ((hadd.comm.cons_none a).cons_none b)

end Weaken

end LCU
