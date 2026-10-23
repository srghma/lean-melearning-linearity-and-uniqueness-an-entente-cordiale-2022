module
public import RequestProject.LCU.Sec3_1_Calculus.Weakening

/-!
# Renaming array references, and weakening configurations

Runtime configurations of the heap model grow at index zero: a reduction step that opens
`d` binders and allocates `e` arrays moves a term `t : Term n ρ` to the scope
`Term (n + d) (ρ + e)` by `Term.wk d e t`, which renames its variables along
`Var.shiftN d` and its array references along `Var.shiftN e`.

## Main definitions

* `TCtx.RenRefs θ Γ Γ'`: `Γ'` is `Γ` with its array references renamed along the injective
  `θ`, and non-linear (or absent) hypotheses for the other references.
* `Term.wk d e t` and `TCtx.lift d e Γ` (the context padded with `d` absent variables and
  `e` absent references).

## Main results

* `HasTypeD.renameRefs`, `HasType.renameRefs`: typing is stable under renaming references.
* `HasType.wk`: `Γ ⊢ t : A` gives `Γ.lift d e ⊢ t.wk d e : A`.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Renaming references on each constructor -/

section Compute

variable {n ρ ρ' : ℕ} (θ : Var ρ → Var ρ')

@[simp] lemma renameRefs_var (i : Var n) : renameRefs θ (var i : Term n ρ) = var i := rfl
@[simp] lemma renameRefs_lam (t : Term (n + 1) ρ) : renameRefs θ (lam t) = lam (renameRefs θ t) :=
  rfl
@[simp] lemma renameRefs_app (t₁ t₂ : Term n ρ) :
    renameRefs θ (app t₁ t₂) = app (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_pair (t₁ t₂ : Term n ρ) :
    renameRefs θ (pair t₁ t₂) = pair (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) :
    renameRefs θ (letPair t₁ t₂) = letPair (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_unit : renameRefs θ (unit : Term n ρ) = unit := rfl
@[simp] lemma renameRefs_letUnit (t₁ t₂ : Term n ρ) :
    renameRefs θ (letUnit t₁ t₂) = letUnit (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_bang (t : Term n ρ) : renameRefs θ (bang t) = bang (renameRefs θ t) := rfl
@[simp] lemma renameRefs_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    renameRefs θ (letBang t₁ t₂) = letBang (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_borrow (t : Term n ρ) :
    renameRefs θ (borrow t) = borrow (renameRefs θ t) := rfl
@[simp] lemma renameRefs_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    renameRefs θ (copy t₁ t₂) = copy (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_star (t : Term n ρ) : renameRefs θ (star t) = star (renameRefs θ t) := rfl
@[simp] lemma renameRefs_nat (k : ℕ) : renameRefs θ (nat k : Term n ρ) = nat k := rfl
@[simp] lemma renameRefs_float (x : FloatLit) : renameRefs θ (float x : Term n ρ) = float x := rfl
@[simp] lemma renameRefs_prim (p : Prim) : renameRefs θ (prim p : Term n ρ) = prim p := rfl
@[simp] lemma renameRefs_ref (a : Var ρ) : renameRefs θ (ref a : Term n ρ) = ref (θ a) := rfl

end Compute

/-! ## Renaming the references of a context -/

namespace TCtx

variable {n ρ ρ' : ℕ}

/-- `RenRefs θ Γ Γ'`: `Γ'` is `Γ` with its array references renamed along the injective
`θ`, and non-linear (or absent) hypotheses for the references outside the image of `θ`.
The variables are unchanged. -/
structure RenRefs (θ : Var ρ → Var ρ') (Γ : TCtx n ρ) (Γ' : TCtx n ρ') : Prop where
  refs : Ctx.Ren NonLin θ Γ.refs Γ'.refs
  vars : Γ'.vars = Γ.vars

namespace RenRefs

variable {θ : Var ρ → Var ρ'} {Γ : TCtx n ρ} {Γ' : TCtx n ρ'}

lemma cons (hr : RenRefs θ Γ Γ') (h : Option (Hyp Ty)) : RenRefs θ (Γ.cons h) (Γ'.cons h) :=
  ⟨hr.refs, by simp [hr.vars]⟩

lemma allNonLin (hr : RenRefs θ Γ Γ') (hΓ : Γ.AllNonLin) : Γ'.AllNonLin :=
  ⟨hr.refs.all hΓ.refs, hr.vars ▸ hΓ.vars⟩

lemma varsNonLin (hr : RenRefs θ Γ Γ') (hΓ : Γ.VarsNonLin) : Γ'.VarsNonLin :=
  show Γ'.vars.All NonLin from hr.vars ▸ hΓ

lemma refsOnly (hr : RenRefs θ Γ Γ') : RenRefs θ Γ.refsOnly Γ'.refsOnly := ⟨hr.refs, rfl⟩

lemma split (hr : RenRefs θ Γ Γ') {Γ₁ Γ₂ : TCtx n ρ} (hadd : Γ₁.Add Γ₂ Γ) :
    ∃ Γ₁' Γ₂', RenRefs θ Γ₁ Γ₁' ∧ RenRefs θ Γ₂ Γ₂' ∧ Γ₁'.Add Γ₂' Γ' := by
  obtain ⟨Δ₁, Δ₂, h₁, h₂, h⟩ := hr.refs.split HypAdd.idem hadd.refs
  exact ⟨⟨Δ₁, Γ₁.vars⟩, ⟨Δ₂, Γ₂.vars⟩, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩, ⟨h, hr.vars ▸ hadd.vars⟩⟩

end RenRefs

end TCtx

/-- Typing is preserved by renaming array references. -/
theorem HasTypeD.renameRefs {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty}
    (ht : HasTypeD Γ t A) :
    ∀ {ρ' : ℕ} {θ : Var ρ → Var ρ'} {Γ' : TCtx n ρ'}, Γ.RenRefs θ Γ' →
      HasTypeD Γ' (LCU.renameRefs θ t) A := by
  induction ht with
  | var hi hr =>
    intro ρ' θ Γ' hθ
    exact .var (hθ.vars ▸ hi) (hθ.refs.all hr)
  | ref ha hv =>
    intro ρ' θ Γ' hθ
    exact .ref (hθ.refs.pick ha) (hθ.vars ▸ hv)
  | abs _ ih => intro ρ' θ Γ' hθ; exact .abs (ih (hθ.cons _))
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro ρ' θ Γ' hθ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hθ.split hadd
    split_rule (ih₁ h₁) (ih₂ (by (repeat apply TCtx.RenRefs.cons); exact h₂)) hadd'
  | unitI hΓ | natI hΓ | floatI hΓ | prim hΓ =>
    intro ρ' θ Γ' hθ; constructor; exact hθ.allNonLin hΓ
  | bangI hΓ _ ih => intro ρ' θ Γ' hθ; exact .bangI (hθ.allNonLin hΓ) (ih hθ)
  | borrow _ ih => intro ρ' θ Γ' hθ; exact .borrow (ih hθ)
  | nec _ hΓ ih => intro ρ' θ Γ' hθ; exact .nec (ih hθ.refsOnly) (hθ.varsNonLin hΓ)

/-- Typing is preserved by renaming array references. -/
theorem HasType.renameRefs {n ρ ρ' : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty}
    {θ : Var ρ → Var ρ'} {Γ' : TCtx n ρ'} (ht : HasType Γ t A) (hθ : Γ.RenRefs θ Γ') :
    HasType Γ' (LCU.renameRefs θ t) A :=
  hasType_iff_hasTypeD.2 ((hasType_iff_hasTypeD.1 ht).renameRefs hθ)

/-! ## Weakening configurations -/

/-- Weakening a term by `d` new variables and `e` new array references (all bound at
index zero). -/
def Term.wk {n ρ : ℕ} (d e : ℕ) (t : Term n ρ) : Term (n + d) (ρ + e) :=
  renameRefs (Var.shiftN e) (t.rename (Var.shiftN d))

/-- Weakening the body of a binder of arity `k`: the bound variables are kept. -/
def Term.wkUnder {n ρ : ℕ} (k d e : ℕ) (t : Term (n + k) ρ) : Term (n + d + k) (ρ + e) :=
  renameRefs (Var.shiftN e) (t.rename (Ren.upN k (Var.shiftN d)))

/-- Padding a context with `d` absent variables and `e` absent array references. -/
def TCtx.lift {n ρ : ℕ} (d e : ℕ) (Γ : TCtx n ρ) : TCtx (n + d) (ρ + e) :=
  ⟨Γ.refs.pad none e, Γ.vars.pad none d⟩

@[simp] lemma TCtx.lift_refs {n ρ : ℕ} (d e : ℕ) (Γ : TCtx n ρ) :
    (Γ.lift d e).refs = Γ.refs.pad none e := rfl
@[simp] lemma TCtx.lift_vars {n ρ : ℕ} (d e : ℕ) (Γ : TCtx n ρ) :
    (Γ.lift d e).vars = Γ.vars.pad none d := rfl

lemma TCtx.lift_empty {n ρ : ℕ} (d e : ℕ) : (TCtx.empty : TCtx n ρ).lift d e = TCtx.empty := by
  simp [TCtx.lift, TCtx.empty]

lemma TCtx.Add.lift {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : Γ₁.Add Γ₂ Γ) (d e : ℕ) :
    (Γ₁.lift d e).Add (Γ₂.lift d e) (Γ.lift d e) :=
  ⟨h.refs.pad (.noneLeft none) e, h.vars.pad (.noneLeft none) d⟩

lemma TCtx.AllNonLin.lift {n ρ : ℕ} {Γ : TCtx n ρ} (h : Γ.AllNonLin) (d e : ℕ) :
    (Γ.lift d e).AllNonLin :=
  ⟨h.refs.pad .none e, h.vars.pad .none d⟩

/-- Typing is preserved by weakening configurations. -/
theorem HasType.wk {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasType Γ t A)
    (d e : ℕ) : HasType (Γ.lift d e) (t.wk d e) A :=
  (ht.rename (Γ' := ⟨Γ.refs, Γ.vars.pad none d⟩) ⟨rfl, Ctx.Ren.pad _ .none d⟩).renameRefs
    ⟨Ctx.Ren.pad _ .none e, rfl⟩

end LCU
