module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax

/-!
# Renaming and substitution of LCU terms

Renaming and substitution are the generic operations of the binding layer
(`RequestProject/Common/Syntax.lean`), instantiated at the LCU signature; their laws are
the generic laws.  This file only gives them their LCU names and records how they compute
on each constructor (all these equations hold by `rfl`).

* `Term.rename ρ t` (with `ρ : Var n → Var m`) and `Term.subst σ t` (with
  `σ : Var n → Term m ρ`);
* `Term.subst1 t s` is the single substitution `[s/x]t` for the variable bound by a
  one-variable binder, `Term.subst2 t s₁ s₂` the double substitution `[s₁/x, s₂/y]t` used by
  `let (x, y) = …` (`y` is `Var.zero`, `x` is `Var.succ Var.zero`);
* `Term.renameRefs θ t` renames the runtime array references of `t` along
  `θ : Var ρ → Var ρ'` (it is the generic operator map); it is the renaming `θ` of the heap
  rule `copy_β`.
-/

@[expose] public section

namespace LCU

open Binding

namespace Term

variable {n m k ρ : ℕ}

/-- Simultaneous renaming of free variables. -/
abbrev rename (r : Var n → Var m) (t : Term n ρ) : Term m ρ := Tm.ren r t

/-- Simultaneous (capture-avoiding) substitution of free variables. -/
abbrev subst (σ : Var n → Term m ρ) (t : Term n ρ) : Term m ρ := Tm.subst σ t

/-- Single substitution `[s/x]t` of `s` for the variable `x = Var.zero` bound in `t`. -/
abbrev subst1 (t : Term (n + 1) ρ) (s : Term n ρ) : Term n ρ := Tm.inst1 t s

/-- Double substitution `[s₁/x, s₂/y]t` for `t` the body of a `let (x, y) = _ in t`. -/
abbrev subst2 (t : Term (n + 2) ρ) (s₁ s₂ : Term n ρ) : Term n ρ := Tm.inst2 t s₁ s₂

/-- Lifting a substitution under a binder. -/
abbrev Subst.up (σ : Var n → Term m ρ) : Var (n + 1) → Term (m + 1) ρ := Binding.Subst.up σ

/-! ## Renaming and substitution on each constructor -/

section Compute

variable (r : Var n → Var m) (σ : Var n → Term m ρ)

@[simp] lemma rename_var (i : Var n) : (var i : Term n ρ).rename r = var (r i) := rfl
@[simp] lemma rename_lam (t : Term (n + 1) ρ) : (lam t).rename r = lam (t.rename (Ren.up r)) := rfl
@[simp] lemma rename_app (t₁ t₂ : Term n ρ) : (app t₁ t₂).rename r = app (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_pair (t₁ t₂ : Term n ρ) :
    (pair t₁ t₂).rename r = pair (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) :
    (letPair t₁ t₂).rename r = letPair (t₁.rename r) (t₂.rename (Ren.up (Ren.up r))) := rfl
@[simp] lemma rename_unit : (unit : Term n ρ).rename r = unit := rfl
@[simp] lemma rename_letUnit (t₁ t₂ : Term n ρ) :
    (letUnit t₁ t₂).rename r = letUnit (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_bang (t : Term n ρ) : (bang t).rename r = bang (t.rename r) := rfl
@[simp] lemma rename_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (letBang t₁ t₂).rename r = letBang (t₁.rename r) (t₂.rename (Ren.up r)) := rfl
@[simp] lemma rename_borrow (t : Term n ρ) : (borrow t).rename r = borrow (t.rename r) := rfl
@[simp] lemma rename_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (copy t₁ t₂).rename r = copy (t₁.rename r) (t₂.rename (Ren.up r)) := rfl
@[simp] lemma rename_star (t : Term n ρ) : (star t).rename r = star (t.rename r) := rfl
@[simp] lemma rename_nat (k : ℕ) : (nat k : Term n ρ).rename r = nat k := rfl
@[simp] lemma rename_float (x : FloatLit) : (float x : Term n ρ).rename r = float x := rfl
@[simp] lemma rename_prim (p : Prim) : (prim p : Term n ρ).rename r = prim p := rfl
@[simp] lemma rename_ref (a : Var ρ) : (ref a : Term n ρ).rename r = ref a := rfl

@[simp] lemma subst_var (i : Var n) : (var i : Term n ρ).subst σ = σ i := rfl
@[simp] lemma subst_lam (t : Term (n + 1) ρ) : (lam t).subst σ = lam (t.subst (Subst.up σ)) := rfl
@[simp] lemma subst_app (t₁ t₂ : Term n ρ) : (app t₁ t₂).subst σ = app (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_pair (t₁ t₂ : Term n ρ) :
    (pair t₁ t₂).subst σ = pair (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) :
    (letPair t₁ t₂).subst σ = letPair (t₁.subst σ) (t₂.subst (Subst.up (Subst.up σ))) := rfl
@[simp] lemma subst_unit : (unit : Term n ρ).subst σ = unit := rfl
@[simp] lemma subst_letUnit (t₁ t₂ : Term n ρ) :
    (letUnit t₁ t₂).subst σ = letUnit (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_bang (t : Term n ρ) : (bang t).subst σ = bang (t.subst σ) := rfl
@[simp] lemma subst_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (letBang t₁ t₂).subst σ = letBang (t₁.subst σ) (t₂.subst (Subst.up σ)) := rfl
@[simp] lemma subst_borrow (t : Term n ρ) : (borrow t).subst σ = borrow (t.subst σ) := rfl
@[simp] lemma subst_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (copy t₁ t₂).subst σ = copy (t₁.subst σ) (t₂.subst (Subst.up σ)) := rfl
@[simp] lemma subst_star (t : Term n ρ) : (star t).subst σ = star (t.subst σ) := rfl
@[simp] lemma subst_nat (k : ℕ) : (nat k : Term n ρ).subst σ = nat k := rfl
@[simp] lemma subst_float (x : FloatLit) : (float x : Term n ρ).subst σ = float x := rfl
@[simp] lemma subst_prim (p : Prim) : (prim p : Term n ρ).subst σ = prim p := rfl
@[simp] lemma subst_ref (a : Var ρ) : (ref a : Term n ρ).subst σ = ref a := rfl

end Compute

/-! ## The laws (instances of the generic laws) -/

lemma rename_id (t : Term n ρ) : t.rename id = t := Tm.ren_id t

lemma rename_rename (r : Var n → Var m) (r' : Var m → Var k) (t : Term n ρ) :
    (t.rename r).rename r' = t.rename (r' ∘ r) := Tm.ren_ren r r' t

lemma subst_var' (t : Term n ρ) : t.subst var = t := Tm.subst_var t

lemma rename_eq_subst (r : Var n → Var m) (t : Term n ρ) : t.rename r = t.subst (var ∘ r) :=
  Tm.ren_eq_subst r t

lemma subst_rename (r : Var n → Var m) (σ : Var m → Term k ρ) (t : Term n ρ) :
    (t.rename r).subst σ = t.subst (σ ∘ r) := Tm.subst_ren r σ t

lemma rename_subst (σ : Var n → Term m ρ) (r : Var m → Var k) (t : Term n ρ) :
    (t.subst σ).rename r = t.subst (rename r ∘ σ) := Tm.ren_subst σ r t

lemma subst_subst (σ : Var n → Term m ρ) (τ : Var m → Term k ρ) (t : Term n ρ) :
    (t.subst σ).subst τ = t.subst (subst τ ∘ σ) := Tm.subst_subst σ τ t

@[simp] lemma subst1_rename_succ (s t : Term n ρ) : (t.rename .succ).subst1 s = t :=
  Tm.inst1_ren_succ s t

lemma subst2_eq (t : Term (n + 2) ρ) (s₁ s₂ : Term n ρ) :
    t.subst2 s₁ s₂ = (t.subst1 (s₂.rename .succ)).subst1 s₁ := Tm.inst2_eq s₁ s₂ t

@[simp] lemma Subst.up_zero (σ : Var n → Term m ρ) : Subst.up σ .zero = var .zero := rfl
@[simp] lemma Subst.up_succ (σ : Var n → Term m ρ) (i : Var n) :
    Subst.up σ (.succ i) = (σ i).rename .succ := rfl

end Term

/-! ## Renaming array references -/

/-- The operator map renaming runtime array references along `θ`. -/
def Op.renameRef {ρ ρ' : ℕ} (θ : Var ρ → Var ρ') : Op ρ → Op ρ'
  | .lam => .lam
  | .app => .app
  | .pair => .pair
  | .letPair => .letPair
  | .unit => .unit
  | .letUnit => .letUnit
  | .bang => .bang
  | .letBang => .letBang
  | .borrow => .borrow
  | .copy => .copy
  | .star => .star
  | .nat k => .nat k
  | .float x => .float x
  | .prim p => .prim p
  | .ref a => .ref (θ a)

/-- Renaming runtime references is an arity-preserving operator map. -/
def refHom {ρ ρ' : ℕ} (θ : Var ρ → Var ρ') : SigHom (sig ρ) (sig ρ') where
  map := Op.renameRef θ
  arity_map o := by cases o <;> rfl

/-- Renaming of array references `θ(t)`. -/
def renameRefs {n ρ ρ' : ℕ} (θ : Var ρ → Var ρ') (t : Term n ρ) : Term n ρ' := Tm.mapOp (refHom θ) t

namespace Term

variable {n m ρ ρ' : ℕ}

lemma renameRefs_rename (θ : Var ρ → Var ρ') (r : Var n → Var m) (t : Term n ρ) :
    renameRefs θ (t.rename r) = (renameRefs θ t).rename r := Tm.mapOp_ren _ r t

lemma renameRefs_subst (θ : Var ρ → Var ρ') (σ : Var n → Term m ρ) (t : Term n ρ) :
    renameRefs θ (t.subst σ) = (renameRefs θ t).subst (renameRefs θ ∘ σ) := Tm.mapOp_subst _ σ t

end Term

end LCU
