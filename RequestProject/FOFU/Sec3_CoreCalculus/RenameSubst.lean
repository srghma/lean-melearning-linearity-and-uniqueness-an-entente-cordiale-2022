module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax

/-!
# Renaming and substitution of term variables

Renaming and substitution are the generic operations of the binding layer
(`RequestProject/Common/Syntax.lean`), instantiated at the FOFU signature; their laws are
the generic σ-calculus laws.  This file gives them their FOFU names and records how they
compute on each constructor (all these equations hold by `rfl`).

* `Term.rename r t` (`r : Var n → Var m`) and `Term.subst σ t` (`σ : Var n → Term R m ρ`);
* `Term.subst1 t s` is `t [s / x]` for the variable `x = Var.zero` bound in `t`, and
  `Term.subst2 t s₁ s₂` is `t [s₁ / x, s₂ / y]` for the body of `let (x, y) = _ in t`;
* `Term.wk d t` weakens `t` by `d` new variables bound in front (`Var.shiftN d`);
* `renameRefs θ t` renames the runtime references of `t` along `θ : Var ρ → Var ρ'`
  (the generic operator map); it is the renaming `θ(t)` of the reduction rule for `clone`
  and the weakening of terms when the heap allocates new references.
-/

@[expose] public section

namespace FOFU

open Binding

namespace Term

variable {R : Type} {n m k ρ : ℕ}

/-- Simultaneous renaming of free variables. -/
abbrev rename (r : Var n → Var m) (t : Term R n ρ) : Term R m ρ := Tm.ren r t

/-- Simultaneous (capture-avoiding) substitution of free variables. -/
abbrev subst (σ : Var n → Term R m ρ) (t : Term R n ρ) : Term R m ρ := Tm.subst σ t

/-- Single substitution `t [s / x]` of `s` for the variable `x = Var.zero` bound in `t`. -/
abbrev subst1 (t : Term R (n + 1) ρ) (s : Term R n ρ) : Term R n ρ := Tm.inst1 t s

/-- Double substitution `t [s₁ / x, s₂ / y]` for `t` the body of a `let (x, y) = _ in t`
(`y` is `Var.zero`, `x` is `Var.succ Var.zero`). -/
abbrev subst2 (t : Term R (n + 2) ρ) (s₁ s₂ : Term R n ρ) : Term R n ρ := Tm.inst2 t s₁ s₂

/-- Weakening by `d` new variables bound in front. -/
abbrev wk (d : ℕ) (t : Term R n ρ) : Term R (n + d) ρ := t.rename (Var.shiftN d)

/-- Lifting a substitution under a binder. -/
abbrev Subst.up (σ : Var n → Term R m ρ) : Var (n + 1) → Term R (m + 1) ρ := Binding.Subst.up σ

/-! ## Renaming and substitution on each constructor -/

section Compute

variable (r : Var n → Var m) (σ : Var n → Term R m ρ)

@[simp] lemma rename_var (i : Var n) : (var i : Term R n ρ).rename r = var (r i) := rfl
@[simp] lemma rename_lam (t : Term R (n + 1) ρ) : (lam t).rename r = lam (t.rename (Ren.up r)) := rfl
@[simp] lemma rename_app (t₁ t₂ : Term R n ρ) :
    (app t₁ t₂).rename r = app (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_pair (t₁ t₂ : Term R n ρ) :
    (pair t₁ t₂).rename r = pair (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_letUnit (t₁ t₂ : Term R n ρ) :
    (letUnit t₁ t₂).rename r = letUnit (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_withBorrow (t₁ t₂ : Term R n ρ) :
    (withBorrow t₁ t₂).rename r = withBorrow (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_join (t₁ t₂ : Term R n ρ) :
    (join t₁ t₂).rename r = join (t₁.rename r) (t₂.rename r) := rfl
@[simp] lemma rename_letPair (t₁ : Term R n ρ) (t₂ : Term R (n + 2) ρ) :
    (letPair t₁ t₂).rename r = letPair (t₁.rename r) (t₂.rename (Ren.up (Ren.up r))) := rfl
@[simp] lemma rename_letBox (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (letBox t₁ t₂).rename r = letBox (t₁.rename r) (t₂.rename (Ren.up r)) := rfl
@[simp] lemma rename_unpack (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (unpack t₁ t₂).rename r = unpack (t₁.rename r) (t₂.rename (Ren.up r)) := rfl
@[simp] lemma rename_clone (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (clone t₁ t₂).rename r = clone (t₁.rename r) (t₂.rename (Ren.up r)) := rfl
@[simp] lemma rename_pack (t : Term R n ρ) : (pack t).rename r = pack (t.rename r) := rfl
@[simp] lemma rename_split (t : Term R n ρ) : (split t).rename r = split (t.rename r) := rfl
@[simp] lemma rename_push (t : Term R n ρ) : (push t).rename r = push (t.rename r) := rfl
@[simp] lemma rename_pull (t : Term R n ρ) : (pull t).rename r = pull (t.rename r) := rfl
@[simp] lemma rename_star (t : Term R n ρ) : (star t).rename r = star (t.rename r) := rfl
@[simp] lemma rename_unborrow (t : Term R n ρ) : (unborrow t).rename r = unborrow (t.rename r) := rfl
@[simp] lemma rename_box (s : R) (t : Term R n ρ) : (box s t).rename r = box s (t.rename r) := rfl
@[simp] lemma rename_share (s : R) (t : Term R n ρ) : (share s t).rename r = share s (t.rename r) := rfl
@[simp] lemma rename_unit : (unit : Term R n ρ).rename r = unit := rfl
@[simp] lemma rename_nat (k : ℕ) : (nat k : Term R n ρ).rename r = nat k := rfl
@[simp] lemma rename_float (x : FloatLit) : (float x : Term R n ρ).rename r = float x := rfl
@[simp] lemma rename_prim (p : Prim) : (prim p : Term R n ρ).rename r = prim p := rfl
@[simp] lemma rename_ref (a : Var ρ) : (ref a : Term R n ρ).rename r = ref a := rfl

@[simp] lemma subst_var (i : Var n) : (var i : Term R n ρ).subst σ = σ i := rfl
@[simp] lemma subst_lam (t : Term R (n + 1) ρ) : (lam t).subst σ = lam (t.subst (Subst.up σ)) := rfl
@[simp] lemma subst_app (t₁ t₂ : Term R n ρ) :
    (app t₁ t₂).subst σ = app (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_pair (t₁ t₂ : Term R n ρ) :
    (pair t₁ t₂).subst σ = pair (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_letUnit (t₁ t₂ : Term R n ρ) :
    (letUnit t₁ t₂).subst σ = letUnit (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_withBorrow (t₁ t₂ : Term R n ρ) :
    (withBorrow t₁ t₂).subst σ = withBorrow (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_join (t₁ t₂ : Term R n ρ) :
    (join t₁ t₂).subst σ = join (t₁.subst σ) (t₂.subst σ) := rfl
@[simp] lemma subst_letPair (t₁ : Term R n ρ) (t₂ : Term R (n + 2) ρ) :
    (letPair t₁ t₂).subst σ = letPair (t₁.subst σ) (t₂.subst (Subst.up (Subst.up σ))) := rfl
@[simp] lemma subst_letBox (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (letBox t₁ t₂).subst σ = letBox (t₁.subst σ) (t₂.subst (Subst.up σ)) := rfl
@[simp] lemma subst_unpack (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (unpack t₁ t₂).subst σ = unpack (t₁.subst σ) (t₂.subst (Subst.up σ)) := rfl
@[simp] lemma subst_clone (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) :
    (clone t₁ t₂).subst σ = clone (t₁.subst σ) (t₂.subst (Subst.up σ)) := rfl
@[simp] lemma subst_pack (t : Term R n ρ) : (pack t).subst σ = pack (t.subst σ) := rfl
@[simp] lemma subst_split (t : Term R n ρ) : (split t).subst σ = split (t.subst σ) := rfl
@[simp] lemma subst_push (t : Term R n ρ) : (push t).subst σ = push (t.subst σ) := rfl
@[simp] lemma subst_pull (t : Term R n ρ) : (pull t).subst σ = pull (t.subst σ) := rfl
@[simp] lemma subst_star (t : Term R n ρ) : (star t).subst σ = star (t.subst σ) := rfl
@[simp] lemma subst_unborrow (t : Term R n ρ) : (unborrow t).subst σ = unborrow (t.subst σ) := rfl
@[simp] lemma subst_box (s : R) (t : Term R n ρ) : (box s t).subst σ = box s (t.subst σ) := rfl
@[simp] lemma subst_share (s : R) (t : Term R n ρ) : (share s t).subst σ = share s (t.subst σ) := rfl
@[simp] lemma subst_unit : (unit : Term R n ρ).subst σ = unit := rfl
@[simp] lemma subst_nat (k : ℕ) : (nat k : Term R n ρ).subst σ = nat k := rfl
@[simp] lemma subst_float (x : FloatLit) : (float x : Term R n ρ).subst σ = float x := rfl
@[simp] lemma subst_prim (p : Prim) : (prim p : Term R n ρ).subst σ = prim p := rfl
@[simp] lemma subst_ref (a : Var ρ) : (ref a : Term R n ρ).subst σ = ref a := rfl

end Compute

/-! ## The laws (instances of the generic laws) -/

lemma rename_id (t : Term R n ρ) : t.rename id = t := Tm.ren_id t

lemma rename_rename (r : Var n → Var m) (r' : Var m → Var k) (t : Term R n ρ) :
    (t.rename r).rename r' = t.rename (r' ∘ r) := Tm.ren_ren r r' t

lemma subst_var' (t : Term R n ρ) : t.subst var = t := Tm.subst_var t

lemma rename_eq_subst (r : Var n → Var m) (t : Term R n ρ) : t.rename r = t.subst (var ∘ r) :=
  Tm.ren_eq_subst r t

lemma subst_rename (r : Var n → Var m) (σ : Var m → Term R k ρ) (t : Term R n ρ) :
    (t.rename r).subst σ = t.subst (σ ∘ r) := Tm.subst_ren r σ t

lemma rename_subst (σ : Var n → Term R m ρ) (r : Var m → Var k) (t : Term R n ρ) :
    (t.subst σ).rename r = t.subst (rename r ∘ σ) := Tm.ren_subst σ r t

lemma subst_subst (σ : Var n → Term R m ρ) (τ : Var m → Term R k ρ) (t : Term R n ρ) :
    (t.subst σ).subst τ = t.subst (subst τ ∘ σ) := Tm.subst_subst σ τ t

@[simp] lemma subst1_rename_succ (s t : Term R n ρ) : (t.rename .succ).subst1 s = t :=
  Tm.inst1_ren_succ s t

lemma subst2_eq (t : Term R (n + 2) ρ) (s₁ s₂ : Term R n ρ) :
    t.subst2 s₁ s₂ = (t.subst1 (s₂.rename .succ)).subst1 s₁ := Tm.inst2_eq s₁ s₂ t

@[simp] lemma Subst.up_zero (σ : Var n → Term R m ρ) : Subst.up σ .zero = var .zero := rfl
@[simp] lemma Subst.up_succ (σ : Var n → Term R m ρ) (i : Var n) :
    Subst.up σ (.succ i) = (σ i).rename .succ := rfl

end Term

/-! ## Renaming runtime references -/

/-- The operator map renaming runtime references along `θ`. -/
def Op.renameRef {R : Type} {ρ ρ' : ℕ} (θ : Var ρ → Var ρ') : Op R ρ → Op R ρ'
  | .lam => .lam
  | .app => .app
  | .pair => .pair
  | .letPair => .letPair
  | .unit => .unit
  | .letUnit => .letUnit
  | .box r => .box r
  | .letBox => .letBox
  | .pack => .pack
  | .unpack => .unpack
  | .share r => .share r
  | .clone => .clone
  | .withBorrow => .withBorrow
  | .split => .split
  | .join => .join
  | .push => .push
  | .pull => .pull
  | .nat m => .nat m
  | .float x => .float x
  | .prim p => .prim p
  | .star => .star
  | .unborrow => .unborrow
  | .ref a => .ref (θ a)

/-- Renaming runtime references is an arity-preserving operator map. -/
def refHom {R : Type} {ρ ρ' : ℕ} (θ : Var ρ → Var ρ') : SigHom (sig R ρ) (sig R ρ') where
  map := Op.renameRef θ
  arity_map o := by cases o <;> rfl

/-- Renaming of runtime references `θ(t)`. -/
def renameRefs {R : Type} {n ρ ρ' : ℕ} (θ : Var ρ → Var ρ') (t : Term R n ρ) : Term R n ρ' :=
  Tm.mapOp (refHom θ) t

namespace Term

variable {R : Type} {n m ρ ρ' : ℕ}

lemma renameRefs_rename (θ : Var ρ → Var ρ') (r : Var n → Var m) (t : Term R n ρ) :
    renameRefs θ (t.rename r) = (renameRefs θ t).rename r := Tm.mapOp_ren _ r t

lemma renameRefs_subst (θ : Var ρ → Var ρ') (σ : Var n → Term R m ρ) (t : Term R n ρ) :
    renameRefs θ (t.subst σ) = (renameRefs θ t).subst (renameRefs θ ∘ σ) := Tm.mapOp_subst _ σ t

end Term

/-! ## References occurring in a term -/

/-- The operator `ref a`. -/
def Op.isRef {R : Type} {ρ : ℕ} (a : Var ρ) : Op R ρ → Bool
  | .ref b => decide (b = a)
  | _ => false

namespace Term

variable {R : Type} {n m ρ ρ' : ℕ}

/-- `a ∈ refs(t)`: the runtime reference `a` occurs in `t`. -/
def RefOccurs (a : Var ρ) (t : Term R n ρ) : Prop := Tm.HasOp (fun o => Op.isRef a o = true) t

instance (a : Var ρ) (t : Term R n ρ) : Decidable (t.RefOccurs a) := Tm.decidableHasOp _ t

/-- The finite set `refs(t)` of runtime references occurring in `t`. -/
def refs (t : Term R n ρ) : Finset (Var ρ) := Finset.univ.filter fun a => t.RefOccurs a

@[simp] lemma mem_refs {t : Term R n ρ} {a : Var ρ} : a ∈ t.refs ↔ t.RefOccurs a := by
  simp [refs]

/-- Renaming variables does not change the references of a term. -/
@[simp] lemma refOccurs_rename (r : Var n → Var m) (t : Term R n ρ) (a : Var ρ) :
    (t.rename r).RefOccurs a ↔ t.RefOccurs a := Tm.hasOp_ren_iff r t

@[simp] lemma renameRefs_var (θ : Var ρ → Var ρ') (i : Var n) :
    renameRefs θ (var i : Term R n ρ) = var i := rfl
@[simp] lemma renameRefs_ref (θ : Var ρ → Var ρ') (a : Var ρ) :
    renameRefs θ (ref a : Term R n ρ) = ref (θ a) := rfl
@[simp] lemma renameRefs_star (θ : Var ρ → Var ρ') (t : Term R n ρ) :
    renameRefs θ (star t) = star (renameRefs θ t) := rfl
@[simp] lemma renameRefs_pack (θ : Var ρ → Var ρ') (t : Term R n ρ) :
    renameRefs θ (pack t) = pack (renameRefs θ t) := rfl
@[simp] lemma renameRefs_pair (θ : Var ρ → Var ρ') (t₁ t₂ : Term R n ρ) :
    renameRefs θ (pair t₁ t₂) = pair (renameRefs θ t₁) (renameRefs θ t₂) := rfl
@[simp] lemma renameRefs_unit (θ : Var ρ → Var ρ') : renameRefs θ (unit : Term R n ρ) = unit := rfl
@[simp] lemma renameRefs_nat (θ : Var ρ → Var ρ') (k : ℕ) :
    renameRefs θ (nat k : Term R n ρ) = nat k := rfl
@[simp] lemma renameRefs_float (θ : Var ρ → Var ρ') (x : FloatLit) :
    renameRefs θ (float x : Term R n ρ) = float x := rfl
@[simp] lemma renameRefs_prim (θ : Var ρ → Var ρ') (p : Prim) :
    renameRefs θ (prim p : Term R n ρ) = prim p := rfl

end Term

end FOFU
