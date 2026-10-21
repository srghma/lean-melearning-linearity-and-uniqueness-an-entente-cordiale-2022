module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax
public import RequestProject.Common.DeBruijn
public import Mathlib.Data.Finset.Basic

/-!
# Renaming and substitution of term variables

Parallel renaming `Term.rename ρ` (`ρ : Fin n → Fin m`) and parallel substitution
`Term.subst σ` (`σ : Fin n → Term R m`) for the de Bruijn terms of the FOFU calculus.
Lifting a renaming under a binder is `DeBruijn.Ren.up`, shared with the LCU
development (`RequestProject/Common/DeBruijn.lean`); the term-specific part below follows
the same structure as `RequestProject/LCU/Sec3_1_Calculus/RenameSubst.lean`, but cannot
be shared since the term languages differ.

* `Term.subst1 s t` is `t [s / x]` for the variable `x = 0` bound in `t`;
* `Term.weaken h t` embeds `Term R n` into `Term R m` for `n ≤ m` (used when the heap
  grows during reduction);
* `Term.refs t` is the finite set of runtime references occurring in `t` (`refs(t)` in
  the paper) and `Term.renameRefs θ t` renames them (`θ(t)` in the rule for `clone`).

The usual laws (`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`, ...)
are proved by induction on terms.
-/

@[expose] public section

namespace FOFU

namespace Term

open DeBruijn

variable {R : Type}

/-! ## Renaming -/

/-- Simultaneous renaming of free variables. -/
def rename : {n m : ℕ} → (Fin n → Fin m) → Term R n → Term R m
  | _, _, ρ, var i => var (ρ i)
  | _, _, ρ, lam t => lam (rename (Ren.up ρ) t)
  | _, _, ρ, app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, pair t₁ t₂ => pair (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, letPair t₁ t₂ => letPair (rename ρ t₁) (rename (Ren.up (Ren.up ρ)) t₂)
  | _, _, _, unit => unit
  | _, _, ρ, letUnit t₁ t₂ => letUnit (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, box r t => box r (rename ρ t)
  | _, _, ρ, letBox t₁ t₂ => letBox (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, pack t => pack (rename ρ t)
  | _, _, ρ, unpack t₁ t₂ => unpack (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, share r t => share r (rename ρ t)
  | _, _, ρ, clone t₁ t₂ => clone (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, withBorrow t₁ t₂ => withBorrow (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, split t => split (rename ρ t)
  | _, _, ρ, join t₁ t₂ => join (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, push t => push (rename ρ t)
  | _, _, ρ, pull t => pull (rename ρ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, ρ, star t => star (rename ρ t)
  | _, _, ρ, unborrow t => unborrow (rename ρ t)
  | _, _, _, ref a => ref a

/-- Weakening a term into a larger scope (`n ≤ m`); new variables are added at the
end, as happens when the heap grows. -/
abbrev weaken {n m : ℕ} (h : n ≤ m) (t : Term R n) : Term R m := rename (Fin.castLE h) t

/-! ## Substitution -/

/-- Lifting a substitution under a binder. -/
def Subst.up {n m : ℕ} (σ : Fin n → Term R m) : Fin (n + 1) → Term R (m + 1) :=
  Fin.cases (var 0) (fun i => rename Fin.succ (σ i))

@[simp] lemma Subst.up_zero {n m : ℕ} (σ : Fin n → Term R m) : Subst.up σ 0 = var 0 := rfl
@[simp] lemma Subst.up_succ {n m : ℕ} (σ : Fin n → Term R m) (i : Fin n) :
    Subst.up σ i.succ = rename Fin.succ (σ i) := rfl

/-- Simultaneous (capture-avoiding) substitution of free variables. -/
def subst : {n m : ℕ} → (Fin n → Term R m) → Term R n → Term R m
  | _, _, σ, var i => σ i
  | _, _, σ, lam t => lam (subst (Subst.up σ) t)
  | _, _, σ, app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | _, _, σ, pair t₁ t₂ => pair (subst σ t₁) (subst σ t₂)
  | _, _, σ, letPair t₁ t₂ => letPair (subst σ t₁) (subst (Subst.up (Subst.up σ)) t₂)
  | _, _, _, unit => unit
  | _, _, σ, letUnit t₁ t₂ => letUnit (subst σ t₁) (subst σ t₂)
  | _, _, σ, box r t => box r (subst σ t)
  | _, _, σ, letBox t₁ t₂ => letBox (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, pack t => pack (subst σ t)
  | _, _, σ, unpack t₁ t₂ => unpack (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, share r t => share r (subst σ t)
  | _, _, σ, clone t₁ t₂ => clone (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, withBorrow t₁ t₂ => withBorrow (subst σ t₁) (subst σ t₂)
  | _, _, σ, split t => split (subst σ t)
  | _, _, σ, join t₁ t₂ => join (subst σ t₁) (subst σ t₂)
  | _, _, σ, push t => push (subst σ t)
  | _, _, σ, pull t => pull (subst σ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, σ, star t => star (subst σ t)
  | _, _, σ, unborrow t => unborrow (subst σ t)
  | _, _, _, ref a => ref a

/-- Single substitution `t [s / x]` of `s` for the variable `x = 0` bound in `t`. -/
def subst1 {n : ℕ} (s : Term R n) (t : Term R (n + 1)) : Term R n :=
  subst (Fin.cons s var) t

/-! ## Basic laws -/

lemma rename_id {n : ℕ} (t : Term R n) : rename id t = t := by
  induction t <;> simp only [rename, Ren.up_id, id_eq, *]

lemma rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Term R n) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m k <;> simp only [rename, Ren.up_comp, Function.comp_apply, *]

lemma Subst.up_var {n : ℕ} : Subst.up (var : Fin n → Term R n) = var := by
  funext i; cases i using Fin.cases <;> rfl

lemma subst_var {n : ℕ} (t : Term R n) : subst var t = t := by
  induction t <;> simp only [subst, Subst.up_var, *]

lemma Subst.up_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    Subst.up (var ∘ ρ : Fin n → Term R m) = var ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

/-- A renaming is a substitution by variables. -/
lemma subst_ren {n m : ℕ} (ρ : Fin n → Fin m) (t : Term R n) :
    subst (var ∘ ρ) t = rename ρ t := by
  induction t generalizing m <;> simp only [subst, rename, Subst.up_ren, Function.comp_apply, *]

lemma Subst.up_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term R k) :
    Subst.up (σ ∘ ρ) = Subst.up σ ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

lemma subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term R k) (t : Term R n) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m k <;>
    simp only [subst, rename, Subst.up_rename, Function.comp_apply, *]

lemma Subst.up_rename' {n m k : ℕ} (σ : Fin n → Term R m) (ρ : Fin m → Fin k) :
    Subst.up (rename ρ ∘ σ) = rename (Ren.up ρ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp only [Subst.up, Function.comp_apply, Fin.cases_succ, rename_rename]; rfl

lemma rename_subst {n m k : ℕ} (σ : Fin n → Term R m) (ρ : Fin m → Fin k) (t : Term R n) :
    rename ρ (subst σ t) = subst (rename ρ ∘ σ) t := by
  induction t generalizing m k <;>
    simp only [subst, rename, Subst.up_rename', Function.comp_apply, *]

lemma Subst.up_comp {n m k : ℕ} (σ : Fin n → Term R m) (τ : Fin m → Term R k) :
    Subst.up (subst τ ∘ σ) = subst (Subst.up τ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp only [Function.comp, Subst.up_succ, rename_subst, subst_rename]
    rfl

lemma subst_subst {n m k : ℕ} (σ : Fin n → Term R m) (τ : Fin m → Term R k) (t : Term R n) :
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t generalizing m k <;> simp only [subst, Subst.up_comp, Function.comp_apply, *]

/-- Substituting into a weakened term has no effect. -/
@[simp] lemma subst1_rename_succ {n : ℕ} (s t : Term R n) :
    subst1 s (rename Fin.succ t) = t := by
  simp only [subst1, subst_rename]
  conv_rhs => rw [← subst_var t]
  rfl

/-! ## Runtime references -/

/-- The set `refs(t)` of runtime references occurring in a term. -/
def refs : {n : ℕ} → Term R n → Finset ℕ
  | _, var _ => ∅
  | _, lam t => refs t
  | _, app t₁ t₂ => refs t₁ ∪ refs t₂
  | _, pair t₁ t₂ => refs t₁ ∪ refs t₂
  | _, letPair t₁ t₂ => refs t₁ ∪ refs t₂
  | _, unit => ∅
  | _, letUnit t₁ t₂ => refs t₁ ∪ refs t₂
  | _, box _ t => refs t
  | _, letBox t₁ t₂ => refs t₁ ∪ refs t₂
  | _, pack t => refs t
  | _, unpack t₁ t₂ => refs t₁ ∪ refs t₂
  | _, share _ t => refs t
  | _, clone t₁ t₂ => refs t₁ ∪ refs t₂
  | _, withBorrow t₁ t₂ => refs t₁ ∪ refs t₂
  | _, split t => refs t
  | _, join t₁ t₂ => refs t₁ ∪ refs t₂
  | _, push t => refs t
  | _, pull t => refs t
  | _, nat _ => ∅
  | _, float _ => ∅
  | _, prim _ => ∅
  | _, star t => refs t
  | _, unborrow t => refs t
  | _, ref a => {a}

/-- Renaming of runtime references `θ(t)`. -/
def renameRefs (θ : ℕ → ℕ) : {n : ℕ} → Term R n → Term R n
  | _, var i => var i
  | _, lam t => lam (renameRefs θ t)
  | _, app t₁ t₂ => app (renameRefs θ t₁) (renameRefs θ t₂)
  | _, pair t₁ t₂ => pair (renameRefs θ t₁) (renameRefs θ t₂)
  | _, letPair t₁ t₂ => letPair (renameRefs θ t₁) (renameRefs θ t₂)
  | _, unit => unit
  | _, letUnit t₁ t₂ => letUnit (renameRefs θ t₁) (renameRefs θ t₂)
  | _, box r t => box r (renameRefs θ t)
  | _, letBox t₁ t₂ => letBox (renameRefs θ t₁) (renameRefs θ t₂)
  | _, pack t => pack (renameRefs θ t)
  | _, unpack t₁ t₂ => unpack (renameRefs θ t₁) (renameRefs θ t₂)
  | _, share r t => share r (renameRefs θ t)
  | _, clone t₁ t₂ => clone (renameRefs θ t₁) (renameRefs θ t₂)
  | _, withBorrow t₁ t₂ => withBorrow (renameRefs θ t₁) (renameRefs θ t₂)
  | _, split t => split (renameRefs θ t)
  | _, join t₁ t₂ => join (renameRefs θ t₁) (renameRefs θ t₂)
  | _, push t => push (renameRefs θ t)
  | _, pull t => pull (renameRefs θ t)
  | _, nat k => nat k
  | _, float x => float x
  | _, prim p => prim p
  | _, star t => star (renameRefs θ t)
  | _, unborrow t => unborrow (renameRefs θ t)
  | _, ref a => ref (θ a)

/-- Renaming variables does not change the references of a term. -/
@[simp] lemma refs_rename {n m : ℕ} (ρ : Fin n → Fin m) (t : Term R n) :
    (rename ρ t).refs = t.refs := by
  induction t generalizing m <;> simp only [rename, refs, *]

end Term

end FOFU
