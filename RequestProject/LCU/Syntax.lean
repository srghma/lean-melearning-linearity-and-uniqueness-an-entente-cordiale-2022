module
public import Mathlib

/-!
# The Linear-Cartesian-Unique (LCU) calculus: syntax

Formalisation of Section 3 of *Linearity and Uniqueness: An Entente Cordiale*
(Marshall, Vollmer, Orchard).

Terms are intrinsically scoped and use de Bruijn indices: `Term n` is the type of
terms with (at most) `n` free variables, `Term.var : Fin n → Term n`, so `Term 0`
is the type of closed terms.  Binders bind index `0`.

Besides the core syntax of Section 3.1 the term language also contains the array
extension of Section 3.3 (natural number and float literals and the four array
primitives) and the runtime array references `a` of Section 3.4.
-/

@[expose] public section

namespace LCU

/-- Types `A, B ::= A ⊸ B | A ⊗ B | 1 | !A | *A`, extended (Section 3.3) with
`Array A`, `ℕ` and `𝔽` (floating point numbers). -/
inductive Ty where
  /-- linear functions `A ⊸ B` -/
  | lolli : Ty → Ty → Ty
  /-- multiplicative products `A ⊗ B` -/
  | tensor : Ty → Ty → Ty
  /-- the multiplicative unit `1` -/
  | unit : Ty
  /-- the non-linearity modality `!A` -/
  | bang : Ty → Ty
  /-- the uniqueness modality `*A` -/
  | star : Ty → Ty
  /-- arrays `Array A` -/
  | array : Ty → Ty
  /-- natural numbers `ℕ` (sizes and indices) -/
  | nat : Ty
  /-- floating point values `𝔽` -/
  | float : Ty
  deriving DecidableEq, Repr

@[inherit_doc] infixr:25 " ⊸ " => Ty.lolli
@[inherit_doc] infixr:35 " ⊗ " => Ty.tensor

/-- The array primitives of Section 3.3. -/
inductive Prim where
  | newArray
  | readArray
  | writeArray
  | deleteArray
  deriving DecidableEq, Repr

/-- Terms of the LCU calculus with de Bruijn indices; `Term n` has `n` free variables.

* `lam t` is `λx. t` where `x` is index `0` of `t`;
* `letPair t₁ t₂` is `let (x, y) = t₁ in t₂`, where in `t₂` the variable `y` is
  index `0` and `x` is index `1`;
* `letBang t₁ t₂` is `let! x = t₁ in t₂`;
* `copy t₁ t₂` is `copy t₁ as x in t₂`;
* `borrow t` is `&t`, `bang t` is `!t` and `star t` is `*t`;
* `ref a` is a runtime array reference (Section 3.4). -/
inductive Term : ℕ → Type where
  | var {n : ℕ} : Fin n → Term n
  | lam {n : ℕ} : Term (n + 1) → Term n
  | app {n : ℕ} : Term n → Term n → Term n
  | pair {n : ℕ} : Term n → Term n → Term n
  | letPair {n : ℕ} : Term n → Term (n + 2) → Term n
  | unit {n : ℕ} : Term n
  | letUnit {n : ℕ} : Term n → Term n → Term n
  | bang {n : ℕ} : Term n → Term n
  | letBang {n : ℕ} : Term n → Term (n + 1) → Term n
  | borrow {n : ℕ} : Term n → Term n
  | copy {n : ℕ} : Term n → Term (n + 1) → Term n
  | star {n : ℕ} : Term n → Term n
  | nat {n : ℕ} : ℕ → Term n
  | float {n : ℕ} : Float → Term n
  | prim {n : ℕ} : Prim → Term n
  | ref {n : ℕ} : ℕ → Term n

/-! ## The core grammars of Section 3.1

`Ty` and `Term` contain the extensions of Sections 3.3 and 3.4 (arrays, literals,
primitives and runtime references).  The grammars of the core calculus are given
separately, by construction, together with their embeddings. -/

/-- The core types of Section 3.1: `A, B ::= A ⊸ B | A ⊗ B | 1 | !A | *A`. -/
inductive CoreTy where
  | lolli : CoreTy → CoreTy → CoreTy
  | tensor : CoreTy → CoreTy → CoreTy
  | unit : CoreTy
  | bang : CoreTy → CoreTy
  | star : CoreTy → CoreTy
  deriving DecidableEq, Repr

/-- The embedding of core types into the extended types. -/
@[simp] def CoreTy.toTy : CoreTy → Ty
  | .lolli A B => .lolli A.toTy B.toTy
  | .tensor A B => .tensor A.toTy B.toTy
  | .unit => .unit
  | .bang A => .bang A.toTy
  | .star A => .star A.toTy

lemma CoreTy.toTy_injective : Function.Injective CoreTy.toTy := by
  intro A B h
  induction A generalizing B with
  | lolli A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [CoreTy.toTy, Ty.lolli.injEq, reduceCtorEq] at h
    rw [ih₁ h.1, ih₂ h.2]
  | tensor A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [CoreTy.toTy, Ty.tensor.injEq, reduceCtorEq] at h
    rw [ih₁ h.1, ih₂ h.2]
  | unit => cases B <;> simp_all
  | bang A ih => cases B <;> simp only [CoreTy.toTy, Ty.bang.injEq, reduceCtorEq] at h; rw [ih h]
  | star A ih => cases B <;> simp only [CoreTy.toTy, Ty.star.injEq, reduceCtorEq] at h; rw [ih h]

/-- The core terms of Section 3.1 (with de Bruijn indices):
`t ::= x | λx. t | t₁ t₂ | (t₁, t₂) | let (x, y) = t₁ in t₂ | unit | let unit = t₁ in t₂
     | !t | let! x = t₁ in t₂ | &t | copy t₁ as x in t₂ | *t`. -/
inductive CoreTerm : ℕ → Type where
  | var {n : ℕ} : Fin n → CoreTerm n
  | lam {n : ℕ} : CoreTerm (n + 1) → CoreTerm n
  | app {n : ℕ} : CoreTerm n → CoreTerm n → CoreTerm n
  | pair {n : ℕ} : CoreTerm n → CoreTerm n → CoreTerm n
  | letPair {n : ℕ} : CoreTerm n → CoreTerm (n + 2) → CoreTerm n
  | unit {n : ℕ} : CoreTerm n
  | letUnit {n : ℕ} : CoreTerm n → CoreTerm n → CoreTerm n
  | bang {n : ℕ} : CoreTerm n → CoreTerm n
  | letBang {n : ℕ} : CoreTerm n → CoreTerm (n + 1) → CoreTerm n
  | borrow {n : ℕ} : CoreTerm n → CoreTerm n
  | copy {n : ℕ} : CoreTerm n → CoreTerm (n + 1) → CoreTerm n
  | star {n : ℕ} : CoreTerm n → CoreTerm n

/-- The embedding of core terms into the extended terms. -/
@[simp] def CoreTerm.toTerm : {n : ℕ} → CoreTerm n → Term n
  | _, .var i => .var i
  | _, .lam t => .lam t.toTerm
  | _, .app t₁ t₂ => .app t₁.toTerm t₂.toTerm
  | _, .pair t₁ t₂ => .pair t₁.toTerm t₂.toTerm
  | _, .letPair t₁ t₂ => .letPair t₁.toTerm t₂.toTerm
  | _, .unit => .unit
  | _, .letUnit t₁ t₂ => .letUnit t₁.toTerm t₂.toTerm
  | _, .bang t => .bang t.toTerm
  | _, .letBang t₁ t₂ => .letBang t₁.toTerm t₂.toTerm
  | _, .borrow t => .borrow t.toTerm
  | _, .copy t₁ t₂ => .copy t₁.toTerm t₂.toTerm
  | _, .star t => .star t.toTerm

lemma CoreTerm.toTerm_injective {n : ℕ} : Function.Injective (CoreTerm.toTerm (n := n)) := by
  intro t u h
  induction t with
  | var => cases u <;> simp_all
  | unit => cases u <;> simp_all
  | _ => cases u <;> simp at h ⊢; grind

namespace Term

/-! ## Renaming -/

/-- Lifting a renaming under a binder. -/
def Ren.up {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] lemma Ren.up_zero {n m : ℕ} (ρ : Fin n → Fin m) : Ren.up ρ 0 = 0 := rfl
@[simp] lemma Ren.up_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    Ren.up ρ i.succ = (ρ i).succ := rfl

/-- Simultaneous renaming of free variables. -/
def rename : {n m : ℕ} → (Fin n → Fin m) → Term n → Term m
  | _, _, ρ, var i => var (ρ i)
  | _, _, ρ, lam t => lam (rename (Ren.up ρ) t)
  | _, _, ρ, app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, pair t₁ t₂ => pair (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, letPair t₁ t₂ => letPair (rename ρ t₁) (rename (Ren.up (Ren.up ρ)) t₂)
  | _, _, _, unit => unit
  | _, _, ρ, letUnit t₁ t₂ => letUnit (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, bang t => bang (rename ρ t)
  | _, _, ρ, letBang t₁ t₂ => letBang (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, borrow t => borrow (rename ρ t)
  | _, _, ρ, copy t₁ t₂ => copy (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, star t => star (rename ρ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, _, ref a => ref a

/-! ## Substitution -/

/-- Lifting a substitution under a binder. -/
def Subst.up {n m : ℕ} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (var 0) (fun i => rename Fin.succ (σ i))

@[simp] lemma Subst.up_zero {n m : ℕ} (σ : Fin n → Term m) : Subst.up σ 0 = var 0 := rfl
@[simp] lemma Subst.up_succ {n m : ℕ} (σ : Fin n → Term m) (i : Fin n) :
    Subst.up σ i.succ = rename Fin.succ (σ i) := rfl

/-- Simultaneous (capture-avoiding) substitution of free variables. -/
def subst : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
  | _, _, σ, var i => σ i
  | _, _, σ, lam t => lam (subst (Subst.up σ) t)
  | _, _, σ, app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | _, _, σ, pair t₁ t₂ => pair (subst σ t₁) (subst σ t₂)
  | _, _, σ, letPair t₁ t₂ => letPair (subst σ t₁) (subst (Subst.up (Subst.up σ)) t₂)
  | _, _, _, unit => unit
  | _, _, σ, letUnit t₁ t₂ => letUnit (subst σ t₁) (subst σ t₂)
  | _, _, σ, bang t => bang (subst σ t)
  | _, _, σ, letBang t₁ t₂ => letBang (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, borrow t => borrow (subst σ t)
  | _, _, σ, copy t₁ t₂ => copy (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, star t => star (subst σ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, _, ref a => ref a

/-- Single substitution `[s/x]t` of `s` for the variable `x = 0` bound in `t`. -/
def subst1 {n : ℕ} (s : Term n) (t : Term (n + 1)) : Term n :=
  subst (Fin.cons s var) t

/-- Double substitution `[s₁/x, s₂/y]t` for `t` the body of a `let (x, y) = _ in t`
(so `y` is index `0` and `x` is index `1`). -/
def subst2 {n : ℕ} (s₁ s₂ : Term n) (t : Term (n + 2)) : Term n :=
  subst (Fin.cons s₂ (Fin.cons s₁ var)) t

/-! ## Basic lemmas about renaming and substitution -/

lemma Ren.up_id {n : ℕ} : Ren.up (id : Fin n → Fin n) = id := by
  funext i; cases i using Fin.cases <;> rfl

lemma Ren.up_comp {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    Ren.up (ρ' ∘ ρ) = Ren.up ρ' ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

lemma rename_id {n : ℕ} (t : Term n) : rename id t = t := by
  induction t <;> simp_all [rename, Ren.up_id]

lemma rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Term n) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m k <;> simp_all [rename, Ren.up_comp]

lemma Subst.up_var {n : ℕ} : Subst.up (var : Fin n → Term n) = var := by
  funext i; cases i using Fin.cases <;> rfl

lemma subst_var {n : ℕ} (t : Term n) : subst var t = t := by
  induction t <;> simp_all [subst, Subst.up_var]

lemma Subst.up_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    Subst.up (var ∘ ρ) = var ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

lemma subst_ren {n m : ℕ} (ρ : Fin n → Fin m) (t : Term n) :
    subst (var ∘ ρ) t = rename ρ t := by
  induction t generalizing m <;> simp_all [subst, rename, Subst.up_ren]

lemma Subst.up_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    Subst.up (σ ∘ ρ) = Subst.up σ ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

lemma subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) (t : Term n) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m k <;> simp_all [subst, rename, Subst.up_rename]

lemma Subst.up_rename' {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    Subst.up (rename ρ ∘ σ) = rename (Ren.up ρ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp [Subst.up, rename_rename]; rfl

lemma rename_subst {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) (t : Term n) :
    rename ρ (subst σ t) = subst (rename ρ ∘ σ) t := by
  induction t generalizing m k <;> simp_all [subst, rename, Subst.up_rename']

lemma Subst.up_comp {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) :
    Subst.up (subst τ ∘ σ) = subst (Subst.up τ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp only [Function.comp, Subst.up_succ, rename_subst, subst_rename]
    rfl

lemma subst_subst {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) (t : Term n) :
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t generalizing m k <;> simp_all [subst, Subst.up_comp]

/-- Substituting into a weakened term has no effect. -/
@[simp] lemma subst1_rename_succ {n : ℕ} (s t : Term n) :
    subst1 s (rename Fin.succ t) = t := by
  simp [subst1, subst_rename]
  conv_rhs => rw [← subst_var t]
  rfl

/-- The double substitution is the composition of two single substitutions. -/
lemma subst2_eq {n : ℕ} (s₁ s₂ : Term n) (t : Term (n + 2)) :
    subst2 s₁ s₂ t = subst1 s₁ (subst1 (rename Fin.succ s₂) t) := by
  simp only [subst2, subst1, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact (subst1_rename_succ s₁ s₂).symm
  | succ i =>
    cases i using Fin.cases <;> simp [subst]

end Term

end LCU
