module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Ring.Defs

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

## Contents

* `Ty`, `Prim`, `Term n`: the (extended) types, primitives and terms;
* `CoreTy`, `CoreTerm n`: the core grammars of Section 3.1, as separate inductive
  types embedded into `Ty` / `Term n`.

Renaming and substitution are defined in `RenameSubst.lean`.
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

end LCU
