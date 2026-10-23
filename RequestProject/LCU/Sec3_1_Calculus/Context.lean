module
public import RequestProject.LCU.Sec3_1_Calculus.RenameSubst
public import RequestProject.Common.Ctx

/-!
# Typing contexts of the LCU calculus

The paper's contexts are `Γ ::= ∅ | Γ, x : A | Γ, x : [A]`: each variable is absent, a
linear assumption `x : A` or a non-linear assumption `x : [A]`.

## Representation

A typing context for `Term n ρ` is a pair of length-indexed lists (`Ctx` from
`RequestProject/Common/Ctx.lean`):

* `Γ.vars : Ctx (Option (Hyp Ty)) n`, an optional hypothesis for each of the `n`
  variables (`none` means that the variable does not occur in the paper's context);
* `Γ.refs : Ctx (Option (Hyp ArrTy)) ρ`, an optional hypothesis for each of the `ρ`
  runtime array references.  A reference hypothesis is about an *array type*
  `Array A` (`ArrTy.array A`), so that `a : Array A` is `Hyp.lin (.array A)`.

## Main definitions

* `Hyp T`: a hypothesis, linear `x : A` (`Hyp.lin A`) or non-linear `x : [A]`
  (`Hyp.nonlin A`).
* `HypAdd a b c`: pointwise context addition (Definition 2).
* `TCtx.Add Γ₁ Γ₂ Γ`: context addition `Γ₁ + Γ₂ = Γ`, the pointwise lifting of `HypAdd`
  (`Ctx.Forall₃`) to both lists.
* `TCtx.AllNonLin Γ`: `Γ` is of the form `[Γ]` (Definition 1).
* `Γ.cons h`: extension with a new variable `Var.zero`.
* `Γ.refsOnly`: `Γ` without its variable assumptions.
-/

@[expose] public section

namespace LCU

/-! ## Hypotheses -/

/-- A hypothesis about a type `A : T`: linear `x : A` or non-linear `x : [A]`. -/
inductive Hyp (T : Type) where
  | lin : T → Hyp T
  | nonlin : T → Hyp T
  deriving DecidableEq, Repr

/-- The type of a hypothesis. -/
def Hyp.ty {T : Type} : Hyp T → T
  | .lin A => A
  | .nonlin A => A

@[simp] lemma Hyp.ty_lin {T : Type} (A : T) : (Hyp.lin A).ty = A := rfl
@[simp] lemma Hyp.ty_nonlin {T : Type} (A : T) : (Hyp.nonlin A).ty = A := rfl

/-- The types of array references: `Array A`. -/
inductive ArrTy where
  | array : Ty → ArrTy
  deriving DecidableEq, Repr

/-- The array type as a type. -/
def ArrTy.toTy : ArrTy → Ty
  | .array A => .array A

/-- The element type of an array type. -/
def ArrTy.elem : ArrTy → Ty
  | .array A => A

@[simp] lemma ArrTy.toTy_array (A : Ty) : (ArrTy.array A).toTy = .array A := rfl
@[simp] lemma ArrTy.elem_array (A : Ty) : (ArrTy.array A).elem = A := rfl

section
variable {T : Type}

/-- An optional hypothesis is *non-linear* if it is absent or of the form `[A]`. -/
inductive NonLin : Option (Hyp T) → Prop where
  /-- no assumption -/
  | none : NonLin none
  /-- a non-linear assumption `x : [A]` -/
  | nonlin (A : T) : NonLin (some (.nonlin A))

@[simp] lemma nonLin_none : NonLin (none : Option (Hyp T)) := .none
@[simp] lemma nonLin_nonlin (A : T) : NonLin (some (Hyp.nonlin A)) := .nonlin A
@[simp] lemma not_nonLin_lin (A : T) : ¬ NonLin (some (Hyp.lin A)) := nofun
lemma NonLin.elim {A : T} {P : Prop} (h : NonLin (some (Hyp.lin A))) : P := nomatch h

/-- Pointwise context addition (Definition 2): the union of two hypotheses is defined if
one of them is absent, or if both are the same non-linear assumption `[A]`. -/
inductive HypAdd : Option (Hyp T) → Option (Hyp T) → Option (Hyp T) → Prop where
  | noneLeft (h : Option (Hyp T)) : HypAdd none h h
  | noneRight (h : Hyp T) : HypAdd (some h) none (some h)
  | nonlin (A : T) : HypAdd (some (.nonlin A)) (some (.nonlin A)) (some (.nonlin A))

end

/-! ## Typing contexts -/

/-- Typing contexts for terms with `n` variables and `ρ` array references. -/
structure TCtx (n ρ : ℕ) where
  /-- the hypotheses of the array references -/
  refs : Ctx (Option (Hyp ArrTy)) ρ
  /-- the hypotheses of the variables -/
  vars : Ctx (Option (Hyp Ty)) n
  deriving DecidableEq

namespace TCtx

variable {n ρ : ℕ}

/-- The empty context `∅`. -/
def empty : TCtx n ρ := ⟨.replicate ρ none, .replicate n none⟩

/-- The context `Γ` with no variable assumptions, keeping its array references. -/
def refsOnly (Γ : TCtx n ρ) : TCtx n ρ := ⟨Γ.refs, .replicate n none⟩

/-- Context extension `Γ, x : h` with a new variable `x` (`Var.zero`). -/
def cons (Γ : TCtx n ρ) (h : Option (Hyp Ty)) : TCtx (n + 1) ρ := ⟨Γ.refs, Γ.vars ,, h⟩

/-- Update the hypothesis of a variable. -/
def setVar (Γ : TCtx n ρ) (i : Var n) (h : Option (Hyp Ty)) : TCtx n ρ :=
  ⟨Γ.refs, Γ.vars.set i h⟩

/-- Update the hypothesis of an array reference. -/
def setRef (Γ : TCtx n ρ) (a : Var ρ) (h : Option (Hyp ArrTy)) : TCtx n ρ :=
  ⟨Γ.refs.set a h, Γ.vars⟩

/-- Context addition `Γ₁ + Γ₂ = Γ` (Definition 2), as a relation (the operation is
partial): `HypAdd` at every variable and every array reference. -/
structure Add (Γ₁ Γ₂ Γ : TCtx n ρ) : Prop where
  refs : Ctx.Forall₃ HypAdd Γ₁.refs Γ₂.refs Γ.refs
  vars : Ctx.Forall₃ HypAdd Γ₁.vars Γ₂.vars Γ.vars

/-- `[Γ]`: all assumptions in `Γ` are non-linear (Definition 1). -/
structure AllNonLin (Γ : TCtx n ρ) : Prop where
  refs : Γ.refs.All NonLin
  vars : Γ.vars.All NonLin

/-- All *variable* assumptions in `Γ` are non-linear. -/
def VarsNonLin (Γ : TCtx n ρ) : Prop := Γ.vars.All NonLin

@[simp] lemma cons_refs (Γ : TCtx n ρ) (h : Option (Hyp Ty)) : (Γ.cons h).refs = Γ.refs := rfl
@[simp] lemma cons_vars (Γ : TCtx n ρ) (h : Option (Hyp Ty)) : (Γ.cons h).vars = Γ.vars ,, h := rfl
@[simp] lemma refsOnly_refs (Γ : TCtx n ρ) : Γ.refsOnly.refs = Γ.refs := rfl
@[simp] lemma refsOnly_vars (Γ : TCtx n ρ) : Γ.refsOnly.vars = .replicate n none := rfl
@[simp] lemma empty_refs : (empty : TCtx n ρ).refs = .replicate ρ none := rfl
@[simp] lemma empty_vars : (empty : TCtx n ρ).vars = .replicate n none := rfl
@[simp] lemma setVar_refs (Γ : TCtx n ρ) (i : Var n) (h : Option (Hyp Ty)) :
    (Γ.setVar i h).refs = Γ.refs := rfl
@[simp] lemma setVar_vars (Γ : TCtx n ρ) (i : Var n) (h : Option (Hyp Ty)) :
    (Γ.setVar i h).vars = Γ.vars.set i h := rfl
@[simp] lemma setRef_refs (Γ : TCtx n ρ) (a : Var ρ) (h : Option (Hyp ArrTy)) :
    (Γ.setRef a h).refs = Γ.refs.set a h := rfl
@[simp] lemma setRef_vars (Γ : TCtx n ρ) (a : Var ρ) (h : Option (Hyp ArrTy)) :
    (Γ.setRef a h).vars = Γ.vars := rfl

lemma ext {Γ Δ : TCtx n ρ} (hr : Γ.refs = Δ.refs) (hv : Γ.vars = Δ.vars) : Γ = Δ := by
  cases Γ; cases Δ; cases hr; cases hv; rfl

lemma ext_iff' {Γ Δ : TCtx n ρ} : Γ = Δ ↔ Γ.refs = Δ.refs ∧ Γ.vars = Δ.vars :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => ext h₁ h₂⟩

end TCtx

end LCU
