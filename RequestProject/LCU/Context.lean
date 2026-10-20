module
public import RequestProject.LCU.Syntax

/-!
# Typing contexts of the LCU calculus

The paper's contexts are `Γ ::= ∅ | Γ, x : A | Γ, x : [A]`, i.e. each variable is
either absent, a linear assumption `x : A`, or a non-linear assumption `x : [A]`.
Since we use de Bruijn indices, a context for `Term n` assigns to each of the `n`
variables an optional hypothesis (`none` meaning that the variable does not occur in
the paper's context).  Runtime array references `a` (Section 3.4) form a separate
syntactic category of names; we index them by natural numbers, so a context is a
function `Fin n ⊕ ℕ → Option Hyp`.
-/

@[expose] public section

namespace LCU

/-- A hypothesis: linear `x : A` or non-linear `x : [A]`.
For an array reference `a`, the type stored is the element type, i.e.
`a ↦ lin A` means `a : Array A`. -/
inductive Hyp where
  | lin : Ty → Hyp
  | nonlin : Ty → Hyp
  deriving DecidableEq, Repr

/-- The type of a hypothesis. -/
def Hyp.ty : Hyp → Ty
  | .lin A => A
  | .nonlin A => A

/-- An optional hypothesis is *non-linear* if it is absent or of the form `[A]`. -/
def NonLin : Option Hyp → Prop
  | some (.lin _) => False
  | _ => True

@[simp] lemma nonLin_none : NonLin none := trivial
@[simp] lemma nonLin_nonlin (A : Ty) : NonLin (some (.nonlin A)) := trivial
@[simp] lemma not_nonLin_lin (A : Ty) : ¬ NonLin (some (.lin A)) := id

/-- Pointwise context addition (Definition 2): the union of two hypotheses is
defined if one of them is absent, or if both are the same non-linear
assumption `[A]`. -/
inductive HypAdd : Option Hyp → Option Hyp → Option Hyp → Prop where
  | noneLeft (h : Option Hyp) : HypAdd none h h
  | noneRight (h : Hyp) : HypAdd (some h) none (some h)
  | nonlin (A : Ty) : HypAdd (some (.nonlin A)) (some (.nonlin A)) (some (.nonlin A))

/-- Typing contexts: an optional hypothesis for each de Bruijn variable `Sum.inl i`
and for each array reference `Sum.inr a`. -/
def Ctx (n : ℕ) : Type := Fin n ⊕ ℕ → Option Hyp

namespace Ctx

variable {n : ℕ}

/-- The empty context `∅`. -/
def empty : Ctx n := fun _ => none

/-- The context `Γ` with no variable assumptions, keeping its array references. -/
def refsOnly (Γ : Ctx n) : Ctx n := Sum.elim (fun _ => none) (fun a => Γ (.inr a))

/-- Context extension `Γ, x : h` with a new variable `x` (de Bruijn index `0`). -/
def cons (Γ : Ctx n) (h : Option Hyp) : Ctx (n + 1) :=
  Sum.elim (Fin.cons h (fun i => Γ (.inl i))) (fun a => Γ (.inr a))

/-- Update the hypothesis of a single name. -/
def set (Γ : Ctx n) (x : Fin n ⊕ ℕ) (h : Option Hyp) : Ctx n := Function.update Γ x h

/-- Context addition `Γ₁ + Γ₂ = Γ` (Definition 2), as a relation (the operation is
partial). -/
def Add (Γ₁ Γ₂ Γ : Ctx n) : Prop := ∀ x, HypAdd (Γ₁ x) (Γ₂ x) (Γ x)

/-- `[Γ]`: all assumptions in `Γ` are non-linear (Definition 1). -/
def AllNonLin (Γ : Ctx n) : Prop := ∀ x, NonLin (Γ x)

/-- All *variable* assumptions in `Γ` are non-linear. -/
def VarsNonLin (Γ : Ctx n) : Prop := ∀ i, NonLin (Γ (.inl i))

@[simp] lemma empty_apply (x : Fin n ⊕ ℕ) : (empty : Ctx n) x = none := rfl
@[simp] lemma refsOnly_inl (Γ : Ctx n) (i : Fin n) : Γ.refsOnly (.inl i) = none := rfl
@[simp] lemma refsOnly_inr (Γ : Ctx n) (a : ℕ) : Γ.refsOnly (.inr a) = Γ (.inr a) := rfl
@[simp] lemma cons_inl_zero (Γ : Ctx n) (h : Option Hyp) : Γ.cons h (.inl 0) = h := rfl
@[simp] lemma cons_inl_succ (Γ : Ctx n) (h : Option Hyp) (i : Fin n) :
    Γ.cons h (.inl i.succ) = Γ (.inl i) := rfl
@[simp] lemma cons_inr (Γ : Ctx n) (h : Option Hyp) (a : ℕ) :
    Γ.cons h (.inr a) = Γ (.inr a) := rfl
@[simp] lemma set_same (Γ : Ctx n) (x : Fin n ⊕ ℕ) (h : Option Hyp) : Γ.set x h x = h := by
  simp [set]
lemma set_ne (Γ : Ctx n) {x y : Fin n ⊕ ℕ} (h : Option Hyp) (hxy : y ≠ x) :
    Γ.set x h y = Γ y := by
  simp [set, hxy]

end Ctx

end LCU
