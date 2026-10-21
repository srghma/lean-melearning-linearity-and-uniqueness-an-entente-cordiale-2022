module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypeSubst
public import RequestProject.Common.Grades.PreorderedSemiring
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Typing contexts, context addition and scalar multiplication (Section 3, §6.1)

Contexts of the paper,

  `Γ ::= ∅ | Γ, x : A | Γ, x : [A]_r | Γ, id`            (§3)
  `    | Γ, ref : Res_id A`                                (§6.1, runtime),

are represented as follows.

* The identifiers `id` of `Γ` are the `k` bound identifiers of the scope: a context is a
  `Ctx R k n`, and the types it contains are `Ty R k`.  Extending `Γ` with an
  identifier is `Ctx.shiftNames` (all types are weakened).
* The term variables are de Bruijn indices `Fin n`; `Γ.vars i` is the assumption on
  variable `i`, or `none` if `i` is not in the context.  Assumptions are linear
  (`Assm.lin A`, `x : A`) or graded (`Assm.grd A r`, `x : [A]_r`).
* Runtime references are named by natural numbers; `Γ.refs a` is the assumption
  `a : Res_id A` (a `RefTy`), if any.

Context addition `Γ₁ + Γ₂` (§3, extended in §6.1) is partial, so it is the relation
`CtxAdd Γ₁ Γ₂ Γ`, defined pointwise:

* `none + a = a + none = a`;
* `(x : [A]_r) + (x : [A]_s) = (x : [A]_(r + s))`;
* a linear assumption may not occur on both sides;
* references: `ref : T` may occur on either side or on both (with the same type).

Scalar multiplication `r · Γ` (§3) is the partial relation `CtxScale r Γ Γ'`: it scales
graded assumptions, keeps references, and is undefined on linear assumptions.

`Ctx.IsZero Γ` says that `Γ` has the form `0 · Γ'`: every variable is absent or graded
by `0` (references are arbitrary).

Grades are elements of a `Grades.PreorderedSemiring`, a class shared with the
formalisation of *Linearity and Uniqueness* (`RequestProject/Common/Grades/`).
-/

@[expose] public section

namespace FOFU

variable {R : Type}

/-- Assumptions on term variables: linear `x : A` or graded `x : [A]_r`. -/
inductive Assm (R : Type) (k : ℕ) where
  /-- a linear assumption `x : A` -/
  | lin : Ty R k → Assm R k
  /-- a graded assumption `x : [A]_r` -/
  | grd : Ty R k → R → Assm R k

/-- The type `Res_id A` of a runtime reference assumption `ref : Res_id A`. -/
structure RefTy (R : Type) (k : ℕ) where
  /-- the kind of resource (`Array` or `Ref`) -/
  kind : ResKind
  /-- the identifier `id` of the resource -/
  id : Ident k
  /-- the type `A` of the contents -/
  ty : Ty R k

/-- The type `Res_id A` denoted by a reference assumption. -/
def RefTy.toTy {k : ℕ} (T : RefTy R k) : Ty R k := Ty.res T.kind T.id T.ty

/-- Typing contexts with `k` identifiers in scope and `n` term variables. -/
@[ext] structure Ctx (R : Type) (k n : ℕ) where
  /-- assumptions on term variables (`none` if the variable is not in the context) -/
  vars : Fin n → Option (Assm R k)
  /-- assumptions `ref : Res_id A` on runtime references -/
  refs : ℕ → Option (RefTy R k)

namespace Assm

variable {k k' : ℕ}

/-- Applying an identifier substitution to an assumption. -/
def subst (σ : Fin k → Ident k') : Assm R k → Assm R k'
  | lin A => lin (A.subst σ)
  | grd A r => grd (A.subst σ) r

end Assm

/-- Applying an identifier substitution to a reference assumption. -/
def RefTy.subst {k k' : ℕ} (σ : Fin k → Ident k') (T : RefTy R k) : RefTy R k' :=
  ⟨T.kind, T.id.subst σ, T.ty.subst σ⟩

section Algebra

variable [Grades.PreorderedSemiring R] {k n : ℕ}

/-- Pointwise context addition on variable assumptions. -/
inductive AssmAdd : Option (Assm R k) → Option (Assm R k) → Option (Assm R k) → Prop where
  | noneLeft (a : Option (Assm R k)) : AssmAdd none a a
  | noneRight (a : Assm R k) : AssmAdd (some a) none (some a)
  | grd (A : Ty R k) (r s : R) :
      AssmAdd (some (.grd A r)) (some (.grd A s)) (some (.grd A (r + s)))

/-- Pointwise context addition on reference assumptions. -/
inductive RefAdd : Option (RefTy R k) → Option (RefTy R k) → Option (RefTy R k) → Prop where
  | noneLeft (a : Option (RefTy R k)) : RefAdd none a a
  | noneRight (T : RefTy R k) : RefAdd (some T) none (some T)
  | both (T : RefTy R k) : RefAdd (some T) (some T) (some T)

/-- Context addition `Γ₁ + Γ₂ = Γ` (a partial operation, hence a relation). -/
structure CtxAdd (Γ₁ Γ₂ Γ : Ctx R k n) : Prop where
  vars : ∀ i, AssmAdd (Γ₁.vars i) (Γ₂.vars i) (Γ.vars i)
  refs : ∀ a, RefAdd (Γ₁.refs a) (Γ₂.refs a) (Γ.refs a)

/-- Pointwise scalar multiplication on variable assumptions (undefined on linear
assumptions). -/
inductive AssmScale (r : R) : Option (Assm R k) → Option (Assm R k) → Prop where
  | none : AssmScale r none none
  | grd (A : Ty R k) (s : R) : AssmScale r (some (.grd A s)) (some (.grd A (r * s)))

/-- Scalar multiplication `r · Γ = Γ'` (partial: undefined if `Γ` contains a linear
assumption); references are preserved. -/
structure CtxScale (r : R) (Γ Γ' : Ctx R k n) : Prop where
  vars : ∀ i, AssmScale r (Γ.vars i) (Γ'.vars i)
  refs : Γ'.refs = Γ.refs

/-- An assumption that is absent or graded by `0`. -/
def ZeroAssm : Option (Assm R k) → Prop
  | none => True
  | some (.lin _) => False
  | some (.grd _ r) => r = 0

/-- `Γ` has the form `0 · Γ'`: every variable is absent or graded by `0`. -/
def Ctx.IsZero (Γ : Ctx R k n) : Prop := ∀ i, ZeroAssm (Γ.vars i)

end Algebra

/-- If the left summand has a reference assumption, so does the sum. -/
lemma RefAdd.ne_none_left {k : ℕ} {x y z : Option (RefTy R k)} (h : RefAdd x y z)
    (hx : x ≠ none) : z ≠ none := by
  cases h <;> simp_all

/-- If the right summand has a reference assumption, so does the sum. -/
lemma RefAdd.ne_none_right {k : ℕ} {x y z : Option (RefTy R k)} (h : RefAdd x y z)
    (hy : y ≠ none) : z ≠ none := by
  cases h <;> simp_all


namespace Ctx

variable {k k' n : ℕ}

/-- The empty context `∅` (no variables, no references). -/
def empty : Ctx R k 0 := ⟨Fin.elim0, fun _ => none⟩

/-- The context with `n` variables, none of which has an assumption, and no references
(the empty context in a scope of `n` variables). -/
def none (n : ℕ) : Ctx R k n := ⟨fun _ => Option.none, fun _ => Option.none⟩

/-- Extending a context by a new variable `0` (going under a binder). -/
def cons (a : Option (Assm R k)) (Γ : Ctx R k n) : Ctx R k (n + 1) :=
  ⟨Fin.cons a Γ.vars, Γ.refs⟩

/-- Extending a context by a new last variable (as a heap grows). -/
def snoc (Γ : Ctx R k n) (a : Option (Assm R k)) : Ctx R k (n + 1) :=
  ⟨Fin.snoc Γ.vars a, Γ.refs⟩

/-- Replacing the assumption on variable `i`. -/
def update (Γ : Ctx R k n) (i : Fin n) (a : Option (Assm R k)) : Ctx R k n :=
  ⟨Function.update Γ.vars i a, Γ.refs⟩

/-- Adding the reference assumption `ref : T`. -/
def addRef (Γ : Ctx R k n) (a : ℕ) (T : RefTy R k) : Ctx R k n :=
  ⟨Γ.vars, Function.update Γ.refs a (some T)⟩

/-- The runtime part `γ` of a context: only its references. -/
def refsOnly (Γ : Ctx R k n) : Ctx R k n := ⟨fun _ => Option.none, Γ.refs⟩

/-- Applying an identifier substitution to all the types of a context. -/
def substNames (σ : Fin k → Ident k') (Γ : Ctx R k n) : Ctx R k' n :=
  ⟨fun i => (Γ.vars i).map (Assm.subst σ), fun a => (Γ.refs a).map (RefTy.subst σ)⟩

/-- Extending the context with a new identifier `Γ, id` (all types are shifted). -/
def shiftNames (Γ : Ctx R k n) : Ctx R (k + 1) n := Γ.substNames (fun i => Ident.bound i.succ)

@[simp] lemma cons_vars_zero (a : Option (Assm R k)) (Γ : Ctx R k n) :
    (Γ.cons a).vars 0 = a := rfl
@[simp] lemma cons_vars_succ (a : Option (Assm R k)) (Γ : Ctx R k n) (i : Fin n) :
    (Γ.cons a).vars i.succ = Γ.vars i := rfl
@[simp] lemma cons_refs (a : Option (Assm R k)) (Γ : Ctx R k n) : (Γ.cons a).refs = Γ.refs := rfl
@[simp] lemma snoc_refs (a : Option (Assm R k)) (Γ : Ctx R k n) : (Γ.snoc a).refs = Γ.refs := rfl
@[simp] lemma update_refs (Γ : Ctx R k n) (i : Fin n) (a : Option (Assm R k)) :
    (Γ.update i a).refs = Γ.refs := rfl
@[simp] lemma refsOnly_refs (Γ : Ctx R k n) : Γ.refsOnly.refs = Γ.refs := rfl
@[simp] lemma refsOnly_vars (Γ : Ctx R k n) (i : Fin n) : Γ.refsOnly.vars i = Option.none := rfl
@[simp] lemma none_vars (i : Fin n) : (Ctx.none n : Ctx R k n).vars i = Option.none := rfl
@[simp] lemma none_refs (a : ℕ) : (Ctx.none n : Ctx R k n).refs a = Option.none := rfl

end Ctx

end FOFU
