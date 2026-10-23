module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypeSubst
public import RequestProject.Common.Grades.PreorderedSemiring
public import RequestProject.Common.Ctx

/-!
# Typing contexts, context addition and scalar multiplication (Section 3, §6.1)

Contexts of the paper,

  `Γ ::= ∅ | Γ, x : A | Γ, x : [A]_r | Γ, id`            (§3)
  `    | Γ, ref : Res_id A`                                (§6.1, runtime),

are represented as follows.

* The identifiers `id` of `Γ` are the `k` bound identifiers of the scope: the types of a
  context `TCtx R k n ρ` are `Ty R k`.  Extending `Γ` with an identifier is
  `TCtx.shiftNames` (all types are weakened).
* The `n` term variables and the `ρ` runtime references each get an optional assumption;
  both are length-indexed lists (`Ctx` from `RequestProject/Common/Ctx.lean`), so
  `Γ.vars.get i` is the assumption on the variable `i` (`none` if `i` is not in the
  paper's context).  Assumptions on variables are linear (`Assm.lin A`, `x : A`) or graded
  (`Assm.grd A r`, `x : [A]_r`); assumptions on references are `ref : Res_id A`
  (`RefTy`).

Context addition `Γ₁ + Γ₂` (§3, extended in §6.1) is partial, so it is the relation
`CtxAdd Γ₁ Γ₂ Γ`, the pointwise lifting (`Ctx.Forall₃`) of

* `none + a = a + none = a`;
* `(x : [A]_r) + (x : [A]_s) = (x : [A]_(r + s))`;
* a linear assumption may not occur on both sides;
* references: `ref : T` may occur on either side or on both (with the same type).

Scalar multiplication `r · Γ` (§3) is the partial relation `CtxScale r Γ Γ'`: it scales
graded assumptions, keeps references, and is undefined on linear assumptions.

`TCtx.IsZero Γ` says that `Γ` has the form `0 · Γ'`: every variable is absent or graded
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
  id : Var k
  /-- the type `A` of the contents -/
  ty : Ty R k

/-- The type `Res_id A` denoted by a reference assumption. -/
def RefTy.toTy {k : ℕ} (T : RefTy R k) : Ty R k := Ty.res T.kind T.id T.ty

/-- Renaming the identifiers of an assumption. -/
def Assm.ren {k k' : ℕ} (r : Var k → Var k') : Assm R k → Assm R k'
  | lin A => lin (A.ren r)
  | grd A s => grd (A.ren r) s

/-- Renaming the identifiers of a reference assumption. -/
def RefTy.ren {k k' : ℕ} (r : Var k → Var k') (T : RefTy R k) : RefTy R k' :=
  ⟨T.kind, r T.id, T.ty.ren r⟩

@[simp] lemma Assm.ren_lin {k k' : ℕ} (r : Var k → Var k') (A : Ty R k) :
    (Assm.lin A).ren r = .lin (A.ren r) := rfl
@[simp] lemma Assm.ren_grd {k k' : ℕ} (r : Var k → Var k') (A : Ty R k) (s : R) :
    (Assm.grd A s).ren r = .grd (A.ren r) s := rfl
@[simp] lemma RefTy.toTy_ren {k k' : ℕ} (r : Var k → Var k') (T : RefTy R k) :
    (T.ren r).toTy = T.toTy.ren r := rfl

lemma Assm.ren_ren {k k' k'' : ℕ} (r : Var k → Var k') (r' : Var k' → Var k'') (a : Assm R k) :
    (a.ren r).ren r' = a.ren (r' ∘ r) := by
  cases a <;> simp [Assm.ren, Ty.ren_ren]

lemma RefTy.ren_ren {k k' k'' : ℕ} (r : Var k → Var k') (r' : Var k' → Var k'')
    (T : RefTy R k) : (T.ren r).ren r' = T.ren (r' ∘ r) := by
  simp [RefTy.ren, Ty.ren_ren]

@[simp] lemma Assm.ren_id {k : ℕ} (a : Assm R k) : a.ren id = a := by
  cases a <;> simp [Assm.ren]

@[simp] lemma RefTy.ren_id {k : ℕ} (T : RefTy R k) : T.ren _root_.id = T := by
  simp [RefTy.ren]

/-- Typing contexts with `k` identifiers, `n` term variables and `ρ` runtime references
in scope. -/
structure TCtx (R : Type) (k n ρ : ℕ) where
  /-- assumptions `ref : Res_id A` on the runtime references -/
  refs : Ctx (Option (RefTy R k)) ρ
  /-- assumptions on the term variables (`none` if the variable is not in the context) -/
  vars : Ctx (Option (Assm R k)) n

section Algebra

variable [Grades.PreorderedSemiring R] {k n ρ : ℕ}

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
structure CtxAdd (Γ₁ Γ₂ Γ : TCtx R k n ρ) : Prop where
  refs : Ctx.Forall₃ RefAdd Γ₁.refs Γ₂.refs Γ.refs
  vars : Ctx.Forall₃ AssmAdd Γ₁.vars Γ₂.vars Γ.vars

/-- Pointwise scalar multiplication on variable assumptions (undefined on linear
assumptions). -/
inductive AssmScale (r : R) : Option (Assm R k) → Option (Assm R k) → Prop where
  | none : AssmScale r none none
  | grd (A : Ty R k) (s : R) : AssmScale r (some (.grd A s)) (some (.grd A (r * s)))

/-- Scalar multiplication `r · Γ = Γ'` (partial: undefined if `Γ` contains a linear
assumption); references are preserved. -/
structure CtxScale (r : R) (Γ Γ' : TCtx R k n ρ) : Prop where
  refs : Γ'.refs = Γ.refs
  vars : Ctx.Forall₂ (AssmScale r) Γ.vars Γ'.vars

/-- An assumption that is absent or graded by `0`. -/
inductive ZeroAssm : Option (Assm R k) → Prop where
  /-- no assumption -/
  | none : ZeroAssm none
  /-- a graded assumption `x : [A]_0` -/
  | grd (A : Ty R k) : ZeroAssm (some (.grd A 0))

@[simp] lemma zeroAssm_none : ZeroAssm (none : Option (Assm R k)) := .none
@[simp] lemma not_zeroAssm_lin (A : Ty R k) : ¬ ZeroAssm (some (.lin A)) := nofun
lemma ZeroAssm.elim {A : Ty R k} {P : Prop} (h : ZeroAssm (some (.lin A))) : P := nomatch h
@[simp] lemma zeroAssm_grd_iff {A : Ty R k} {r : R} : ZeroAssm (some (.grd A r)) ↔ r = 0 :=
  ⟨fun | .grd _ => rfl, fun h => h ▸ .grd A⟩

/-- `Γ` has the form `0 · Γ'`: every variable is absent or graded by `0`. -/
def TCtx.IsZero (Γ : TCtx R k n ρ) : Prop := Γ.vars.All ZeroAssm

end Algebra

namespace TCtx

variable {k k' n ρ : ℕ}

/-- The empty context `∅` in a scope of `n` variables and `ρ` references: no variable and
no reference has an assumption. -/
def empty : TCtx R k n ρ := ⟨.replicate ρ none, .replicate n none⟩

/-- Extending a context by a new variable `Var.zero` (going under a binder). -/
def cons (Γ : TCtx R k n ρ) (a : Option (Assm R k)) : TCtx R k (n + 1) ρ := ⟨Γ.refs, Γ.vars ,, a⟩

/-- Replacing the assumption on variable `i`. -/
def setVar (Γ : TCtx R k n ρ) (i : Var n) (a : Option (Assm R k)) : TCtx R k n ρ :=
  ⟨Γ.refs, Γ.vars.set i a⟩

/-- The runtime part `γ` of a context: only its references. -/
def refsOnly (Γ : TCtx R k n ρ) : TCtx R k n ρ := ⟨Γ.refs, .replicate n none⟩

/-- Renaming the identifiers in all the types of a context. -/
def renNames (r : Var k → Var k') (Γ : TCtx R k n ρ) : TCtx R k' n ρ :=
  ⟨Γ.refs.map (Option.map (RefTy.ren r)), Γ.vars.map (Option.map (Assm.ren r))⟩

/-- Extending the context with a new identifier `Γ, id` (all types are shifted). -/
def shiftNames (Γ : TCtx R k n ρ) : TCtx R (k + 1) n ρ := Γ.renNames Var.succ

@[simp] lemma empty_refs : (empty : TCtx R k n ρ).refs = .replicate ρ none := rfl
@[simp] lemma empty_vars : (empty : TCtx R k n ρ).vars = .replicate n none := rfl
@[simp] lemma cons_refs (Γ : TCtx R k n ρ) (a : Option (Assm R k)) : (Γ.cons a).refs = Γ.refs :=
  rfl
@[simp] lemma cons_vars (Γ : TCtx R k n ρ) (a : Option (Assm R k)) :
    (Γ.cons a).vars = Γ.vars ,, a := rfl
@[simp] lemma setVar_refs (Γ : TCtx R k n ρ) (i : Var n) (a : Option (Assm R k)) :
    (Γ.setVar i a).refs = Γ.refs := rfl
@[simp] lemma setVar_vars (Γ : TCtx R k n ρ) (i : Var n) (a : Option (Assm R k)) :
    (Γ.setVar i a).vars = Γ.vars.set i a := rfl
@[simp] lemma refsOnly_refs (Γ : TCtx R k n ρ) : Γ.refsOnly.refs = Γ.refs := rfl
@[simp] lemma refsOnly_vars (Γ : TCtx R k n ρ) : Γ.refsOnly.vars = .replicate n none := rfl
@[simp] lemma renNames_refs (r : Var k → Var k') (Γ : TCtx R k n ρ) :
    (Γ.renNames r).refs = Γ.refs.map (Option.map (RefTy.ren r)) := rfl
@[simp] lemma renNames_vars (r : Var k → Var k') (Γ : TCtx R k n ρ) :
    (Γ.renNames r).vars = Γ.vars.map (Option.map (Assm.ren r)) := rfl

lemma ext {Γ Δ : TCtx R k n ρ} (hr : Γ.refs = Δ.refs) (hv : Γ.vars = Δ.vars) : Γ = Δ := by
  cases Γ; cases Δ; cases hr; cases hv; rfl

lemma ext_iff' {Γ Δ : TCtx R k n ρ} : Γ = Δ ↔ Γ.refs = Δ.refs ∧ Γ.vars = Δ.vars :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => ext h₁ h₂⟩

end TCtx

end FOFU
