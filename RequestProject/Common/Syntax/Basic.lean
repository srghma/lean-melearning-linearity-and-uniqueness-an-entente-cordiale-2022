module
public import RequestProject.Common.Var

/-!
# Generic binding layer: signatures and terms

Signatures `Sig`, the terms `Tm S n` over a signature with their argument lists
`Args S n ks`, and injectivity of the constructors.  See `RequestProject/Common/Syntax.lean`
for an overview of the binding layer.
-/

@[expose] public section

namespace Binding

/-- A signature: operators with the binding arities of their arguments. -/
structure Sig where
  /-- the operators (constructors) of the syntax, possibly carrying data -/
  Op : Type
  /-- `arity o = [k₁, …, kₘ]`: `o` has `m` arguments, the `j`-th binding `kⱼ` variables -/
  arity : Op → List ℕ

mutual
/-- Terms over the signature `S` with `n` free variables. -/
inductive Tm (S : Sig) : ℕ → Type where
  /-- a variable -/
  | var {n : ℕ} : Var n → Tm S n
  /-- an operator applied to its arguments -/
  | op {n : ℕ} (o : S.Op) : Args S n (S.arity o) → Tm S n

/-- Argument lists: `Args S n ks` is a list of terms, the `j`-th of which lives in scope
`n + kⱼ`. -/
inductive Args (S : Sig) : ℕ → List ℕ → Type where
  | nil {n : ℕ} : Args S n []
  | cons {n k : ℕ} {ks : List ℕ} : Tm S (n + k) → Args S n ks → Args S n (k :: ks)
end

variable {S : Sig}

/-! ## Injectivity -/

lemma Tm.op_heq_iff {n : ℕ} {o o' : S.Op} {as : Args S n (S.arity o)}
    {as' : Args S n (S.arity o')} : Tm.op o as = Tm.op o' as' ↔ o = o' ∧ HEq as as' := by
  constructor
  · intro h; cases h; exact ⟨rfl, HEq.rfl⟩
  · rintro ⟨rfl, h⟩; cases h; rfl

/-- Equality of operator applications (a `simp` lemma: for distinct operators the first
conjunct is decided by the constructors of `S.Op`, for equal ones the second becomes an
equation). -/
@[simp] lemma Tm.op_eq_op_iff {n : ℕ} {o o' : S.Op} {as : Args S n (S.arity o)}
    {as' : Args S n (S.arity o')} : Tm.op o as = Tm.op o' as' ↔ o = o' ∧ HEq as as' :=
  Tm.op_heq_iff

@[simp] lemma Tm.var_inj {n : ℕ} {i j : Var n} : (Tm.var i : Tm S n) = Tm.var j ↔ i = j := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

@[simp] lemma Tm.var_ne_op {n : ℕ} (i : Var n) (o : S.Op) (as : Args S n (S.arity o)) :
    Tm.var i ≠ Tm.op o as := nofun

@[simp] lemma Tm.op_ne_var {n : ℕ} (i : Var n) (o : S.Op) (as : Args S n (S.arity o)) :
    Tm.op o as ≠ Tm.var i := nofun

lemma Tm.op_inj {n : ℕ} {o : S.Op} {as as' : Args S n (S.arity o)} :
    Tm.op o as = Tm.op o as' ↔ as = as' := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

lemma Tm.op_ne_of_ne {n : ℕ} {o o' : S.Op} (h : o ≠ o') (as : Args S n (S.arity o))
    (as' : Args S n (S.arity o')) : Tm.op o as ≠ Tm.op o' as' := by
  intro e; cases e; exact h rfl

@[simp] lemma Args.cons_inj {n k : ℕ} {ks : List ℕ} {t t' : Tm S (n + k)}
    {as as' : Args S n ks} : Args.cons t as = Args.cons t' as' ↔ t = t' ∧ as = as' := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma Args.eq_nil {n : ℕ} (as : Args S n []) : as = .nil := by cases as; rfl

end Binding
