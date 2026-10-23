module
public import RequestProject.Common.Var

/-!
# A generic binding layer: syntax over a signature

Both formalisations of this project use intrinsically scoped de Bruijn syntax.  Instead of
defining renaming and substitution (and proving their laws) once for every term language,
each language is described by a *signature* and the term type is the generic `Tm S n`.

* A signature `S : Sig` is a type of operators `S.Op` together with, for every operator,
  the list of *binding arities* of its arguments: `S.arity o = [k₁, …, kₘ]` means that
  `o` takes `m` arguments and that the `j`-th argument binds `kⱼ` new variables.  For
  instance `let (x, y) = t₁ in t₂` has arity `[0, 2]`.  Operators may carry data
  (grades, literals, primitives, …): these are simply part of `S.Op`.
* `Tm S n` is the type of terms with `n` free variables: a variable `var i` (`i : Var n`)
  or an operator applied to arguments `op o as`, where `as : Args S n (S.arity o)`.
  An argument with binding arity `k` is a term of `Tm S (n + k)`; its new variables are
  `Var.zero, …` (the last bound variable is `Var.zero`).

Generic operations, defined once for all signatures:

* `Tm.ren ρ` (renaming along `ρ : Var n → Var m`) and `Tm.subst σ` (parallel
  substitution along `σ : Var n → Tm S m`), lifted under binders by `Ren.upN` /
  `Subst.upN`;
* the single and double instantiations `t.inst1 s = [s/x]t` and
  `t.inst2 s₁ s₂ = [s₁/x, s₂/y]t`;
* `Tm.mapOp f`, applying an arity-preserving map `f` to every operator (used for example to
  rename runtime names stored in operators);
* `Tm.Occurs i t`, "the variable `i` occurs free in `t`".

Generic laws, proved once (the σ-calculus laws): `ren_id`, `ren_ren`, `subst_var`,
`ren_eq_subst`, `subst_ren`, `ren_subst`, `subst_subst`, and their consequences for
`inst1` / `inst2`, plus commutation of `mapOp` with renaming and substitution and the
behaviour of `Occurs` under renaming.
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

/-! ## Renaming -/

mutual
/-- Parallel renaming of the free variables of a term. -/
def Tm.ren {n m : ℕ} (ρ : Var n → Var m) : Tm S n → Tm S m
  | .var i => .var (ρ i)
  | .op o as => .op o (as.ren ρ)

/-- Parallel renaming of argument lists (each argument is renamed under its binders). -/
def Args.ren {n m : ℕ} {ks : List ℕ} (ρ : Var n → Var m) : Args S n ks → Args S m ks
  | .nil => .nil
  | .cons (k := k) t as => .cons (t.ren (Ren.upN k ρ)) (as.ren ρ)
end

@[simp] lemma Tm.ren_var {n m : ℕ} (ρ : Var n → Var m) (i : Var n) :
    (Tm.var i : Tm S n).ren ρ = .var (ρ i) := rfl
@[simp] lemma Tm.ren_op {n m : ℕ} (ρ : Var n → Var m) (o : S.Op) (as : Args S n (S.arity o)) :
    (Tm.op o as).ren ρ = .op o (as.ren ρ) := rfl
@[simp] lemma Args.ren_nil {n m : ℕ} (ρ : Var n → Var m) : (Args.nil : Args S n []).ren ρ = .nil :=
  rfl
@[simp] lemma Args.ren_cons {n m k : ℕ} {ks : List ℕ} (ρ : Var n → Var m) (t : Tm S (n + k))
    (as : Args S n ks) : (Args.cons t as).ren ρ = .cons (t.ren (Ren.upN k ρ)) (as.ren ρ) := rfl

mutual
theorem Tm.ren_id {n : ℕ} : (t : Tm S n) → t.ren id = t
  | .var _ => rfl
  | .op o as => by rw [Tm.ren_op, Args.ren_id]
theorem Args.ren_id {n : ℕ} {ks : List ℕ} : (as : Args S n ks) → as.ren id = as
  | .nil => rfl
  | .cons t as => by rw [Args.ren_cons, Ren.upN_id, Tm.ren_id, Args.ren_id]
end

@[simp] lemma Tm.ren_id' {n : ℕ} (t : Tm S n) : t.ren (fun i => i) = t := Tm.ren_id t

mutual
theorem Tm.ren_ren {n m l : ℕ} (ρ : Var n → Var m) (ρ' : Var m → Var l) :
    (t : Tm S n) → (t.ren ρ).ren ρ' = t.ren (ρ' ∘ ρ)
  | .var _ => rfl
  | .op o as => by rw [Tm.ren_op, Tm.ren_op, Tm.ren_op, Args.ren_ren]
theorem Args.ren_ren {n m l : ℕ} {ks : List ℕ} (ρ : Var n → Var m) (ρ' : Var m → Var l) :
    (as : Args S n ks) → (as.ren ρ).ren ρ' = as.ren (ρ' ∘ ρ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.ren_cons, Args.ren_cons, Args.ren_cons, Tm.ren_ren, Args.ren_ren, Ren.upN_comp]
end

/-! ## Substitution -/

namespace Subst

/-- Lifting a substitution under a binder. -/
def up {n m : ℕ} (σ : Var n → Tm S m) : Var (n + 1) → Tm S (m + 1) :=
  Var.cons (.var .zero) (fun i => (σ i).ren .succ)

@[simp] lemma up_zero {n m : ℕ} (σ : Var n → Tm S m) : up σ .zero = .var .zero := rfl
@[simp] lemma up_succ {n m : ℕ} (σ : Var n → Tm S m) (i : Var n) :
    up σ (.succ i) = (σ i).ren .succ := rfl

/-- Lifting a substitution under `k` binders. -/
def upN {n m : ℕ} : (k : ℕ) → (Var n → Tm S m) → Var (n + k) → Tm S (m + k)
  | 0, σ => σ
  | k + 1, σ => up (upN k σ)

@[simp] lemma upN_zero {n m : ℕ} (σ : Var n → Tm S m) : upN 0 σ = σ := rfl
@[simp] lemma upN_succ {n m : ℕ} (k : ℕ) (σ : Var n → Tm S m) : upN (k + 1) σ = up (upN k σ) :=
  rfl

lemma up_var {n : ℕ} : up (Tm.var : Var n → Tm S n) = Tm.var := by
  funext i; cases i <;> rfl

lemma upN_var {n : ℕ} : (k : ℕ) → upN k (Tm.var : Var n → Tm S n) = Tm.var
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_var k, up_var]

lemma up_ren {n m : ℕ} (ρ : Var n → Var m) :
    up (Tm.var ∘ ρ : Var n → Tm S m) = Tm.var ∘ Ren.up ρ := by
  funext i; cases i <;> rfl

lemma upN_ren {n m : ℕ} (ρ : Var n → Var m) :
    (k : ℕ) → upN k (Tm.var ∘ ρ : Var n → Tm S m) = Tm.var ∘ Ren.upN k ρ
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_ren ρ k, up_ren]; rfl

lemma up_comp_ren {n m l : ℕ} (ρ : Var n → Var m) (σ : Var m → Tm S l) :
    up (σ ∘ ρ) = up σ ∘ Ren.up ρ := by
  funext i; cases i <;> rfl

lemma upN_comp_ren {n m l : ℕ} (ρ : Var n → Var m) (σ : Var m → Tm S l) :
    (k : ℕ) → upN k (σ ∘ ρ) = upN k σ ∘ Ren.upN k ρ
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_comp_ren ρ σ k, up_comp_ren]; rfl

lemma up_ren_comp {n m l : ℕ} (σ : Var n → Tm S m) (ρ : Var m → Var l) :
    up (Tm.ren ρ ∘ σ) = Tm.ren (Ren.up ρ) ∘ up σ := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp only [Function.comp_apply, up_succ, Tm.ren_ren]; rfl

lemma upN_ren_comp {n m l : ℕ} (σ : Var n → Tm S m) (ρ : Var m → Var l) :
    (k : ℕ) → upN k (Tm.ren ρ ∘ σ) = Tm.ren (Ren.upN k ρ) ∘ upN k σ
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_ren_comp σ ρ k, up_ren_comp]; rfl

end Subst

mutual
/-- Parallel substitution of the free variables of a term. -/
def Tm.subst {n m : ℕ} (σ : Var n → Tm S m) : Tm S n → Tm S m
  | .var i => σ i
  | .op o as => .op o (as.subst σ)

/-- Parallel substitution in argument lists. -/
def Args.subst {n m : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) : Args S n ks → Args S m ks
  | .nil => .nil
  | .cons (k := k) t as => .cons (t.subst (Subst.upN k σ)) (as.subst σ)
end

@[simp] lemma Tm.subst_var' {n m : ℕ} (σ : Var n → Tm S m) (i : Var n) :
    (Tm.var i : Tm S n).subst σ = σ i := rfl
@[simp] lemma Tm.subst_op {n m : ℕ} (σ : Var n → Tm S m) (o : S.Op) (as : Args S n (S.arity o)) :
    (Tm.op o as).subst σ = .op o (as.subst σ) := rfl
@[simp] lemma Args.subst_nil {n m : ℕ} (σ : Var n → Tm S m) :
    (Args.nil : Args S n []).subst σ = .nil := rfl
@[simp] lemma Args.subst_cons {n m k : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) (t : Tm S (n + k))
    (as : Args S n ks) : (Args.cons t as).subst σ = .cons (t.subst (Subst.upN k σ)) (as.subst σ) :=
  rfl

mutual
/-- Substituting every variable by itself does nothing. -/
theorem Tm.subst_var {n : ℕ} : (t : Tm S n) → t.subst Tm.var = t
  | .var _ => rfl
  | .op o as => by rw [Tm.subst_op, Args.subst_var]
theorem Args.subst_var {n : ℕ} {ks : List ℕ} : (as : Args S n ks) → as.subst Tm.var = as
  | .nil => rfl
  | .cons t as => by rw [Args.subst_cons, Subst.upN_var, Tm.subst_var, Args.subst_var]
end

mutual
/-- A renaming is the substitution by variables. -/
theorem Tm.ren_eq_subst {n m : ℕ} (ρ : Var n → Var m) :
    (t : Tm S n) → t.ren ρ = t.subst (Tm.var ∘ ρ)
  | .var _ => rfl
  | .op o as => by rw [Tm.subst_op, Tm.ren_op, Args.ren_eq_subst]
theorem Args.ren_eq_subst {n m : ℕ} {ks : List ℕ} (ρ : Var n → Var m) :
    (as : Args S n ks) → as.ren ρ = as.subst (Tm.var ∘ ρ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.subst_cons, Args.ren_cons, Subst.upN_ren, Tm.ren_eq_subst, Args.ren_eq_subst]
end

mutual
/-- Substitution after renaming. -/
theorem Tm.subst_ren {n m l : ℕ} (ρ : Var n → Var m) (σ : Var m → Tm S l) :
    (t : Tm S n) → (t.ren ρ).subst σ = t.subst (σ ∘ ρ)
  | .var _ => rfl
  | .op o as => by rw [Tm.ren_op, Tm.subst_op, Tm.subst_op, Args.subst_ren]
theorem Args.subst_ren {n m l : ℕ} {ks : List ℕ} (ρ : Var n → Var m) (σ : Var m → Tm S l) :
    (as : Args S n ks) → (as.ren ρ).subst σ = as.subst (σ ∘ ρ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.ren_cons, Args.subst_cons, Args.subst_cons, Tm.subst_ren, Args.subst_ren,
      Subst.upN_comp_ren]
end

mutual
/-- Renaming after substitution. -/
theorem Tm.ren_subst {n m l : ℕ} (σ : Var n → Tm S m) (ρ : Var m → Var l) :
    (t : Tm S n) → (t.subst σ).ren ρ = t.subst (Tm.ren ρ ∘ σ)
  | .var _ => rfl
  | .op o as => by rw [Tm.subst_op, Tm.ren_op, Tm.subst_op, Args.ren_subst]
theorem Args.ren_subst {n m l : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) (ρ : Var m → Var l) :
    (as : Args S n ks) → (as.subst σ).ren ρ = as.subst (Tm.ren ρ ∘ σ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.subst_cons, Args.ren_cons, Args.subst_cons, Tm.ren_subst, Args.ren_subst,
      Subst.upN_ren_comp]
end

lemma Subst.up_comp {n m l : ℕ} (σ : Var n → Tm S m) (τ : Var m → Tm S l) :
    up (Tm.subst τ ∘ σ) = Tm.subst (up τ) ∘ up σ := by
  funext i; cases i with
  | zero => rfl
  | succ i =>
    simp only [Function.comp_apply, up_succ, Tm.ren_subst, Tm.subst_ren]
    rfl

lemma Subst.upN_comp {n m l : ℕ} (σ : Var n → Tm S m) (τ : Var m → Tm S l) :
    (k : ℕ) → upN k (Tm.subst τ ∘ σ) = Tm.subst (upN k τ) ∘ upN k σ
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_comp σ τ k, up_comp]; rfl

mutual
/-- Substitutions compose. -/
theorem Tm.subst_subst {n m l : ℕ} (σ : Var n → Tm S m) (τ : Var m → Tm S l) :
    (t : Tm S n) → (t.subst σ).subst τ = t.subst (Tm.subst τ ∘ σ)
  | .var _ => rfl
  | .op o as => by rw [Tm.subst_op, Tm.subst_op, Tm.subst_op, Args.subst_subst]
theorem Args.subst_subst {n m l : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) (τ : Var m → Tm S l) :
    (as : Args S n ks) → (as.subst σ).subst τ = as.subst (Tm.subst τ ∘ σ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.subst_cons, Args.subst_cons, Args.subst_cons, Tm.subst_subst, Args.subst_subst,
      Subst.upN_comp]
end

/-- Substitution only depends on the values of the substitution. -/
lemma Tm.subst_congr {n m : ℕ} {σ τ : Var n → Tm S m} (h : ∀ i, σ i = τ i) (t : Tm S n) :
    t.subst σ = t.subst τ := by
  rw [funext h]

/-! ## Single and double instantiation -/

/-- `[s/x]t`: instantiate the variable `x = Var.zero` bound in `t` by `s`. -/
def Tm.inst1 {n : ℕ} (t : Tm S (n + 1)) (s : Tm S n) : Tm S n :=
  t.subst (Var.cons s Tm.var)

/-- `[s₁/x, s₂/y]t`: instantiate the two variables bound in `t` (as in
`let (x, y) = _ in t`, where `y` is `Var.zero` and `x` is `Var.succ Var.zero`). -/
def Tm.inst2 {n : ℕ} (t : Tm S (n + 2)) (s₁ s₂ : Tm S n) : Tm S n :=
  t.subst (Var.cons s₂ (Var.cons s₁ Tm.var))

/-- Instantiating a weakened term has no effect. -/
@[simp] lemma Tm.inst1_ren_succ {n : ℕ} (s t : Tm S n) : (t.ren .succ).inst1 s = t := by
  rw [Tm.inst1, Tm.subst_ren]
  exact Tm.subst_var t

/-- The double instantiation is the composition of two single instantiations. -/
lemma Tm.inst2_eq {n : ℕ} (s₁ s₂ : Tm S n) (t : Tm S (n + 2)) :
    t.inst2 s₁ s₂ = (t.inst1 (s₂.ren .succ)).inst1 s₁ := by
  rw [Tm.inst2, Tm.inst1, Tm.inst1, Tm.subst_subst]
  congr 1
  funext i
  cases i with
  | zero => exact (Tm.inst1_ren_succ s₁ s₂).symm
  | succ i => cases i <;> rfl

/-- Renaming commutes with instantiation. -/
lemma Tm.ren_inst1 {n m : ℕ} (ρ : Var n → Var m) (s : Tm S n) (t : Tm S (n + 1)) :
    (t.inst1 s).ren ρ = (t.ren (Ren.up ρ)).inst1 (s.ren ρ) := by
  rw [Tm.inst1, Tm.inst1, Tm.ren_subst, Tm.subst_ren]
  congr 1; funext i; cases i <;> rfl

/-- Substitution commutes with instantiation. -/
lemma Tm.subst_inst1 {n m : ℕ} (σ : Var n → Tm S m) (s : Tm S n) (t : Tm S (n + 1)) :
    (t.inst1 s).subst σ = (t.subst (Subst.up σ)).inst1 (s.subst σ) := by
  rw [Tm.inst1, Tm.inst1, Tm.subst_subst, Tm.subst_subst]
  congr 1; funext i; cases i with
  | zero => rfl
  | succ i =>
    simp only [Function.comp_apply, Var.cons_succ, Tm.subst_var', Subst.up_succ, Tm.subst_ren]
    exact (Tm.subst_var _).symm

/-- Renaming commutes with double instantiation. -/
lemma Tm.ren_inst2 {n m : ℕ} (ρ : Var n → Var m) (s₁ s₂ : Tm S n) (t : Tm S (n + 2)) :
    (t.inst2 s₁ s₂).ren ρ = (t.ren (Ren.upN 2 ρ)).inst2 (s₁.ren ρ) (s₂.ren ρ) := by
  rw [Tm.inst2, Tm.inst2, Tm.ren_subst, Tm.subst_ren]
  congr 1; funext i; cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

/-- Substitution commutes with double instantiation. -/
lemma Tm.subst_inst2 {n m : ℕ} (σ : Var n → Tm S m) (s₁ s₂ : Tm S n) (t : Tm S (n + 2)) :
    (t.inst2 s₁ s₂).subst σ = (t.subst (Subst.upN 2 σ)).inst2 (s₁.subst σ) (s₂.subst σ) := by
  rw [Tm.inst2, Tm.inst2, Tm.subst_subst, Tm.subst_subst]
  congr 1; funext i; cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Function.comp_apply, Var.cons_succ, Tm.subst_var', Subst.upN_succ,
        Subst.upN_zero, Subst.up_succ, Tm.subst_ren, Tm.ren_ren]
      exact (Tm.subst_var _).symm

/-! ## Mapping operators -/

/-- An arity-preserving map between the operators of two signatures. -/
structure SigHom (S S' : Sig) where
  /-- the map on operators -/
  map : S.Op → S'.Op
  /-- operators keep their binding arities -/
  arity_map : ∀ o, S'.arity (map o) = S.arity o

variable {S' : Sig}

mutual
/-- Apply a map to every operator of a term. -/
def Tm.mapOp (f : SigHom S S') {n : ℕ} : Tm S n → Tm S' n
  | .var i => .var i
  | .op o as => .op (f.map o) ((f.arity_map o).symm ▸ as.mapOp f)

/-- Apply a map to every operator of an argument list. -/
def Args.mapOp (f : SigHom S S') {n : ℕ} {ks : List ℕ} : Args S n ks → Args S' n ks
  | .nil => .nil
  | .cons t as => .cons (t.mapOp f) (as.mapOp f)
end

lemma Args.ren_cast {n m : ℕ} (ρ : Var n → Var m) {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : (h ▸ as).ren ρ = h ▸ (as.ren ρ) := by
  subst h; rfl

lemma Args.subst_cast {n m : ℕ} (σ : Var n → Tm S m) {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : (h ▸ as).subst σ = h ▸ (as.subst σ) := by
  subst h; rfl

mutual
/-- Mapping operators commutes with renaming. -/
theorem Tm.mapOp_ren (f : SigHom S S') {n m : ℕ} (ρ : Var n → Var m) :
    (t : Tm S n) → (t.ren ρ).mapOp f = (t.mapOp f).ren ρ
  | .var _ => rfl
  | .op o as => by
    rw [Tm.ren_op, Tm.mapOp, Tm.mapOp, Tm.ren_op, Args.ren_cast, Args.mapOp_ren]
theorem Args.mapOp_ren (f : SigHom S S') {n m : ℕ} {ks : List ℕ} (ρ : Var n → Var m) :
    (as : Args S n ks) → (as.ren ρ).mapOp f = (as.mapOp f).ren ρ
  | .nil => rfl
  | .cons t as => by
    rw [Args.ren_cons, Args.mapOp, Args.mapOp, Args.ren_cons, Tm.mapOp_ren, Args.mapOp_ren]
end

lemma Subst.up_mapOp {n m : ℕ} (f : SigHom S S') (σ : Var n → Tm S m) :
    Subst.up (Tm.mapOp f ∘ σ) = Tm.mapOp f ∘ Subst.up σ := by
  funext i; cases i with
  | zero => rfl
  | succ i => exact (Tm.mapOp_ren f .succ (σ i)).symm

lemma Subst.upN_mapOp {n m : ℕ} (f : SigHom S S') (σ : Var n → Tm S m) :
    (k : ℕ) → Subst.upN k (Tm.mapOp f ∘ σ) = Tm.mapOp f ∘ Subst.upN k σ
  | 0 => rfl
  | k + 1 => by rw [Subst.upN_succ, Subst.upN_mapOp f σ k, Subst.up_mapOp]; rfl

mutual
/-- Mapping operators commutes with substitution. -/
theorem Tm.mapOp_subst (f : SigHom S S') {n m : ℕ} (σ : Var n → Tm S m) :
    (t : Tm S n) → (t.subst σ).mapOp f = (t.mapOp f).subst (Tm.mapOp f ∘ σ)
  | .var _ => rfl
  | .op o as => by
    rw [Tm.subst_op, Tm.mapOp, Tm.mapOp, Tm.subst_op, Args.subst_cast, Args.mapOp_subst]
theorem Args.mapOp_subst (f : SigHom S S') {n m : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) :
    (as : Args S n ks) → (as.subst σ).mapOp f = (as.mapOp f).subst (Tm.mapOp f ∘ σ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.subst_cons, Args.mapOp, Args.mapOp, Args.subst_cons, Tm.mapOp_subst,
      Args.mapOp_subst, Subst.upN_mapOp]
end

end Binding

namespace Binding

variable {S S' : Sig}

lemma Args.cast_heq {n : ℕ} {ks ks' : List ℕ} (h : ks = ks') (as : Args S n ks) :
    HEq (h ▸ as) as := by
  subst h; rfl

mutual
/-- Mapping operators along an injective map is injective. -/
theorem Tm.mapOp_inj (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} :
    (t t' : Tm S n) → t.mapOp f = t'.mapOp f → t = t'
  | .var i, .var j, h => by
    simp only [Tm.mapOp, Tm.var_inj] at h; rw [h]
  | .var _, .op _ _, h => by simp [Tm.mapOp] at h
  | .op _ _, .var _, h => by simp [Tm.mapOp] at h
  | .op o as, .op o' as', h => by
    simp only [Tm.mapOp, Tm.op_eq_op_iff] at h
    obtain ⟨ho, hh⟩ := h
    have := hf ho; subst this
    have : as.mapOp f = as'.mapOp f :=
      eq_of_heq ((Args.cast_heq _ _).symm.trans (hh.trans (Args.cast_heq _ _)))
    rw [Args.mapOp_inj f hf as as' this]
theorem Args.mapOp_inj (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} {ks : List ℕ} :
    (as as' : Args S n ks) → as.mapOp f = as'.mapOp f → as = as'
  | .nil, .nil, _ => rfl
  | .cons t as, .cons t' as', h => by
    simp only [Args.mapOp, Args.cons_inj] at h
    rw [Tm.mapOp_inj f hf t t' h.1, Args.mapOp_inj f hf as as' h.2]
end

lemma Tm.mapOp_injective (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} :
    Function.Injective (Tm.mapOp f : Tm S n → Tm S' n) :=
  fun t t' h => Tm.mapOp_inj f hf t t' h

end Binding

/-! ## Free occurrences of variables -/

namespace Binding

variable {S : Sig}

mutual
/-- `Tm.Occurs i t`: the variable `i` occurs free in `t`. -/
inductive Tm.Occurs : {n : ℕ} → Var n → Tm S n → Prop where
  | var {n : ℕ} {i : Var n} : Tm.Occurs i (.var i)
  | op {n : ℕ} {i : Var n} {o : S.Op} {as : Args S n (S.arity o)} :
      Args.Occurs i as → Tm.Occurs i (.op o as)

/-- `Args.Occurs i as`: the variable `i` occurs free in one of the arguments (under the
binders of that argument, where it is `Var.shiftN k i`). -/
inductive Args.Occurs : {n : ℕ} → {ks : List ℕ} → Var n → Args S n ks → Prop where
  | head {n k : ℕ} {ks : List ℕ} {i : Var n} {t : Tm S (n + k)} {as : Args S n ks} :
      Tm.Occurs (Var.shiftN k i) t → Args.Occurs i (.cons t as)
  | tail {n k : ℕ} {ks : List ℕ} {i : Var n} {t : Tm S (n + k)} {as : Args S n ks} :
      Args.Occurs i as → Args.Occurs i (.cons t as)
end

/-- A lifted renaming hits a shifted variable only at shifted variables. -/
lemma _root_.Ren.upN_eq_shiftN {n m : ℕ} {r : Var n → Var m} :
    (k : ℕ) → {x : Var (n + k)} → {j : Var m} → Ren.upN k r x = Var.shiftN k j →
      ∃ i, x = Var.shiftN k i ∧ r i = j
  | 0, x, _, h => ⟨x, rfl, h⟩
  | k + 1, x, j, h => by
    cases x with
    | zero => cases h
    | succ x =>
      simp only [Ren.upN_succ, Ren.up_succ, Var.shiftN_succ, Var.succ.injEq] at h
      obtain ⟨i, rfl, hi⟩ := Ren.upN_eq_shiftN k h
      exact ⟨i, rfl, hi⟩

mutual
/-- A variable occurring in a renamed term is the image of a variable occurring in the
term. -/
theorem Tm.Occurs.of_ren {n m : ℕ} {r : Var n → Var m} {j : Var m} :
    {t : Tm S n} → Tm.Occurs j (t.ren r) → ∃ i, r i = j ∧ Tm.Occurs i t
  | .var i, h => by cases h; exact ⟨i, rfl, .var⟩
  | .op o as, h => by
    cases h with
    | op h =>
      obtain ⟨i, hi, h'⟩ := Args.Occurs.of_ren h
      exact ⟨i, hi, .op h'⟩
theorem Args.Occurs.of_ren {n m : ℕ} {r : Var n → Var m} {j : Var m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.Occurs j (as.ren r) →
      ∃ i, r i = j ∧ Args.Occurs i as
  | _, .cons (k := k) t as, h => by
    cases h with
    | head h =>
      obtain ⟨x, hx, h'⟩ := Tm.Occurs.of_ren h
      obtain ⟨i, rfl, hi⟩ := Ren.upN_eq_shiftN k hx
      exact ⟨i, hi, .head h'⟩
    | tail h =>
      obtain ⟨i, hi, h'⟩ := Args.Occurs.of_ren h
      exact ⟨i, hi, .tail h'⟩
end

/-- Variables that do not occur in a term can be renamed arbitrarily. -/
lemma Tm.Occurs.not_of_ren {n m : ℕ} {r : Var n → Var m} {j : Var m} {t : Tm S n}
    (hj : ∀ i, r i ≠ j) : ¬ Tm.Occurs j (t.ren r) := fun h => by
  obtain ⟨i, hi, _⟩ := Tm.Occurs.of_ren h
  exact hj i hi

/-! ## Operators occurring in a term -/

mutual
/-- `Tm.HasOp P t`: some operator satisfying `P` occurs in `t` (possibly under binders). -/
inductive Tm.HasOp (P : S.Op → Prop) : {n : ℕ} → Tm S n → Prop where
  | here {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} : P o → Tm.HasOp P (.op o as)
  | arg {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} : Args.HasOp P as → Tm.HasOp P (.op o as)

/-- `Args.HasOp P as`: some operator satisfying `P` occurs in one of the arguments. -/
inductive Args.HasOp (P : S.Op → Prop) : {n : ℕ} → {ks : List ℕ} → Args S n ks → Prop where
  | head {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)} {as : Args S n ks} :
      Tm.HasOp P t → Args.HasOp P (.cons t as)
  | tail {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)} {as : Args S n ks} :
      Args.HasOp P as → Args.HasOp P (.cons t as)
end

@[simp] lemma Tm.not_hasOp_var {P : S.Op → Prop} {n : ℕ} {i : Var n} :
    ¬ Tm.HasOp P (.var i : Tm S n) := nofun

lemma Tm.hasOp_op_iff {P : S.Op → Prop} {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} :
    Tm.HasOp P (.op o as) ↔ P o ∨ Args.HasOp P as :=
  ⟨fun h => by cases h with | here h => exact .inl h | arg h => exact .inr h,
   fun h => h.elim .here .arg⟩

@[simp] lemma Args.not_hasOp_nil {P : S.Op → Prop} {n : ℕ} :
    ¬ Args.HasOp P (.nil : Args S n []) := nofun

lemma Args.hasOp_cons_iff {P : S.Op → Prop} {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)}
    {as : Args S n ks} : Args.HasOp P (.cons t as) ↔ Tm.HasOp P t ∨ Args.HasOp P as :=
  ⟨fun h => by cases h with | head h => exact .inl h | tail h => exact .inr h,
   fun h => h.elim .head .tail⟩

mutual
theorem Tm.HasOp.of_ren {P : S.Op → Prop} {n m : ℕ} {r : Var n → Var m} :
    {t : Tm S n} → Tm.HasOp P (t.ren r) → Tm.HasOp P t
  | .var _, h => by cases h
  | .op o as, h => by
    cases h with
    | here h => exact .here h
    | arg h => exact .arg (Args.HasOp.of_ren h)
theorem Args.HasOp.of_ren {P : S.Op → Prop} {n m : ℕ} {r : Var n → Var m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.ren r) → Args.HasOp P as
  | _, .cons t as, h => by
    cases h with
    | head h => exact .head (Tm.HasOp.of_ren h)
    | tail h => exact .tail (Args.HasOp.of_ren h)
end

/-- An operator occurring in a lifted substitution occurs in the substitution. -/
lemma Subst.hasOp_upN {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    (k : ℕ) → (x : Var (n + k)) → Tm.HasOp P (Subst.upN k σ x) → ∃ i, Tm.HasOp P (σ i)
  | 0, x, h => ⟨x, h⟩
  | k + 1, x, h => by
    cases x with
    | zero => cases h
    | succ x => exact Subst.hasOp_upN k x (Tm.HasOp.of_ren h)

mutual
theorem Tm.HasOp.of_subst {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {t : Tm S n} → Tm.HasOp P (t.subst σ) → Tm.HasOp P t ∨ ∃ i, Tm.HasOp P (σ i)
  | .var i, h => .inr ⟨i, h⟩
  | .op o as, h => by
    cases h with
    | here h => exact .inl (.here h)
    | arg h => exact (Args.HasOp.of_subst h).imp .arg id
theorem Args.HasOp.of_subst {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.subst σ) →
      Args.HasOp P as ∨ ∃ i, Tm.HasOp P (σ i)
  | _, .cons (k := k) t as, h => by
    cases h with
    | head h =>
      rcases Tm.HasOp.of_subst h with h | ⟨x, hx⟩
      · exact .inl (.head h)
      · exact .inr (Subst.hasOp_upN k x hx)
    | tail h => exact (Args.HasOp.of_subst h).imp .tail id
end

/-- An operator occurring in a lifted substitution at `x` occurs in the substitution at a
variable `i` with `x = Var.shiftN k i`. -/
lemma Subst.hasOp_upN' {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    (k : ℕ) → (x : Var (n + k)) → Tm.HasOp P (Subst.upN k σ x) →
      ∃ i, x = Var.shiftN k i ∧ Tm.HasOp P (σ i)
  | 0, x, h => ⟨x, rfl, h⟩
  | k + 1, x, h => by
    cases x with
    | zero => cases h
    | succ x =>
      obtain ⟨i, rfl, hi⟩ := Subst.hasOp_upN' k x (Tm.HasOp.of_ren h)
      exact ⟨i, rfl, hi⟩

mutual
/-- If an operator occurs in `t[σ]`, it occurs in `t` or in `σ i` for a variable `i`
occurring free in `t`. -/
theorem Tm.HasOp.of_subst_occurs {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {t : Tm S n} → Tm.HasOp P (t.subst σ) → Tm.HasOp P t ∨ ∃ i, Tm.Occurs i t ∧ Tm.HasOp P (σ i)
  | .var i, h => .inr ⟨i, .var, h⟩
  | .op o as, h => by
    cases h with
    | here h => exact .inl (.here h)
    | arg h =>
      rcases Args.HasOp.of_subst_occurs h with h | ⟨i, hi, h⟩
      · exact .inl (.arg h)
      · exact .inr ⟨i, .op hi, h⟩
theorem Args.HasOp.of_subst_occurs {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.subst σ) →
      Args.HasOp P as ∨ ∃ i, Args.Occurs i as ∧ Tm.HasOp P (σ i)
  | _, .cons (k := k) t as, h => by
    cases h with
    | head h =>
      rcases Tm.HasOp.of_subst_occurs h with h | ⟨x, hx, h⟩
      · exact .inl (.head h)
      · obtain ⟨i, rfl, hi⟩ := Subst.hasOp_upN' k x h
        exact .inr ⟨i, .head hx, hi⟩
    | tail h =>
      rcases Args.HasOp.of_subst_occurs h with h | ⟨i, hi, h⟩
      · exact .inl (.tail h)
      · exact .inr ⟨i, .tail hi, h⟩
end

lemma Args.hasOp_cast {P : S.Op → Prop} {n : ℕ} {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : Args.HasOp P (h ▸ as) ↔ Args.HasOp P as := by
  subst h; rfl

mutual
/-- An operator occurring in `t.mapOp f` is the image of an operator occurring in `t`. -/
theorem Tm.HasOp.of_mapOp {S' : Sig} {f : SigHom S S'} {P : S'.Op → Prop} {n : ℕ} :
    {t : Tm S n} → Tm.HasOp P (t.mapOp f) → Tm.HasOp (fun o => P (f.map o)) t
  | .var _, h => by cases h
  | .op o as, h => by
    cases h with
    | here h => exact .here h
    | arg h => exact .arg (Args.HasOp.of_mapOp ((Args.hasOp_cast _ _).1 h))
theorem Args.HasOp.of_mapOp {S' : Sig} {f : SigHom S S'} {P : S'.Op → Prop} {n : ℕ} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.mapOp f) →
      Args.HasOp (fun o => P (f.map o)) as
  | _, .cons t as, h => by
    cases h with
    | head h => exact .head (Tm.HasOp.of_mapOp h)
    | tail h => exact .tail (Args.HasOp.of_mapOp h)
end

mutual
/-- If an operator satisfying `P` occurs, then some operator satisfies `P`. -/
theorem Tm.HasOp.exists_op {P : S.Op → Prop} {n : ℕ} :
    {t : Tm S n} → Tm.HasOp P t → ∃ o, P o
  | .op o _, .here h => ⟨o, h⟩
  | .op _ _, .arg h => Args.HasOp.exists_op h
theorem Args.HasOp.exists_op {P : S.Op → Prop} {n : ℕ} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P as → ∃ o, P o
  | _, .cons _ _, .head h => Tm.HasOp.exists_op h
  | _, .cons _ _, .tail h => Args.HasOp.exists_op h
end

mutual
/-- If an operator satisfying `P` occurs in `t`, it occurs in every renaming of `t`. -/
theorem Tm.HasOp.ren {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) :
    {t : Tm S n} → Tm.HasOp P t → Tm.HasOp P (t.ren r)
  | .op _ _, .here h => .here h
  | .op _ _, .arg h => .arg (Args.HasOp.ren r h)
theorem Args.HasOp.ren {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P as → Args.HasOp P (as.ren r)
  | _, .cons _ _, .head h => .head (Tm.HasOp.ren _ h)
  | _, .cons _ _, .tail h => .tail (Args.HasOp.ren r h)
end

/-- Renaming does not change which operators occur in a term. -/
@[simp] lemma Tm.hasOp_ren_iff {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) (t : Tm S n) :
    Tm.HasOp P (t.ren r) ↔ Tm.HasOp P t :=
  ⟨Tm.HasOp.of_ren, Tm.HasOp.ren r⟩

/-! ### Deciding whether an operator occurs -/

mutual
/-- `Tm.anyOp f t`: some operator `o` of `t` has `f o = true` (a decision procedure for
`Tm.HasOp`). -/
def Tm.anyOp (f : S.Op → Bool) {n : ℕ} : Tm S n → Bool
  | .var _ => false
  | .op o as => f o || as.anyOp f
/-- `Args.anyOp f as`: `Tm.anyOp f` holds for some argument. -/
def Args.anyOp (f : S.Op → Bool) {n : ℕ} {ks : List ℕ} : Args S n ks → Bool
  | .nil => false
  | .cons t as => t.anyOp f || as.anyOp f
end

mutual
theorem Tm.anyOp_iff (f : S.Op → Bool) {n : ℕ} :
    (t : Tm S n) → t.anyOp f = true ↔ Tm.HasOp (fun o => f o = true) t
  | .var _ => by simp [Tm.anyOp]
  | .op o as => by
    rw [Tm.hasOp_op_iff, ← Args.anyOp_iff f as]; simp [Tm.anyOp]
theorem Args.anyOp_iff (f : S.Op → Bool) {n : ℕ} {ks : List ℕ} :
    (as : Args S n ks) → as.anyOp f = true ↔ Args.HasOp (fun o => f o = true) as
  | .nil => by simp [Args.anyOp]
  | .cons t as => by
    rw [Args.hasOp_cons_iff, ← Tm.anyOp_iff f t, ← Args.anyOp_iff f as]; simp [Args.anyOp]
end

instance Tm.decidableHasOp (P : S.Op → Prop) [DecidablePred P] {n : ℕ} (t : Tm S n) :
    Decidable (Tm.HasOp P t) :=
  decidable_of_iff (t.anyOp (fun o => decide (P o))) (by rw [Tm.anyOp_iff]; simp)

end Binding
