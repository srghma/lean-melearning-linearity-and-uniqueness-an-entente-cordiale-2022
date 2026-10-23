module
public import RequestProject.Common.Syntax.Basic

/-!
# Generic binding layer: renaming and substitution

Renaming `Tm.ren`, parallel substitution `Tm.subst` with its liftings `Subst.up` /
`Subst.upN`, the σ-calculus laws (`ren_id`, `ren_ren`, `subst_var`, `ren_eq_subst`,
`subst_ren`, `ren_subst`, `subst_subst`), and the single and double instantiations
`Tm.inst1` / `Tm.inst2`.
-/

@[expose] public section

namespace Binding

variable {S : Sig}

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

end Binding
