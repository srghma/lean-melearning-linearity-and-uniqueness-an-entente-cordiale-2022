module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Function.Basic

/-!
# De Bruijn variables `Var n`

Both formalisations in this project use intrinsically scoped de Bruijn syntax: a term with
`n` free variables has type `Term n` (or `Term R n`), and its variables are elements of
`Var n`.  `Var n` is an inductive family with two constructors:

* `Var.zero : Var (n + 1)`: the most recently bound variable;
* `Var.succ : Var n → Var (n + 1)`: an older variable.

Unlike `Fin n`, whose successor `Fin.succ` is a function and not a constructor, both
constructors of `Var` can be used by `cases`, `induction` and pattern matching on
derivations whose index is `.succ i` (dependent elimination works without detours).
`Var n` is equivalent to `Fin n` (`Var.toFin`, `Var.ofFin`, `Var.equivFin`).

## Renamings

A renaming is a function `Var n → Var m`.

* `Ren.up ρ` lifts `ρ` under one binder: `zero ↦ zero`, `succ i ↦ succ (ρ i)`;
* `Ren.upN k ρ` lifts `ρ` under `k` binders;
* `Ren.shiftN k : Var n → Var (n + k)` weakens by `k` new variables bound in front.
-/

@[expose] public section

/-- De Bruijn variables: `Var n` has exactly `n` elements. -/
inductive Var : ℕ → Type where
  /-- the most recently bound variable (index `0`) -/
  | zero {n : ℕ} : Var (n + 1)
  /-- an older variable (index `i + 1`) -/
  | succ {n : ℕ} : Var n → Var (n + 1)
  deriving DecidableEq

namespace Var

/-- There are no variables in the empty scope. -/
def elim0 {α : Sort _} : Var 0 → α := nofun

instance : IsEmpty (Var 0) := ⟨nofun⟩

/-- The numeric value of a variable. -/
def toNat : {n : ℕ} → Var n → ℕ
  | _, zero => 0
  | _, succ i => i.toNat + 1

lemma toNat_lt : {n : ℕ} → (i : Var n) → i.toNat < n
  | _, zero => Nat.succ_pos _
  | _, succ i => Nat.succ_lt_succ (toNat_lt i)

/-- The variable as an element of `Fin n`. -/
def toFin {n : ℕ} (i : Var n) : Fin n := ⟨i.toNat, i.toNat_lt⟩

/-- The variable with index `i`. -/
def ofFin : {n : ℕ} → Fin n → Var n
  | 0, i => i.elim0
  | _ + 1, i => Fin.cases zero (fun j => succ (ofFin j)) i

@[simp] lemma ofFin_zero {n : ℕ} : ofFin (0 : Fin (n + 1)) = zero := rfl
@[simp] lemma ofFin_succ {n : ℕ} (i : Fin n) : ofFin i.succ = succ (ofFin i) := by
  simp [ofFin]

@[simp] lemma toFin_zero {n : ℕ} : (zero : Var (n + 1)).toFin = 0 := rfl
@[simp] lemma toFin_succ {n : ℕ} (i : Var n) : (succ i).toFin = i.toFin.succ := rfl

@[simp] lemma ofFin_toFin : {n : ℕ} → (i : Var n) → ofFin i.toFin = i
  | _, zero => rfl
  | _, succ i => by rw [toFin_succ, ofFin_succ, ofFin_toFin i]

@[simp] lemma toFin_ofFin : {n : ℕ} → (i : Fin n) → (ofFin i).toFin = i
  | 0, i => i.elim0
  | _ + 1, i => by
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rw [ofFin_succ, toFin_succ, toFin_ofFin j]

/-- `Var n` is equivalent to `Fin n`. -/
def equivFin (n : ℕ) : Var n ≃ Fin n where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

instance (n : ℕ) : Fintype (Var n) := Fintype.ofEquiv _ (equivFin n).symm

lemma succ_injective {n : ℕ} : Function.Injective (succ : Var n → Var (n + 1)) := by
  intro i j h; cases h; rfl

@[simp] lemma succ_inj {n : ℕ} {i j : Var n} : succ i = succ j ↔ i = j :=
  succ_injective.eq_iff

@[simp] lemma succ_ne_zero {n : ℕ} (i : Var n) : succ i ≠ zero := nofun
@[simp] lemma zero_ne_succ {n : ℕ} (i : Var n) : zero ≠ succ i := nofun

/-- Extending a function on variables at `zero`: `cons a f` maps `zero` to `a` and
`succ i` to `f i`. -/
def cons {α : Sort _} {n : ℕ} (a : α) (f : Var n → α) : Var (n + 1) → α
  | zero => a
  | succ i => f i

@[simp] lemma cons_zero {α : Sort _} {n : ℕ} (a : α) (f : Var n → α) : cons a f zero = a := rfl
@[simp] lemma cons_succ {α : Sort _} {n : ℕ} (a : α) (f : Var n → α) (i : Var n) :
    cons a f (succ i) = f i := rfl

lemma cons_self_tail {α : Sort _} {n : ℕ} (f : Var (n + 1) → α) :
    cons (f zero) (fun i => f (succ i)) = f := by
  funext i; cases i <;> rfl

lemma comp_cons {α β : Sort _} {n : ℕ} (g : α → β) (a : α) (f : Var n → α) :
    g ∘ cons a f = cons (g a) (g ∘ f) := by
  funext i; cases i <;> rfl

/-- Weakening a variable by `k` binders added in front: `shiftN k i = succ^k i`. -/
def shiftN {n : ℕ} : (k : ℕ) → Var n → Var (n + k)
  | 0, i => i
  | k + 1, i => succ (shiftN k i)

@[simp] lemma shiftN_zero {n : ℕ} (i : Var n) : shiftN 0 i = i := rfl
@[simp] lemma shiftN_succ {n : ℕ} (k : ℕ) (i : Var n) : shiftN (k + 1) i = succ (shiftN k i) :=
  rfl

lemma shiftN_injective {n : ℕ} : (k : ℕ) → Function.Injective (shiftN k : Var n → Var (n + k))
  | 0 => fun _ _ h => h
  | k + 1 => fun _ _ h => shiftN_injective k (succ_injective h)

@[simp] lemma shiftN_inj {n k : ℕ} {i j : Var n} : shiftN k i = shiftN k j ↔ i = j :=
  (shiftN_injective k).eq_iff

/-- The embedding of the `m` most recent variables of the scope `n + m`
(`lowAdd i` has the same de Bruijn index as `i`). -/
def lowAdd {n : ℕ} : {m : ℕ} → Var m → Var (n + m)
  | _ + 1, zero => zero
  | _ + 1, succ i => succ (lowAdd i)

@[simp] lemma lowAdd_zero {n m : ℕ} : (lowAdd (zero : Var (m + 1)) : Var (n + (m + 1))) = zero :=
  rfl
@[simp] lemma lowAdd_succ {n m : ℕ} (i : Var m) :
    (lowAdd (succ i) : Var (n + (m + 1))) = succ (lowAdd i) := rfl

lemma lowAdd_injective {n : ℕ} : {m : ℕ} → Function.Injective (lowAdd : Var m → Var (n + m))
  | _ + 1, zero, zero, _ => rfl
  | _ + 1, succ _, succ _, h => congrArg succ (lowAdd_injective (succ_injective h))
  | _ + 1, zero, succ _, h => nomatch h
  | _ + 1, succ _, zero, h => nomatch h

lemma lowAdd_ne_shiftN {n : ℕ} : {m : ℕ} → (i : Var m) → (j : Var n) →
    (lowAdd i : Var (n + m)) ≠ shiftN m j
  | _ + 1, zero, _ => nofun
  | _ + 1, succ i, j => fun h => lowAdd_ne_shiftN i j (succ_injective h)

/-- Every variable of the scope `n + m` is one of the `m` most recent ones or an old one. -/
lemma lowAdd_or_shiftN {n : ℕ} : {m : ℕ} → (x : Var (n + m)) →
    (∃ i, (lowAdd i : Var (n + m)) = x) ∨ ∃ j, shiftN m j = x
  | 0, x => .inr ⟨x, rfl⟩
  | m + 1, x => by
    change Var (n + m + 1) at x
    cases x with
    | zero => exact .inl ⟨zero, rfl⟩
    | succ x =>
      rcases lowAdd_or_shiftN (m := m) x with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact .inl ⟨succ i, rfl⟩
      · exact .inr ⟨j, rfl⟩

/-- The *oldest* variable of a non-empty scope (de Bruijn index `n`). -/
def last : (n : ℕ) → Var (n + 1)
  | 0 => zero
  | n + 1 => succ (last n)

/-- Embedding of `Var n` into `Var (n + 1)` that keeps every index: the new variable is
the oldest one, `last n`. -/
def castSucc : {n : ℕ} → Var n → Var (n + 1)
  | _, zero => zero
  | _, succ i => succ (castSucc i)

lemma castSucc_injective {n : ℕ} : Function.Injective (castSucc : Var n → Var (n + 1)) := by
  intro i j h
  induction i with
  | zero => cases j <;> first | rfl | cases h
  | succ i ih =>
    cases j with
    | zero => cases h
    | succ j => simp only [castSucc, succ.injEq] at h; rw [ih h]

lemma castSucc_ne_last : {n : ℕ} → (i : Var n) → castSucc i ≠ last n
  | _ + 1, zero => by simp [castSucc, last]
  | _ + 1, succ i => by simp [castSucc, last, castSucc_ne_last i]

end Var

/-! ## Renamings -/

namespace Ren

/-- Lifting a renaming under a binder: `zero` is fixed and the others are shifted. -/
def up {n m : ℕ} (ρ : Var n → Var m) : Var (n + 1) → Var (m + 1) :=
  Var.cons Var.zero (fun i => Var.succ (ρ i))

@[simp] lemma up_zero {n m : ℕ} (ρ : Var n → Var m) : up ρ Var.zero = Var.zero := rfl
@[simp] lemma up_succ {n m : ℕ} (ρ : Var n → Var m) (i : Var n) :
    up ρ (Var.succ i) = Var.succ (ρ i) := rfl

@[simp] lemma up_id {n : ℕ} : up (id : Var n → Var n) = id := by
  funext i; cases i <;> rfl

@[simp] lemma up_id' {n : ℕ} : up (fun i : Var n => i) = id := up_id

lemma up_comp {n m k : ℕ} (ρ : Var n → Var m) (ρ' : Var m → Var k) :
    up (ρ' ∘ ρ) = up ρ' ∘ up ρ := by
  funext i; cases i <;> rfl

lemma up_injective {n m : ℕ} {ρ : Var n → Var m} (h : Function.Injective ρ) :
    Function.Injective (up ρ) := by
  intro i j e
  cases i <;> cases j
  · rfl
  · cases e
  · cases e
  · simp only [up_succ, Var.succ.injEq] at e; rw [h e]

/-- A successor variable in the image of a lifted renaming comes from the original
renaming. -/
lemma exists_of_up {n m : ℕ} {ρ : Var n → Var m} {j : Var m} :
    (∃ i, up ρ i = Var.succ j) → ∃ i, ρ i = j
  | ⟨Var.zero, hi⟩ => by cases hi
  | ⟨Var.succ i, hi⟩ => ⟨i, by simpa using hi⟩

/-- Lifting a renaming under `k` binders. -/
def upN {n m : ℕ} : (k : ℕ) → (Var n → Var m) → Var (n + k) → Var (m + k)
  | 0, ρ => ρ
  | k + 1, ρ => up (upN k ρ)

@[simp] lemma upN_zero {n m : ℕ} (ρ : Var n → Var m) : upN 0 ρ = ρ := rfl
@[simp] lemma upN_succ {n m : ℕ} (k : ℕ) (ρ : Var n → Var m) : upN (k + 1) ρ = up (upN k ρ) :=
  rfl

@[simp] lemma upN_id {n : ℕ} : (k : ℕ) → upN k (id : Var n → Var n) = id
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_id k, up_id]

lemma upN_comp {n m l : ℕ} (ρ : Var n → Var m) (ρ' : Var m → Var l) :
    (k : ℕ) → upN k (ρ' ∘ ρ) = upN k ρ' ∘ upN k ρ
  | 0 => rfl
  | k + 1 => by rw [upN_succ, upN_comp ρ ρ' k, up_comp]; rfl

lemma upN_injective {n m : ℕ} {ρ : Var n → Var m} (h : Function.Injective ρ) :
    (k : ℕ) → Function.Injective (upN k ρ)
  | 0 => h
  | k + 1 => up_injective (upN_injective h k)

end Ren

namespace Var

/-- Numerals for variables: `(k : Var n)` is the variable with index `k` (modulo `n`), so
that concrete terms can be written as `Term.var 2`. -/
instance instOfNat {n : ℕ} [NeZero n] (k : ℕ) : OfNat (Var n) k := ⟨ofFin (Fin.ofNat n k)⟩

end Var
