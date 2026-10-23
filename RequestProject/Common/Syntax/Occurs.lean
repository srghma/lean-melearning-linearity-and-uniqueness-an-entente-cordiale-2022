module
public import RequestProject.Common.Syntax.RenSubst

/-!
# Generic binding layer: free occurrences of variables

`Tm.Occurs i t`: the variable `i` occurs free in `t`, and its behaviour under renaming.
-/

@[expose] public section

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

end Binding
