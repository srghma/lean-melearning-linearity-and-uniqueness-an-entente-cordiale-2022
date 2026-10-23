module
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.ZeroWeakening

/-!
# Free occurrences of variables

* `Term.Occurs i t`: the variable `i` occurs free in `t` (the generic `Binding.Tm.Occurs`).
* `HasTypeD.occurs`: a variable that occurs in a well-typed term has an assumption in the
  context.
* `Term.allocates_subst`: if `t[σ]` allocates resources, then either `t` does, or some
  `σ j` does for a variable `j` occurring in `t` (the generic
  `Binding.Tm.HasOp.of_subst_occurs`).

These are used in the case of the promotion rule `pr` (side condition
`¬ resourceAllocator(t)`) of the substitution lemmas.
-/

@[expose] public section

namespace FOFU

open Binding

variable {R : Type}

/-- `Term.Occurs i t`: the variable `i` occurs free in `t`. -/
abbrev Term.Occurs {n ρ : ℕ} (i : Var n) (t : Term R n ρ) : Prop := Tm.Occurs i t

lemma Term.allocates_subst {n m ρ : ℕ} {t : Term R n ρ} {σ : Var n → Term R m ρ}
    (h : (t.subst σ).Allocates) : t.Allocates ∨ ∃ j, t.Occurs j ∧ (σ j).Allocates :=
  Tm.HasOp.of_subst_occurs h

variable [Grades.PreorderedSemiring R]

lemma AssmAdd.ne_none_left {k : ℕ} {a b c : Option (Assm R k)} (h : AssmAdd a b c)
    (ha : a ≠ none) : c ≠ none := by
  cases h <;> simp_all

lemma AssmAdd.ne_none_right {k : ℕ} {a b c : Option (Assm R k)} (h : AssmAdd a b c)
    (hb : b ≠ none) : c ≠ none := by
  cases h <;> simp_all

lemma AssmScale.ne_none {k : ℕ} {r : R} {a b : Option (Assm R k)} (h : AssmScale r a b)
    (ha : a ≠ Option.none) : b ≠ Option.none := by
  cases h <;> simp_all

/-- A variable occurring in a well-typed term has an assumption. -/
theorem HasTypeD.occurs {k n ρ : ℕ} {Δ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasTypeD Δ t B) : ∀ {i : Var n}, t.Occurs i → Δ.vars.get i ≠ none := by
  induction h with
  | var hi | varG hi =>
    intro i hocc; cases hocc; simp [hi.get]
  | abs _ ih =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact ih h
    · cases h
  | app hadd _ _ ih₁ ih₂ | tensorI hadd _ _ ih₁ ih₂ | unitE hadd _ _ ih₁ ih₂
  | withBorrow hadd _ _ ih₁ ih₂ | join _ hadd _ _ ih₁ ih₂ | elim hadd _ _ ih₁ ih₂
  | clone _ hadd _ _ _ _ _ ih₁ ih₂ | tensorE hadd _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact (hadd.vars.get i).ne_none_left (ih₁ h)
    · rcases h with h | h
      · exact (hadd.vars.get i).ne_none_right (ih₂ h)
      · cases h
  | unpack hadd _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact (hadd.vars.get i).ne_none_left (ih₁ h)
    · rcases h with h | h
      · refine (hadd.vars.get i).ne_none_right ?_
        have := ih₂ h
        simpa [TCtx.shiftNames] using this
      · cases h
  | pr hs _ _ ih =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact (hs.vars.get i).ne_none (ih h)
    · cases h
  | @approx k n ρ Γ t B j C r s hj hrs _ ih =>
    intro i hocc
    by_cases hij : i = j
    · subst hij; simp
    · rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ hij]; exact ih hocc
  | pack _ _ ih | share _ _ ih | split _ ih | push _ ih | pull _ ih | unborrow _ ih =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact ih h
    · cases h
  | nec _ _ _ ih =>
    intro i hocc
    rcases hocc with _ | ⟨h | h⟩
    · exact absurd (by simp) (ih h)
    · cases h
  | unitI _ | nat _ _ | float _ _ | prim _ _ | ref _ _ =>
    intro i hocc; rcases hocc with _ | ⟨h⟩; cases h

end FOFU
