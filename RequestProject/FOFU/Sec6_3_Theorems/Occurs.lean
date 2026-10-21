module
public import RequestProject.FOFU.Sec6_3_Theorems.ZeroWeakening

/-!
# Free occurrences of variables

* `Term.Occurs i t`: the variable `i` occurs free in `t`.
* `HasTypeD.occurs`: a variable that occurs in a well-typed term has an assumption in the
  context.
* `Term.allocates_subst`: if `t[σ]` allocates resources, then either `t` does, or some
  `σ j` does for a variable `j` occurring in `t`.

These are used in the case of the promotion rule `pr` (side condition
`¬ resourceAllocator(t)`) of the substitution lemmas.
-/

@[expose] public section

namespace FOFU

open DeBruijn

variable {R : Type}

/-- `Term.Occurs i t`: the variable `i` occurs free in `t`. -/
def Term.Occurs : {n : ℕ} → Fin n → Term R n → Prop
  | _, i, .var j => i = j
  | _, i, .lam t => t.Occurs i.succ
  | _, i, .app t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .pair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .letPair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ.succ
  | _, _, .unit => False
  | _, i, .letUnit t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .box _ t => t.Occurs i
  | _, i, .letBox t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ
  | _, i, .pack t => t.Occurs i
  | _, i, .unpack t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ
  | _, i, .share _ t => t.Occurs i
  | _, i, .clone t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ
  | _, i, .withBorrow t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .split t => t.Occurs i
  | _, i, .join t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .push t => t.Occurs i
  | _, i, .pull t => t.Occurs i
  | _, _, .nat _ => False
  | _, _, .float _ => False
  | _, _, .prim _ => False
  | _, i, .star t => t.Occurs i
  | _, i, .unborrow t => t.Occurs i
  | _, _, .ref _ => False

/-- An allocating entry of a lifted substitution comes from the original substitution. -/
lemma Term.Subst.up_allocates {n m : ℕ} {σ : Fin n → Term R m} {j : Fin (n + 1)}
    (h : (Term.Subst.up σ j).Allocates) : ∃ j', j = j'.succ ∧ (σ j').Allocates := by
  cases j using Fin.cases with
  | zero => simp [Term.Subst.up, Term.Allocates] at h
  | succ j => exact ⟨j, rfl, Term.allocates_rename.mp h⟩

lemma Term.allocates_subst {n : ℕ} {t : Term R n} :
    ∀ {m : ℕ} {σ : Fin n → Term R m}, (t.subst σ).Allocates →
      t.Allocates ∨ ∃ j, t.Occurs j ∧ (σ j).Allocates := by
  induction t with
  | var i => intro m σ h; exact Or.inr ⟨i, rfl, h⟩
  | lam t ih =>
    intro m σ h
    rcases ih h with h | ⟨j, hj, ha⟩
    · exact Or.inl h
    · obtain ⟨j', rfl, h'⟩ := Term.Subst.up_allocates ha
      exact Or.inr ⟨j', hj, h'⟩
  | letPair t₁ t₂ ih₁ ih₂ =>
    intro m σ h
    rcases h with h | h
    · rcases ih₁ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨j, Or.inl hj, ha⟩
    · rcases ih₂ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inr h)
      · obtain ⟨j', rfl, h'⟩ := Term.Subst.up_allocates ha
        obtain ⟨j'', rfl, h''⟩ := Term.Subst.up_allocates h'
        exact Or.inr ⟨j'', Or.inr hj, h''⟩
  | letBox t₁ t₂ ih₁ ih₂ | unpack t₁ t₂ ih₁ ih₂ =>
    intro m σ h
    rcases h with h | h
    · rcases ih₁ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨j, Or.inl hj, ha⟩
    · rcases ih₂ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inr h)
      · obtain ⟨j', rfl, h'⟩ := Term.Subst.up_allocates ha
        exact Or.inr ⟨j', Or.inr hj, h'⟩
  | clone t₁ t₂ _ _ => intro m σ _; exact Or.inl trivial
  | app t₁ t₂ ih₁ ih₂ | pair t₁ t₂ ih₁ ih₂ | letUnit t₁ t₂ ih₁ ih₂
  | withBorrow t₁ t₂ ih₁ ih₂ | join t₁ t₂ ih₁ ih₂ =>
    intro m σ h
    rcases h with h | h
    · rcases ih₁ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨j, Or.inl hj, ha⟩
    · rcases ih₂ h with h | ⟨j, hj, ha⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨j, Or.inr hj, ha⟩
  | box _ t ih | pack t ih | share _ t ih | split t ih | push t ih | pull t ih | star t ih
  | unborrow t ih =>
    intro m σ h
    exact ih h
  | unit | nat _ | float _ | ref _ => intro m σ h; exact h.elim
  | prim p => intro m σ h; exact Or.inl h

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
theorem HasTypeD.occurs {k n : ℕ} {Δ : Ctx R k n} {t : Term R n} {B : Ty R k}
    (h : HasTypeD Δ t B) : ∀ {i : Fin n}, t.Occurs i → Δ.vars i ≠ none := by
  induction h with
  | var hi _ | varG hi _ =>
    intro i hocc; simp only [Term.Occurs] at hocc; subst hocc; simp [hi]
  | abs _ ih => intro i hocc; exact ih hocc
  | app hadd _ _ ih₁ ih₂ | tensorI hadd _ _ ih₁ ih₂ | unitE hadd _ _ ih₁ ih₂
  | withBorrow hadd _ _ ih₁ ih₂ | join _ hadd _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with h | h
    · exact (hadd.vars i).ne_none_left (ih₁ h)
    · exact (hadd.vars i).ne_none_right (ih₂ h)
  | elim hadd _ _ ih₁ ih₂ | clone _ hadd _ _ _ _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with h | h
    · exact (hadd.vars i).ne_none_left (ih₁ h)
    · exact (hadd.vars i).ne_none_right (ih₂ h)
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with h | h
    · exact (hadd.vars i).ne_none_left (ih₁ h)
    · exact (hadd.vars i).ne_none_right (ih₂ h)
  | unpack hadd _ _ ih₁ ih₂ =>
    intro i hocc
    rcases hocc with h | h
    · exact (hadd.vars i).ne_none_left (ih₁ h)
    · refine (hadd.vars i).ne_none_right ?_
      have := ih₂ h
      simpa [Ctx.shiftNames, Ctx.substNames] using this
  | pr hs _ _ ih =>
    intro i hocc; exact (hs.vars i).ne_none (ih hocc)
  | @approx k n Γ t B j C r s hj hrs _ ih =>
    intro i hocc
    by_cases hij : i = j
    · subst hij; simp [Ctx.update]
    · rw [Ctx.update_vars_ne _ hij]; exact ih hocc
  | pack _ _ ih | share _ _ ih | split _ ih | push _ ih | pull _ ih | unborrow _ ih =>
    intro i hocc; exact ih hocc
  | nec _ _ _ ih => intro i hocc; exact absurd rfl (ih hocc)
  | unitI _ | nat _ _ | float _ _ | prim _ _ | ref _ _ => intro i hocc; exact hocc.elim

end FOFU
