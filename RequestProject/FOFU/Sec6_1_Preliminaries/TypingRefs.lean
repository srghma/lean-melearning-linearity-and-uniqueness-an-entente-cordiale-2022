module
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst

/-!
# References of well-typed terms

A runtime reference `ref` can only be typed by the rule `ref`, which requires the
assumption `ref : Res_id A` in the context, and every typing rule keeps the reference
assumptions of its premises in its conclusion.  Hence every reference occurring in a
well-typed term is assumed in its context (`HasType.refs_ne_none`).
-/

@[expose] public section

namespace FOFU

open Binding

variable {R : Type} [Grades.PreorderedSemiring R]

omit [Grades.PreorderedSemiring R] in
lemma RefAdd.ne_none_left {k : ℕ} {a b c : Option (RefTy R k)} (h : RefAdd a b c)
    (ha : a ≠ none) : c ≠ none := by
  cases h <;> simp_all

omit [Grades.PreorderedSemiring R] in
lemma RefAdd.ne_none_right {k : ℕ} {a b c : Option (RefTy R k)} (h : RefAdd a b c)
    (hb : b ≠ none) : c ≠ none := by
  cases h <;> simp_all

/-- Every runtime reference occurring in a well-typed term is assumed in its context. -/
theorem HasType.refOccurs_ne_none {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ}
    {A : Ty R k} (h : HasType Γ t A) : ∀ {a : Var ρ}, t.RefOccurs a → Γ.refs.get a ≠ none := by
  induction h with
  | var _ => intro a hocc; exact absurd hocc Tm.not_hasOp_var
  | abs _ ih =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · exact ih h
    · cases h
  | app hadd _ _ ih₁ ih₂ | tensorI hadd _ _ ih₁ ih₂ | unitE hadd _ _ ih₁ ih₂
  | withBorrow hadd _ _ ih₁ ih₂ | join _ hadd _ _ ih₁ ih₂ | elim hadd _ _ ih₁ ih₂
  | clone _ hadd _ _ _ _ _ ih₁ ih₂ | tensorE hadd _ _ ih₁ ih₂ =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · exact (hadd.refs.get a).ne_none_left (ih₁ h)
    · rcases h with h | h
      · exact (hadd.refs.get a).ne_none_right (ih₂ h)
      · cases h
  | unpack hadd _ _ ih₁ ih₂ =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · exact (hadd.refs.get a).ne_none_left (ih₁ h)
    · rcases h with h | h
      · refine (hadd.refs.get a).ne_none_right ?_
        have := ih₂ h
        simpa [TCtx.shiftNames] using this
      · cases h
  | pr hs _ _ ih =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · rw [hs.refs]; exact ih h
    · cases h
  | approx _ _ _ ih | der _ _ ih =>
    intro a hocc; simpa using ih hocc
  | pack _ _ ih | share _ _ ih | split _ ih | push _ ih | pull _ ih | unborrow _ ih =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · exact ih h
    · cases h
  | nec _ _ _ ih =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h | h⟩
    · simpa using ih h
    · cases h
  | unitI _ | nat _ _ | float _ _ | prim _ _ =>
    intro a hocc
    rcases hocc with ⟨⟨⟩⟩ | ⟨h⟩
    cases h
  | ref _ hT =>
    intro a hocc
    rcases hocc with ⟨h⟩ | ⟨h⟩
    · simp only [Op.isRef, decide_eq_true_eq] at h
      subst h; simp [hT.eq]
    · cases h

/-- Every runtime reference in `refs(t)` of a well-typed term `t` is assumed in its
context. -/
theorem HasType.refs_ne_none {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k}
    (h : HasType Γ t A) {a : Var ρ} (ha : a ∈ t.refs) : Γ.refs.get a ≠ none :=
  h.refOccurs_ne_none (Term.mem_refs.1 ha)

end FOFU
