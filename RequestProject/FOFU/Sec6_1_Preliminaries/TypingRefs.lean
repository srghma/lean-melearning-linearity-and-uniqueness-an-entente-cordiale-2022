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

variable {R : Type} [Grades.PreorderedSemiring R]

/-- Every runtime reference occurring in a well-typed term is assumed in its context. -/
theorem HasType.refs_ne_none {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R k}
    (h : HasType Γ t A) {a : ℕ} (ha : a ∈ t.refs) : Γ.refs a ≠ none := by
  induction h with
  | var => simp [Term.refs] at ha
  | abs _ ih => exact ih ha
  | app hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | pr hs _ _ ih => rw [hs.refs]; exact ih ha
  | elim hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | der _ _ ih => exact ih ha
  | approx _ _ _ ih => exact ih ha
  | tensorI hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | tensorE hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | unitI => simp [Term.refs] at ha
  | unitE hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | pack _ _ ih => exact ih ha
  | unpack hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · apply (hadd.refs a).ne_none_right
      have := ih₂ h
      simpa [Ctx.shiftNames, Ctx.substNames] using this
  | share _ _ ih => exact ih ha
  | clone _ hadd _ _ _ _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | withBorrow hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | split _ ih => exact ih ha
  | join _ hadd _ _ ih₁ ih₂ =>
    rcases Finset.mem_union.1 ha with h | h
    · exact (hadd.refs a).ne_none_left (ih₁ h)
    · exact (hadd.refs a).ne_none_right (ih₂ h)
  | push _ ih => exact ih ha
  | pull _ ih => exact ih ha
  | nat => simp [Term.refs] at ha
  | float => simp [Term.refs] at ha
  | prim => simp [Term.refs] at ha
  | nec _ _ _ ih => exact ih ha
  | unborrow _ ih => exact ih ha
  | ref _ hT =>
    simp only [Term.refs, Finset.mem_singleton] at ha
    subst ha; simp [hT]

end FOFU
