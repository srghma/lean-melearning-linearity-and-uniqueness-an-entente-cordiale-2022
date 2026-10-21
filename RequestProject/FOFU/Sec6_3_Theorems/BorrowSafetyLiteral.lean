module
public import RequestProject.FOFU.Sec6_3_Theorems.Statements

/-!
# Lemma 6.8 holds for Definition 6.4 as printed

With Definition 6.4 as printed (`gc = false`), a compatible heap has no resource entries
(`Compat.ress_eq_none`), so the first part of Lemma 6.8 (about identifiers of the initial
heap) is vacuous.  The second part, about identifiers created by the step, does hold:

* `Step.new_ident`: if `H` has no resource entries and `H ⊢ t ⤳_s H' ⊢ t'`, then every
  identifier `id'` with an entry in `H'` was created by the step (by `newArray` or
  `newRef`; `clone` cannot copy anything out of a heap without resources), and there is
  exactly one reference to it in `H'`, with permission `1`, which occurs in `t'`.

Hence its permissions in `t'` sum to `1` (`borrowSafety_literal`).  No typing or heap
compatibility is needed beyond the absence of resource entries.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

omit [Grades.PreorderedSemiring R] in
/-- Copying resources out of a heap without resource entries copies nothing. -/
lemma CopyHeap.eq_of_ress_none {n : ℕ} {H H' : Heap R n} {as : List ℕ} {θ : ℕ → ℕ}
    (h : CopyHeap H as θ H') (hH : ∀ j, H.ress j = none) : H' = H := by
  cases h with
  | nil => rfl
  | cons _ hres => rw [hH] at hres; cases hres

/-- **Identifiers created by a step.**  If `H` has no resource entries and
`H ⊢ t ⤳_s H' ⊢ t'`, then every identifier with an entry in `H'` has exactly one
reference in `H'`, of permission `1`, and this reference occurs in `t'`. -/
theorem Step.new_ident {n m : ℕ} {H : Heap R n} {t : Term R n} {s : R} {H' : Heap R m}
    {t' : Term R m} (hst : Step H t s H' t') (hH : ∀ j, H.ress j = none) :
    ∀ id', H'.ress id' ≠ none →
      ∃ a ∈ t'.refs, ∀ b p, H'.refs b = some (p, id') ↔ (b = a ∧ p = 1) := by
  induction hst with
  | var => intro id' h; exact absurd (hH id') h
  | beta => intro id' h; simp [Heap.snoc, hH id'] at h
  | exBeta => intro id' h; simp [Heap.snoc, hH id'] at h
  | tensorBeta => intro id' h; simp [Heap.snoc, hH id'] at h
  | boxBeta => intro id' h; simp [Heap.snoc, hH id'] at h
  | withBorrow => intro id' h; simp [Heap.snoc, hH id'] at h
  | clone _ _ _ hc =>
    rw [hc.eq_of_ress_none hH]
    intro id' h; simp [Heap.snoc, hH id'] at h
  | @newArray H k s a id ha hfresh =>
    intro id' h
    have e : id' = id := by
      by_contra hne
      simp [Heap.addRes, Function.update_of_ne hne, hH id'] at h
    subst e
    refine ⟨a, by simp [Term.refs], fun b p => ?_⟩
    by_cases hb : b = a
    · subst hb; simp [Heap.addRes, Heap.addRef, eq_comm]
    · simp only [Heap.addRes_refs, Heap.addRef, Function.update_of_ne hb, hb, false_and,
        iff_false]
      exact hfresh.2 b p
  | @newRef H v s a id _ ha hfresh =>
    intro id' h
    have e : id' = id := by
      by_contra hne
      simp [Heap.addRes, Function.update_of_ne hne, hH id'] at h
    subst e
    refine ⟨a, by simp [Term.refs], fun b p => ?_⟩
    by_cases hb : b = a
    · subst hb; simp [Heap.addRes, Heap.addRef, eq_comm]
    · simp only [Heap.addRes_refs, Heap.addRef, Function.update_of_ne hb, hb, false_and,
        iff_false]
      exact hfresh.2 b p
  | readArray _ hres => rw [hH] at hres; cases hres
  | writeArray _ hres => rw [hH] at hres; cases hres
  | deleteArray _ hres => rw [hH] at hres; cases hres
  | readRef _ hres => rw [hH] at hres; cases hres
  | readRefSplit _ hres => rw [hH] at hres; cases hres
  | swapRef _ hres => rw [hH] at hres; cases hres
  | freezeRef _ hres => rw [hH] at hres; cases hres
  | share => intro id' h; exact absurd (hH id') h
  | unborrow => intro id' h; exact absurd (hH id') h
  | push => intro id' h; exact absurd (hH id') h
  | pull => intro id' h; exact absurd (hH id') h
  | splitRef _ hres => rw [hH] at hres; cases hres
  | joinRef _ _ _ hres => rw [hH] at hres; cases hres
  | unitBeta => intro id' h; exact absurd (hH id') h
  | appL _ _ ih | appR _ _ _ ih | pairL _ _ ih | pairR _ _ _ ih | letPairCong _ _ ih
  | letUnitCong _ _ ih | letBoxCong _ _ ih | unpackCong _ _ ih | cloneCong _ _ ih
  | withBorrowL _ _ ih | withBorrowR _ _ _ ih | joinL _ _ ih | joinR _ _ _ ih =>
    intro id' h
    obtain ⟨a, ha, hu⟩ := ih hH id' h
    exact ⟨a, by simp [Term.refs, ha], hu⟩
  | boxCong _ ih | packCong _ ih | shareCong _ ih | splitCong _ ih | pushCong _ ih
  | pullCong _ ih | unborrowCong _ ih =>
    intro id' h
    obtain ⟨a, ha, hu⟩ := ih hH id' h
    exact ⟨a, by simp [Term.refs, ha], hu⟩

omit [Grades.PreorderedSemiring R] in
/-- If `a ∈ refs(t)` is the only reference to `id` in `H`, with permission `1`, the
permissions of `id` in `t` sum to `1`. -/
lemma permSum_eq_one {n m : ℕ} {H : Heap R n} {t : Term R m} {id a : ℕ} (ha : a ∈ t.refs)
    (hu : ∀ b p, H.refs b = some (p, id) ↔ (b = a ∧ p = 1)) : permSum H t id = 1 := by
  unfold permSum
  rw [Finset.sum_eq_single a]
  · rw [(hu a 1).2 ⟨rfl, rfl⟩]; simp
  · intro b _ hb
    rcases e : H.refs b with _ | ⟨p, id''⟩
    · rfl
    · simp only
      split_ifs with hid
      · subst hid; exact absurd ((hu b p).1 e).1 hb
      · rfl
  · intro h; exact absurd ha h

/-- **Lemma 6.8 holds** for Definition 6.4 as printed.  The part about identifiers of the
initial heap is vacuous (`Compat.ress_eq_none`); the part about new identifiers follows
from `Step.new_ident`. -/
theorem borrowSafety_literal : BorrowSafety (R := R) false := by
  intro n m Γ t A _ s Γ₀ Γs Δ H H' t' _ _ hc hst
  have hH := Compat.ress_eq_none hc
  refine ⟨fun id hid => absurd (hH id) hid, fun id' hid' _ => ?_⟩
  obtain ⟨a, ha, hu⟩ := hst.new_ident hH id' hid'
  exact permSum_eq_one ha hu

end FOFU
