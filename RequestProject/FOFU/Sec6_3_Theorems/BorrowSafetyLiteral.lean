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
lemma CopyHeap.ress_none {n ρ ι e : ℕ} {H : Heap R n ρ ι} {as : List (Var ρ)}
    {H' : Heap R n (ρ + e) (ι + e)} {θ : Var ρ → Var (ρ + e)} (h : CopyHeap H as e H' θ)
    (hH : ∀ j, H.ress.get j = none) : ∀ j, H'.ress.get j = none := by
  induction h with
  | nil => exact hH
  | cons _ _ hres ih => exact absurd (hres.eq.symm.trans (ih _)) (by simp)

/-- **Identifiers created by a step.**  If `H` has no resource entries and
`H ⊢ t ⤳_s H' ⊢ t'`, then every identifier with an entry in `H'` has exactly one
reference in `H'`, of permission `1`, and this reference occurs in `t'`. -/
theorem Step.new_ident {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {t : Term R n ρ} {s : R}
    {H' : Heap R (n + d) (ρ + e) (ι + f)} {t' : Term R (n + d) (ρ + e)}
    (hst : Step H t s d e f H' t') (hH : ∀ j, H.ress.get j = none) :
    ∀ id', H'.ress.get id' ≠ none →
      ∃ a, t'.RefOccurs a ∧ ∀ b p, H'.refs.get b = some (p, id') ↔ (b = a ∧ p = Frac.one) := by
  induction hst with
  | var | share | unborrow | push | pull | unitBeta =>
    intro id' h; exact absurd (hH id') h
  | beta | exBeta | boxBeta | withBorrow | tensorBeta =>
    intro id' h; simp [hH] at h
  | clone _ _ _ hc =>
    intro id' h; simp [hc.ress_none hH] at h
  | newArray | newRef =>
    intro id' h
    cases id' with
    | succ j => simp [hH] at h
    | zero =>
      refine ⟨.zero, .arg (.head (.arg (.head (.here rfl)))), fun b p => ?_⟩
      cases b with
      | zero => simp [eq_comm]
      | succ b => simp
  | readArray _ hres | writeArray _ hres | deleteArray _ hres | readRef _ hres
  | readRefSplit _ hres | swapRef _ hres | freezeRef _ hres | splitRef _ hres
  | joinRef _ _ _ _ hres =>
    exact absurd (hres.eq.symm.trans (hH _)) (by simp)
  | appL _ ih | pairL _ ih | letPairCong _ ih | letUnitCong _ ih | letBoxCong _ ih
  | unpackCong _ ih | cloneCong _ ih | withBorrowL _ ih | joinL _ ih
  | boxCong _ ih | packCong _ ih | shareCong _ ih | splitCong _ ih | pushCong _ ih
  | pullCong _ ih | unborrowCong _ ih =>
    intro id' h
    obtain ⟨a, ha, hu⟩ := ih hH id' h
    exact ⟨a, .arg (.head ha), hu⟩
  | appR _ _ ih | pairR _ _ ih | withBorrowR _ _ ih | joinR _ _ ih =>
    intro id' h
    obtain ⟨a, ha, hu⟩ := ih hH id' h
    exact ⟨a, .arg (.tail (.head ha)), hu⟩

omit [Grades.PreorderedSemiring R] in
/-- If `a ∈ refs(t)` is the only reference to `id` in `H`, with permission `1`, the
permissions of `id` in `t` sum to `1`. -/
lemma permSum_eq_one {n ρ ι : ℕ} {H : Heap R n ρ ι} {t : Term R n ρ} {id : Var ι} {a : Var ρ}
    (ha : t.RefOccurs a) (hu : ∀ b p, H.refs.get b = some (p, id) ↔ (b = a ∧ p = Frac.one)) :
    permSum H t id = 1 := by
  unfold permSum
  rw [Finset.sum_eq_single a]
  · rw [(hu a Frac.one).2 ⟨rfl, rfl⟩]; simp [permOf]
  · intro b _ hb
    rcases e : H.refs.get b with _ | ⟨p, id''⟩
    · rfl
    · simp only [permOf]
      split_ifs with hid
      · subst hid; exact absurd ((hu b p).1 e).1 hb
      · rfl
  · intro h; exact absurd (Term.mem_refs.2 ha) h

/-- **Lemma 6.8 holds** for Definition 6.4 as printed.  The part about identifiers of the
initial heap is vacuous (`Compat.ress_eq_none`); the part about new identifiers follows
from `Step.new_ident`. -/
theorem borrowSafety_literal : BorrowSafety (R := R) false := by
  intro n ρ ι d e f Γ t A _ s Γ₀ Γs Δ H H' t' _ _ hc hst
  have hH := Compat.ress_eq_none hc
  refine ⟨fun id hid => absurd (hH id) hid, fun id' hid' _ => ?_⟩
  obtain ⟨a, ha, hu⟩ := hst.new_ident hH id' hid'
  exact permSum_eq_one ha hu

end FOFU
