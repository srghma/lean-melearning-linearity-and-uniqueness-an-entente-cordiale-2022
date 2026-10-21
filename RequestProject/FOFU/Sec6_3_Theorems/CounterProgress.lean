module
public import RequestProject.FOFU.Sec6_3_Theorems.Statements

/-!
# Theorem 6.6 (Progress) is false

The closed term `split (*())` has type `&_(1/2) unit ⊗ &_(1/2) unit` in the empty
context: by the runtime rule `nec`, `*()` has type `&_p unit` for *any* permission `p`,
in particular `p = 1`, and `split` accepts any fractional borrow.  The paper's remark that
"the type `A` above will always contain a resource identifier" is not enforced by the
typing rule of `split`.

`split (*())` is not a value, and it cannot reduce: the only reduction rule for `split`
(`⤳splitRef`) requires its argument to be `*ref` for a reference `ref`, and `*()` is a
value (there is nothing to reduce inside it, even with the reconstructed congruence
rules).  With the empty heap (`∅ ⋈ ∅`), this refutes progress for both variants of
heap compatibility.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

open Term

/-- The stuck term `split (*())`. -/
def stuckSplit {n : ℕ} : Term R n := split (star unit)

/-- Its type `&_(1/2) unit ⊗ &_(1/2) unit`. -/
def stuckSplitTy : Ty R 0 :=
  Ty.tensor (Ty.borrow (.frac Frac.one.half) Ty.unit) (Ty.borrow (.frac Frac.one.half) Ty.unit)

lemma isZero_empty {k : ℕ} : (Ctx.empty : Ctx R k 0).IsZero := fun i => i.elim0

/-- `∅ ⊢ split (*()) : &_(1/2) unit ⊗ &_(1/2) unit`. -/
theorem stuckSplit_typed : HasType (Ctx.empty : Ctx R 0 0) stuckSplit stuckSplitTy :=
  HasType.split (HasType.nec (.frac Frac.one) isZero_empty (HasType.unitI (fun i => i.elim0)))

omit [Grades.PreorderedSemiring R] in
/-- `split (*())` is not a value. -/
theorem stuckSplit_not_value {n : ℕ} : ¬ IsValue (stuckSplit : Term R n) := by
  intro h
  cases h with
  | prim hs _ => cases hs

/-- `*()` does not reduce. -/
theorem star_unit_no_step {n m : ℕ} (H : Heap R n) (s : R) (H' : Heap R m) (t' : Term R m) :
    ¬ Step H (star unit) s H' t' := by
  intro h; cases h

/-- `split (*())` does not reduce, in any heap. -/
theorem stuckSplit_no_step {n m : ℕ} (H : Heap R n) (s : R) (H' : Heap R m) (t' : Term R m) :
    ¬ Step H stuckSplit s H' t' := by
  intro h
  cases h with
  | splitCong h' => exact star_unit_no_step _ _ _ _ h'

lemma ctxScale_empty (s : R) : CtxScale s (Ctx.empty : Ctx R 0 0) Ctx.empty :=
  ⟨fun i => i.elim0, rfl⟩

lemma ctxAdd_empty : CtxAdd (Ctx.empty : Ctx R 0 0) Ctx.empty Ctx.empty :=
  ⟨fun i => i.elim0, fun _ => RefAdd.noneLeft _⟩

/-- **Theorem 6.6 is false** (for Definition 6.4 as printed and for its repair). -/
theorem not_progress (gc : Bool) : ¬ Progress (R := R) gc := by
  intro h
  rcases h Ctx.empty stuckSplit stuckSplitTy stuckSplit_typed with hv | hstep
  · exact stuckSplit_not_value hv
  · obtain ⟨m, H', t', hs⟩ := hstep 1 Ctx.empty Ctx.empty Ctx.empty Heap.empty
      (ctxScale_empty 1) ctxAdd_empty Compat.empty
    exact stuckSplit_no_step _ _ _ _ hs

end FOFU
