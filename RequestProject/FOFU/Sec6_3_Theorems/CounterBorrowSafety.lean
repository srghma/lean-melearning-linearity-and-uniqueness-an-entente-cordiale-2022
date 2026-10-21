module
public import RequestProject.FOFU.Sec6_3_Theorems.CounterPreservation

/-!
# Lemma 6.8, Theorem 6.9 and Corollary 6.10 (borrow safety and uniqueness)

All three statements quantify over identifiers `id ∈ dom(H)` of the initial heap.  With
Definition 6.4 as printed, compatible heaps have no identifiers
(`Compat.ress_eq_none`), so these parts are vacuous; in particular Corollary 6.10 holds
vacuously (`uniqueness_literal`).  For Lemma 6.8 and Theorem 6.9 with the printed
definition, the second conjunct (about new identifiers) is not vacuous: Lemma 6.8 holds
(`borrowSafety_literal`, in `BorrowSafetyLiteral.lean`) and Theorem 6.9 is false
(`not_multiBorrowSafety_literal`, in `CounterMultiBorrowLiteral.lean`).

With the repaired heap compatibility (`gc = true`) all three statements are false; each
counterexample starts from the heap `ref₀ ↦_1 id₀, id₀ ↦ init` and the context
`ref₀ : Array_id₀ 𝔽` (`CounterSetup.lean`).

* **Lemma 6.8**: `clone [ref₀]_1 as x in x` steps (by `⤳clone β`) to a fresh heap
  variable `y`, bound to `pack ⟨id₁, *ref₁⟩` where `ref₁ ↦_1 id₁` is the copy.  The new
  identifier `id₁` is in `dom(H') \ dom(H)`, but `refs(y) = ∅`, so the sum of its
  permissions over `refs(t')` is `0`, not `1`.
* **Theorem 6.9**: `split (*ref₀)` reduces in one step to the value `(*ref₁, *ref₂)` with
  `ref₁ ↦_(1/2) id₀` and `ref₂ ↦_(1/2) id₀`; the permissions of `id₀` in the initial term
  sum to `1`, but no reference has permission `1` on `id₀` afterwards.
* **Corollary 6.10**: `unborrow (let (x, y) = split (*ref₀) in join x y) : *(Array_id₀ 𝔽)`
  reduces to the value `*ref₃` where `ref₃ ↦_1 id₀`.  The reference `ref₀ ∈ refs(t)` had
  `ref₀ ↦_1 id₀` in the initial heap but has been removed (by `⤳splitRef`), so
  `ref₀ ↦_1 id₀` does not hold in the final heap.  (Split and join always create new
  references, so the statement could only hold for references that are not borrowed.)
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

open Term

omit [Grades.PreorderedSemiring R] in
lemma weaken_refl {n : ℕ} (t : Term R n) : t.weaken le_rfl = t := rename_id t

/-! ## Corollary 6.10 holds vacuously for Definition 6.4 as printed -/

/-- With Definition 6.4 as printed, Corollary 6.10 holds vacuously: compatible heaps have
no identifiers, and the statement only concerns identifiers of the initial heap. -/
theorem uniqueness_literal : Uniqueness (R := R) false := by
  intro n m Γ t A _ s Γ₀ Γs Δ H H' v _ _ hc _ _ id hid
  exact absurd (Compat.ress_eq_none hc id) hid

/-! ## Lemma 6.8 with the repaired compatibility -/

/-- `A' = Array_id 𝔽` with `id` the bound identifier, so that `A'[id₀/id] = Array_id₀ 𝔽`. -/
abbrev arrBound : Ty R 1 := Ty.array (.bound 0)

/-- The term `clone [ref₀]_1 as x in x`. -/
def cloneTerm : Term R 0 := clone (box 1 (ref 0)) (var 0)

lemma cloneTerm_typed :
    HasType (Γa : Ctx R 0 0) cloneTerm (Ty.ex (Ty.star arrBound)) := by
  refine HasType.clone (A := arrTy) (A' := arrBound) (r := 1) (.rt 0) (ctxAdd_self_of_fin0 Γa)
    ?_ le_rfl (Cloneable.array _) rfl ?_
  · exact HasType.pr (ctxScale_of_fin0 1 Γa) (ref0_typed (isZero_of_fin0 _) Γa_refs0)
      (fun h => h)
  · exact HasType.var rfl (fun j hj => absurd (Fin.fin_one_eq_zero j) hj)

/-- The heap after copying the array: `ref₁ ↦_1 id₁, id₁ ↦ init` is added. -/
def HaCopy : Heap R 0 := ((Ha : Heap R 0).addRef 1 1 1).addRes 1 (.arr .init)

omit [Grades.PreorderedSemiring R] in
lemma copyHeap_Ha : CopyHeap (Ha : Heap R 0) [0] (fun a => a + 1) HaCopy := by
  refine CopyHeap.cons (q := 1) (id := 0) (id' := 1) (vr := .arr .init)
    (by simp [Ha_refs]) (by simp [Ha_ress]) (by simp [Ha_refs]) ⟨by simp [Ha_ress], ?_⟩
    (CopyHeap.nil _ _)
  intro a q h
  rw [Ha_refs] at h
  split_ifs at h
  simp at h

lemma cloneTerm_step :
    Step (Ha : Heap R 0) cloneTerm 1
      (HaCopy.snoc 1 (pack (star ((ref 0 : Term R 0).renameRefs (fun a => a + 1)))))
      (var 0 : Term R 1).openLast :=
  Step.clone (IsValue.ref 0) (List.nodup_singleton 0) (by simp [Term.refs]) copyHeap_Ha

/-- **Lemma 6.8 is false** for the repaired heap compatibility. -/
theorem not_borrowSafety_gc : ¬ BorrowSafety (R := R) true := by
  intro h
  have h2 := (h Γa cloneTerm _ cloneTerm_typed 1 Ctx.empty Γa Γa Ha _ _
    (ctxScale_of_fin0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha cloneTerm_step).2 1
    (by simp [Heap.snoc, HaCopy, Heap.addRes]) (by simp [Ha_ress])
  simp [permSum, Term.openLast, Term.rename, Term.refs] at h2

/-! ## Theorem 6.9 with the repaired compatibility -/

omit [Grades.PreorderedSemiring R] in
lemma HaSplit_refs (a : ℕ) :
    (HaSplit : Heap R 0).refs a =
      if a = 2 then some (1 / 2, 0) else if a = 1 then some (1 / 2, 0) else none := by
  simp only [HaSplit, Heap.addRef, Heap.eraseRef, Function.update]
  by_cases h2 : a = 2
  · subst h2; simp
  · by_cases h1 : a = 1
    · subst h1; simp
    · simp [h1, h2, Ha_refs]

omit [Grades.PreorderedSemiring R] in
/-- No reference has permission `1` on `id₀` after the split. -/
lemma HaSplit_no_full (a : ℕ) : (HaSplit : Heap R 0).refs a ≠ some (1, 0) := by
  rw [HaSplit_refs]
  split_ifs <;> simp

/-- **Theorem 6.9 is false** for the repaired heap compatibility. -/
theorem not_multiBorrowSafety_gc : ¬ MultiBorrowSafety (R := R) true := by
  intro h
  have h1 := (h Γa (split (star (ref 0))) halvesTy
    (HasType.split (star_ref0_typed (R := R) (isZero_of_fin0 _) Γa_refs0 (.frac Frac.one)))
    1 Ctx.empty Γa Γa Ha HaSplit _ (ctxScale_of_fin0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha
    (Steps.ext split_ref0_step (Steps.refl _ _ _))
    (IsValue.pair (IsValue.star (IsValue.ref 1)) (IsValue.star (IsValue.ref 2)))).1 0
    (by simp [Ha_ress]) (by simp [permSum, Term.refs, Ha_refs])
  obtain ⟨a, ha, -⟩ := h1
  exact HaSplit_no_full a ha

/-! ## Corollary 6.10 with the repaired compatibility -/

/-- The body `join x y` of `let (x, y) = _ in join x y` (`x` is index `1`, `y` index `0`). -/
def joinBody : Term R 2 := join (var 1) (var 0)

/-- The term `unborrow (let (x, y) = split (*ref₀) in join x y)`. -/
def reborrowTerm : Term R 0 := unborrow (letPair (split (star (ref 0))) joinBody)

lemma reborrowTerm_typed : HasType (Γa : Ctx R 0 0) reborrowTerm (Ty.star arrTy) := by
  have e : Frac.add Frac.one.half Frac.one.half (Frac.half_add_half _) = Frac.one :=
    Frac.add_half_half _
  have hj : HasType (((Γa : Ctx R 0 0).cons (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))).cons
      (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))) joinBody
      (Ty.borrow (.frac (Frac.add Frac.one.half Frac.one.half (Frac.half_add_half _))) arrTy) := by
    refine HasType.join (Frac.half_add_half _)
      (Γ₁ := ((Γa : Ctx R 0 0).cons (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))).cons none)
      (Γ₂ := ((Γa : Ctx R 0 0).cons none).cons (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy))))
      ⟨fun i => ?_, fun _ => RefAdd.self _⟩ ?_ ?_
    · cases i using Fin.cases with
      | zero => exact AssmAdd.noneLeft _
      | succ i =>
        rw [Fin.fin_one_eq_zero i]
        exact AssmAdd.noneRight _
    · refine HasType.var rfl (fun j hj => ?_)
      cases j using Fin.cases with
      | zero => trivial
      | succ j => rw [Fin.fin_one_eq_zero j] at hj; exact absurd rfl hj
    · refine HasType.var rfl (fun j hj => ?_)
      cases j using Fin.cases with
      | zero => exact absurd rfl hj
      | succ j => rw [Fin.fin_one_eq_zero j]; trivial
  rw [e] at hj
  exact HasType.unborrow (HasType.tensorE (ctxAdd_self_of_fin0 Γa)
    (HasType.split (star_ref0_typed (isZero_of_fin0 _) Γa_refs0 (.frac Frac.one))) hj)

/-- The heap after the `⊗β` step: `x' ↦_1 *ref₁, y' ↦_1 *ref₂`. -/
def HaVars : Heap R 2 :=
  ((HaSplit : Heap R 0).snoc 1 (star (ref 1))).snoc 1 ((star (ref 2) : Term R 0).rename Fin.castSucc)

/-- The final heap after joining: `ref₁`, `ref₂` are replaced by `ref₃ ↦_1 id₀`. -/
def HaJoined : Heap R 2 := (((HaVars : Heap R 2).eraseRef 1).eraseRef 2).addRef 3 (1 / 2 + 1 / 2) 0

lemma HaVars_vars0 : (HaVars : Heap R 2).vars 0 = (1, star (ref 1)) := rfl
lemma HaVars_vars1 : (HaVars : Heap R 2).vars 1 = (1, star (ref 2)) := rfl

lemma HaVars_refs (a : ℕ) : (HaVars : Heap R 2).refs a = (HaSplit : Heap R 0).refs a := rfl

lemma var_step_one {n : ℕ} {H : Heap R n} {i : Fin n} (h : (H.vars i).1 = 1) :
    Step H (var i) 1 H (H.vars i).2 :=
  Step.var ⟨0, by rw [h, add_zero]⟩

lemma reborrow_steps :
    Steps (Ha : Heap R 0) reborrowTerm 1 HaJoined (star (ref 3)) := by
  -- step 1: split `*ref₀`
  have s1 : Step (Ha : Heap R 0) reborrowTerm 1 HaSplit
      (unborrow (letPair (pair (star (ref 1)) (star (ref 2))) joinBody)) := by
    have := Step.unborrowCong (Step.letPairCong (t₂ := (joinBody : Term R 2)) le_rfl
      split_ref0_step)
    simpa [weaken_refl, joinBody, Term.rename] using this
  -- step 2: `⊗β`
  have s2 : Step (HaSplit : Heap R 0)
      (unborrow (letPair (pair (star (ref 1)) (star (ref 2))) joinBody)) 1 HaVars
      (unborrow (join (var 0) (var 1))) :=
    Step.unborrowCong (Step.tensorBeta (IsValue.star (IsValue.ref 1)) (IsValue.star (IsValue.ref 2)))
  -- step 3: look up `x'`
  have s3 : Step (HaVars : Heap R 2) (unborrow (join (var 0) (var 1))) 1 HaVars
      (unborrow (join (star (ref 1)) (var 1))) := by
    have := Step.unborrowCong (Step.joinL (t₂ := (var 1 : Term R 2)) le_rfl
      (var_step_one (H := (HaVars : Heap R 2)) (i := 0) rfl))
    simpa [weaken_refl, HaVars_vars0] using this
  -- step 4: look up `y'`
  have s4 : Step (HaVars : Heap R 2) (unborrow (join (star (ref 1)) (var 1))) 1 HaVars
      (unborrow (join (star (ref 1)) (star (ref 2)))) := by
    have := Step.unborrowCong (Step.joinR le_rfl (IsValue.star (IsValue.ref 1))
      (var_step_one (H := (HaVars : Heap R 2)) (i := 1) rfl))
    simpa [weaken_refl, HaVars_vars1] using this
  -- step 5: join into the fresh reference `ref₃`
  have s5 : Step (HaVars : Heap R 2) (unborrow (join (star (ref 1)) (star (ref 2)))) 1 HaJoined
      (unborrow (star (ref 3))) :=
    Step.unborrowCong (Step.joinRef (vr := .arr .init) (by simp [HaVars_refs, HaSplit_refs])
      (by simp [HaVars_refs, HaSplit_refs]) (by decide)
      (by simp [HaVars, Heap.snoc, HaSplit, Heap.addRef, Heap.eraseRef, Ha_ress, ResVal.rename,
        ArrVal.rename])
      (by simp [Heap.eraseRef, HaVars_refs, HaSplit_refs]))
  -- step 6: `⤳un&`
  have s6 : Step (HaJoined : Heap R 2) (unborrow (star (ref 3))) 1 HaJoined (star (ref 3)) :=
    Step.unborrow (IsValue.ref 3)
  exact Steps.ext s1 (Steps.ext s2 (Steps.ext s3 (Steps.ext s4 (Steps.ext s5
    (Steps.ext s6 (Steps.refl _ _ _))))))

/-- **Corollary 6.10 is false** for the repaired heap compatibility. -/
theorem not_uniqueness_gc : ¬ Uniqueness (R := R) true := by
  intro h
  have h1 := (h Γa reborrowTerm arrTy reborrowTerm_typed 1 Ctx.empty Γa Γa Ha HaJoined (ref 3)
    (ctxScale_of_fin0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha reborrow_steps (IsValue.ref 3) 0
    (by simp [Ha_ress])).1 0 (by simp [reborrowTerm, Term.refs]) (by simp [Ha_refs])
  have : (HaJoined : Heap R 2).refs 0 = none := by
    simp [HaJoined, Heap.addRef, Heap.eraseRef, Function.update, HaVars_refs, HaSplit_refs]
  rw [this] at h1
  exact absurd h1 (by simp)

end FOFU
