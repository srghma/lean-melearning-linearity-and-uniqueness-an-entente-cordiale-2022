module
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.Preservation

/-!
# Lemma 6.8, Theorem 6.9 and Corollary 6.10 (borrow safety and uniqueness)

All three statements quantify over identifiers `id ∈ dom(H)` of the initial heap.  With
Definition 6.4 as printed, compatible heaps have no identifiers
(`Compat.ress_eq_none`), so these parts are vacuous; in particular Corollary 6.10 holds
vacuously (`uniqueness_literal`).  For Lemma 6.8 and Theorem 6.9 with the printed
definition, the second conjunct (about new identifiers) is not vacuous: Lemma 6.8 holds
(`borrowSafety_literal`, in `BorrowSafetyLiteral.lean`) and Theorem 6.9 is false
(`not_multiBorrowSafety_literal`, in `MultiBorrowLiteral.lean`).

With the repaired heap compatibility (`gc = true`) all three statements are false; each
counterexample starts from the heap `ref₀ ↦_1 id₀, id₀ ↦ init` and the context
`ref₀ : Array_id₀ 𝔽` (`Setup.lean`).

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

/-! ## Corollary 6.10 holds vacuously for Definition 6.4 as printed -/

/-- With Definition 6.4 as printed, Corollary 6.10 holds vacuously: compatible heaps have
no identifiers, and the statement only concerns identifiers of the initial heap. -/
theorem uniqueness_literal : Uniqueness (R := R) false := by
  intro n ρ ι n' ρ' ι' Γ t A _ s Γ₀ Γs Δ H H' v θr θi _ _ hc _ _ id hid
  exact absurd (Compat.ress_eq_none hc id) hid

/-! ## Lemma 6.8 with the repaired compatibility -/

/-- `A' = Array_id 𝔽` with `id` the bound identifier, so that `A'[id₀/id] = Array_id₀ 𝔽`. -/
abbrev arrBound : Ty R 2 := Ty.array .zero

/-- The term `clone [ref₀]_1 as x in x`. -/
def cloneTerm : Term R 0 1 := clone (box 1 (ref .zero)) (var .zero)

lemma cloneTerm_typed :
    HasType (Γa : TCtx R 1 0 1) cloneTerm (Ty.ex (Ty.star arrBound)) := by
  refine HasType.clone (A := arrTy) (A' := arrBound) (r := 1) .zero (ctxAdd_self_of_vars0 Γa)
    ?_ le_rfl rfl rfl (HasType.var (by pick_var))
  exact HasType.pr (ctxScale_of_vars0 1 Γa) (ref0_typed (isZero_of_vars0 _) (by simp))
    (by rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩))

/-- The heap after copying the array: `ref₁ ↦_1 id₁, id₁ ↦ init` is added. -/
def HaCopy : Heap R 0 2 2 := ((Ha : Heap R 0 1 1).addId (some (.arr .init))).newRef Frac.one .zero

omit [Grades.PreorderedSemiring R] in
lemma copyHeap_Ha :
    CopyHeap (Ha : Heap R 0 1 1) [.zero] 1 HaCopy
      (fun b => if b = .zero then .zero else (id b).succ) :=
  CopyHeap.cons (e := 0) (H' := Ha) (θ := id) (q := Frac.one) (id := .zero) (vr := .arr .init)
    CopyHeap.nil (Ctx.Lookup.of_eq rfl) (Ctx.Lookup.of_eq rfl)

lemma cloneTerm_step :
    Step (Ha : Heap R 0 1 1) cloneTerm 1 1 1 1
      (HaCopy.snoc 1 (pack (star (renameRefs (fun b => if b = .zero then .zero else (id b).succ)
        (ref .zero : Term R 0 1)))))
      (renameRefs (Var.shiftN 1) (var .zero : Term R 1 1)) :=
  Step.clone (IsValue.ref .zero) (List.nodup_singleton _)
    (fun a => by
      cases a with
      | zero => exact ⟨fun _ => .here rfl, fun _ => List.mem_singleton_self _⟩
      | succ a => cases a)
    copyHeap_Ha

/-- **Lemma 6.8 is false** for the repaired heap compatibility. -/
theorem not_borrowSafety_gc : ¬ BorrowSafety (R := R) true := by
  intro h
  have h2 := (h Γa cloneTerm _ cloneTerm_typed 1 TCtx.empty Γa Γa Ha _ _
    (ctxScale_of_vars0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha cloneTerm_step).2 .zero
    (by change some _ ≠ none; simp) (fun id h => by cases h)
  have h0 : permSum (HaCopy.snoc 1 (pack (star (renameRefs
      (fun b => if b = .zero then .zero else (id b).succ) (ref .zero : Term R 0 1)))))
      (renameRefs (Var.shiftN 1) (var .zero : Term R 1 1)) .zero = 0 := by
    simp [permSum, Term.refs, Term.RefOccurs]
  rw [h0] at h2
  exact zero_ne_one h2

/-! ## Theorem 6.9 with the repaired compatibility -/

omit [Grades.PreorderedSemiring R] in
/-- No reference has permission `1` on `id₀` after the split. -/
lemma HaSplit_no_full (a : Var 3) : (HaSplit : Heap R 0 3 1).refs.get a ≠ some (Frac.one, .zero) := by
  have hhalf : Frac.one.half ≠ Frac.one := by
    intro e
    have := congrArg Subtype.val e
    norm_num at this
  cases a with
  | zero => change some (Frac.one.half, (Var.zero : Var 1)) ≠ _; simp [hhalf]
  | succ a =>
    cases a with
    | zero => change some (Frac.one.half, (Var.zero : Var 1)) ≠ _; simp [hhalf]
    | succ a =>
      cases a with
      | zero => change none ≠ _; simp
      | succ a => cases a

omit [Grades.PreorderedSemiring R] in
lemma refs_split_star_ref0 : (split (star (ref .zero)) : Term R 0 1).refs = {Var.zero} := by
  ext a
  cases a with
  | zero => simpa using (.arg (.head (.arg (.head (.here rfl)))) :
      (split (star (ref .zero)) : Term R 0 1).RefOccurs .zero)
  | succ a => cases a

/-- **Theorem 6.9 is false** for the repaired heap compatibility. -/
theorem not_multiBorrowSafety_gc : ¬ MultiBorrowSafety (R := R) true := by
  intro h
  have h1 := (h Γa (split (star (ref .zero))) halvesTy
    (HasType.split (star_ref0_typed (R := R) (isZero_of_vars0 _) (by simp) (.frac Frac.one)))
    1 TCtx.empty Γa Γa Ha HaSplit _ _ _ (ctxScale_of_vars0 1 Γa) (ctxAdd_empty_left Γa)
    compat_Ha (Steps.ext split_ref0_step (Steps.refl _ _ _))
    (IsValue.pair (IsValue.star (IsValue.ref _)) (IsValue.star (IsValue.ref _)))).1 .zero
    (by simp) (by simp [permSum, refs_split_star_ref0, permOf, Frac.one])
  obtain ⟨a, ha, -⟩ := h1
  exact HaSplit_no_full a ha

/-! ## Corollary 6.10 with the repaired compatibility -/

/-- The body `join x y` of `let (x, y) = _ in join x y` (`y` is `Var.zero`). -/
def joinBody {ρ : ℕ} : Term R 2 ρ := join (var (.succ .zero)) (var .zero)

/-- The term `unborrow (let (x, y) = split (*ref₀) in join x y)`. -/
def reborrowTerm : Term R 0 1 := unborrow (letPair (split (star (ref .zero))) joinBody)

lemma reborrowTerm_typed : HasType (Γa : TCtx R 1 0 1) reborrowTerm (Ty.star arrTy) := by
  have e : Frac.add Frac.one.half Frac.one.half (Frac.half_add_half _) = Frac.one :=
    Frac.add_half_half _
  have hj : HasType (((Γa : TCtx R 1 0 1).cons
      (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))).cons
      (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))) joinBody
      (Ty.borrow (.frac (Frac.add Frac.one.half Frac.one.half (Frac.half_add_half _))) arrTy) :=
    HasType.join (Frac.half_add_half _)
      (Γ₁ := ((Γa : TCtx R 1 0 1).cons
        (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy)))).cons none)
      (Γ₂ := ((Γa : TCtx R 1 0 1).cons none).cons
        (some (.lin (Ty.borrow (.frac Frac.one.half) arrTy))))
      (by ctx_add) (HasType.var (by pick_var)) (HasType.var (by pick_var))
  rw [e] at hj
  exact HasType.unborrow (HasType.tensorE (ctxAdd_self_of_vars0 Γa)
    (HasType.split (star_ref0_typed (isZero_of_vars0 _) (by simp) (.frac Frac.one))) hj)

/-- The heap after the `⊗β` step: `x' ↦_1 *ref₁, y' ↦_1 *ref₂`. -/
def HaVars : Heap R 2 3 1 :=
  ((HaSplit : Heap R 0 3 1).snoc 1 (star (ref (.succ .zero)))).snoc 1
    ((star (ref .zero) : Term R 0 3).rename Var.succ)

/-- The final heap after joining: the two halves are replaced by a new reference
`ref₃ ↦_1 id₀`. -/
def HaJoined : Heap R 2 4 1 :=
  (((HaVars : Heap R 2 3 1).eraseRef (.succ .zero)).eraseRef .zero).newRef
    (Frac.one.half.add Frac.one.half (Frac.half_add_half _)) .zero

lemma var_step_one {n ρ ι : ℕ} {H : Heap R n ρ ι} {i : Var n} {v : Term R n ρ}
    (h : H.vars.get i = (1, v)) : Step H (var i) 1 0 0 0 H v :=
  Step.var (Ctx.Lookup.of_eq h) ⟨0, by rw [add_zero]⟩

lemma reborrow_steps :
    ∃ (θr : Var 1 → Var 4) (θi : Var 1 → Var 1),
      Steps (Ha : Heap R 0 1 1) reborrowTerm 1 HaJoined (star (ref .zero)) θr θi ∧
        θr .zero = .succ (.succ (.succ .zero)) := by
  -- step 1: split `*ref₀`
  have s1 : Step (Ha : Heap R 0 1 1) reborrowTerm 1 0 2 0 HaSplit
      (unborrow (letPair (pair (star (ref (.succ .zero))) (star (ref .zero))) joinBody)) :=
    Step.unborrowCong (Step.letPairCong split_ref0_step)
  -- step 2: `⊗β`
  have s2 : Step (HaSplit : Heap R 0 3 1)
      (unborrow (letPair (pair (star (ref (.succ .zero))) (star (ref .zero))) joinBody)) 1
      2 0 0 HaVars (unborrow joinBody) :=
    Step.unborrowCong (Step.tensorBeta (IsValue.star (IsValue.ref _))
      (IsValue.star (IsValue.ref _)))
  -- step 3: look up `x'`
  have s3 : Step (HaVars : Heap R 2 3 1) (unborrow joinBody) 1 0 0 0 HaVars
      (unborrow (join (star (ref (.succ .zero))) (var .zero))) :=
    Step.unborrowCong (Step.joinL (var_step_one rfl))
  -- step 4: look up `y'`
  have s4 : Step (HaVars : Heap R 2 3 1) (unborrow (join (star (ref (.succ .zero))) (var .zero)))
      1 0 0 0 HaVars (unborrow (join (star (ref (.succ .zero))) (star (ref .zero)))) :=
    Step.unborrowCong (Step.joinR (IsValue.star (IsValue.ref _)) (var_step_one rfl))
  -- step 5: join into a new reference
  have s5 : Step (HaVars : Heap R 2 3 1)
      (unborrow (join (star (ref (.succ .zero))) (star (ref .zero)))) 1 0 1 0 HaJoined
      (unborrow (star (ref .zero))) :=
    Step.unborrowCong (Step.joinRef (Frac.half_add_half _) (Ctx.Lookup.of_eq rfl)
      (Ctx.Lookup.of_eq rfl) (by simp) (Ctx.Lookup.of_eq rfl))
  -- step 6: `⤳un&`
  have s6 : Step (HaJoined : Heap R 2 4 1) (unborrow (star (ref .zero))) 1 0 0 0 HaJoined
      (star (ref .zero)) :=
    Step.unborrow (IsValue.ref _)
  exact ⟨_, _, Steps.ext s1 (Steps.ext s2 (Steps.ext s3 (Steps.ext s4 (Steps.ext s5
    (Steps.ext s6 (Steps.refl _ _ _)))))), rfl⟩

/-- **Corollary 6.10 is false** for the repaired heap compatibility. -/
theorem not_uniqueness_gc : ¬ Uniqueness (R := R) true := by
  intro h
  obtain ⟨θr, θi, hsteps, hθ⟩ := reborrow_steps (R := R)
  have h1 := (h Γa reborrowTerm arrTy reborrowTerm_typed 1 TCtx.empty Γa Γa Ha HaJoined
    (ref .zero) θr θi (ctxScale_of_vars0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha hsteps
    (IsValue.ref _) .zero (by simp)).1 .zero
    (Term.mem_refs.2 (.arg (.head (.arg (.head (.arg (.head (.arg (.head (.here rfl))))))))))
    (by simp)
  rw [hθ] at h1
  change none = _ at h1
  cases h1

end FOFU
