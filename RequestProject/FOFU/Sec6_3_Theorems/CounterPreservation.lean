module
public import RequestProject.FOFU.Sec6_3_Theorems.CounterSetup

/-!
# Theorem 6.7 (Type preservation) is false

**Definition 6.4 as printed (`gc = false`).**  `newArray 3 : ∃ id. *(Array_id 𝔽)` in the
empty context and the empty heap, and `∅ ⊢ newArray 3 ⤳_1 ref₀ ↦_1 id₀, id₀ ↦ init ⊢
pack ⟨id₀, *ref₀⟩`.  The new heap contains a resource entry, so it is compatible with no
context at all (`Compat.ress_eq_none`).

**Repaired compatibility (`gc = true`).**  The context `ref₀ : Array_id₀ 𝔽` types

  `t = (λz. (z, *ref₀)) (split (*ref₀)) : (&_(1/2) A ⊗ &_(1/2) A) ⊗ &_1 A`

(`A = Array_id₀ 𝔽`): reference assumptions may be shared between the two sides of a
context addition, and `nec` gives `*ref₀` any permission.  The heap
`ref₀ ↦_1 id₀, id₀ ↦ init` is compatible with this context.  The argument reduces by
`⤳splitRef`, which *removes* `ref₀` from the heap, while `t'` still mentions `ref₀`
inside the function.  Any context typing `t'` must assume `ref₀`
(`HasType.refs_ne_none`) and any context compatible with the new heap only assumes
allocated references (`Compat.refs_ne_none`), so no `Γ'` exists.

Neither term involves `Ref` types, so the restriction of Theorem 6.7 to references of
non-function types holds.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

open Term

/-! ## Definition 6.4 as printed -/

/-- The type `∃ id. *(Array_id 𝔽)` of `newArray 3`. -/
def newArrayTy : Ty R 0 := Ty.ex (Ty.star (Ty.array (.bound 0)))

lemma newArray_typed : HasType (Ctx.empty : Ctx R 0 0) (app (prim .newArray) (nat 3)) newArrayTy :=
  HasType.app ctxAdd_empty (HasType.prim isZero_empty PrimTy.newArray) (HasType.nat 3 isZero_empty)

lemma newArray_step :
    Step (Heap.empty : Heap R 0) (app (prim .newArray) (nat 3)) 1
      ((Heap.empty.addRef 0 1 0).addRes 0 (.arr .init)) (pack (star (ref 0))) :=
  Step.newArray rfl ⟨rfl, fun _ _ h => by simp [Heap.empty] at h⟩

omit [Grades.PreorderedSemiring R] in
lemma refsFunFree_empty {k : ℕ} : (Ctx.empty : Ctx R k 0).RefsFunFree :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun _ _ h => by simp [Ctx.empty] at h⟩

/-- **Theorem 6.7 is false** for Definition 6.4 as printed. -/
theorem not_preservation_literal : ¬ Preservation (R := R) false := by
  intro h
  obtain ⟨Γ', Γs', Δ', -, -, -, hc⟩ :=
    h Ctx.empty _ newArrayTy newArray_typed refsFunFree_empty
      (by simp [Ty.RefsFunFree, newArrayTy]) 1 Ctx.empty Ctx.empty Ctx.empty Heap.empty _ _
      (ctxScale_empty 1) ctxAdd_empty Compat.empty newArray_step
  have := Compat.ress_eq_none hc 0
  simp [Heap.addRes] at this

/-! ## Repaired heap compatibility -/

/-- `A = Array_id₀ 𝔽`. -/
abbrev arrTy : Ty R 0 := (arrT : RefTy R 0).toTy

/-- `&_(1/2) A ⊗ &_(1/2) A`. -/
abbrev halvesTy : Ty R 0 :=
  Ty.tensor (Ty.borrow (.frac Frac.one.half) arrTy) (Ty.borrow (.frac Frac.one.half) arrTy)

/-- The function `λz. (z, *ref₀)`. -/
def danglingFun : Term R 0 := lam (pair (var 0) (star (ref 0)))

/-- The term `(λz. (z, *ref₀)) (split (*ref₀))`. -/
def danglingTerm : Term R 0 := app danglingFun (split (star (ref 0)))

/-- Its type `(&_(1/2) A ⊗ &_(1/2) A) ⊗ &_1 A`. -/
abbrev danglingTy : Ty R 0 := Ty.tensor halvesTy (Ty.borrow Perm.one arrTy)

omit [Grades.PreorderedSemiring R] in
lemma Γa_refs0 : (Γa : Ctx R 0 0).refs 0 = some arrT := by simp [Γa_refs]

lemma danglingFun_typed :
    HasType (Γa : Ctx R 0 0) danglingFun (Ty.lolli halvesTy danglingTy) := by
  refine HasType.abs (HasType.tensorI (Γ₁ := Γa.cons (some (.lin halvesTy)))
    (Γ₂ := Γa.cons none) ?_ ?_ ?_)
  · refine ⟨fun i => ?_, fun _ => RefAdd.self _⟩
    rw [Fin.fin_one_eq_zero i]
    exact AssmAdd.noneRight _
  · exact HasType.var rfl (fun j hj => absurd (Fin.fin_one_eq_zero j) hj)
  · refine star_ref0_typed (R := R) (Γ := Γa.cons none) (fun i => ?_) Γa_refs0 Perm.one
    rw [Fin.fin_one_eq_zero i]; trivial

lemma danglingTerm_typed : HasType (Γa : Ctx R 0 0) danglingTerm danglingTy :=
  HasType.app (ctxAdd_self_of_fin0 Γa) danglingFun_typed
    (HasType.split (star_ref0_typed (isZero_of_fin0 _) Γa_refs0 (.frac Frac.one)))

/-- The heap after splitting `ref₀` into `ref₁` and `ref₂`. -/
def HaSplit : Heap R 0 := (((Ha : Heap R 0).eraseRef 0).addRef 1 (1 / 2) 0).addRef 2 (1 / 2) 0

omit [Grades.PreorderedSemiring R] in
lemma HaSplit_refs0 : (HaSplit : Heap R 0).refs 0 = none := by
  simp [HaSplit, Heap.addRef, Heap.eraseRef, Function.update]

lemma split_ref0_step :
    Step (Ha : Heap R 0) (split (star (ref 0))) 1 HaSplit (pair (star (ref 1)) (star (ref 2))) := by
  have h := Step.splitRef (H := (Ha : Heap R 0)) (a := 0) (a₁ := 1) (a₂ := 2) (p := 1) (id := 0)
    (vr := .arr .init) (s := (1 : R)) (by simp [Ha_refs]) (by simp [Ha_ress])
    (by simp [Heap.eraseRef, Ha_refs]) (by simp [Heap.eraseRef, Ha_refs]) (by decide)
  simpa [HaSplit] using h

lemma danglingTerm_step :
    Step (Ha : Heap R 0) danglingTerm 1 HaSplit
      (app (danglingFun.weaken le_rfl) (pair (star (ref 1)) (star (ref 2)))) :=
  Step.appR le_rfl (IsValue.lam _) split_ref0_step

/-- **Theorem 6.7 is false** for the repaired heap compatibility. -/
theorem not_preservation_gc : ¬ Preservation (R := R) true := by
  intro h
  have hff : (Γa : Ctx R 0 0).RefsFunFree := by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun a T hT => ?_⟩
    rw [Γa_refs] at hT
    split_ifs at hT
    cases hT
    simp [Ty.RefsFunFree, arrT, RefTy.toTy]
  obtain ⟨Γ', Γs', Δ', ht, hs, hadd, hc⟩ :=
    h Γa danglingTerm danglingTy danglingTerm_typed hff
      (by simp [Ty.RefsFunFree, arrT, RefTy.toTy])
      1 Ctx.empty Γa Γa Ha _ _ (ctxScale_of_fin0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha
      danglingTerm_step
  have h0 : 0 ∈ (app (danglingFun.weaken le_rfl) (pair (star (ref 1)) (star (ref 2))) :
      Term R 0).refs := by
    simp [Term.refs, danglingFun]
  have hΓ' := ht.refs_ne_none h0
  rw [← hs.refs] at hΓ'
  exact Compat.refs_ne_none hc ((hadd.refs 0).ne_none_right hΓ') HaSplit_refs0

end FOFU
