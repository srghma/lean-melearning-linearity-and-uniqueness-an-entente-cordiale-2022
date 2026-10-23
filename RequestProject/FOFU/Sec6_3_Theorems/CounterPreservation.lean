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
(`HasType.refOccurs_ne_none`) and any context compatible with the new heap only assumes
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
def newArrayTy {k : ℕ} : Ty R k := Ty.ex (Ty.star (Ty.array .zero))

lemma newArray_typed {k n ρ : ℕ} :
    HasType (TCtx.empty : TCtx R k n ρ) (app (prim .newArray) (nat 3)) newArrayTy :=
  HasType.app ctxAdd_empty (HasType.prim TCtx.IsZero.empty PrimTy.newArray)
    (HasType.nat 3 TCtx.IsZero.empty)

/-- `∅ ⊢ newArray 3 ⤳_1 ref₀ ↦_1 id₀, id₀ ↦ init ⊢ pack ⟨id₀, *ref₀⟩`. -/
lemma newArray_step :
    Step (Heap.empty : Heap R 0 0 0) (app (prim .newArray) (nat 3)) 1 0 1 1 Ha
      (pack (star (ref .zero))) :=
  Step.newArray

omit [Grades.PreorderedSemiring R] in
lemma refsFunFree_empty {k n ρ : ℕ} : (TCtx.empty : TCtx R k n ρ).RefsFunFree :=
  ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ h => by simp at h⟩

/-- **Theorem 6.7 is false** for Definition 6.4 as printed. -/
theorem not_preservation_literal : ¬ Preservation (R := R) false := by
  intro h
  obtain ⟨Γ', Γs', Δ', -, -, -, hc⟩ :=
    h TCtx.empty _ newArrayTy newArray_typed refsFunFree_empty
      (by simp [Ty.RefsFunFree, newArrayTy]) 1 TCtx.empty TCtx.empty TCtx.empty Heap.empty _ _
      (ctxScale_empty 1) ctxAdd_empty Compat.empty newArray_step
  have := Compat.ress_eq_none hc .zero
  simp at this

/-! ## Repaired heap compatibility -/

/-- `A = Array_id₀ 𝔽`. -/
abbrev arrTy : Ty R 1 := (arrT : RefTy R 1).toTy

/-- `&_(1/2) A ⊗ &_(1/2) A`. -/
abbrev halvesTy : Ty R 1 :=
  Ty.tensor (Ty.borrow (.frac Frac.one.half) arrTy) (Ty.borrow (.frac Frac.one.half) arrTy)

/-- The function `λz. (z, *ref₀)`. -/
def danglingFun : Term R 0 1 := lam (pair (var .zero) (star (ref .zero)))

/-- The term `(λz. (z, *ref₀)) (split (*ref₀))`. -/
def danglingTerm : Term R 0 1 := app danglingFun (split (star (ref .zero)))

/-- Its type `(&_(1/2) A ⊗ &_(1/2) A) ⊗ &_1 A`. -/
abbrev danglingTy : Ty R 1 := Ty.tensor halvesTy (Ty.borrow Perm.one arrTy)

lemma danglingFun_typed :
    HasType (Γa : TCtx R 1 0 1) danglingFun (Ty.lolli halvesTy danglingTy) := by
  refine HasType.abs (HasType.tensorI (Γ₁ := Γa.cons (some (.lin halvesTy)))
    (Γ₂ := Γa.cons none) (by ctx_add) (HasType.var (by pick_var)) ?_)
  exact star_ref0_typed (by zero_ctx) (by simp) Perm.one

lemma danglingTerm_typed : HasType (Γa : TCtx R 1 0 1) danglingTerm danglingTy :=
  HasType.app (ctxAdd_self_of_vars0 Γa) danglingFun_typed
    (HasType.split (star_ref0_typed (isZero_of_vars0 _) (by simp) (.frac Frac.one)))

/-- The heap after splitting `ref₀` into two new references `ref₁`, `ref₂` (the most
recent being `Var.zero`). -/
def HaSplit : Heap R 0 3 1 :=
  (((Ha : Heap R 0 1 1).eraseRef .zero).newRef Frac.one.half .zero).newRef Frac.one.half .zero

lemma split_ref0_step :
    Step (Ha : Heap R 0 1 1) (split (star (ref .zero))) 1 0 2 0 HaSplit
      (pair (star (ref (.succ .zero))) (star (ref .zero))) :=
  Step.splitRef (vr := .arr .init) (Ctx.Lookup.of_eq (by simp)) (Ctx.Lookup.of_eq (by simp))

lemma danglingTerm_step :
    Step (Ha : Heap R 0 1 1) danglingTerm 1 0 2 0 HaSplit
      (app (danglingFun.wk2 0 2) (pair (star (ref (.succ .zero))) (star (ref .zero)))) :=
  Step.appR (IsValue.lam _) split_ref0_step

/-- **Theorem 6.7 is false** for the repaired heap compatibility. -/
theorem not_preservation_gc : ¬ Preservation (R := R) true := by
  intro h
  have hff : (Γa : TCtx R 1 0 1).RefsFunFree := by
    unfold TCtx.RefsFunFree
    refine ⟨fun i => (nomatch i), fun i => (nomatch i), fun a T hT => ?_⟩
    simp only [Γa_refs, Option.some.injEq] at hT
    subst hT
    simp [Ty.RefsFunFree, arrT, RefTy.toTy]
  obtain ⟨Γ', Γs', Δ', ht, hs, hadd, hc⟩ :=
    h Γa danglingTerm danglingTy danglingTerm_typed hff
      (by simp [Ty.RefsFunFree, arrT, RefTy.toTy])
      1 TCtx.empty Γa Γa Ha _ _ (ctxScale_of_vars0 1 Γa) (ctxAdd_empty_left Γa) compat_Ha
      danglingTerm_step
  have h0 : (app (danglingFun.wk2 0 2) (pair (star (ref (.succ .zero))) (star (ref .zero))) :
      Term R 0 3).RefOccurs (.succ (.succ .zero)) := by
    exact .arg (.head (.arg (.head (.arg (.tail (.head (.arg (.head (.here rfl)))))))))
  have hΓ' := ht.refOccurs_ne_none h0
  rw [← hs.refs] at hΓ'
  exact Compat.refs_ne_none hc ((hadd.refs.get _).ne_none_right hΓ') rfl

end FOFU
