module
public import RequestProject.FOFU.Sec6_3_Theorems.CounterProgress
public import RequestProject.FOFU.Sec6_1_Preliminaries.TypingRefs

/-!
# A one-array configuration used by several counterexamples

The counterexamples to Theorem 6.7 (with the repaired heap compatibility), Lemma 6.8,
Theorem 6.9 and Corollary 6.10 all start from the heap

  `Ha = ref₀ ↦_1 id₀, id₀ ↦ init`

holding a single (uninitialised) array, and the context `Γa = ref₀ : Array_id₀ 𝔽`.
`Ha ⋈ Γa` holds for the repaired heap compatibility (`gc = true`, `compat_Ha`), but not
for Definition 6.4 as printed (`Compat.ress_eq_none`).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The reference type `Array_id₀ 𝔽`. -/
def arrT : RefTy R 0 := ⟨.array, .rt 0, .float⟩

/-- The context `ref₀ : Array_id₀ 𝔽`. -/
def Γa : Ctx R 0 0 := Ctx.empty.addRef 0 arrT

/-- The heap `ref₀ ↦_1 id₀, id₀ ↦ init`. -/
def Ha : Heap R 0 := (Heap.empty.addRef 0 1 0).addRes 0 (.arr .init)

omit [Grades.PreorderedSemiring R] in
lemma Ha_refs (a : ℕ) : (Ha : Heap R 0).refs a = if a = 0 then some (1, 0) else none := by
  by_cases h : a = 0 <;> simp [Ha, Heap.addRef, Heap.addRes, Heap.empty, Function.update, h]

omit [Grades.PreorderedSemiring R] in
lemma Ha_ress (id : ℕ) :
    (Ha : Heap R 0).ress id = if id = 0 then some (.arr .init) else none := by
  by_cases h : id = 0 <;> simp [Ha, Heap.addRef, Heap.addRes, Heap.empty, Function.update, h]

omit [Grades.PreorderedSemiring R] in
lemma Γa_refs (a : ℕ) : (Γa : Ctx R 0 0).refs a = if a = 0 then some arrT else none := by
  by_cases h : a = 0 <;> simp [Γa, Ctx.addRef, Ctx.empty, Function.update, h]

omit [Grades.PreorderedSemiring R] in
/-- Reference assumptions can always be added to themselves. -/
lemma RefAdd.self {k : ℕ} (x : Option (RefTy R k)) : RefAdd x x x := by
  cases x with
  | none => exact RefAdd.noneLeft none
  | some T => exact RefAdd.both T

/-- A context without variables is its own sum. -/
lemma ctxAdd_self_of_fin0 {k : ℕ} (Γ : Ctx R k 0) : CtxAdd Γ Γ Γ :=
  ⟨fun i => i.elim0, fun _ => RefAdd.self _⟩

/-- `∅ + Γ = Γ` for contexts without variables. -/
lemma ctxAdd_empty_left {k : ℕ} (Γ : Ctx R k 0) : CtxAdd Ctx.empty Γ Γ :=
  ⟨fun i => i.elim0, fun _ => RefAdd.noneLeft _⟩

/-- `s · Γ = Γ` for contexts without variables. -/
lemma ctxScale_of_fin0 {k : ℕ} (s : R) (Γ : Ctx R k 0) : CtxScale s Γ Γ :=
  ⟨fun i => i.elim0, rfl⟩

lemma isZero_of_fin0 {k : ℕ} (Γ : Ctx R k 0) : Γ.IsZero := fun i => i.elim0

/-- `Ha ⋈ Γa` with the repaired heap compatibility. -/
theorem compat_Ha : Compat true (Ha : Heap R 0) Γa := by
  refine Compat.extRes (Γ := Ctx.empty) (γ := Ctx.empty) (Δ := Ctx.empty) rfl rfl rfl
    (fun i => i.elim0) (ResValTy.arr (ArrValTy.init _)) ctxAdd_empty ?_
  exact Compat.gcRes rfl rfl Compat.empty

/-- `Γ ⊢ ref₀ : Array_id₀ 𝔽` in any context assuming `ref₀ : Array_id₀ 𝔽` with no
variables. -/
lemma ref0_typed {n : ℕ} {Γ : Ctx R 0 n} (hz : Γ.IsZero) (h : Γ.refs 0 = some arrT) :
    HasType Γ (.ref 0) (arrT.toTy) :=
  HasType.ref hz h

/-- `*ref₀ : &_p (Array_id₀ 𝔽)` for any permission `p`. -/
lemma star_ref0_typed {n : ℕ} {Γ : Ctx R 0 n} (hz : Γ.IsZero) (h : Γ.refs 0 = some arrT)
    (p : Perm) : HasType Γ (.star (.ref 0)) (Ty.borrow p arrT.toTy) :=
  HasType.nec p hz (HasType.ref (fun _ => trivial) h)

end FOFU
