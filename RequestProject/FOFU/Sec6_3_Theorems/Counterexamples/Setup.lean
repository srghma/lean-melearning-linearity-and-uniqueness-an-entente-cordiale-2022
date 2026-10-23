module
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.Progress
public import RequestProject.FOFU.Sec6_1_Preliminaries.TypingRefs
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# A one-array configuration used by several counterexamples

The counterexamples to Theorem 6.7 (with the repaired heap compatibility), Lemma 6.8,
Theorem 6.9 and Corollary 6.10 all start from the heap

  `Ha = ref₀ ↦_1 id₀, id₀ ↦ init`

holding a single (uninitialised) array, and the context `Γa = ref₀ : Array_id₀ 𝔽`.  Both
have one reference `ref₀ = Var.zero` and one identifier `id₀ = Var.zero` in scope.
`Ha ⋈ Γa` holds for the repaired heap compatibility (`gc = true`, `compat_Ha`), but not
for Definition 6.4 as printed (`Compat.ress_eq_none`).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The reference type `Array_id₀ 𝔽`. -/
def arrT : RefTy R 1 := ⟨.array, .zero, .float⟩

/-- The context `ref₀ : Array_id₀ 𝔽`. -/
def Γa : TCtx R 1 0 1 := TCtx.empty.addRef (some arrT)

/-- The heap `ref₀ ↦_1 id₀, id₀ ↦ init`. -/
def Ha : Heap R 0 1 1 := (Heap.empty.addId (some (.arr .init))).newRef Frac.one .zero

omit [Grades.PreorderedSemiring R] in
@[simp] lemma Ha_refs (a : Var 1) : (Ha : Heap R 0 1 1).refs.get a = some (Frac.one, .zero) := by
  cases a with
  | zero => rfl
  | succ a => cases a

omit [Grades.PreorderedSemiring R] in
@[simp] lemma Ha_ress (id : Var 1) : (Ha : Heap R 0 1 1).ress.get id = some (.arr .init) := by
  cases id with
  | zero => rfl
  | succ a => cases a

omit [Grades.PreorderedSemiring R] in
@[simp] lemma Γa_refs (a : Var 1) : (Γa : TCtx R 1 0 1).refs.get a = some arrT := by
  cases a with
  | zero => rfl
  | succ a => cases a

/-- A context without variables is its own sum. -/
lemma ctxAdd_self_of_vars0 {k ρ : ℕ} (Γ : TCtx R k 0 ρ) : CtxAdd Γ Γ Γ :=
  ⟨Ctx.forall₃_iff.2 fun _ => RefAdd.idem _, Ctx.forall₃_iff.2 fun i => nomatch i⟩

/-- `∅ + Γ = Γ` for contexts without variables. -/
lemma ctxAdd_empty_left {k ρ : ℕ} (Γ : TCtx R k 0 ρ) : CtxAdd TCtx.empty Γ Γ :=
  ⟨Ctx.Forall₃.replicate_left (fun _ => .noneLeft _) _, Ctx.forall₃_iff.2 fun i => nomatch i⟩

/-- `s · Γ = Γ` for contexts without variables. -/
lemma ctxScale_of_vars0 {k ρ : ℕ} (s : R) (Γ : TCtx R k 0 ρ) : CtxScale s Γ Γ :=
  ⟨rfl, Ctx.forall₂_iff.2 fun i => nomatch i⟩

lemma isZero_of_vars0 {k ρ : ℕ} (Γ : TCtx R k 0 ρ) : Γ.IsZero :=
  Ctx.all_iff.2 fun i => nomatch i

/-- `Ha ⋈ Γa` with the repaired heap compatibility. -/
theorem compat_Ha : Compat true (Ha : Heap R 0 1 1) Γa :=
  Compat.extRes (Γ := TCtx.empty) (γ := TCtx.empty) (Δ := TCtx.empty) (id := .zero)
    (Ctx.Lookup.of_eq rfl) rfl (ResValTy.arr (ArrValTy.init _)) ctxAdd_empty
    (Compat.gcRes Compat.empty)

/-- `Γ ⊢ ref₀ : Array_id₀ 𝔽` in any context `0 · Γ` assuming `ref₀ : Array_id₀ 𝔽`. -/
lemma ref0_typed {n ρ : ℕ} {Γ : TCtx R 1 n (ρ + 1)} (hz : Γ.IsZero)
    (h : Γ.refs.get .zero = some arrT) : HasType Γ (.ref .zero) (arrT.toTy) :=
  HasType.ref hz (Ctx.Lookup.of_eq h)

/-- `*ref₀ : &_p (Array_id₀ 𝔽)` for any permission `p`. -/
lemma star_ref0_typed {n ρ : ℕ} {Γ : TCtx R 1 n (ρ + 1)} (hz : Γ.IsZero)
    (h : Γ.refs.get .zero = some arrT) (p : Perm) :
    HasType Γ (.star (.ref .zero)) (Ty.borrow p arrT.toTy) :=
  HasType.nec p hz (HasType.ref (TCtx.IsZero.refsOnly _) (Ctx.Lookup.of_eq h))

end FOFU
