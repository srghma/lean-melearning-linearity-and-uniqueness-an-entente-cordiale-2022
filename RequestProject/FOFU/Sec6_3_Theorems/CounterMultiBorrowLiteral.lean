module
public import RequestProject.FOFU.Sec6_3_Theorems.CounterBorrowSafety
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# Theorem 6.9 is false for Definition 6.4 as printed

With Definition 6.4 as printed (`gc = false`) the first part of Theorem 6.9 is vacuous
(compatible heaps have no identifiers, `Compat.ress_eq_none`), but the second part, about
identifiers created during the reduction, fails.  Starting from the empty heap and the
empty context, the closed, well-typed term (`leakTerm_typed`)

  `( unpack ⟨id, x⟩ = newArray 3 in
       withBorrow (λb. unpack ⟨id', c⟩ = newRef (split b) in let [d] = share₀ c in *()) x,
     newArray 3 ) : *unit ⊗ ∃ id. *(Array_id 𝔽)`

reduces in 13 steps (`leak_steps`) to the value `(*(), pack ⟨id₂, *ref₄⟩)`:

1. the first `newArray 3` allocates `ref₀ ↦_1 id₀, id₀ ↦ init`;
2. the borrowed `b = *ref₀` is split into `ref₁ ↦_(1/2) id₀` and `ref₂ ↦_(1/2) id₀`;
3. both halves are stored in a new reference cell `ref₃ ↦_1 id₁, id₁ ↦ ref(( *ref₁, *ref₂ ))`;
4. the cell is discarded with `share₀` (a box of grade `0`) and the borrowing function
   returns `*()`, so the halves are never joined;
5. the second `newArray 3` allocates `ref₄ ↦_1 id₂`.

The identifier `id₀` is new (not in the empty initial heap), `ref₄ ∈ refs(v)`, but in the
final heap only `ref₁` and `ref₂`, each with permission `1/2`, point to `id₀`: there is no
reference `ref' ↦_1 id₀` (`L8_no_full`).

The term is typed by the rules of the paper: `split` needs only a fractional borrow,
`newRef` accepts a value of any type (here `&_(1/2) A ⊗ &_(1/2) A`), `share` applies to the
owned cell `*Ref_id' (…)` at any grade, in particular `0`, and a variable of grade `0`
may be discarded.  The reduction uses the rule `⤳share β` with the heap left unchanged
(the paper's `[H]_0` is undefined, see `Step.lean`); any reading of `[H]_0` that discards
the cell without joining the halves gives the same result.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

open Term

/-- `newArray 3`. -/
abbrev newArr3 {n : ℕ} : Term R n := app (prim .newArray) (nat 3)

/-- The body `unpack ⟨id', c⟩ = newRef (split b) in let [d] = share₀ c in *()` of the
borrowing function (`b` is index `0`). -/
def leakBody : Term R 2 :=
  unpack (app (prim .newRef) (split (var 0))) (letBox (share 0 (var 0)) (star unit))

/-- The term `(unpack ⟨id, x⟩ = newArray 3 in withBorrow (λb. leakBody) x, newArray 3)`. -/
def leakTerm : Term R 0 := pair (unpack newArr3 (withBorrow (lam leakBody) (var 0))) newArr3

/-- `Array_id 𝔽` for the bound identifier `id`. -/
abbrev arrB : Ty R 1 := Ty.array (.bound 0)

/-- `&_(1/2) A ⊗ &_(1/2) A` for `A = Array_id 𝔽`. -/
abbrev halvesB : Ty R 1 := Ty.tensor (Ty.borrow (.frac Frac.one.half) arrB) (Ty.borrow (.frac Frac.one.half) arrB)

/-- The type `*unit ⊗ ∃ id. *(Array_id 𝔽)` of `leakTerm`. -/
abbrev leakTy : Ty R 0 := Ty.tensor (Ty.star Ty.unit) newArrayTy

lemma leakBody_typed :
    HasType (Ctx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none] : Ctx R 1 2) leakBody
      (Ty.borrow Perm.one Ty.unit) := by
  refine HasType.unpack (A := Ty.star (Ty.ref (.bound 0) (halvesB (R := R)).shift))
    (Γ₁ := Ctx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none])
    (Γ₂ := Ctx.ofList [none, none]) (by ctx_add) ?_ ?_
  · refine HasType.app (A := halvesB)
      (Γ₁ := Ctx.ofList [none, none]) (Γ₂ := Ctx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none])
      (by ctx_add) (HasType.prim (by zero_rest) (PrimTy.newRef _)) ?_
    exact HasType.split (f := Frac.one) (A := arrB)
      (HasType.var (Γ := Ctx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none]) (i := 0)
        rfl (by zero_rest))
  · refine HasType.elim (r := 0) (A := Ty.ref (.bound 0) (halvesB (R := R)).shift)
      (Γ₁ := Ctx.ofList [some (.lin (Ty.star (Ty.ref (.bound 0) (halvesB (R := R)).shift))),
        none, none])
      (Γ₂ := Ctx.ofList [none, none, none]) ?_ ?_ ?_
    · refine ⟨fun i => ?_, fun _ => RefAdd.noneLeft _⟩
      fin_cases i <;> first | exact AssmAdd.noneLeft _ | exact AssmAdd.noneRight _
    · exact HasType.share 0 (HasType.var rfl (by zero_rest))
    · refine HasType.nec Perm.one ?_ (HasType.unitI (fun _ => trivial))
      intro j
      fin_cases j <;> first | rfl | trivial

lemma leakTerm_typed : HasType (Ctx.empty : Ctx R 0 0) leakTerm leakTy := by
  refine HasType.tensorI ctxAdd_empty ?_ newArray_typed
  refine HasType.unpack (A := Ty.star arrB) ctxAdd_empty newArray_typed ?_
  refine HasType.withBorrow (A := arrB) (Γ₁ := Ctx.ofList [none])
    (Γ₂ := Ctx.ofList [some (.lin (Ty.star arrB))]) ?_ ?_ ?_
  · refine ⟨fun i => ?_, fun _ => RefAdd.noneLeft _⟩
    fin_cases i
    exact AssmAdd.noneLeft _
  · exact HasType.abs leakBody_typed
  · exact HasType.var rfl (by zero_rest)

/-! ## The reduction -/

/-- The body `let [d] = share₀ c in *()` of the inner `unpack`. -/
abbrev leakK : Term R 3 := letBox (share 0 (var 0)) (star unit)

def L1 : Heap R 0 := (Heap.empty.addRef 0 1 0).addRes 0 (.arr .init)
def L2 : Heap R 1 := (L1 : Heap R 0).snoc 1 (star (ref 0))
def L3 : Heap R 2 := (L2 : Heap R 1).snoc 1 (star (ref 0))
def L4 : Heap R 2 := (((L3 : Heap R 2).eraseRef 0).addRef 1 (1 / 2) 0).addRef 2 (1 / 2) 0
def L5 : Heap R 2 :=
  ((L4 : Heap R 2).addRef 3 1 1).addRes 1 (.ref (pair (star (ref 1)) (star (ref 2))))
def L6 : Heap R 3 := (L5 : Heap R 2).snoc 1 (star (ref 3))
def L7 : Heap R 4 := (L6 : Heap R 3).snoc (1 * 0) (ref 3)
def L8 : Heap R 4 := ((L7 : Heap R 4).addRef 4 1 2).addRes 2 (.arr .init)

lemma leak_steps :
    Steps (Heap.empty : Heap R 0) leakTerm 1 L8 (pair (star unit) (pack (star (ref 4)))) := by
  have s1 : Step (Heap.empty : Heap R 0) leakTerm 1 L1
      (pair (unpack (pack (star (ref 0))) (withBorrow (lam leakBody) (var 0))) newArr3) :=
    Step.pairL le_rfl (Step.unpackCong le_rfl newArray_step)
  have s2 : Step (L1 : Heap R 0)
      (pair (unpack (pack (star (ref 0))) (withBorrow (lam leakBody) (var 0))) newArr3) 1 L2
      (pair (withBorrow (lam leakBody) (var 0)) newArr3) :=
    Step.pairL (Nat.le_succ 0) (Step.exBeta (IsValue.star (IsValue.ref 0)))
  have s3 : Step (L2 : Heap R 1) (pair (withBorrow (lam leakBody) (var 0)) newArr3) 1 L2
      (pair (withBorrow (lam leakBody) (star (ref 0))) newArr3) :=
    Step.pairL le_rfl (Step.withBorrowR le_rfl (IsValue.lam _)
      (var_step_one (H := (L2 : Heap R 1)) (i := 0) rfl))
  have s4 : Step (L2 : Heap R 1) (pair (withBorrow (lam leakBody) (star (ref 0))) newArr3) 1 L3
      (pair (unborrow (unpack (app (prim .newRef) (split (var 1))) leakK)) newArr3) :=
    Step.pairL (Nat.le_succ 1) (Step.withBorrow (IsValue.ref 0))
  have s5 : Step (L3 : Heap R 2)
      (pair (unborrow (unpack (app (prim .newRef) (split (var 1))) leakK)) newArr3) 1 L3
      (pair (unborrow (unpack (app (prim .newRef) (split (star (ref 0)))) leakK)) newArr3) :=
    Step.pairL le_rfl (Step.unborrowCong (Step.unpackCong le_rfl
      (Step.appR le_rfl (IsValue.prim (PrimSpine.prim _) (by decide))
        (Step.splitCong (var_step_one (H := (L3 : Heap R 2)) (i := 1) rfl)))))
  have s6 : Step (L3 : Heap R 2)
      (pair (unborrow (unpack (app (prim .newRef) (split (star (ref 0)))) leakK)) newArr3) 1 L4
      (pair (unborrow (unpack (app (prim .newRef) (pair (star (ref 1)) (star (ref 2)))) leakK))
        newArr3) :=
    Step.pairL le_rfl (Step.unborrowCong (Step.unpackCong le_rfl
      (Step.appR le_rfl (IsValue.prim (PrimSpine.prim _) (by decide))
        (Step.splitRef (p := 1) (vr := .arr .init) rfl rfl rfl rfl (by decide)))))
  have s7 : Step (L4 : Heap R 2)
      (pair (unborrow (unpack (app (prim .newRef) (pair (star (ref 1)) (star (ref 2)))) leakK))
        newArr3) 1 L5
      (pair (unborrow (unpack (pack (star (ref 3))) leakK)) newArr3) := by
    refine Step.pairL le_rfl (Step.unborrowCong (Step.unpackCong le_rfl
      (Step.newRef (IsValue.pair (IsValue.star (IsValue.ref 1)) (IsValue.star (IsValue.ref 2)))
        rfl ⟨rfl, fun a q => ?_⟩)))
    simp only [L4, L3, L2, L1, Heap.addRef, Heap.eraseRef, Heap.snoc, Heap.addRes, Heap.empty,
      Function.update]
    split_ifs <;> simp
  have s8 : Step (L5 : Heap R 2)
      (pair (unborrow (unpack (pack (star (ref 3))) leakK)) newArr3) 1 L6
      (pair (unborrow (letBox (share 0 (var 2)) (star unit))) newArr3) :=
    Step.pairL (Nat.le_succ 2) (Step.unborrowCong (Step.exBeta (IsValue.star (IsValue.ref 3))))
  have s9 : Step (L6 : Heap R 3)
      (pair (unborrow (letBox (share 0 (var 2)) (star unit))) newArr3) 1 L6
      (pair (unborrow (letBox (share 0 (star (ref 3))) (star unit))) newArr3) :=
    Step.pairL le_rfl (Step.unborrowCong (Step.letBoxCong le_rfl
      (Step.shareCong (var_step_one (H := (L6 : Heap R 3)) (i := 2) rfl))))
  have s10 : Step (L6 : Heap R 3)
      (pair (unborrow (letBox (share 0 (star (ref 3))) (star unit))) newArr3) 1 L6
      (pair (unborrow (letBox (box 0 (ref 3)) (star unit))) newArr3) :=
    Step.pairL le_rfl (Step.unborrowCong (Step.letBoxCong le_rfl (Step.share (IsValue.ref 3))))
  have s11 : Step (L6 : Heap R 3)
      (pair (unborrow (letBox (box 0 (ref 3)) (star unit))) newArr3) 1 L7
      (pair (unborrow (star unit)) newArr3) :=
    Step.pairL (Nat.le_succ 3) (Step.unborrowCong (Step.boxBeta (IsValue.ref 3)))
  have s12 : Step (L7 : Heap R 4) (pair (unborrow (star unit)) newArr3) 1 L7
      (pair (star unit) newArr3) :=
    Step.pairL le_rfl (Step.unborrow IsValue.unit)
  have s13 : Step (L7 : Heap R 4) (pair (star unit) newArr3) 1 L8
      (pair (star unit) (pack (star (ref 4)))) := by
    refine Step.pairR le_rfl (IsValue.star IsValue.unit) (Step.newArray rfl ⟨rfl, fun a q => ?_⟩)
    simp only [L7, L6, L5, L4, L3, L2, L1, Heap.addRef, Heap.eraseRef, Heap.snoc, Heap.addRes,
      Heap.empty, Function.update]
    split_ifs <;> simp
  exact Steps.ext s1 (Steps.ext s2 (Steps.ext s3 (Steps.ext s4 (Steps.ext s5 (Steps.ext s6
    (Steps.ext s7 (Steps.ext s8 (Steps.ext s9 (Steps.ext s10 (Steps.ext s11 (Steps.ext s12
    (Steps.ext s13 (Steps.refl _ _ _)))))))))))))

/-- After the reduction no reference has permission `1` on the identifier `id₀` of the
first array. -/
lemma L8_no_full (a : ℕ) : (L8 : Heap R 4).refs a ≠ some (1, 0) := by
  simp only [L8, L7, L6, L5, L4, L3, L2, L1, Heap.addRef, Heap.eraseRef, Heap.snoc, Heap.addRes,
    Heap.empty, Function.update]
  split_ifs <;> simp

/-- **Theorem 6.9 is false** for Definition 6.4 as printed. -/
theorem not_multiBorrowSafety_literal : ¬ MultiBorrowSafety (R := R) false := by
  intro h
  have h2 := (h Ctx.empty leakTerm leakTy leakTerm_typed 1 Ctx.empty Ctx.empty Ctx.empty
    Heap.empty L8 _ (ctxScale_empty 1) ctxAdd_empty Compat.empty leak_steps
    (IsValue.pair (IsValue.star IsValue.unit) (IsValue.pack (IsValue.star (IsValue.ref 4))))).2 0
    (by simp [L8, L7, L6, L5, L4, L3, L2, L1, Heap.addRes, Heap.snoc, Heap.addRef, Heap.eraseRef])
    rfl 4 (by simp [Term.refs])
  obtain ⟨a, ha, -⟩ := h2
  exact L8_no_full a ha

end FOFU
