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
abbrev newArr3 {n ρ : ℕ} : Term R n ρ := app (prim .newArray) (nat 3)

/-- The body `let [d] = share₀ c in *()` of the inner `unpack`. -/
abbrev leakK {ρ : ℕ} : Term R 3 ρ := letBox (share 0 (var .zero)) (star unit)

/-- The body `unpack ⟨id', c⟩ = newRef (split b) in let [d] = share₀ c in *()` of the
borrowing function (`b` is `Var.zero`). -/
def leakBody {ρ : ℕ} : Term R 2 ρ := unpack (app (prim .newRef) (split (var .zero))) leakK

/-- The term `(unpack ⟨id, x⟩ = newArray 3 in withBorrow (λb. leakBody) x, newArray 3)`. -/
def leakTerm : Term R 0 0 := pair (unpack newArr3 (withBorrow (lam leakBody) (var .zero))) newArr3

/-- `Array_id 𝔽` for the bound identifier `id`. -/
abbrev arrB : Ty R 1 := Ty.array .zero

/-- `&_(1/2) A ⊗ &_(1/2) A` for `A = Array_id 𝔽`. -/
abbrev halvesB : Ty R 1 :=
  Ty.tensor (Ty.borrow (.frac Frac.one.half) arrB) (Ty.borrow (.frac Frac.one.half) arrB)

/-- The type `*unit ⊗ ∃ id. *(Array_id 𝔽)` of `leakTerm`. -/
abbrev leakTy : Ty R 0 := Ty.tensor (Ty.star Ty.unit) newArrayTy

lemma leakBody_typed :
    HasType (TCtx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none] : TCtx R 1 2 0) leakBody
      (Ty.borrow Perm.one Ty.unit) := by
  refine HasType.unpack (A := Ty.star (Ty.ref .zero (halvesB (R := R)).shift))
    (Γ₁ := TCtx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none])
    (Γ₂ := TCtx.ofList [none, none]) (by ctx_add) ?_ ?_
  · refine HasType.app (A := halvesB)
      (Γ₁ := TCtx.ofList [none, none])
      (Γ₂ := TCtx.ofList [some (.lin (Ty.borrow Perm.one arrB)), none])
      (by ctx_add) (HasType.prim (by zero_ctx) (PrimTy.newRef _)) ?_
    exact HasType.split (f := Frac.one) (A := arrB) (HasType.var (by pick_var))
  · refine HasType.elim (r := 0) (A := Ty.ref .zero (halvesB (R := R)).shift)
      (Γ₁ := TCtx.ofList [some (.lin (Ty.star (Ty.ref .zero (halvesB (R := R)).shift))),
        none, none])
      (Γ₂ := TCtx.ofList [none, none, none]) (by ctx_add) ?_ ?_
    · exact HasType.share 0 (HasType.var (by pick_var))
    · exact HasType.nec Perm.one (by zero_ctx) (HasType.unitI (TCtx.IsZero.refsOnly _))

lemma leakTerm_typed : HasType (TCtx.empty : TCtx R 0 0 0) leakTerm leakTy := by
  refine HasType.tensorI ctxAdd_empty ?_ newArray_typed
  refine HasType.unpack (A := Ty.star arrB) ctxAdd_empty newArray_typed ?_
  refine HasType.withBorrow (A := arrB) (Γ₁ := TCtx.ofList [none])
    (Γ₂ := TCtx.ofList [some (.lin (Ty.star arrB))]) (by ctx_add) ?_ ?_
  · exact HasType.abs leakBody_typed
  · exact HasType.var (by pick_var)

/-! ## The reduction -/

/-- After the first `newArray 3`: `ref₀ ↦_1 id₀, id₀ ↦ init`. -/
abbrev L1 : Heap R 0 1 1 := Ha
/-- `x ↦_1 *ref₀` (the unpacked array). -/
def L2 : Heap R 1 1 1 := (L1 : Heap R 0 1 1).snoc 1 (star (ref .zero))
/-- `b ↦_1 *ref₀` (the borrowed array). -/
def L3 : Heap R 2 1 1 := (L2 : Heap R 1 1 1).snoc 1 (star (ref .zero))
/-- `ref₀` is split into two halves. -/
def L4 : Heap R 2 3 1 :=
  (((L3 : Heap R 2 1 1).eraseRef .zero).newRef Frac.one.half .zero).newRef Frac.one.half .zero
/-- A new reference cell holding both halves. -/
def L5 : Heap R 2 4 2 :=
  ((L4 : Heap R 2 3 1).addId (some (.ref (pair (star (ref (.succ .zero))) (star (ref .zero)))))).newRef
    Frac.one .zero
/-- `c ↦_1 *ref_cell`. -/
def L6 : Heap R 3 4 2 := (L5 : Heap R 2 4 2).snoc 1 (star (ref .zero))
/-- `d ↦_0 ref_cell`. -/
def L7 : Heap R 4 4 2 := (L6 : Heap R 3 4 2).snoc (1 * 0) (ref .zero)
/-- After the second `newArray 3`. -/
def L8 : Heap R 4 5 3 :=
  ((L7 : Heap R 4 4 2).addId (some (.arr .init))).newRef Frac.one .zero

lemma leak_steps :
    ∃ (θr : Var 0 → Var 5) (θi : Var 0 → Var 3),
      Steps (Heap.empty : Heap R 0 0 0) leakTerm 1 L8
        (pair (star unit) (pack (star (ref .zero)))) θr θi := by
  have s1 : Step (Heap.empty : Heap R 0 0 0) leakTerm 1 0 1 1 L1
      (pair (unpack (pack (star (ref .zero))) (withBorrow (lam leakBody) (var .zero))) newArr3) :=
    Step.pairL (Step.unpackCong newArray_step)
  have s2 : Step (L1 : Heap R 0 1 1)
      (pair (unpack (pack (star (ref .zero))) (withBorrow (lam leakBody) (var .zero))) newArr3)
      1 1 0 0 L2 (pair (withBorrow (lam leakBody) (var .zero)) newArr3) :=
    Step.pairL (Step.exBeta (IsValue.star (IsValue.ref _)))
  have s3 : Step (L2 : Heap R 1 1 1) (pair (withBorrow (lam leakBody) (var .zero)) newArr3)
      1 0 0 0 L2 (pair (withBorrow (lam leakBody) (star (ref .zero))) newArr3) :=
    Step.pairL (Step.withBorrowR (IsValue.lam _) (var_step_one rfl))
  have s4 : Step (L2 : Heap R 1 1 1) (pair (withBorrow (lam leakBody) (star (ref .zero))) newArr3)
      1 1 0 0 L3 (pair (unborrow leakBody) newArr3) :=
    Step.pairL (Step.withBorrow (IsValue.ref _))
  have s5 : Step (L3 : Heap R 2 1 1) (pair (unborrow leakBody) newArr3) 1 0 0 0 L3
      (pair (unborrow (unpack (app (prim .newRef) (split (star (ref .zero)))) leakK)) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.unpackCong
      (Step.appR (IsValue.prim (PrimSpine.prim _) (by decide))
        (Step.splitCong (var_step_one rfl)))))
  have s6 : Step (L3 : Heap R 2 1 1)
      (pair (unborrow (unpack (app (prim .newRef) (split (star (ref .zero)))) leakK)) newArr3)
      1 0 2 0 L4
      (pair (unborrow (unpack (app (prim .newRef)
        (pair (star (ref (.succ .zero))) (star (ref .zero)))) leakK)) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.unpackCong
      (Step.appR (IsValue.prim (PrimSpine.prim _) (by decide))
        (Step.splitRef (Ctx.Lookup.of_eq rfl) (Ctx.Lookup.of_eq rfl)))))
  have s7 : Step (L4 : Heap R 2 3 1)
      (pair (unborrow (unpack (app (prim .newRef)
        (pair (star (ref (.succ .zero))) (star (ref .zero)))) leakK)) newArr3)
      1 0 1 1 L5 (pair (unborrow (unpack (pack (star (ref .zero))) leakK)) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.unpackCong
      (Step.newRef (IsValue.pair (IsValue.star (IsValue.ref _)) (IsValue.star (IsValue.ref _))))))
  have s8 : Step (L5 : Heap R 2 4 2)
      (pair (unborrow (unpack (pack (star (ref .zero))) leakK)) newArr3) 1 1 0 0 L6
      (pair (unborrow leakK) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.exBeta (IsValue.star (IsValue.ref _))))
  have s9 : Step (L6 : Heap R 3 4 2) (pair (unborrow leakK) newArr3) 1 0 0 0 L6
      (pair (unborrow (letBox (share 0 (star (ref .zero))) (star unit))) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.letBoxCong (Step.shareCong (var_step_one rfl))))
  have s10 : Step (L6 : Heap R 3 4 2)
      (pair (unborrow (letBox (share 0 (star (ref .zero))) (star unit))) newArr3) 1 0 0 0 L6
      (pair (unborrow (letBox (box 0 (ref .zero)) (star unit))) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.letBoxCong (Step.share (IsValue.ref _))))
  have s11 : Step (L6 : Heap R 3 4 2)
      (pair (unborrow (letBox (box 0 (ref .zero)) (star unit))) newArr3) 1 1 0 0 L7
      (pair (unborrow (star unit)) newArr3) :=
    Step.pairL (Step.unborrowCong (Step.boxBeta (IsValue.ref _)))
  have s12 : Step (L7 : Heap R 4 4 2) (pair (unborrow (star unit)) newArr3) 1 0 0 0 L7
      (pair (star unit) newArr3) :=
    Step.pairL (Step.unborrow IsValue.unit)
  have s13 : Step (L7 : Heap R 4 4 2) (pair (star unit) newArr3) 1 0 1 1 L8
      (pair (star unit) (pack (star (ref .zero)))) :=
    Step.pairR (IsValue.star IsValue.unit) Step.newArray
  exact ⟨_, _, Steps.ext s1 (Steps.ext s2 (Steps.ext s3 (Steps.ext s4 (Steps.ext s5
    (Steps.ext s6 (Steps.ext s7 (Steps.ext s8 (Steps.ext s9 (Steps.ext s10 (Steps.ext s11
    (Steps.ext s12 (Steps.ext s13 (Steps.refl _ _ _)))))))))))))⟩

/-- After the reduction no reference has permission `1` on the identifier `id₀` of the
first array (now called `Var.succ (Var.succ Var.zero)`). -/
lemma L8_no_full (a : Var 5) :
    (L8 : Heap R 4 5 3).refs.get a ≠ some (Frac.one, .succ (.succ .zero)) := by
  have hhalf : Frac.one.half ≠ Frac.one := by
    intro e
    have := congrArg Subtype.val e
    norm_num at this
  cases a with
  | zero => change some (Frac.one, (Var.zero : Var 3)) ≠ _; simp
  | succ a =>
  cases a with
  | zero => change some (Frac.one, (Var.succ Var.zero : Var 3)) ≠ _; simp
  | succ a =>
  cases a with
  | zero => change some (Frac.one.half, (Var.succ (Var.succ Var.zero) : Var 3)) ≠ _; simp [hhalf]
  | succ a =>
  cases a with
  | zero => change some (Frac.one.half, (Var.succ (Var.succ Var.zero) : Var 3)) ≠ _; simp [hhalf]
  | succ a =>
  cases a with
  | zero => change none ≠ _; simp
  | succ a => cases a

/-- **Theorem 6.9 is false** for Definition 6.4 as printed. -/
theorem not_multiBorrowSafety_literal : ¬ MultiBorrowSafety (R := R) false := by
  intro h
  obtain ⟨θr, θi, hsteps⟩ := leak_steps (R := R)
  have h2 := (h TCtx.empty leakTerm leakTy leakTerm_typed 1 TCtx.empty TCtx.empty TCtx.empty
    Heap.empty L8 _ θr θi (ctxScale_empty 1) ctxAdd_empty Compat.empty hsteps
    (IsValue.pair (IsValue.star IsValue.unit) (IsValue.pack (IsValue.star (IsValue.ref _))))).2
    (.succ (.succ .zero)) (by change some _ ≠ none; simp) (fun id => nomatch id) .zero
    (Term.mem_refs.2 (.arg (.tail (.head (.arg (.head (.arg (.head (.here rfl)))))))))
  obtain ⟨a, ha, -⟩ := h2
  exact L8_no_full a ha

end FOFU
