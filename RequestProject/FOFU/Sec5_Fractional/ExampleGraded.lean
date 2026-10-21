module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra

/-!
# §5 — `exampleGraded`, with the amended (grade-splitting) `readRef`

```haskell
test : Float [6]
test = [42.0]

exampleGraded : (Float [4], Float [2])
exampleGraded =
  unpack <id, ref> = newRef test in
  let ([x], ref') : (Float [4], *(Ref id (Float [2]))) = readRef ref in
  let [y] : Float [2] = freezeRef ref' in ([x], [y])
```

## Why the printed interface does not suffice

The interface printed in §5 is

  `readRef : &_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))`.

It (1) returns the *unboxed* contents `A`, whereas the example binds the result with the
box pattern `[x]` at type `Float [4] = □_4 𝔽`; and (2) gives back the reference at the
*same* type `□_r A`, whereas the example uses it afterwards at `Ref id (Float [2])`.  With
`ref : *(Ref id (□_6 𝔽))`, the only instance is `r = 6`, `A = 𝔽`, so `x : 𝔽` (linear,
cannot be promoted to `□_4 𝔽`) and `ref' : *(Ref id (□_6 𝔽))`, so `freezeRef ref' : □_6 𝔽`,
not `□_2 𝔽` (over `ℕ`, whose order is equality, approximation cannot help either).

## The amendment

We add the primitive `readRefSplit` (`PrimTy.readRefSplit`, `Step.readRefSplit`):

  `readRefSplit : *(Ref_id (□_(q+r) A)) ⊸ □_q A ⊗ *(Ref_id (□_r A))`

with reduction `ref ↦ [v]_(q+r)  ⤳  ([v]_q, *ref)` and heap `ref ↦ [v]_r`.  This is what
Granule's `readRef` does (it splits the grade `q + r` of the stored box).  It is offered
only at the unique permission `*`, because it changes the type of the reference; the
printed `readRef` is kept unchanged.  With it, `exampleGraded` type-checks
(`exampleGraded_typing`, with `q = 4`, `r = 2`, over the semiring `ℕ`).

As elsewhere, `let p = t₁ in t₂` with a pattern `p` is `letPair`/`letBox`, and the
trailing `([x], [y])` is kept literally (re-promoting the graded variables `x` and `y`).
-/

@[expose] public section

namespace FOFU

open Ty

/-- A variable graded `1` can be used once (`var` followed by dereliction). -/
theorem HasType.var_grd_one {R : Type} [Grades.PreorderedSemiring R] {k n : ℕ}
    {Γ : Ctx R k n} {i : Fin n} {A : Ty R k}
    (hi : Γ.vars i = some (.grd A 1)) (hz : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
    HasType Γ (.var i) A := by
  have h := HasType.der (Γ := Γ.update i (some (.lin A))) (i := i) (t := .var i) (A := A) (B := A)
    (by simp [Ctx.update])
    (HasType.var (by simp [Ctx.update])
      (fun j hj => by simpa [Ctx.update, Function.update, hj] using hz j hj))
  have e : (Γ.update i (some (.lin A))).update i (some (.grd A 1)) = Γ := by
    cases Γ with
    | mk vars refs =>
      simp only [Ctx.update, Function.update_idem]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simpa using hi.symm
      · simp [Function.update, hj]
  rwa [e] at h

/-- The printed `readRef` has no instance of the type at which `exampleGraded` uses it:
`readRef : *(Ref_id (□_6 𝔽)) ⊸ □_4 𝔽 ⊗ *(Ref_id (□_2 𝔽))` is not derivable from the printed
interface `&_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))`. -/
theorem not_primTy_readRef_graded {k : ℕ} (ι : Ident k) :
    ¬ PrimTy (R := ℕ) .readRef
      (lolli (star (ref ι (box 6 .float))) (tensor (box 4 .float) (star (ref ι (box 2 .float))))) := by
  intro h
  cases h

/-- `test = [42.0] : Float [6]`. -/
def testBox {n : ℕ} : Term ℕ n := .box 6 (.float 42.0)

/-- `exampleGraded` (with the amended `readRefSplit` in place of `readRef`):
`unpack ⟨id, ref⟩ = newRef test in let (bx, ref') = readRef ref in let [x] = bx in
let [y] = freezeRef ref' in ([x], [y])`. -/
def exampleGraded : Term ℕ 0 :=
  .unpack (.app (.prim .newRef) testBox)
    (.letPair (.app (.prim .readRefSplit) (.var 0))
      (.letBox (.var 1)
        (.letBox (.app (.prim .freezeRef) (.var 1))
          (.pair (.box 4 (.var 1)) (.box 2 (.var 0))))))

/-- `⊢ exampleGraded : Float [4] ⊗ Float [2]`, using the amended grade-splitting read
`readRefSplit : *(Ref_id (□_(4+2) 𝔽)) ⊸ □_4 𝔽 ⊗ *(Ref_id (□_2 𝔽))`. -/
theorem exampleGraded_typing :
    HasType (Ctx.empty : Ctx ℕ 0 0) exampleGraded (tensor (box 4 .float) (box 2 .float)) := by
  -- `newRef test : ∃ id. *(Ref_id (□_6 𝔽))`
  refine HasType.unpack (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty)
    (A := star (ref (.bound 0) (box 6 .float))) CtxAdd.empty
    (HasType.app (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) CtxAdd.empty
      (HasType.prim Ctx.IsZero.empty (PrimTy.newRef (box 6 .float)))
      (HasType.pr (Γ₀ := Ctx.empty) (CtxScale.of_isZero Ctx.IsZero.empty 6)
        (HasType.float 42.0 Ctx.IsZero.empty) (by simp [Term.Allocates]))) ?_
  set A : Ty ℕ 1 := star (ref (.bound 0) (box 6 .float))
  set B : Ty ℕ 1 := star (ref (.bound 0) (box 2 .float))
  -- `ref : A ⊢ let (bx, ref') = readRefSplit ref in ...`
  refine HasType.tensorE (A := box 4 .float) (B := B)
    (Γ₁ := Ctx.ofList [some (.lin A)]) (Γ₂ := Ctx.ofList [none]) (by ctx_add) ?_ ?_
  · exact HasType.app (Γ₁ := Ctx.ofList [none]) (Γ₂ := Ctx.ofList [some (.lin A)])
      (by ctx_add) (HasType.prim (by zero_rest) (PrimTy.readRefSplit (.bound 0) 4 2 .float))
      (HasType.var rfl (by zero_rest))
  -- `ref' : B, bx : □_4 𝔽, ref : − ⊢ let [x] = bx in ...`
  refine HasType.elim (A := .float) (r := 4)
    (Γ₁ := Ctx.ofList [none, some (.lin (box 4 .float)), none])
    (Γ₂ := Ctx.ofList [some (.lin B), none, none]) (by ctx_add)
    (HasType.var rfl (by zero_rest)) ?_
  -- `x : [𝔽]_4, ref' : B, bx, ref : − ⊢ let [y] = freezeRef ref' in ([x], [y])`
  refine HasType.elim (A := .float) (r := 2)
    (Γ₁ := Ctx.ofList [none, some (.lin B), none, none])
    (Γ₂ := Ctx.ofList [some (.grd .float 4), none, none, none]) (by ctx_add)
    (HasType.app (Γ₁ := Ctx.ofList [none, none, none, none])
      (Γ₂ := Ctx.ofList [none, some (.lin B), none, none]) (by ctx_add)
      (HasType.prim (by zero_rest) (PrimTy.freezeRef (.bound 0) (box 2 .float)))
      (HasType.var rfl (by zero_rest))) ?_
  -- `y : [𝔽]_2, x : [𝔽]_4, ... ⊢ ([x], [y]) : □_4 𝔽 ⊗ □_2 𝔽`
  refine HasType.tensorI
    (Γ₁ := Ctx.ofList [none, some (.grd .float 4), none, none, none])
    (Γ₂ := Ctx.ofList [some (.grd .float 2), none, none, none, none]) (by ctx_add) ?_ ?_
  · refine HasType.pr (Γ₀ := Ctx.ofList [none, some (.grd .float 1), none, none, none])
      ⟨fun i => ?_, rfl⟩ (HasType.var_grd_one rfl (by zero_rest)) (by simp [Term.Allocates])
    fin_cases i
    all_goals first
      | exact AssmScale.none
      | exact (AssmScale.grd (r := (4 : ℕ)) Ty.float 1 :)
  · refine HasType.pr (Γ₀ := Ctx.ofList [some (.grd .float 1), none, none, none, none])
      ⟨fun i => ?_, rfl⟩ (HasType.var_grd_one rfl (by zero_rest)) (by simp [Term.Allocates])
    fin_cases i
    all_goals first
      | exact AssmScale.none
      | exact (AssmScale.grd (r := (2 : ℕ)) Ty.float 1 :)

end FOFU
