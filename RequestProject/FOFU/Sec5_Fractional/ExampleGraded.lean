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

/-- The printed `readRef` has no instance of the type at which `exampleGraded` uses it:
`readRef : *(Ref_id (□_6 𝔽)) ⊸ □_4 𝔽 ⊗ *(Ref_id (□_2 𝔽))` is not derivable from the printed
interface `&_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))`. -/
theorem not_primTy_readRef_graded {k : ℕ} (ι : Var k) :
    ¬ PrimTy (R := ℕ) .readRef
      (lolli (star (ref ι (box 6 .float))) (tensor (box 4 .float) (star (ref ι (box 2 .float))))) := by
  intro h
  cases h

/-- `test = [42.0] : Float [6]`. -/
def testBox {n ρ : ℕ} : Term ℕ n ρ := .box 6 (.float 42.0)

/-- `exampleGraded` (with the amended `readRefSplit` in place of `readRef`):
`unpack ⟨id, ref⟩ = newRef test in let (bx, ref') = readRef ref in let [x] = bx in
let [y] = freezeRef ref' in ([x], [y])`. -/
def exampleGraded : Term ℕ 0 0 :=
  .unpack (.app (.prim .newRef) testBox)
    (.letPair (.app (.prim .readRefSplit) (.var 0))
      (.letBox (.var 1)
        (.letBox (.app (.prim .freezeRef) (.var 1))
          (.pair (.box 4 (.var 1)) (.box 2 (.var 0))))))

/-- `⊢ exampleGraded : Float [4] ⊗ Float [2]`, using the amended grade-splitting read
`readRefSplit : *(Ref_id (□_(4+2) 𝔽)) ⊸ □_4 𝔽 ⊗ *(Ref_id (□_2 𝔽))`. -/
theorem exampleGraded_typing :
    HasType (TCtx.ofList [] : TCtx ℕ 0 0 0) exampleGraded (tensor (box 4 .float) (box 2 .float)) := by
  -- `newRef test : ∃ id. *(Ref_id (□_6 𝔽))`
  refine HasType.unpack (Γ₁ := TCtx.ofList []) (Γ₂ := TCtx.ofList [])
    (A := star (ref .zero (box 6 .float))) (by ctx_add)
    (HasType.app (Γ₁ := TCtx.ofList []) (Γ₂ := TCtx.ofList []) (by ctx_add)
      (HasType.prim (by zero_ctx) (PrimTy.newRef (box 6 .float)))
      (HasType.pr (Γ₀ := TCtx.ofList []) (CtxScale.of_isZero (by zero_ctx) 6)
        (HasType.float 42.0 (by zero_ctx)) (by decide))) ?_
  set A : Ty ℕ 1 := star (ref .zero (box 6 .float))
  set B : Ty ℕ 1 := star (ref .zero (box 2 .float))
  -- `ref : A ⊢ let (bx, ref') = readRefSplit ref in ...`
  refine HasType.tensorE (A := box 4 .float) (B := B)
    (Γ₁ := TCtx.ofList [some (.lin A)]) (Γ₂ := TCtx.ofList [none]) (by ctx_add) ?_ ?_
  · exact HasType.app (Γ₁ := TCtx.ofList [none]) (Γ₂ := TCtx.ofList [some (.lin A)])
      (by ctx_add) (HasType.prim (by zero_ctx) (PrimTy.readRefSplit .zero 4 2 .float))
      (HasType.var (by pick_var))
  -- `ref' : B, bx : □_4 𝔽, ref : − ⊢ let [x] = bx in ...`
  refine HasType.elim (A := .float) (r := 4)
    (Γ₁ := TCtx.ofList [none, some (.lin (box 4 .float)), none])
    (Γ₂ := TCtx.ofList [some (.lin B), none, none]) (by ctx_add)
    (HasType.var (by pick_var)) ?_
  -- `x : [𝔽]_4, ref' : B, bx, ref : − ⊢ let [y] = freezeRef ref' in ([x], [y])`
  refine HasType.elim (A := .float) (r := 2)
    (Γ₁ := TCtx.ofList [none, some (.lin B), none, none])
    (Γ₂ := TCtx.ofList [some (.grd .float 4), none, none, none]) (by ctx_add)
    (HasType.app (Γ₁ := TCtx.ofList [none, none, none, none])
      (Γ₂ := TCtx.ofList [none, some (.lin B), none, none]) (by ctx_add)
      (HasType.prim (by zero_ctx) (PrimTy.freezeRef .zero (box 2 .float)))
      (HasType.var (by pick_var))) ?_
  -- `y : [𝔽]_2, x : [𝔽]_4, ... ⊢ ([x], [y]) : □_4 𝔽 ⊗ □_2 𝔽`
  refine HasType.tensorI
    (Γ₁ := TCtx.ofList [none, some (.grd .float 4), none, none, none])
    (Γ₂ := TCtx.ofList [some (.grd .float 2), none, none, none, none]) (by ctx_add) ?_ ?_
  · refine HasType.pr (Γ₀ := TCtx.ofList [none, some (.grd .float 1), none, none, none])
      ⟨rfl, ?_⟩ (HasType.var' (by pick_var)) (by decide)
    repeat' (first
      | exact Ctx.Forall₂.nil
      | refine Ctx.Forall₂.snoc ?_ ?_
      | exact AssmScale.none
      | exact (AssmScale.grd (r := (4 : ℕ)) Ty.float 1 :))
  · refine HasType.pr (Γ₀ := TCtx.ofList [some (.grd .float 1), none, none, none, none])
      ⟨rfl, ?_⟩ (HasType.var' (by pick_var)) (by decide)
    repeat' (first
      | exact Ctx.Forall₂.nil
      | refine Ctx.Forall₂.snoc ?_ ?_
      | exact AssmScale.none
      | exact (AssmScale.grd (r := (2 : ℕ)) Ty.float 1 :))

end FOFU
