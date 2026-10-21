module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# §3.2 — the example derivation over the natural-number semiring

The paper derives (with `(var')` = `var` followed by dereliction)

  `y : [A]_2 ⊢ (λx. (x, y)) (v, y) : (A ⊗ A) ⊗ A`        given  `∅ ⊢ v : A`.

In de Bruijn notation the context is the single variable `y = #0`; under the `λ`,
`x = #0` and `y = #1`.  The term `v` lives in the scope of `y` but does not use it
(`∅ ⊢ v : A` becomes `y : − ⊢ v : A`, with no assumption on `y`).

This is also the Granule program `exampleNat` of §3.
-/

@[expose] public section

namespace FOFU

open Ty

/-- The context `y : [A]_r` (one variable, no references). -/
abbrev ctxY {k : ℕ} (A : Ty ℕ k) (r : ℕ) : Ctx ℕ k 1 := Ctx.empty.cons (some (.grd A r))

/-- The term `(λx. (x, y)) (v, y)` of §3.2 (with `y = #0`). -/
def exampleNatTerm (v : Term ℕ 1) : Term ℕ 1 :=
  .app (.lam (.pair (.var 0) (.var 1))) (.pair v (.var 0))

/-- The example derivation of §3.2:
`y : [A]_2 ⊢ (λx. (x, y)) (v, y) : (A ⊗ A) ⊗ A`, assuming `∅ ⊢ v : A`. -/
theorem exampleNat_typing {k : ℕ} (A : Ty ℕ k) (v : Term ℕ 1)
    (hv : HasType (Ctx.empty.cons none) v A) :
    HasType (ctxY A 2) (exampleNatTerm v) (tensor (tensor A A) A) := by
  -- the two halves `y : [A]_1` of `y : [A]_2`
  refine HasType.app (Γ₁ := ctxY A 1) (Γ₂ := ctxY A 1) (A := tensor A A)
    (CtxAdd.cons (AssmAdd.grd A 1 1) CtxAdd.empty) ?_ ?_
  · -- `y : [A]_1 ⊢ λx. (x, y) : (A ⊗ A) ⊸ ((A ⊗ A) ⊗ A)`
    refine HasType.abs (HasType.tensorI
      (Γ₁ := (Ctx.empty.cons none).cons (some (.lin (tensor A A))))
      (Γ₂ := (ctxY A 1).cons none)
      (CtxAdd.cons (AssmAdd.noneRight _) (CtxAdd.cons (AssmAdd.noneLeft _) CtxAdd.empty))
      ?_ ?_)
    · exact HasType.var rfl (zeroRest_cons_zero (Ctx.IsZero.cons (a := none) trivial Ctx.IsZero.empty))
    · exact HasType.var' (i := (0 : Fin 1).succ) rfl
        (zeroRest_cons_succ (a := none) trivial (zeroRest_cons_zero Ctx.IsZero.empty))
  · -- `y : [A]_1 ⊢ (v, y) : A ⊗ A`
    refine HasType.tensorI (Γ₁ := Ctx.empty.cons none) (Γ₂ := ctxY A 1)
      (CtxAdd.cons (AssmAdd.noneLeft _) CtxAdd.empty) hv ?_
    exact HasType.var' (i := 0) rfl (zeroRest_cons_zero Ctx.IsZero.empty)

end FOFU
