module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# §3.2 — the example derivation over the natural-number semiring

The paper derives (with `(var')` = `var` followed by dereliction)

  `y : [A]_2 ⊢ (λx. (x, y)) (v, y) : (A ⊗ A) ⊗ A`        given  `∅ ⊢ v : A`.

In de Bruijn notation the context is the single variable `y = Var.zero`; under the `λ`,
`x` is `Var.zero` and `y` is `Var.succ Var.zero`.  The term `v` lives in the scope of `y` but does not use it
(`∅ ⊢ v : A` becomes `y : − ⊢ v : A`, with no assumption on `y`).

This is also the Granule program `exampleNat` of §3.
-/

@[expose] public section

namespace FOFU

open Ty

/-- The context `y : [A]_r` (one variable, no references). -/
abbrev ctxY {k : ℕ} (A : Ty ℕ k) (r : ℕ) : TCtx ℕ k 1 0 := TCtx.ofList [some (.grd A r)]

/-- The term `(λx. (x, y)) (v, y)` of §3.2 (with `y = Var.zero`). -/
def exampleNatTerm (v : Term ℕ 1 0) : Term ℕ 1 0 :=
  .app (.lam (.pair (.var 0) (.var 1))) (.pair v (.var 0))

/-- The example derivation of §3.2:
`y : [A]_2 ⊢ (λx. (x, y)) (v, y) : (A ⊗ A) ⊗ A`, assuming `∅ ⊢ v : A`. -/
theorem exampleNat_typing {k : ℕ} (A : Ty ℕ k) (v : Term ℕ 1 0)
    (hv : HasType (TCtx.ofList [none]) v A) :
    HasType (ctxY A 2) (exampleNatTerm v) (tensor (tensor A A) A) := by
  -- the two halves `y : [A]_1` of `y : [A]_2`
  refine HasType.app (Γ₁ := ctxY A 1) (Γ₂ := ctxY A 1) (A := tensor A A) (by ctx_add) ?_ ?_
  · -- `y : [A]_1 ⊢ λx. (x, y) : (A ⊗ A) ⊸ ((A ⊗ A) ⊗ A)`
    refine HasType.abs (HasType.tensorI
      (Γ₁ := TCtx.ofList [some (.lin (tensor A A)), none])
      (Γ₂ := TCtx.ofList [none, some (.grd A 1)])
      (by ctx_add) ?_ ?_)
    · exact HasType.var (by pick_var)
    · exact HasType.var' (by pick_var)
  · -- `y : [A]_1 ⊢ (v, y) : A ⊗ A`
    refine HasType.tensorI (Γ₁ := TCtx.ofList [none]) (Γ₂ := ctxY A 1) (by ctx_add) hv ?_
    exact HasType.var' (by pick_var)

end FOFU
