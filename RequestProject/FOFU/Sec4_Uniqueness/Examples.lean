module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# §4 — the examples `exampleMove` and `exampleShare`

The core calculus has no `let x = t₁ in t₂`; as usual we read it as `(λx. t₂) t₁`.
The type `Colour` is an arbitrary type `C`.  We use the natural-number semiring; the paper
shares at the interval grade `[0..2]`, here we share at the exact grade `2` (both uses are
consumed).

* `exampleMove`: `⊢ λscarlet. let x = scarlet in let y = x in y : *C ⊸ *C`
* `exampleShare`: `⊢ λscarlet. let [s] = share scarlet in (s, s) : *C ⊸ C ⊗ C`
-/

@[expose] public section

namespace FOFU

open Ty

/-- `λscarlet. let x = scarlet in let y = x in y`, i.e. `λ. (λ. (λ. #0) #0) #0`. -/
def exampleMove : Term ℕ 0 0 := .lam (.app (.lam (.app (.lam (.var 0)) (.var 0))) (.var 0))

/-- `exampleMove : *C ⊸ *C`: ownership is moved from `scarlet` to `x` to `y`. -/
theorem exampleMove_typing {k : ℕ} (C : Ty ℕ k) :
    HasType (TCtx.ofList []) exampleMove (lolli (star C) (star C)) := by
  refine HasType.abs (HasType.app (Γ₁ := TCtx.ofList [none])
    (Γ₂ := TCtx.ofList [some (.lin (star C))]) (A := star C) (by ctx_add) ?_ ?_)
  · refine HasType.abs (HasType.app (Γ₁ := TCtx.ofList [none, none])
      (Γ₂ := TCtx.ofList [some (.lin (star C)), none]) (A := star C) (by ctx_add) ?_ ?_)
    · exact HasType.abs (HasType.var (by pick_var))
    · exact HasType.var (by pick_var)
  · exact HasType.var (by pick_var)

/-- `λscarlet. let [s] = share scarlet in (s, s)`, sharing at grade `2`. -/
def exampleShare : Term ℕ 0 0 := .lam (.letBox (.share 2 (.var 0)) (.pair (.var 0) (.var 0)))

/-- `exampleShare : *C ⊸ C ⊗ C`: the unique value is shared and then used twice. -/
theorem exampleShare_typing {k : ℕ} (C : Ty ℕ k) :
    HasType (TCtx.ofList []) exampleShare (lolli (star C) (tensor C C)) := by
  refine HasType.abs (HasType.elim (Γ₁ := TCtx.ofList [some (.lin (star C))])
    (Γ₂ := TCtx.ofList [none]) (A := C) (r := 2) (by ctx_add)
    (HasType.share 2 (HasType.var (by pick_var))) ?_)
  refine HasType.tensorI (Γ₁ := TCtx.ofList [some (.grd C 1), none])
    (Γ₂ := TCtx.ofList [some (.grd C 1), none]) (by ctx_add) ?_ ?_ <;>
  exact HasType.var' (by pick_var)

end FOFU
