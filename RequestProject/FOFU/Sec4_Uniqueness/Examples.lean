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
def exampleMove : Term ℕ 0 := .lam (.app (.lam (.app (.lam (.var 0)) (.var 0))) (.var 0))

/-- `exampleMove : *C ⊸ *C`: ownership is moved from `scarlet` to `x` to `y`. -/
theorem exampleMove_typing {k : ℕ} (C : Ty ℕ k) :
    HasType Ctx.empty exampleMove (lolli (star C) (star C)) := by
  refine HasType.abs (HasType.app (Γ₁ := Ctx.empty.cons none) (Γ₂ := Ctx.empty.cons
    (some (.lin (star C)))) (A := star C)
    (CtxAdd.cons (AssmAdd.noneLeft _) CtxAdd.empty) ?_ ?_)
  · refine HasType.abs (HasType.app (Γ₁ := (Ctx.empty.cons none).cons none)
      (Γ₂ := (Ctx.empty.cons none).cons (some (.lin (star C)))) (A := star C)
      (CtxAdd.cons (AssmAdd.noneLeft _) (CtxAdd.cons (AssmAdd.noneLeft _) CtxAdd.empty))
      ?_ ?_)
    · exact HasType.abs (HasType.var rfl (zeroRest_cons_zero
        ((Ctx.IsZero.empty.cons (a := none) trivial).cons (a := none) trivial)))
    · exact HasType.var rfl (zeroRest_cons_zero (Ctx.IsZero.empty.cons (a := none) trivial))
  · exact HasType.var rfl (zeroRest_cons_zero Ctx.IsZero.empty)

/-- `λscarlet. let [s] = share scarlet in (s, s)`, sharing at grade `2`. -/
def exampleShare : Term ℕ 0 := .lam (.letBox (.share 2 (.var 0)) (.pair (.var 0) (.var 0)))

/-- `exampleShare : *C ⊸ C ⊗ C`: the unique value is shared and then used twice. -/
theorem exampleShare_typing {k : ℕ} (C : Ty ℕ k) :
    HasType Ctx.empty exampleShare (lolli (star C) (tensor C C)) := by
  refine HasType.abs (HasType.elim (Γ₁ := Ctx.empty.cons (some (.lin (star C))))
    (Γ₂ := Ctx.empty.cons none) (A := C) (r := 2)
    (CtxAdd.cons (AssmAdd.noneRight _) CtxAdd.empty)
    (HasType.share 2 (HasType.var rfl (zeroRest_cons_zero Ctx.IsZero.empty))) ?_)
  refine HasType.tensorI (Γ₁ := (Ctx.empty.cons none).cons (some (.grd C 1)))
    (Γ₂ := (Ctx.empty.cons none).cons (some (.grd C 1)))
    (CtxAdd.cons (AssmAdd.grd C 1 1) (CtxAdd.cons (AssmAdd.noneLeft _) CtxAdd.empty)) ?_ ?_ <;>
  exact HasType.var' rfl (zeroRest_cons_zero (Ctx.IsZero.empty.cons (a := none) trivial))

end FOFU
