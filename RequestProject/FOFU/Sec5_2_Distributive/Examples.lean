module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# §5.2 — the example `examplePartial`

`examplePartial indigo = let (r, p) = push indigo in let r' = withBorrow alter r in
pull (r', p)`: the component `r` of a uniquely owned pair is mutably borrowed by
`alter` while the owner keeps the other component `p`.

As in §4/§5, `Colour` is an arbitrary pair type `A ⊗ B`, the semiring is `ℕ`, the
function `alter : &₁ A ⊸ &₁ A` (only declared in the paper) is a linear context variable,
and `let r' = withBorrow alter r in pull (r', p)` is inlined to
`pull (withBorrow alter r, p)`.
-/

@[expose] public section

namespace FOFU

open Ty

/-- `λindigo. let (r, p) = push indigo in pull (withBorrow alter r, p)`, in the scope of
`alter = #0`. -/
def examplePartial : Term ℕ 1 :=
  .lam (.letPair (.push (.var 0)) (.pull (.pair (.withBorrow (.var 3) (.var 1)) (.var 0))))

/-- `alter : &₁ A ⊸ &₁ A ⊢ examplePartial : *(A ⊗ B) ⊸ *(A ⊗ B)`. -/
theorem examplePartial_typing {k : ℕ} (A B : Ty ℕ k) :
    HasType (Ctx.ofList [some (.lin (lolli (borrow Perm.one A) (borrow Perm.one A)))])
      examplePartial (lolli (star (tensor A B)) (star (tensor A B))) := by
  set Alt : Ty ℕ k := lolli (borrow Perm.one A) (borrow Perm.one A)
  refine HasType.abs (HasType.tensorE
    (Γ₁ := Ctx.ofList [some (.lin (star (tensor A B))), none])
    (Γ₂ := Ctx.ofList [none, some (.lin Alt)])
    (by ctx_add) (HasType.push (HasType.var rfl (by zero_rest))) ?_)
  -- `p : *B, r : *A, indigo : −, alter : Alt ⊢ pull (withBorrow alter r, p) : *(A ⊗ B)`
  exact HasType.pull (HasType.tensorI
    (Γ₁ := Ctx.ofList [none, some (.lin (star A)), none, some (.lin Alt)])
    (Γ₂ := Ctx.ofList [some (.lin (star B)), none, none, none])
    (by ctx_add)
    (HasType.withBorrow
      (Γ₁ := Ctx.ofList [none, none, none, some (.lin Alt)])
      (Γ₂ := Ctx.ofList [none, some (.lin (star A)), none, none])
      (by ctx_add) (HasType.var rfl (by zero_rest)) (HasType.var rfl (by zero_rest)))
    (HasType.var rfl (by zero_rest)))

end FOFU
