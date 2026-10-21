# Summary of changes for run 0545220a-5d41-4c05-b75d-f042eaac3543
`exampleGraded` needs a `readRef` that splits the grade of the stored box. The interface printed in §5 can't do that. I added such a primitive alongside the printed `readRef`, and with it `exampleGraded` is now formalized and type-checks. The whole project builds with no `sorry`, and both new theorems use only the standard axioms.

**Why the printed interface fails.** The paper gives
\[ \mathsf{readRef} : \&_p(\mathsf{Ref}_{id}(\Box_r A)) \multimap A \otimes \&_p(\mathsf{Ref}_{id}(\Box_r A)) \]
The example stores `test : Float [6]`, then binds the result as `([x], ref') : (Float [4], *(Ref id (Float [2])))`. This conflicts with the interface in two ways:
1. The interface returns the unboxed contents `A`, but the pattern `[x]` expects a box, `□_4 Float`.
2. The interface returns the reference at the same type `□_r A`, but the example then uses it at `□_2 Float`.

With `r = 6` and `A = Float`, you get a linear `x : Float`, which can't be promoted to `□_4 Float`. Freezing `ref'` gives `□_6 Float`, not `□_2 Float`, and with `ℕ` grades approximation doesn't help. `not_primTy_readRef_graded` proves that the printed `readRef` has no instance of the needed type.

**What changes.** `readRef` has to split the stored grade \(q + r\), handing out \(q\) and keeping \(r\):
\[ \mathsf{readRefSplit} : {*}(\mathsf{Ref}_{id}(\Box_{q+r} A)) \multimap \Box_q A \otimes {*}(\mathsf{Ref}_{id}(\Box_r A)) \]
- **Reduction:** if the reference holds `[v]_(q+r)`, the call returns `([v]_q, *ref)` and the reference afterwards holds `[v]_r`.
- **Unique permission only:** the primitive changes the reference's type. With a fractional borrow, other borrows or the owner waiting in `withBorrow` would still expect the old type. So it is offered only at the unique permission `*`. That is all the example needs.

**Lean changes.** `readRefSplit` is a new primitive, and the printed `readRef` is unchanged.
- `Sec3_CoreCalculus/Syntax.lean`: new primitive name, arity 1.
- `Sec5_Fractional/Resources.lean`: its typing rule.
- `Sec6_2_Reduction/Step.lean`: its reduction rule.
- `NameSubst.lean` and `BorrowSafetyLiteral.lean`: one extra case each.
- New file `Sec5_Fractional/ExampleGraded.lean`:
  - `exampleGraded`, a de Bruijn term over `ℕ` grades that keeps the paper's `let [x]`, `let [y]` and the final `([x], [y])`.
  - `exampleGraded_typing`: `⊢ exampleGraded : □_4 𝔽 ⊗ □_2 𝔽`, using `readRefSplit` at \(q = 4, r = 2\).
  - `not_primTy_readRef_graded`, described above.
  - A helper, `HasType.var_grd_one`, for using a variable graded `1`.

**Effect on the §6.3 results.** Because `readRefSplit` is now part of the calculus, those statements also cover terms that use it. They all rebuild unchanged: none of the counterexamples uses it, and `borrowSafety_literal` still holds.

I updated `README.md`, the reading guide and the note in `Examples.lean`. Both new theorems are in the Properties table as proved.