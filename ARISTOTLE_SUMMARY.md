# Summary of changes for run 193e9862-0d20-4f36-86aa-b189dcc46fa9
The request was just "refactor", so I worked on the refactoring items that `PROPOSAL.md` still listed as open. The full project builds, there is no `sorry`, `admit` or `axiom` in `RequestProject/`, and the changes are committed and pushed.

**1. Function-free restriction of Theorem 6.7 (`FOFU/Sec6_3_Theorems/Statements.lean`)**
- The two checks for "contains no function type" are now `Bool`-valued functions, `Ty.funFree` and `Ty.refsFunFree`. They used to be predicates (`Ty.FunFree`, `Ty.RefsFunFree`). This matches how `Ty.copyable` and `Ty.cloneable` were already done.
- `TCtx.RefsFunFree` used to be three `∀ i, Γ.vars.get i = some …` clauses. It is now two uses of the existing `Ctx.All` predicate, with a small helper `Assm.ty` that returns the type of an assumption.
- `Preservation` means the same as before. The two disproofs in `CounterPreservation.lean` were updated, now use simpler proofs, and still build. The Lean statements in the Properties table did not change, so no entries needed updating.

**2. Grade class (`Common/Grades/PreorderedSemiring.lean`)**
- `Grades.PreorderedSemiring` is now connected to Mathlib's ordering classes (`AddLeftMono`, `AddRightMono`, `MulLeftMono`, `MulRightMono`), in both directions:
  - any grade semiring automatically gets these instances, so Mathlib's lemmas such as `add_le_add` and `mul_le_mul'` work on grades;
  - `PreorderedSemiring.ofMono` builds the class from them. The ℕ instance now uses it.
- `FOFU/Sec3_CoreCalculus/CtxAlgebra.lean` now uses Mathlib's lemmas instead of the class fields.
- I did not switch to Mathlib's `IsOrderedRing` because it requires a partial order, and the papers only assume a pre-order. The file's documentation says this.

**3. Permission algebra (`FOFU/Sec5_Fractional/Permission.lean`)**
- I added the basic laws for the partial addition of fractions `Frac.add`: commutativity (`add_comm`), associativity (`add_assoc`) and cancellation (`add_left_cancel`).
- I also added `not_one_add` (nothing can be added to the full permission `1`), `lt_add_left` (a sum is larger than each part) and `half_lt` (halving makes a fraction smaller).
- The typing rules still take the proof that `f + g ≤ 1` directly; I did not change them to use these laws.

**4. Documentation**
- The status table in `PROPOSAL.md` now records items 6 and 7 as partly done, describing exactly what changed, and the small clean-ups in item 11 as done. Those clean-ups (`Step.appL`, `weakenTo`, a dedicated type for LCU array references) had already been made earlier; this run only finished the context-restriction one.

**Not done:** a separate grammar of function-free types (the rest of item 6), and the process and tooling items 9, 10 and 12–14 (a verified type checker, a file of checks that each hypothesis can actually be satisfied, and process rules).