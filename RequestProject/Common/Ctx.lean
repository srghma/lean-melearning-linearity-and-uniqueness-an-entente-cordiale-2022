module
public import RequestProject.Common.Ctx.Basic
public import RequestProject.Common.Ctx.Pointwise
public import RequestProject.Common.Ctx.Algebra
public import RequestProject.Common.Ctx.Ren
public import RequestProject.Common.Ctx.Combine

/-!
# Length-indexed contexts

Contexts, heaps and stores of both formalisations are *lists* whose length is the number of
variables (or runtime names) in scope: `Ctx α n` is a snoc list of `n` entries of type
`α`.  The entry for `Var.zero` is the last one (the most recently bound variable).

* `Ctx.nil : Ctx α 0` and `Ctx.snoc Γ a : Ctx α (n + 1)` (notation `Γ ,, a`);
* `Γ.get i`: the entry of the variable `i`, by recursion on the context;
* `Ctx.Lookup Γ i a`: the inductive lookup judgment (`here` / `there`);
* `Ctx.map`, `Ctx.set`, `Ctx.replicate`, `Ctx.ofFn`;
* `Ctx.All P Γ`, `Ctx.Forall₂ R Γ Δ`, `Ctx.Forall₃ R Γ₁ Γ₂ Γ`: pointwise predicates and
  relations, defined by recursion on the contexts (`nil` / `snoc`).  Context addition and
  scaling of both papers are instances of `Forall₃` and `Forall₂`.

Equality of contexts is equality of lists: two contexts are equal when their entries are
(`Ctx.ext`), and `snoc` is injective (`Ctx.snoc_inj`).  There is no function extensionality
involved.

## Files

* `Ctx/Basic.lean`: the type, `get`, `Lookup`, `map`, `replicate`, `set`;
* `Ctx/Pointwise.lean`: `All`, `Forall₂`, `Forall₃`, `Pick`;
* `Ctx/Algebra.lean`: algebraic laws of `Forall₃` (used for context addition);
* `Ctx/Ren.lean`: renaming of contexts `Ctx.Ren`;
* `Ctx/Combine.lean`: `pad`, `zipWith`, `append`, and mapping.
-/
