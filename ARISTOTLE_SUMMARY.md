# Summary of changes for run 268ad72a-0149-4d34-82a5-d4f99ce1077f
I continued the formalisation with a positive type-safety result for LCU. In the earlier run, Theorems 4–7 turned out to be false for the heap model as written in the text. This run adds a repaired operational semantics and proves syntactic type safety for it. The whole project builds with no `sorry`, and the only axioms used are `propext`, `Classical.choice` and `Quot.sound`. Terms still use de Bruijn indices, with `Term 0` for closed terms.

**New file `RequestProject/LCU/CbnSemantics.lean`.** `CbnStep` is a call-by-name reduction (the same strategy as the paper's heap model) for the fragment without arrays. It follows the heap rules but substitutes instead of allocating heap bindings:
- \((\lambda x.t)\,u \to [u/x]t\) and the β-rules for \(\otimes\), \(1\) and \(!\);
- `&(*t) ⟶ !t` for any `t`, not only values. This fixes the progress counterexample;
- `copy !u as x in t ⟶ [*u/x]t`;
- congruence rules in the position each elimination form evaluates.

The theorems below hold for terms with no free variables whose runtime array references are non-linear (for example closed terms in the empty context):
- **Subject reduction:** `CbnStep.preserves` and `CbnSteps.preserves`.
- **Progress** for terms with no array primitives: `cbn_progress`. A well-typed term is either a value in the paper's sense or can take a step. Array primitives are excluded because they need a heap to reduce.
- **Type safety for closed terms:** `cbn_type_safety`. Every reduct keeps its type and is either a value or can step again.
- **Values don't step, and reduction is deterministic:** `IsValue.not_cbnStep` and `CbnStep.deterministic`.
- **The no-free-variables restriction is needed:** `not_cbnStep_preserves_open`. With `x : [1]`, the term `copy !x as y in &y : !1` steps to `&(*x)`, which has no type because `nec` forbids variable assumptions.

**New file `RequestProject/LCU/CbnExamples.lean`.** The two earlier counterexample terms behave well under the new semantics. `&(*((λz.z) unit))` takes a step, and `copy !((λz.z) unit) as x in &x` reduces to the value `!((λz.z) unit)` of type `!1`.

**Caveat:** this is a repaired semantics that I designed, not the paper's heap model. It does not track usage or uniqueness, so it does not rescue Theorems 4–7 themselves.

`README.md` now describes the new files, and the new definition and theorems are in the Properties table, all marked proved. `ARISTOTLE_SUMMARY.md` was left unchanged.