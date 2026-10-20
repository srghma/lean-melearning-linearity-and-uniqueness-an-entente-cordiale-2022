# Summary of changes for run 76352643-5294-4f92-a239-b6c7225e842e
I refactored the project to cut down on duplicated code. No registered definition or theorem statement changed, so the Properties table still applies as it was. The whole project builds with no errors, no warnings and no `sorry`. I spot-checked the main results (`array_type_safety`, `cbn_eval_core`, the substitution and weakening lemmas, determinism, the counterexamples, `possible_cake`) and they use only the standard axioms. Across the 14 files I touched, the diff is 290 lines added and 711 removed; the `RequestProject/LCU` files went from 5457 to about 5000 lines.

**Shared helpers I added**
- **`split_rule h₁ h₂ hadd`** (in `TypingD.lean`): one tactic that applies whichever of the six context-splitting typing rules fits (`app`, `tensorI`, `tensorE`, `unitE`, `bangE`, `copy`). Proofs by induction on typing used to repeat a near-identical case for each of these rules. Those cases are now one shared case in `der`, `rename`, `weaken`, `shiftRefs`, `subst_gen`, `freeIn_of_lin` and `ne_none_of_freeIn`. Rules that differ only in which literal or primitive they type (`unitI`, `natI`, `floatI`, `prim`) are also handled together.
- **`hyp_add`** (in `CtxAlgebra.lean`): a 3-line tactic that replaces two very long hand-written lists of constructor combinations (`hyp_add2` and `hyp_add3`).
- **New context lemmas** in `CtxAlgebra.lean`: `AllNonLin.set`, `AllNonLin.set'`, `AllNonLin.of_set`, `AllNonLin.cons_none`, `Add.cons_none`, `HypAdd.some_of_nonLin`. Each replaces the same small argument that had been re-proved by hand in several files.
- **Variable/reference rule side conditions:** these are now proved once, in `Ctx.Add.weaken_name` and `Ctx.remove_set_allNonLin`. The variable and array-reference cases of weakening and substitution now just call them.
- **`not_value`** (in `Values.lean`): one tactic for the seven "this term is not a value" lemmas, which all had the same proof.
- **`CbnSteps.congr`** (in `CbnNormalization.lean`): one lemma replacing six per-constructor congruence lemmas.

**Definitions merged**
- `Term.shiftRefs N` (array semantics) duplicated the heap model's `renameRefs`. `renameRefs` now lives in `Syntax.lean`, and `shiftRefs N` is defined as `renameRefs (N + ·)`.
- The dereliction-free substitution lemmas (`HasTypeD.subst_lin`, `subst_nonlin`, `subst_none`) are now proved directly in `Substitution.lean`. Lemmas 1 and 2 (`HasType.subst_lin`/`subst_nonlin`) follow from them, which removes the wrapper lemmas that used to go back and forth in `Equational.lean`.

**Other compactions:** many proofs now treat structurally identical cases together. This applies to `hasType_iff_hasTypeD`, the term traversals (`PrimFree`, `freeIn_rename`), subject reduction, progress, determinism, and the store-based progress and preservation proofs.

**Left as is**
- The paper's typing judgment `HasType` and the dereliction-free `HasTypeD` still have two parallel lists of rules. Merging them into one parametrised definition would change how the registered `HasType` definition reads, so I didn't do it.
- Several elimination-form cases (in `CbnStep.preserves` and `AStep.preserves`) still each have their own case. Merging them would rely on the order in which Lean names the inverted hypotheses, and that order differs between typing rules, so it would be fragile.

All changes are committed and pushed.