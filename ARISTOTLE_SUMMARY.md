# Summary of changes for run 4cc4945b-f8d0-4151-8f07-e63fe5c3bdb4
I made the project build faster without changing any definitions or theorem statements. A from-scratch build of the project's own files went from about 1 min 47 s to about 43 s on this machine.

**Where the time went.** I timed and profiled each file. Most of each file's time was spent loading all of Mathlib, about 6–7 s per file. That cost was paid in all 23 files, one after another, because they import each other in a chain. The only real proof work that stood out was in `RequestProject/LCU/Syntax.lean`, where five lemmas took 3–4.5 s each.

**What I changed**
- **Smaller imports.** `Syntax.lean` and `Granule.lean` were the only files that imported Mathlib directly, and both used `import Mathlib`. They now import only what they need:
  - `Syntax.lean`: `Mathlib.Data.Fin.Tuple.Basic`, `Mathlib.Data.Fintype.Defs` and `Mathlib.Algebra.Ring.Defs`.
  - `Granule.lean`: `Mathlib.Algebra.Ring.Defs`, `Mathlib.Tactic.DeriveFintype`, `Mathlib.Data.Fintype.Basic` and `Mathlib.Order.Basic`.
  
  Load time per file dropped from about 6 s to about 1.7 s, and every later file in the chain benefits.
- **Faster proofs in `Syntax.lean`.** The renaming/substitution lemmas (`rename_id`, `rename_rename`, `subst_var`, `subst_ren`, `subst_rename`, `rename_subst`, `subst_subst`) used `induction t <;> simp_all [...]`. That searched the full simp lemma set across all 16 term cases. They now use `simp only` with just the definitions and lemmas they need. Each lemma dropped from up to about 4.5 s to about 0.8 s, and the file went from about 13 s to about 5 s.

**Checks**
- The whole project builds with no errors and no `sorry`.
- `#print axioms` shows only the standard axioms for `cbn_eval_core` (`propext`, `Classical.choice`, `Quot.sound`) and `Term.subst_subst` (`propext`, `Quot.sound`).
- The Properties table did not need updating, since no statements changed.

**Left as is**
- `RequestProject/Main.lean` still does `import Mathlib` and contains only option settings. It doesn't hold up the other files, so I didn't touch it.
- The proof of `HypAdd.interchange` in `CtxAlgebra.lean` uses a long backtracking tactic. It takes about 1.3 s, which wasn't worth reworking.

The changes are committed and pushed.