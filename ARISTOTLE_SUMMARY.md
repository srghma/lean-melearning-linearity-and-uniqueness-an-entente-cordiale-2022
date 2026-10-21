# Summary of changes for run 83d9b41c-c1f3-4dbc-88b3-bafecb299d45
I moved the formalisation into one directory per paper section, split the longer files, added a reading guide, and added comments throughout. No theorem statement or proof changed. The whole project still builds with no errors, no warnings and no `sorry`. I re-checked the axioms of `array_type_safety`, `cbn_eval_core`, `not_uniqueness`, `HasType.subst_lin` and `possible_cake`: they use only `propext`, `Classical.choice` and `Quot.sound`.

**New layout** (under `RequestProject/LCU/`; `RequestProject/LCU.lean` imports everything):
- `Sec2_KeyIdeas/`: `KeyIdeas.lean`
- `Sec3_1_Calculus/`: `Syntax`, `RenameSubst`, `Context`, `CtxAlgebra`, `Typing`, `TypingD`, `Weakening`, `Substitution`, `Values`, `FreeVars`
- `Sec3_2_Equational/`: `Equational` (the definitions), `EqAxiomTyping` (the axioms preserve typing)
- `Sec3_4_HeapModel/`: `Heap`
- `Sec3_5_Metatheory/`: `Metatheory` and the four `Counter*` files
- `Sec4_Implementation/`: `Granule`
- `Ext1_CallByName/` (beyond the paper): `CbnSemantics`, `CbnExamples`, `CbnNormalization`
- `Ext2_MutableArrays/` (§3.3 and beyond): `RefShift`, `ArraySemantics`, `ArrayPreservation`, `ArrayProgress`, `ArrayExamples`

**Files split:**
- `Syntax` → `Syntax` + `RenameSubst` (renaming and substitution).
- `Equational` → `Equational` + `FreeVars` + `EqAxiomTyping`.
- `ArraySemantics` (740 lines) → `ArraySemantics` (definitions) + `ArrayPreservation` (subject reduction) + `ArrayProgress` (progress and type safety).
- The four counterexample files used to import each other in a chain; each now imports only `Metatheory`.

**Reading guide:** `READING_GUIDE.md` covers:
- the de Bruijn and context conventions you need first;
- a table mapping each directory to its paper section;
- a table mapping every numbered item of the paper (Definitions 1–3, Figure 1, Lemmas 1–3, Theorems 4–7, the §2 examples, §4.1) to its Lean name and file;
- two reading paths: statements only, or the full development in dependency order, with infrastructure files marked as skippable on a first read;
- a dependency diagram and some tips for browsing.

The file table in `README.md` now follows the new layout and points to the guide.

**Comments added:**
- Module docstrings now list main definitions and results, with implementation notes where useful. For example, `TypingD` explains why the dereliction-free system exists, `Substitution` explains why the lemma is generalised to any variable, and `Metatheory` has a table pointing each of Theorems 4–7 to its disproof.
- Longer files are divided by section headers.
- About 150 previously undocumented lemmas and definitions now have docstrings. These include each step and intermediate heap of the uniqueness counterexample, the context-algebra laws, and the inversion and progress helpers. The `HasType` docstring also explains how the paper's rules are encoded.

The Properties table now points to the new file locations, and every entry keeps its earlier status. Everything is committed and pushed.