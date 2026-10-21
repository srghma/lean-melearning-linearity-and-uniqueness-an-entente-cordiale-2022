# Summary of changes for run 8177784b-a0d8-431e-9137-5a3ec513bcd3
I formalized the second paper, *Functional Ownership through Fractional Uniqueness* (`paper.typ`), and reorganized the project so the two papers keep their code apart. The whole project builds with no `sorry`. The FOFU results I registered use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Several of the paper's §6.3 theorems turned out to be false as stated; details are below.

**Layout**
- `RequestProject/Common/` holds the code both papers use: the de Bruijn infrastructure (`DeBruijn.lean`, with `Term n`-style scoping and `Fin n` variables) and the preordered-semiring grades (`Grades/PreorderedSemiring.lean`). The first paper's code (`RequestProject/LCU/`) now imports it from there, and comments mark the reuse in both papers' files.
- `RequestProject/FOFU/` (namespace `FOFU`, root module `RequestProject/FOFU.lean`) holds the second paper's code, in one subdirectory per section: `Sec3_CoreCalculus`, `Sec4_Uniqueness`, `Sec5_Fractional`, `Sec5_1_Equational`, `Sec5_2_Distributive`, `Sec6_1_Preliminaries`, `Sec6_2_Reduction` and `Sec6_3_Theorems`. The core calculus has graded types, so its syntax and typing rules are separate definitions, not copies of the first paper's.
- I renamed the old reading guide to `READING_GUIDE-linearity-and-uniqueness.md` and added `READING_GUIDE-functional-ownership-through-fractional-uniqueness.md`, which maps the paper's sections and results to Lean names. `README.md` now covers both papers.

**Proved**
- Lemma 6.2, linear substitution (`HasType.subst_lin`).
- Lemma 6.3, graded substitution (`HasType.subst_grd`).
- Example 6.5, heap compatibility (`example_6_5`). The paper leaves the typing of `v₁` implicit; I assumed `∅ ⊢ v₁ : A`.
- Typing of the code examples: `exampleNat`, `exampleMove`, `exampleShare`, `exampleBorrow`, `exampleReborrow`, `exampleArray`, `exampleClone`, `exampleReference` and `examplePartial`. A few are stated in a context supplying the functions they call, or with `Colour` replaced by a general type. `exampleGraded` is not formalized; the reading guide explains why.

**Disproved**
§6.3 is formalized for two versions of heap compatibility (Definition 6.4): the rules as printed, and a repaired version with one extra rule for resource entries. Each counterexample is a machine-checked proof that the statement is false:
- Theorem 6.6 (Progress) is false for both versions. `split (*())` is well typed but stuck.
- Theorem 6.7 (Preservation) is false for both versions. With the printed rules, `newArray 3` produces a heap that is compatible with no context. With the repaired rules, `⤳splitRef` removes a reference from the heap while the reduced term still mentions it.
- Lemma 6.8, Theorem 6.9 and Corollary 6.10 are false for the repaired version.
- Theorem 6.11 (equational soundness) is false for both versions, whatever relation on final heaps and values is used.

**Holds only vacuously**
- Corollary 6.10 with the printed rules (`uniqueness_literal`). Under those rules no compatible heap contains a resource identifier, and the statement only talks about such identifiers.

**Still open**
- Lemma 6.8 and Theorem 6.9 with the printed rules: the part about newly created identifiers is neither proved nor disproved.

The Properties table now has entries for the second paper with these statuses, each linked to its line in `paper.typ`. The 30 existing first-paper entries are unchanged, but their line links were written against the first paper's text and probably no longer match, since `paper.typ` now holds the second paper.