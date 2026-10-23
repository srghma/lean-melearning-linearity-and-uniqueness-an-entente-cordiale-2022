# Summary of changes for run 192af3e0-5e8b-42a7-bd3a-49fba301d17d
I split the large files and tidied up the directory layout. Only code was moved: no definition, statement or proof changed. The whole project still builds (`lake build`, 1004 jobs) with no warnings, and there is no `sorry`, `admit` or `axiom`. The longest file is now 331 lines (`LCU/Ext2_MutableArrays/ArrayProgress.lean`); before, it was 761.

**How files were split.** A big file became a directory of smaller files. A file with the original name stays next to it, keeps the overview docstring and imports all the parts. Because of this, existing `import`s of these files did not need to change. Each new file has its own short docstring.

| Old file (lines) | New parts |
| --- | --- |
| `Common/Syntax.lean` (761) | `Common/Syntax/`: `Basic`, `RenSubst`, `MapOp`, `Occurs`, `HasOp` |
| `Common/Ctx.lean` (717) | `Common/Ctx/`: `Basic`, `Pointwise`, `Algebra`, `Ren`, `Combine` |
| `FOFU/Sec3_CoreCalculus/Syntax.lean` (570) | `Syntax/`: `Types`, `Terms`, `Eliminators`, `Source` |
| `LCU/Sec3_1_Calculus/Syntax.lean` (393) | `Syntax/`: `Types`, `Terms`, `Eliminators`, `Core` |
| `FOFU/Sec3_CoreCalculus/TypingD.lean` (405) | `TypingD/`: `Basic`, `Equiv` |
| `FOFU/Sec3_CoreCalculus/CtxAlgebra.lean` (389) | `CtxAlgebra/`: `Add`, `Scale`, `Approx` |

Three files were split differently, into separate files with their own names:
- `LCU/Sec3_4_HeapModel/Heap.lean` (510) is now `Heap.lean` (heaps), `Step.lean` (reduction, and the notes on the rules that had to be reconstructed) and `Compat.lean` (Definition 3).
- The FOFU substitution lemmas are now `SubstSetup.lean` (supporting definitions) and `Substitution.lean` (Lemmas 6.2 and 6.3).
- `LCU/Ext1_CallByName/CbnSemantics.lean` is now `PrimFree.lean` (terms without array primitives) and `CbnSemantics.lean`.

**Directory changes**
- **FOFU, §6.3:** `Sec6_3_Theorems/` had 18 files. The proof of the substitution lemmas is now in `SubstitutionLemmas/` (`NameSubst`, `Renaming`, `ZeroWeakening`, `Occurs`, `SubstSetup`, `Substitution`). The counterexamples are in `Counterexamples/`, without the `Counter` prefix (`Setup`, `Progress`, `Preservation`, `BorrowSafety`, `MultiBorrowLiteral`, `EqSoundness`).
- **LCU, §3.5:** the same was done for `Sec3_5_Metatheory/Counterexamples/` (`Conservation`, `Uniqueness`, `Progress`, `EqSoundness`).
- **FOFU, §5:** `Sec5_1_Equational/` and `Sec5_2_Distributive/` each held one file, so they are merged into `Sec5_Fractional/` as `Equational.lean` and `Distributive.lean`.

**Documentation and tracking**
- `RequestProject/FOFU.lean` and `RequestProject/LCU.lean` list all the files, grouped by section, and describe the layout. `LCU.lean` now also imports `RefRenaming`, which it was missing before.
- File references were updated in the docstrings, `README.md` and both reading guides, including the LCU dependency diagram. `PROPOSAL.md` now says that its older file references may be out of date.
- In the Properties table, the 16 entries whose declarations moved now point to their new files. Their statuses and evidence are unchanged.