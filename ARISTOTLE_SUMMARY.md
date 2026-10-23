# Summary of changes for run feda3a25-de51-43a2-9f19-2b52b9c82dd5
**What `RequestProject/Proposal/` was, and whether you need it**
It held one file, `Prototype.lean`. This was a small standalone sketch written before `PROPOSAL.md` was implemented, to try out the planned design (snoc-list contexts, a structural variable rule, values as their own type, and permissions restricted to \(0 < p \le 1\)). No file in the project imported it, and the real versions of those ideas now live in `Common/Var.lean`, `Common/Ctx.lean`, `Common/Syntax.lean`, `FOFU/` and `LCU/`. Neither paper's formalisation needs it, so I removed it.

**Does anything deleted need restoring? No.** I checked every file in your deleted list:
- **The 23 files deleted from the top of `RequestProject/LCU/`** (`Syntax`, `Typing`, `TypingD`, `Context`, `CtxAlgebra`, `Substitution`, `Weakening`, `Values`, `Equational`, `Heap`, `Metatheory`, the four `Counter*` files, `KeyIdeas`, `Granule`, the `Cbn*` and `Array*` files, `RefShift`). Each one already has a counterpart with the same name in the section folders (`Sec2_KeyIdeas/`, `Sec3_1_Calculus/`, `Sec3_2_Equational/`, `Sec3_4_HeapModel/`, `Sec3_5_Metatheory/`, `Sec4_Implementation/`, `Ext1_CallByName/`, `Ext2_MutableArrays/`). Those counterparts were already tracked in git, which is why they show as "modified" rather than new, and they use the new design. The deleted files were old copies from before the folder split.
- **`Common/DeBruijn.lean`** (and the earlier `Common/Lookup.lean`) were the old `Fin`-based helpers. `Common/Var.lean` and `Common/Ctx.lean` replace them.
- To catch anything lost along the way, I also checked that:
  - all 57 entries in the Properties table point to files and names that still exist;
  - every Lean file and declaration named in `README.md` and both reading guides exists. The only exceptions are a few paper examples the FOFU reading guide already says are not formalised (`exampleConcurrent`, `exampleDeriving`), plus the planned `Sanity.lean` and the old `Common/DeBruijn.lean`, which `PROPOSAL.md` mentions only as a proposed item and in its pre-change description of the code.

  Note that the repository history starts at a single commit, so I could not compare file contents against the old versions. This check is by file names, declarations and the docs.

**What else I removed**
- `RequestProject/Main.lean`: an unused template file. It contained only `import Mathlib` and some `set_option` lines, and nothing imported it.

I left the many small unreferenced lemmas in place. They are mostly `@[simp]` rewrite and injectivity lemmas that the simplifier uses implicitly, or results listed in the Properties table, not leftovers from the old design. I also kept everything else: `paper.typ`, `paper.bib`, `lncs-alpha.csl`, the reading guides and `PROPOSAL.md`.

**Documentation**
I removed the mention of the prototype from `README.md`. In `PROPOSAL.md` I replaced the pointer to the prototype file with a note that it has been removed, so the later references to "the prototype" make sense.

**Status**
`lake build` succeeds, there is no `sorry`, `admit` or `axiom` in `RequestProject/`, and the changes are committed and pushed.