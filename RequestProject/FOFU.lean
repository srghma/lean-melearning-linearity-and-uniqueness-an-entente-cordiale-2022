module
public import RequestProject.FOFU.Sec3_CoreCalculus.Context
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra
public import RequestProject.FOFU.Sec3_CoreCalculus.Example
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax
public import RequestProject.FOFU.Sec3_CoreCalculus.TypeSubst
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas
public import RequestProject.FOFU.Sec4_Uniqueness.Examples
public import RequestProject.FOFU.Sec5_Fractional.Permission
public import RequestProject.FOFU.Sec5_Fractional.Resources
public import RequestProject.FOFU.Sec5_Fractional.Examples
public import RequestProject.FOFU.Sec5_Fractional.ExampleGraded
public import RequestProject.FOFU.Sec5_Fractional.Equational
public import RequestProject.FOFU.Sec5_Fractional.Distributive
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap
public import RequestProject.FOFU.Sec6_1_Preliminaries.TypingRefs
public import RequestProject.FOFU.Sec6_1_Preliminaries.Values
public import RequestProject.FOFU.Sec6_2_Reduction.Step
public import RequestProject.FOFU.Sec6_3_Theorems.Compat
public import RequestProject.FOFU.Sec6_3_Theorems.Statements
public import RequestProject.FOFU.Sec6_3_Theorems.BorrowSafetyLiteral
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.NameSubst
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.Renaming
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.ZeroWeakening
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.Occurs
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.SubstSetup
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.Substitution
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.Setup
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.Progress
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.Preservation
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.BorrowSafety
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.MultiBorrowLiteral
public import RequestProject.FOFU.Sec6_3_Theorems.Counterexamples.EqSoundness

/-!
# Formalisation of *Functional Ownership through Fractional Uniqueness*

Importing this module imports the whole formalisation of the second paper (namespace
`FOFU`).  The files are grouped into directories by section of the paper
(`Sec3_CoreCalculus/`, `Sec4_Uniqueness/`, `Sec5_Fractional/` (including §5.1 and §5.2),
`Sec6_1_Preliminaries/`, `Sec6_2_Reduction/`, `Sec6_3_Theorems/`).  In
`Sec6_3_Theorems/`, the infrastructure and proofs of the substitution lemmas are in
`SubstitutionLemmas/` and the disproofs of the theorems in `Counterexamples/`.  Large files
are split into a directory of smaller files plus a file of the same name that imports
them all (for example `Sec3_CoreCalculus/Syntax.lean` and `Sec3_CoreCalculus/Syntax/`).
Code shared with the formalisation of *Linearity and Uniqueness* (`RequestProject/LCU/`)
lives in `RequestProject/Common/`.

See `READING_GUIDE-functional-ownership-through-fractional-uniqueness.md` at the root of
the project for a guide to the files.
-/
