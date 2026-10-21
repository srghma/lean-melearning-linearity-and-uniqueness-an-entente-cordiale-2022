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
public import RequestProject.FOFU.Sec5_1_Equational.Equational
public import RequestProject.FOFU.Sec5_2_Distributive.Examples
public import RequestProject.FOFU.Sec5_Fractional.Examples
public import RequestProject.FOFU.Sec5_Fractional.ExampleGraded
public import RequestProject.FOFU.Sec5_Fractional.Permission
public import RequestProject.FOFU.Sec5_Fractional.Resources
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap
public import RequestProject.FOFU.Sec6_1_Preliminaries.TypingRefs
public import RequestProject.FOFU.Sec6_1_Preliminaries.Values
public import RequestProject.FOFU.Sec6_2_Reduction.Step
public import RequestProject.FOFU.Sec6_3_Theorems.Compat
public import RequestProject.FOFU.Sec6_3_Theorems.BorrowSafetyLiteral
public import RequestProject.FOFU.Sec6_3_Theorems.CounterBorrowSafety
public import RequestProject.FOFU.Sec6_3_Theorems.CounterMultiBorrowLiteral
public import RequestProject.FOFU.Sec6_3_Theorems.CounterEqSoundness
public import RequestProject.FOFU.Sec6_3_Theorems.CounterPreservation
public import RequestProject.FOFU.Sec6_3_Theorems.CounterProgress
public import RequestProject.FOFU.Sec6_3_Theorems.CounterSetup
public import RequestProject.FOFU.Sec6_3_Theorems.NameSubst
public import RequestProject.FOFU.Sec6_3_Theorems.Occurs
public import RequestProject.FOFU.Sec6_3_Theorems.Renaming
public import RequestProject.FOFU.Sec6_3_Theorems.Statements
public import RequestProject.FOFU.Sec6_3_Theorems.Substitution
public import RequestProject.FOFU.Sec6_3_Theorems.ZeroWeakening

/-!
# Formalisation of *Functional Ownership through Fractional Uniqueness*

Importing this module imports the whole formalisation of the second paper (namespace
`FOFU`).  The files are grouped into directories by section of the paper
(`Sec3_CoreCalculus/`, `Sec4_Uniqueness/`, `Sec5_Fractional/`, `Sec5_1_Equational/`,
`Sec5_2_Distributive/`, `Sec6_1_Preliminaries/`, `Sec6_2_Reduction/`,
`Sec6_3_Theorems/`).  Code shared with the formalisation of *Linearity and Uniqueness*
(`RequestProject/LCU/`) lives in `RequestProject/Common/`.

See `READING_GUIDE-functional-ownership-through-fractional-uniqueness.md` at the root of
the project for a guide to the files.
-/
