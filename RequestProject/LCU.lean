module
public import RequestProject.LCU.Sec2_KeyIdeas.KeyIdeas
public import RequestProject.LCU.Sec3_1_Calculus.Syntax
public import RequestProject.LCU.Sec3_1_Calculus.RenameSubst
public import RequestProject.LCU.Sec3_1_Calculus.RefRenaming
public import RequestProject.LCU.Sec3_1_Calculus.Context
public import RequestProject.LCU.Sec3_1_Calculus.Typing
public import RequestProject.LCU.Sec3_1_Calculus.CtxAlgebra
public import RequestProject.LCU.Sec3_1_Calculus.TypingD
public import RequestProject.LCU.Sec3_1_Calculus.Weakening
public import RequestProject.LCU.Sec3_1_Calculus.Substitution
public import RequestProject.LCU.Sec3_1_Calculus.Values
public import RequestProject.LCU.Sec3_1_Calculus.FreeVars
public import RequestProject.LCU.Sec3_2_Equational.Equational
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping
public import RequestProject.LCU.Sec3_4_HeapModel.Heap
public import RequestProject.LCU.Sec3_4_HeapModel.Step
public import RequestProject.LCU.Sec3_4_HeapModel.Compat
public import RequestProject.LCU.Sec3_5_Metatheory.Metatheory
public import RequestProject.LCU.Sec3_5_Metatheory.Counterexamples.Uniqueness
public import RequestProject.LCU.Sec3_5_Metatheory.Counterexamples.Conservation
public import RequestProject.LCU.Sec3_5_Metatheory.Counterexamples.EqSoundness
public import RequestProject.LCU.Sec3_5_Metatheory.Counterexamples.Progress
public import RequestProject.LCU.Sec4_Implementation.Granule
public import RequestProject.LCU.Ext1_CallByName.PrimFree
public import RequestProject.LCU.Ext1_CallByName.CbnSemantics
public import RequestProject.LCU.Ext1_CallByName.CbnExamples
public import RequestProject.LCU.Ext1_CallByName.CbnNormalization
public import RequestProject.LCU.Ext2_MutableArrays.RefShift
public import RequestProject.LCU.Ext2_MutableArrays.ArraySemantics
public import RequestProject.LCU.Ext2_MutableArrays.ArrayPreservation
public import RequestProject.LCU.Ext2_MutableArrays.ArrayProgress
public import RequestProject.LCU.Ext2_MutableArrays.ArrayExamples

/-!
# Formalisation of *Linearity and Uniqueness: An Entente Cordiale*

Importing this module imports the whole formalisation.  The files are grouped into
directories by section of the paper (`Sec2_…`, `Sec3_1_…`, …); the directories
`Ext1_…` and `Ext2_…` contain material that goes beyond the paper (a repaired
call-by-name semantics and a store-based semantics for mutable arrays).  Large files are
split into a directory of smaller files plus a file of the same name that imports them
all (for example `Sec3_1_Calculus/Syntax.lean` and `Sec3_1_Calculus/Syntax/`).  The
disproofs of the metatheorems of §3.5 are in `Sec3_5_Metatheory/Counterexamples/`.

See `READING_GUIDE-linearity-and-uniqueness.md` at the root of the project for a suggested
reading order.
-/
