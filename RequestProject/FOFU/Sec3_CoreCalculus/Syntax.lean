module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Types
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Terms
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Eliminators
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Source

/-!
# Syntax of types and terms (Section 3, extended by Sections 4–6)

*Functional Ownership through Fractional Uniqueness* (Marshall, Orchard).

The paper extends the syntax of §3 step by step (§4 adds `share`/`clone` and `*A`, §5
adds borrowing, split/join, push/pull and resources, §6.1 adds runtime terms).  A Lean
inductive type cannot be extended afterwards, so the types `Ty` and terms `Term` below
contain all constructors at once; each constructor's docstring names the section it
comes from.  The source grammar (without the runtime forms of §6.1) is given separately
as `SrcTerm`, embedded into `Term` by the generic operator map.

## Conventions

* **Grades.**  Everything is parameterised by the type `R` of grades of the graded
  modality `□_r A`; the typing rules require `[Grades.PreorderedSemiring R]`.
* **Term variables** are intrinsically scoped de Bruijn indices `Var n`: `Term R n ρ` has
  `n` free variables (`Term.var : Var n → Term R n ρ`), so `Term R 0 ρ` is the type of
  closed terms.  Binders bind `Var.zero`.  In `letPair t₁ t₂` (`let (x, y) = t₁ in t₂`)
  the variable `y` is `Var.zero` and `x` is `Var.succ Var.zero`.
* **Terms are built with the generic binding layer** (`RequestProject/Common/Syntax.lean`):
  `Term R n ρ` is `Binding.Tm` over the signature `sig R ρ`, so renaming, substitution and
  their laws are inherited.  The constructors `Term.lam`, … are pattern synonyms, and
  `Term.rec'` / `Term.cases'` are the default `induction` / `cases` eliminators.
* **Runtime references are scoped** like variables: `ρ` is the number of runtime
  references in scope and `Term.ref : Var ρ → Term R n ρ`.  Source programs are terms
  with `ρ = 0`.
* **Identifiers** (type variables of kind `Name`) are de Bruijn indices `Var k`: `Ty R k`
  is the type of types with `k` identifiers in scope, and `∃ id. A` is `Ty.ex A` with
  `A : Ty R (k + 1)`.  At runtime, resources are named by *runtime identifiers*; these are
  simply the identifiers in scope (the heap of §6.1 has `ι` resources, and runtime types
  are `Ty R ι`).  There is no separate constructor for runtime identifiers.
* **Existentials are Curry-style.**  The identifier of `pack ⟨id, t⟩` and the
  identifier bound by `unpack ⟨id, x⟩ = t₁ in t₂` only appear in types: the terms are
  `pack t` and `unpack t₁ t₂`.  Terms never mention identifiers.
* **Grade annotations.**  Promotion is always annotated with its grade, `[t]_r`
  (`Term.box r t`), as in §6.1, and `share` carries the grade of the box it produces
  (`Term.share r t`).
* **Float literals** are `Lean.JsonNumber`s (`FloatLit`: a mantissa and a decimal
  exponent, with lawful decidable equality), not Lean's built-in `Float`.

## Files

* `Syntax/Types.lean`: float literals, types `Ty`, primitives `Prim`;
* `Syntax/Terms.lean`: operators, the signature, terms `Term` and their constructors;
* `Syntax/Eliminators.lean`: `Term.rec'`, `Term.cases'`, injectivity of the constructors;
* `Syntax/Source.lean`: source terms `SrcTerm` and their embedding into `Term`.
-/
