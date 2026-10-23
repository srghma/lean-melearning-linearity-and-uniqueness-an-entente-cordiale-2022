module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Types
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Terms
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Eliminators
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Core

/-!
# The Linear-Cartesian-Unique (LCU) calculus: syntax

Formalisation of Section 3 of *Linearity and Uniqueness: An Entente Cordiale*
(Marshall, Vollmer, Orchard).

## Representation

Terms are intrinsically scoped de Bruijn terms, built with the generic binding layer of
`RequestProject/Common/Syntax.lean`: the term language is described by a signature (its
operators and their binding arities), and `Term n ρ` is the generic `Binding.Tm` over that
signature.  Renaming, substitution and their laws come from the generic layer.

* `Term n ρ` has `n` free variables, `Term.var : Var n → Term n ρ`, so `Term 0 ρ` is the
  type of closed terms.  Binders bind `Var.zero`.
* Runtime array references `a` (Section 3.4) are scoped too: `ρ` is the number of runtime
  references in scope and `Term.ref : Var ρ → Term n ρ`.  Source programs have no
  references: they are terms of `Term n 0`.
* Float literals are `Lean.JsonNumber`s (a mantissa and a decimal exponent, with lawful
  decidable equality), not Lean's built-in `Float`.

The constructors `Term.lam`, `Term.app`, … are pattern synonyms (`@[match_pattern]`) for
the corresponding operator applications, and `Term.rec'` / `Term.cases'` are registered
as the default `induction` / `cases` eliminators, so that terms can be used as if `Term`
were an ordinary inductive type.

## Contents

* `Ty`, `Prim`, `Op`, `Term n ρ`: types, primitives, operators and terms;
* `CoreTy`, `CoreTerm n`: the core grammars of Section 3.1, as separate types embedded
  into `Ty` / `Term n ρ`.  `CoreTerm n` is the generic syntax over a sub-signature, and
  its embedding is the generic operator map `Binding.Tm.mapOp`.

## Files

* `Syntax/Types.lean`: float literals, types `Ty`, primitives `Prim`;
* `Syntax/Terms.lean`: operators, the signature, terms `Term` and their constructors;
* `Syntax/Eliminators.lean`: `Term.rec'`, `Term.cases'`, injectivity of the constructors;
* `Syntax/Core.lean`: the core grammars `CoreTy`, `CoreTerm` and their embeddings.
-/
