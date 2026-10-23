module
public import RequestProject.Common.Syntax.Basic
public import RequestProject.Common.Syntax.RenSubst
public import RequestProject.Common.Syntax.MapOp
public import RequestProject.Common.Syntax.Occurs
public import RequestProject.Common.Syntax.HasOp

/-!
# A generic binding layer: syntax over a signature

Both formalisations of this project use intrinsically scoped de Bruijn syntax.  Instead of
defining renaming and substitution (and proving their laws) once for every term language,
each language is described by a *signature* and the term type is the generic `Tm S n`.

* A signature `S : Sig` is a type of operators `S.Op` together with, for every operator,
  the list of *binding arities* of its arguments: `S.arity o = [k₁, …, kₘ]` means that
  `o` takes `m` arguments and that the `j`-th argument binds `kⱼ` new variables.  For
  instance `let (x, y) = t₁ in t₂` has arity `[0, 2]`.  Operators may carry data
  (grades, literals, primitives, …): these are simply part of `S.Op`.
* `Tm S n` is the type of terms with `n` free variables: a variable `var i` (`i : Var n`)
  or an operator applied to arguments `op o as`, where `as : Args S n (S.arity o)`.
  An argument with binding arity `k` is a term of `Tm S (n + k)`; its new variables are
  `Var.zero, …` (the last bound variable is `Var.zero`).

Generic operations, defined once for all signatures:

* `Tm.ren ρ` (renaming along `ρ : Var n → Var m`) and `Tm.subst σ` (parallel
  substitution along `σ : Var n → Tm S m`), lifted under binders by `Ren.upN` /
  `Subst.upN`;
* the single and double instantiations `t.inst1 s = [s/x]t` and
  `t.inst2 s₁ s₂ = [s₁/x, s₂/y]t`;
* `Tm.mapOp f`, applying an arity-preserving map `f` to every operator (used for example to
  rename runtime names stored in operators);
* `Tm.Occurs i t`, "the variable `i` occurs free in `t`".

Generic laws, proved once (the σ-calculus laws): `ren_id`, `ren_ren`, `subst_var`,
`ren_eq_subst`, `subst_ren`, `ren_subst`, `subst_subst`, and their consequences for
`inst1` / `inst2`, plus commutation of `mapOp` with renaming and substitution and the
behaviour of `Occurs` under renaming.

## Files

* `Syntax/Basic.lean`: signatures, terms, injectivity of the constructors;
* `Syntax/RenSubst.lean`: renaming, substitution, their laws, `inst1` / `inst2`;
* `Syntax/MapOp.lean`: mapping operators;
* `Syntax/Occurs.lean`: free occurrences of variables;
* `Syntax/HasOp.lean`: operators occurring in a term.
-/
