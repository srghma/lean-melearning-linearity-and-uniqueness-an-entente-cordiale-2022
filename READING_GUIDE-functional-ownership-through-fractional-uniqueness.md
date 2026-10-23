# Reading guide: *Functional Ownership through Fractional Uniqueness*

This guide explains how the Lean formalisation of *Functional Ownership through Fractional
Uniqueness* (Marshall and Orchard; the paper in `paper.typ`) is organised and suggests an
order for reading it. The first paper of the project, *Linearity and Uniqueness: An
Entente Cordiale*, has its own guide, `READING_GUIDE-linearity-and-uniqueness.md`.

All Lean files of this paper live in `RequestProject/FOFU/`, in the namespace `FOFU`.
`RequestProject/FOFU.lean` imports all of them. The development builds with no `sorry`,
and the only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Code shared with the first paper

The two papers do not share files. Code that both use lives in `RequestProject/Common/`,
and each place where the FOFU code reuses something says so in a comment:

| Shared file | Contents | Use in FOFU | Use in LCU |
| --- | --- | --- | --- |
| `Common/Var.lean` | de Bruijn variables `Var n` (constructors `zero`, `succ`), renamings `Ren.up`, `Ren.upN`, `Var.shiftN` | term variables, runtime references and identifiers | term variables and array references |
| `Common/Ctx.lean` (`Common/Ctx/`) | length-indexed snoc lists `Ctx α n`, the lookup judgment `Ctx.Lookup`, `Ctx.Pick`, and the pointwise relations `Ctx.All`, `Ctx.Forall₂`, `Ctx.Forall₃` | typing contexts, context addition and scaling, heaps | typing contexts, heaps, stores |
| `Common/Syntax.lean` (`Common/Syntax/`) | the generic binding layer: terms `Binding.Tm S n` over a signature `S`, renaming, substitution and their laws, `Tm.Occurs`, `Tm.HasOp` | `Term R n ρ` is `Tm (sig R ρ) n` | `Term n ρ` is `Tm (sig ρ) n` |
| `Common/Grades/PreorderedSemiring.lean` | the class `Grades.PreorderedSemiring R` (semiring, preorder, monotone `+` and `*`), with the instance for `ℕ` | the parameter `R` of the whole calculus (§3) | the `{0, 1, ω}` semiring of §4.1 is an instance |

Two proof techniques are also reused from the first paper (the code is separate because
the rule sets differ), as noted in the module docstrings: the dereliction-free typing
judgment (`Sec3_CoreCalculus/TypingD.lean`), and the structure of the general substitution
lemma (`Sec6_3_Theorems/SubstitutionLemmas/Substitution.lean`).

## Conventions you need first

* **Grades.** Everything is parameterised by a type `R` of grades with
  `[Grades.PreorderedSemiring R]`. The semiring need not be commutative. The paper's
  examples use the natural numbers (`ℕ`), and so do ours.
* **De Bruijn terms.** `Term R n ρ` is the type of terms with `n` free variables and `ρ`
  runtime references in scope, and `Term.var : Var n → Term R n ρ`. `Term R 0 0` is the
  type of closed source terms. A binder binds `Var.zero`. In `letPair t₁ t₂`
  (`let (x, y) = t₁ in t₂`), `y` is `Var.zero` and `x` is `Var.succ Var.zero`. Runtime
  references are scoped too: `Term.ref : Var ρ → Term R n ρ`. Terms are an instance of
  the generic binding layer (`Common/Syntax.lean`), so renaming and substitution and
  their laws come from there.
* **De Bruijn identifiers.** Identifiers (type variables of kind `Name`) are de Bruijn
  too. `Ty R k` is the type of types with `k` identifiers in scope, `Ty.res κ id A` has
  `id : Var k`, and `∃ id. A` is `Ty.ex A` with `A : Ty R (k + 1)`. Runtime identifiers of
  resources are identifiers in scope like any other (there is no separate kind of
  runtime identifier). `pack` and `unpack` are Curry-style: the identifiers only appear
  in types.
* **Float literals** are `Lean.JsonNumber` (exact decimal numbers, `FloatLit`).
* **Contexts.** `TCtx R k n ρ` gives every variable an optional assumption, linear
  (`Assm.lin A`, `x : A`) or graded (`Assm.grd A r`, `x : [A]_r`), and every runtime
  reference an optional `Res_id A` (`RefTy`). Both parts are length-indexed lists
  (`Ctx`). Context addition `Γ₁ + Γ₂ = Γ` and scaling `r · Γ = Γ'` are partial, so they
  are relations, `CtxAdd Γ₁ Γ₂ Γ` and `CtxScale r Γ Γ'`, built from the pointwise
  relations `Ctx.Forall₃` and `Ctx.Forall₂`. "`0 · Γ`" is the predicate `Γ.IsZero`, and
  "`0 · Γ, x : A`" (rule `var`) is the structural judgment
  `Γ.vars.Pick ZeroAssm i (some (.lin A))`.
* **Heaps and configurations are scoped.** A heap `Heap R n ρ ι` has exactly one entry
  for each of its `n` variables, `ρ` references (`none` once deallocated) and `ι`
  identifiers (`none` if the identifier has no resource). A configuration is a heap and a
  term `Term R n ρ`, so the free variables and references of the term are in the heap by
  construction. A step `Step H t s d e f H' t'` adds `d` variables, `e` references and
  `f` identifiers; new names are always `Var.zero` and old ones are weakened, so no
  freshness side conditions are needed.
* **One syntax for all sections.** The paper extends types and terms section by section.
  A Lean inductive type cannot be extended later, so `Ty` and `Term` contain all
  constructors at once, and `HasType` contains the typing rules of all sections. Each
  constructor's docstring names its section.
* **`let x = t₁ in t₂`** (used in the Granule examples) is read as `(λx. t₂) t₁`.

## Directory layout

The directory names follow the sections of the paper. Large files are split into a
directory of smaller files, next to a file of the same name that imports them all: for
example `Sec3_CoreCalculus/Syntax.lean` imports `Sec3_CoreCalculus/Syntax/Types.lean`,
`Terms.lean`, `Eliminators.lean` and `Source.lean`. The same holds for
`Sec3_CoreCalculus/CtxAlgebra.lean` (`Add`, `Scale`, `Approx`) and
`Sec3_CoreCalculus/TypingD.lean` (`Basic`, `Equiv`).

| Directory | Paper | Contents |
| --- | --- | --- |
| `Sec3_CoreCalculus/` | §3 Core calculus | syntax, identifier substitution, renaming and substitution of terms, contexts and their algebra, the typing rules, the dereliction-free judgment, the example derivation |
| `Sec4_Uniqueness/` | §4 Uniqueness and sharing | `exampleMove`, `exampleShare` |
| `Sec5_Fractional/` | §5 Fractional uniqueness, §5.1, §5.2 | permissions, resource interfaces, `copyable`/`cloneable`, `resourceAllocator`, the examples of §5, the equational theory `≡` of §5.1 (and the axioms of §4) (`Equational.lean`), `examplePartial` of §5.2 (`Distributive.lean`) |
| `Sec6_1_Preliminaries/` | §6.1 | values, heaps, the references of a typed term |
| `Sec6_2_Reduction/` | §6.2 | single-step and multi-step reduction |
| `Sec6_3_Theorems/` | §6.3 | heap compatibility, Example 6.5, Theorems 6.6–6.11 as stated |
| `Sec6_3_Theorems/SubstitutionLemmas/` | §6.3 | Lemmas 6.2 and 6.3 and the lemmas they need |
| `Sec6_3_Theorems/Counterexamples/` | §6.3 | the counterexamples to Theorems 6.6–6.11 |

The permissions of §5 (`Permission.lean`) are imported by `Sec3_CoreCalculus/Syntax.lean`,
because the single type of types contains the borrowing modality.

## Where to find the items of the paper

| Paper | Lean | File (under `RequestProject/FOFU/`) |
| --- | --- | --- |
| Types and terms (§3–§6.1) | `Ty`, `Term`, `Prim`, `FloatLit` | `Sec3_CoreCalculus/Syntax.lean` |
| `A [ι / id]`, weakening by an identifier | `Ty.inst`, `Ty.shift`, `Ty.ren` | `Sec3_CoreCalculus/TypeSubst.lean` |
| `t [t' / x]`, renaming of references | `Term.subst1`, `Term.subst`, `Term.rename`, `renameRefs`, `Term.refs` | `Sec3_CoreCalculus/RenameSubst.lean` |
| Contexts, `Γ₁ + Γ₂`, `r · Γ`, `0 · Γ` | `TCtx`, `CtxAdd`, `CtxScale`, `TCtx.IsZero` | `Sec3_CoreCalculus/Context.lean` |
| Algebra of contexts | `CtxAdd.assoc`, `CtxAdd.interchange`, `CtxScale.add_scale`, `CtxLe` | `Sec3_CoreCalculus/CtxAlgebra.lean` |
| Typing rules (all sections) | `HasType` | `Sec3_CoreCalculus/Typing.lean` |
| Rule `(var')` | `HasType.var'` | `Sec3_CoreCalculus/TypingLemmas.lean` |
| Dereliction-free judgment | `HasTypeD`, `hasType_iff_hasTypeD`, `HasType.approxCtx` | `Sec3_CoreCalculus/TypingD.lean` |
| Example derivation of §3 (`exampleNat`) | `exampleNat_typing` | `Sec3_CoreCalculus/Example.lean` |
| `exampleMove`, `exampleShare` (§4) | `exampleMove_typing`, `exampleShare_typing` | `Sec4_Uniqueness/Examples.lean` |
| Permissions `p ::= * \| f` (§5) | `Frac`, `Perm` | `Sec5_Fractional/Permission.lean` |
| Resource interfaces, `copyable`, `cloneable`, `resourceAllocator` | `PrimTy`, `Ty.copyable`, `Ty.cloneable`, `Term.Allocates` | `Sec5_Fractional/Resources.lean` |
| `exampleBorrow`, `exampleReborrow`, `exampleArray`, `exampleClone`, `exampleReference` | `…_typing` | `Sec5_Fractional/Examples.lean` |
| Equational theory (§4, §5.1) | `EqAxiom`, `Equiv` (`≡`) | `Sec5_Fractional/Equational.lean` |
| `examplePartial` (§5.2) | `examplePartial_typing` | `Sec5_Fractional/Distributive.lean` |
| Values (§6.1) | `IsValue`, `PrimSpine` | `Sec6_1_Preliminaries/Values.lean` |
| Heaps (§6.1) | `Heap`, `ArrVal`, `ResVal`, `ArrVal.Reads` | `Sec6_1_Preliminaries/Heap.lean` |
| Reduction (§6.2) | `Step`, `Steps`, `CopyHeap` | `Sec6_2_Reduction/Step.lean` |
| Definition 6.4 (heap compatibility) | `Compat gc` | `Sec6_3_Theorems/Compat.lean` |
| Example 6.5 | `example_6_5` | `Sec6_3_Theorems/Compat.lean` |
| **Lemma 6.2** (linear substitution) | `HasType.subst_lin` | `Sec6_3_Theorems/SubstitutionLemmas/Substitution.lean` |
| **Lemma 6.3** (graded substitution) | `HasType.subst_grd` | `Sec6_3_Theorems/SubstitutionLemmas/Substitution.lean` |
| Theorems 6.6–6.11 as stated | `Progress`, `Preservation`, `BorrowSafety`, `MultiBorrowSafety`, `Uniqueness`, `EqSoundness` | `Sec6_3_Theorems/Statements.lean` |
| Counterexamples | `not_progress`, `not_preservation_literal`, `not_preservation_gc`, `not_borrowSafety_gc`, `not_multiBorrowSafety_gc`, `not_multiBorrowSafety_literal`, `not_uniqueness_gc`, `not_eqSoundness` | `Sec6_3_Theorems/Counterexamples/*.lean` |
| Lemma 6.8 for the printed Definition 6.4 | `borrowSafety_literal`, `Step.new_ident` | `Sec6_3_Theorems/BorrowSafetyLiteral.lean` |

## Results on the theorems of §6.3

**Lemmas 6.2 and 6.3 are proved.** `HasType.subst_lin`: if `Γ₁ ⊢ t₁ : A` and
`Γ₂, x : A ⊢ t₂ : B`, then `Γ ⊢ t₂[t₁/x] : B` for every `Γ` with `Γ₂ + Γ₁ = Γ`.
`HasType.subst_grd`: if `Γ₁ ⊢ t₁ : A`, `Γ₂, x : [A]_r ⊢ t₂ : B`, `¬ resourceAllocator(t₁)`,
`r · Γ₁ = Γ₁ʳ` and `Γ₂ + Γ₁ʳ = Γ`, then `Γ ⊢ t₂[t₁/x] : B`. The paper's hypothesis that
`Γ₁` has only graded assumptions follows from `r · Γ₁` being defined. The proof uses
these lemmas, all in `Sec6_3_Theorems/SubstitutionLemmas/`:

* `HasTypeD.renNames` and `HasTypeD.shiftNames` (`NameSubst.lean`): renaming of
  identifiers, needed for `unpack`;
* `HasTypeD.rename` and `HasTypeD.shift` (`Renaming.lean`): renaming and weakening by an
  absent variable;
* `HasTypeD.weakenZero` (`ZeroWeakening.lean`): weakening by zero-graded assumptions;
* `HasTypeD.occurs` and `Term.allocates_subst` (`Occurs.lean`): needed for the side
  condition of promotion;
* `SubstSetup`, `TCtx.remove` and `SubstHyp` (`SubstSetup.lean`): the data of a
  substitution and the side condition on the substituted term;
* `HasTypeD.subst_gen` (`Substitution.lean`): the general lemma, substituting for any
  variable whose assumption may be absent, linear or graded.

**Theorems 6.6–6.11.** Definition 6.4 is formalised in two variants: `gc = false` is the
definition as printed, and `gc = true` adds a garbage-collection rule `gcRes` for
resource entries. The rule is needed because, as printed, no heap that contains a
resource entry `id ↦ v_r` is compatible with any context (`Compat.ress_eq_none`). Both
variants also have a structural rule `freshId` (`H ⋈ Γ ⟹ H, id ⋈ Γ, id`) that adds an
identifier without resource entry; it only reflects that identifiers are scoped in the
formalisation, and it adds no resource entries.

The statements are over scoped configurations: after a step, the type and the frame
`Γ₀` are moved into the larger scope (`Ty.ren (Var.shiftN f)`, `TCtx.lift`), an old
identifier `id` is called `Var.shiftN f id`, and after a reduction sequence (`Steps`)
the old references and identifiers are tracked by the maps `θr`, `θi` recorded by
`Steps`.

| Paper | `gc = false` (as printed) | `gc = true` (with `gcRes`) |
| --- | --- | --- |
| Theorem 6.6 (Progress) | false: `not_progress` | false: `not_progress` |
| Theorem 6.7 (Preservation) | false: `not_preservation_literal` | false: `not_preservation_gc` |
| Lemma 6.8 (Borrow safety) | true: `borrowSafety_literal` | false: `not_borrowSafety_gc` |
| Theorem 6.9 (Multi-reduction borrow safety) | false: `not_multiBorrowSafety_literal` | false: `not_multiBorrowSafety_gc` |
| Corollary 6.10 (Uniqueness) | true, vacuously: `uniqueness_literal` | false: `not_uniqueness_gc` |
| Theorem 6.11 (Soundness w.r.t. `≡`) | false: `not_eqSoundness` | false: `not_eqSoundness` |

The counterexamples (details in the docstrings of the files in `Sec6_3_Theorems/Counterexamples/`):

* **Progress, Soundness:** `split (*())` is well typed (`nec` gives `*()` every
  permission, and `split` does not require a resource type), is not a value, and
  cannot reduce.
* **Preservation (printed):** `newArray 3` steps to a heap with a resource entry, which
  is compatible with no context.
* **Preservation (repaired):** `(λz. (z, *ref₀)) (split (*ref₀))`: `split` removes
  `ref₀` from the heap, but the function still mentions it.
* **Borrow safety:** `clone [ref₀]₁ as x in x` creates a new identifier whose
  reference only occurs in the heap, so its permissions in the term sum to `0`.
* **Multi-reduction borrow safety (repaired):** `split (*ref₀)` ends with two references
  of permission `1/2` and none of permission `1`.
* **Multi-reduction borrow safety (printed):** starting from the empty heap,
  `(unpack ⟨id, x⟩ = newArray 3 in withBorrow (λb. unpack ⟨id', c⟩ = newRef (split b) in
  let [d] = share₀ c in *()) x, newArray 3)` creates an array, splits the borrow into two
  halves, stores them in a new reference cell and discards the cell with `share₀`. The
  value is `(*(), pack ⟨id, *ref⟩)` for the second array, and the first array's
  identifier has two references of permission `1/2` and none of permission `1`.
* **Uniqueness:** after `split` and `join` the original reference `ref₀` has been
  replaced by a new one.

**Lemma 6.8 with the printed rules** holds (`borrowSafety_literal`). The part about
identifiers of the initial heap is vacuous. For the part about new identifiers,
`Step.new_ident` shows that if the heap has no resource entries, every identifier
created by a step has exactly one reference, with permission `1`, and that reference
occurs in the reduced term. The proof does not use typing.

These results concern the rules as printed in the provided text. They do not
necessarily apply to the full rule set in the paper's appendices.

## Formalisation choices and reconstructed rules

The docstrings of `Typing.lean`, `Step.lean` and `Compat.lean` list every choice. The
main ones are:

* `pr` follows the restatement of §6.1, `r · Γ ⊢ [t]_r : □_r A` from `Γ ⊢ t : A`.
* `approx` goes from `x : [A]_r` to `x : [A]_s` when `r ⊑ s`. The printed side condition
  `s ⊑ r` contradicts the order used everywhere else in the paper.
* `withBorrow` takes the function first, as in the reduction rule, the equations and the
  examples. The printed typing rule takes it second.
* `clone` binds `x : ∃ id. *A'`, as in the reduction rule and in `exampleClone`.
* `nec` gives the runtime context `γ` the references of the conclusion.
* Literals, the reference primitives and the congruence rules that the paper omits are
  reconstructed. `share` leaves the heap unchanged, because `[H]_0` is not defined.
* Resource values are typed by `ResValTy`, because the paper does not define
  `γ ⊢ v_r : Res_id A`.

## Notes on the examples

* `exampleShare` shares at grade `2` instead of the interval `[0..2]`, since the examples
  use `ℕ`.
* Functions that the paper only declares (`observe`, `alter`) are linear variables of
  the context.
* `exampleGraded` reads a `Float [4]` out of a reference that holds a `Float [6]`, and
  afterwards uses the reference at type `Ref id (Float [2])`. The printed interface of
  `readRef` returns the unboxed contents and keeps the type of the reference unchanged,
  so the example does not type-check against it (`not_primTy_readRef_graded`). It is
  formalised in `Sec5_Fractional/ExampleGraded.lean` (`exampleGraded_typing`) with an
  added primitive that is **not in the paper**,
  `readRefSplit : *(Ref_id (□_(q+r) A)) ⊸ □_q A ⊗ *(Ref_id (□_r A))`, with reduction
  `Step.readRefSplit` (the stored `[v]_(q+r)` becomes `[v]_r` and `[v]_q` is returned).
  The printed `readRef` is kept unchanged.
* `exampleConcurrent`, `exampleDeriving` and the parallel-sum example use Granule
  features (`par`, `Maybe`/`Either`, length-indexed vectors) that are outside the
  calculus, so they are not formalised.

## Suggested reading order

1. `Common/Var.lean`, `Common/Ctx.lean`, `Common/Syntax.lean`: variables, contexts and
   the generic binding layer; then `Sec3_CoreCalculus/Syntax.lean`, `Context.lean`,
   `Typing.lean`: the calculus.
2. `Sec3_CoreCalculus/Example.lean` and the examples of §4, §5 and §5.2: concrete
   derivations, built with the tactics `ctx_add`, `zero_ctx` and `pick_var` of
   `TypingLemmas.lean`.
3. `Sec6_1_Preliminaries/`, `Sec6_2_Reduction/Step.lean`, `Sec6_3_Theorems/Compat.lean`:
   the semantics and heap compatibility.
4. `Sec6_3_Theorems/Statements.lean`, then the files of `Sec6_3_Theorems/Counterexamples/`.
5. `Sec6_3_Theorems/SubstitutionLemmas/Substitution.lean` for Lemmas 6.2 and 6.3, going back to
   `Sec3_CoreCalculus/CtxAlgebra.lean`, `TypingD.lean` and the other files of
   `Sec6_3_Theorems/SubstitutionLemmas/` for the lemmas they use.
