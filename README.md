# Formalisations of two papers on linearity, uniqueness and ownership

This Lean 4 / Mathlib project formalises two papers:

1. *Linearity and Uniqueness: An Entente Cordiale* (the LCU calculus), in
   `RequestProject/LCU/`, namespace `LCU`. Reading guide:
   `READING_GUIDE-linearity-and-uniqueness.md`.
2. *Functional Ownership through Fractional Uniqueness* (Marshall and Orchard, the paper in
   `paper.typ`), in `RequestProject/FOFU/`, namespace `FOFU`. Reading guide:
   `READING_GUIDE-functional-ownership-through-fractional-uniqueness.md`.

`RequestProject/LCU.lean` and `RequestProject/FOFU.lean` import the respective
developments. The whole project builds with no `sorry`, and the only axioms used are the
standard `propext`, `Classical.choice` and `Quot.sound`.

Both formalisations follow the design of `PROPOSAL.md` (with the review decisions: a
custom variable type `Var n`, a generic binding layer, and `Lean.JsonNumber` for float
literals).

## Shared infrastructure (`RequestProject/Common/`)

* `Common/Var.lean`: de Bruijn variables. `Var n` is an inductive family with
  constructors `Var.zero : Var (n + 1)` and `Var.succ : Var n → Var (n + 1)`, so `cases`
  and dependent pattern matching work on indices of the form `.succ i`. Renamings are
  functions `Var n → Var m`, lifted under binders by `Ren.up` / `Ren.upN`, and
  `Var.shiftN k` weakens by `k` new names.
* `Common/Ctx.lean`: length-indexed snoc lists `Ctx α n` (`Ctx.nil`, `Γ ,, a`). Typing
  contexts, heaps and stores of both papers are built from them. Lookups are the
  inductive judgment `Ctx.Lookup Γ i a` (*here* / *there*); `Ctx.Pick P Γ i a` says that
  `i` carries `a` and every other entry satisfies `P` (this is the paper's
  "`0 · Γ, x : A`"); `Ctx.All`, `Ctx.Forall₂` and `Ctx.Forall₃` are pointwise predicates
  and relations defined by recursion on the lists, and context addition and scaling are
  instances of them. The files are in `Common/Ctx/` (`Basic`, `Pointwise`, `Algebra`,
  `Ren`, `Combine`); `Common/Ctx.lean` imports them all.
* `Common/Syntax.lean`: a generic binding layer. A signature lists the operators of a
  language with the binding arities of their arguments, and `Binding.Tm S n` is the type
  of terms with `n` free variables. Renaming, parallel substitution, single and double
  instantiation, operator maps (`Tm.mapOp`, used to rename runtime names stored in
  operators), free occurrences (`Tm.Occurs`) and operator occurrences (`Tm.HasOp`) are
  defined once, with their laws proved once. The files are in `Common/Syntax/` (`Basic`,
  `RenSubst`, `MapOp`, `Occurs`, `HasOp`); `Common/Syntax.lean` imports them all.
* `Common/Grades/PreorderedSemiring.lean`: the class of pre-ordered semirings of grades,
  with the instance for `ℕ`. The `{0, 1, ω}` semiring of the first paper is an instance,
  and the second paper's calculus is parameterised by it.

Terms of both papers are instances of the binding layer and are indexed by the number of
free variables and the number of runtime names in scope: LCU's `Term n ρ` and FOFU's
`Term R n ρ` have variables `Term.var : Var n → _` and runtime references
`Term.ref : Var ρ → _`, so `Term R 0 0` is the type of closed source terms. Float
literals are `Lean.JsonNumber` (`FloatLit`).

## Correct by construction

* **Scoped configurations.** A heap has exactly one entry per variable and runtime name
  in scope, and a configuration is a heap together with a term over the same scope, so
  "the free variables and references of the term are in the heap" holds by
  construction. A reduction step records how many variables (`d`), references (`e`) and,
  for FOFU, identifiers (`f`) it adds; new names are always `Var.zero` and old ones are
  weakened, so no freshness premise is needed and the heap only grows by construction.
* **Premises are structural judgments.** Side conditions such as "`x : a ∈ Γ`",
  "`ref ↦_p id ∈ H`" or "`0 · Γ, x : A`" are the inductive judgments `Ctx.Lookup` and
  `Ctx.Pick`, not equations between `Option`s; context addition and scaling are the
  pointwise relations `Ctx.Forall₃` and `Ctx.Forall₂`. Equational characterisations
  (`Ctx.lookup_iff`, `Ctx.pick_iff`, `Ctx.forall₃_iff`, …) are theorems.
* **Meaningful data only.** FOFU heap permissions are fractions `0 < p ≤ 1` (`Frac`), so
  a heap cannot store a meaningless permission, and LCU heap entries carry the typing
  derivation of the stored term.

## *Functional Ownership through Fractional Uniqueness*

The directories of `RequestProject/FOFU/` follow the sections of the paper:
`Sec3_CoreCalculus/`, `Sec4_Uniqueness/`, `Sec5_Fractional/` (§5, including the
equational theory of §5.1 and the partial-views example of §5.2),
`Sec6_1_Preliminaries/`, `Sec6_2_Reduction/` and `Sec6_3_Theorems/`. In
`Sec6_3_Theorems/`, the proof of the substitution lemmas is in `SubstitutionLemmas/` and
the disproofs of the theorems are in `Counterexamples/`. The reading guide maps every item of the paper to its Lean name and
lists the formalisation choices.

* **Calculus.** Types `Ty R k` (with `k` de Bruijn identifiers in scope), terms
  `Term R n ρ`, contexts `TCtx R k n ρ` with partial addition and scaling, and the typing
  rules of all sections (`HasType`), over an arbitrary pre-ordered semiring of grades.
  Values, scoped heaps `Heap R n ρ ι` (variables, references and identifiers), the
  reduction relation of §6.2 (`Step`, `Steps`), heap compatibility (Definition 6.4,
  `Compat`) and the equational theory (`Equiv`).
* **Examples.** The example derivation of §3 (`exampleNat_typing`), `exampleMove`,
  `exampleShare`, `exampleBorrow`, `exampleReborrow`, `exampleArray`, `exampleClone`,
  `exampleReference`, `examplePartial` (all with `ℕ` grades), and Example 6.5
  (`example_6_5`).
* **`exampleGraded`** does not type-check with the printed `readRef` interface
  (`not_primTy_readRef_graded`). It is typed (`exampleGraded_typing`,
  `Sec5_Fractional/ExampleGraded.lean`) using an added primitive that is not in the paper,
  `readRefSplit : *(Ref_id (□_(q+r) A)) ⊸ □_q A ⊗ *(Ref_id (□_r A))`, with reduction rule
  `Step.readRefSplit`. The printed `readRef` is unchanged. Because the primitive is part of
  the calculus, the §6.3 statements below range over terms that may use it too. None of
  the counterexamples uses it, and the positive results still hold.
* **Lemmas 6.2 and 6.3 (substitution) are proved**: `HasType.subst_lin` and
  `HasType.subst_grd`. The proof uses a dereliction-free version of the typing judgment
  (`hasType_iff_hasTypeD`), the algebra of contexts, renaming of identifiers, renaming,
  weakening by zero-graded assumptions and approximation of whole contexts.
* **Theorems 6.6–6.11** are stated literally (`Statements.lean`) for two variants of
  Definition 6.4: as printed, and with a garbage-collection rule for resource entries
  (as printed, no heap with a resource entry is compatible with any context,
  `Compat.ress_eq_none`). Progress (`not_progress`), preservation
  (`not_preservation_literal`, `not_preservation_gc`) and soundness with respect to `≡`
  (`not_eqSoundness`) are false for both variants. Borrow safety, multi-reduction borrow
  safety and uniqueness are false for the repaired variant (`not_borrowSafety_gc`,
  `not_multiBorrowSafety_gc`, `not_uniqueness_gc`). For the printed variant, borrow
  safety holds (`borrowSafety_literal`), multi-reduction borrow safety is false
  (`not_multiBorrowSafety_literal`), and uniqueness holds vacuously
  (`uniqueness_literal`). These results concern the rules as printed in the provided
  text, not necessarily the full rule set in the paper's appendices.
* **Scoping in the statements.** Since configurations are scoped, the statements move the
  result type and the frame `Γ₀` into the scope after the step (`Ty.ren (Var.shiftN f)`,
  `TCtx.lift`), and follow old references and identifiers through a reduction sequence
  with the maps recorded by `Steps`. Heap compatibility has one structural rule that the
  paper does not need, `freshId` (`H ⋈ Γ ⟹ H, id ⋈ Γ, id`), which adds an identifier
  without resource entry.

## *Linearity and Uniqueness: An Entente Cordiale*

This part formalises the first paper of the project (its source was the earlier
`paper.typ`; that file now contains the second paper). All files live in
`RequestProject/LCU/` under the namespace `LCU`.

### Representation

Terms use de Bruijn variables and are intrinsically scoped: `Term n ρ` is the type of
terms with `n` free variables and `ρ` runtime array references, `Term.var : Var n → Term n ρ`,
and `Term 0 0` is the type of closed source terms. Binders bind `Var.zero`. In
`letPair t₁ t₂` (`let (x, y) = t₁ in t₂`), `y` is `Var.zero` and `x` is
`Var.succ Var.zero`. A context `TCtx n ρ` gives each variable and each runtime array
reference an optional linear hypothesis `x : A` or non-linear hypothesis `x : [A]`.
Context addition (Definition 2, `TCtx.Add`) and `[Γ]` (Definition 1, `TCtx.AllNonLin`)
are pointwise relations on the length-indexed lists.

### Grammars by construction

Every grammar of the paper is an inductive type (or a structure) whose inhabitants are
exactly the objects the grammar describes. Where a sub-grammar is used as a condition on
terms, the predicate only says that the term is the image of an element of that type.

| Grammar | Lean type | Notes |
| --- | --- | --- |
| core types `A ::= A ⊸ B \| A ⊗ B \| 1 \| !A \| *A` (§3.1) | `CoreTy` | embeds into the extended types `Ty` (`CoreTy.toTy`, injective) |
| core terms (§3.1) | `CoreTerm n` | embeds into the extended terms `Term n ρ` (`CoreTerm.toTerm`, injective); `cbn_eval_core` states evaluation for them |
| values `v ::= (t₁, t₂) \| unit \| *t \| !t \| λx. t \| i \| a \| p` (Theorem 6) | `Value n ρ` | `IsValue t := ∃ v : Value n ρ, v.toTerm = t` |
| partially applied primitives `p` | `PrimFun n ρ` | a primitive applied to fewer arguments than its arity, each argument being a `Value`; `IsPrimFun` |
| usage `r ::= 1 \| ω` | `Usage` | a `PartialOrder` with `1 ≤ ω` (decidable) |
| heaps `H ::= ∅ \| H, x ↦ᵣ (Γ ⊢ t : A) \| H, a ↦ᵣ arr` | `Heap n ρ`, `VarEntry n ρ` | each entry contains a proof of its judgment `Γ ⊢ t : A`; one optional entry per variable and array reference in scope |
| arrays `arr` | `ArrObj := List Float` | finite arrays, no holes |
| stores of the array semantics | `Store ρ` | one optional array per reference in scope |
| values of the array semantics | `StoreValue n ρ`, `ReadyPrim n ρ` | embed into `Value n ρ` and `PrimFun n ρ`; `AValue`, `PrimReady` |

Because a heap entry carries its typing derivation, a step rule can only add derivable
judgments to the heap. For `copy_β` this means the rule requires `Γ ⊢ *θ(v) : *A`, in a
context that refers to the fresh copies `θ a`. The text writes this judgment in the new
heap entry but only assumes `Γ ⊢ v : A`, which does not imply it in general.

### Files

The files are grouped into directories by section of the paper;
`READING_GUIDE-linearity-and-uniqueness.md` explains the layout, maps every numbered definition, lemma and theorem of the paper to
its Lean name, and suggests reading orders. `RequestProject/LCU.lean` imports everything.

Large files are split into a directory of smaller files, next to a file of the same name
that imports them all. For example, `Sec3_1_Calculus/Syntax.lean` imports
`Sec3_1_Calculus/Syntax/Types.lean`, `Terms.lean`, `Eliminators.lean` and `Core.lean`.
The same layout is used in `RequestProject/Common/` and `RequestProject/FOFU/`.

| Directory (under `RequestProject/LCU/`) | Files | Contents |
| --- | --- | --- |
| `Sec2_KeyIdeas/` | `KeyIdeas.lean` | the examples of Section 2 (impossible/possible cake and coffee programs, `sip`, dereliction, borrowing, `uniqueReturn`/`uniqueBind`) |
| `Sec3_1_Calculus/` | `Syntax.lean` (`Syntax/`), `RenameSubst.lean`, `RefRenaming.lean` | types `Ty`, primitives, terms `Term n ρ`, the core grammars `CoreTy` and `CoreTerm n`; renaming and substitution of variables and of array references |
| | `Context.lean`, `CtxAlgebra.lean` | contexts, context addition and its algebra |
| | `Typing.lean` | the typing judgment `HasType` (Figure 1 plus the array primitives of §3.3) |
| | `TypingD.lean` | an equivalent system with no separate dereliction rule (`hasType_iff_hasTypeD`) |
| | `Weakening.lean` | **Lemma 3** (weakening) `HasType.weaken`, plus renaming/shifting |
| | `Substitution.lean` | **Lemma 1** `HasType.subst_lin`, **Lemma 2** `HasType.subst_nonlin` |
| | `Values.lean` | the value grammar `Value n ρ` and partially applied primitives `PrimFun n ρ`, with an induction principle `IsValue.induction` |
| | `FreeVars.lean` | free variables; linear variables must occur; strengthening |
| `Sec3_2_Equational/` | `Equational.lean`, `EqAxiomTyping.lean` | the equational theory `≡ₗ` (§3.2); every axiom preserves typing (`EqAxiom.preserves`) |
| `Sec3_4_HeapModel/` | `Heap.lean` | the heap model (§3.4): usage and binding contexts, heaps |
| | `Step.lean` | single-step reduction `Step`, multi-step `Steps`, full β-reduction `FullStep` |
| | `Compat.lean` | heap-context compatibility `Compat` (**Definition 3**) |
| `Sec3_5_Metatheory/` | `Metatheory.lean` | **Theorems 4–7** stated literally as propositions `Conservation`, `Uniqueness`, `Progress`, `EqSoundness` |
| | `Counterexamples/*.lean` | formal disproofs of these four statements (see below) |
| `Sec4_Implementation/` | `Granule.lean` | the `{0, 1, ω}` semiring of §4.1: a commutative semiring and partial order with monotone `+` and `*` |
| `Ext1_CallByName/` | `PrimFree.lean` | terms without array primitives |
| | `CbnSemantics.lean` | a repaired, substitution-based call-by-name reduction `CbnStep` with subject reduction, progress, type safety and determinism (see below) |
| | `CbnExamples.lean` | the progress and conservation counterexamples reduce to values under `CbnStep` |
| | `CbnNormalization.lean` | termination of `CbnStep` evaluation on well-typed closed terms (logical relation); `cbn_eval_core` for core terms |
| `Ext2_MutableArrays/` | `RefShift.lean` | renaming of array references (for `copy_β`) and weakening into larger non-linear contexts |
| | `ArraySemantics.lean` | a store-based semantics with mutable arrays: stores, `AStep`, well-typed configurations |
| | `ArrayPreservation.lean`, `ArrayProgress.lean` | subject reduction, progress and type safety for `AStep` |
| | `ArrayExamples.lean` | an example run: `readArray (writeArray (newArray 3) 0 x) 0` evaluates to `(x, *a)` |

### Reconstruction choices

The provided text leaves out a few rules: the runtime typing rule for array references
(found in the paper's appendix) and some heap-model rules. We reconstructed them as
follows. Array references are typed by `[Γ], a : Array A ⊢ a : Array A`, and `nec`
passes the array references of its conclusion to its premise. For source programs (no
array references), the typing rules are exactly the paper's. The heap-model rules we
reconstructed are documented in the docstring of `Sec3_4_HeapModel/Step.lean`.

### Results on Theorems 4–7

Read literally against the rules in the text, all four metatheorems are **false**. We proved
each negation in Lean:

* **Theorem 4 (Conservation)**, `not_conservation`: in the empty heap,
  `copy !((λz.z) unit) as x in &x : !1` steps to `z ↦₁ unit ⊢ copy !z as x in &x`.
  The heap forces `z` to be linear, but the reduct can only be typed if `z` is non-linear.
* **Theorem 5 (Uniqueness)**, `not_uniqueness`: the term
  `let! z = (copy !(newArray 1) as x in &x) in z` reduces to `*a`, where `a` is a fresh
  array bound with grade `ω` rather than `1`.
* **Theorem 6 (Progress)**, `not_progress`: `&(*((λz.z) unit)) : !1` is not a value and
  is stuck. No rule reduces under `*`, and `&β` needs `*v` with `v` a value.
* **Theorem 7 (Equational soundness)**, `not_eqSoundness`: in the η! instance
  `let! x = !unit in !x ≡ !unit`, the right side is irreducible in the empty heap. The
  left side must allocate a heap binding and so can never reach the same final heap.

These counterexamples point to gaps or imprecision in the rules as written in the
provided text. They do not necessarily apply to the full rule set in the paper's appendix.

### A repaired call-by-name semantics with type safety

`CbnSemantics.lean` gives a substitution-based call-by-name reduction `CbnStep`. It
follows the heap rules, but substitutes instead of allocating heap bindings:
`(λx.t) u ⟶ [u/x]t`, `let (x,y) = (t₁,t₂) in t ⟶ [t₁/x,t₂/y]t`, `let unit = unit in t ⟶ t`,
`let! x = !u in t ⟶ [u/x]t`, `&(*t) ⟶ !t` (for any `t`, not only values) and
`copy !u as x in t ⟶ [*u/x]t`, plus congruence rules for the eliminated position of
each elimination form. For terms with no free variables, in contexts whose runtime
array references are non-linear (for example closed terms in the empty context), we prove:

* subject reduction: `CbnStep.preserves` and `CbnSteps.preserves`;
* progress for terms with no array primitives: `cbn_progress`;
* syntactic type safety for closed terms: `cbn_type_safety`;
* values are normal forms (`IsValue.not_cbnStep`), and the reduction is deterministic
  (`CbnStep.deterministic`).

The restriction to terms with no free variables is needed. `not_cbnStep_preserves_open`
shows that with `x : [1]`, the term `copy !x as y in &y : !1` steps to the untypable `&(*x)`.

### Termination of call-by-name evaluation

`CbnNormalization.lean` proves that `CbnStep` evaluation terminates. It uses a unary
logical relation `Reducible A t`, and the fundamental lemma `HasTypeD.reducible`.

* `cbn_normalization`: every well-typed closed term without array primitives reduces
  to a value;
* `cbn_eval`: the value has the same type (in a context whose array references are
  non-linear);
* `cbn_value_unique`: the value is unique.

### The examples of Section 2

`KeyIdeas.lean` checks the typing claims of the paper's Key Ideas section in LCU. The
types `Cake`, `Happy`, `Coffee` and `Awake` are arbitrary. The functions `eat`, `have`,
`drink` and `keep` are free non-linear variables.

* `not_hasType_lam_pair_dup`: `λx. (t₁, t₂)` is ill-typed whenever `x` occurs in both
  `t₁` and `t₂`. As instances, `impossible_cake` (`λc. (eat c, have c)`) and
  `impossible_coffee` (`λc. (drink c, keep c)`) are ill-typed at every type.
* `possible_cake`: `λlots. let! cake = lots in (eat cake, have cake) : !Cake ⊸ Happy ⊗ Cake`.
* `sip_hasType`: `λfresh. let! coffee = &fresh in (keep coffee, drink coffee) : *Coffee ⊸ Coffee ⊗ Awake`.
* `derelict_hasType` (`!A ⊸ A`), `uniqueReturn_hasType` (`*A ⊸ !A`),
  `unique_to_linear_hasType` (`*A ⊸ A`), `bang_contract_hasType` (`!A ⊸ !A ⊗ !A`),
  `bang_weaken_hasType` (`!A ⊸ 1`) and `uniqueBind_hasType` (`(*A ⊸ !B) ⊸ !A ⊸ !B`).

### Mutable arrays: a store-based semantics with type safety

`Ext2_MutableArrays/` extends the call-by-name semantics with a store of mutable float
arrays. The reduction `σ ⊢ t ⟶ σ' ⊢ t'` (`AStep`) uses these rules:

* `newArray k` allocates a fresh array;
* `readArray (*a) k` reads from the store;
* `writeArray (*a) k x` updates the store destructively;
* `copy !u as x in t ⟶ [*θ(u)/x]t` copies every array referenced by `u` to a fresh
  reference (all arrays of the store are duplicated, `Store.copyAll`), as in the paper's
  `copy_β`;
* arguments of primitives are evaluated, including under `*`.

Configurations are typed by a context `Γ` compatible with the store (`ConfOK`): no
variable assumptions, non-linear array references, and every typed reference allocated.
The results are:

* `AStep.preserves`: subject reduction. The context may grow, for example by fresh
  arrays.
* `astep_progress`: progress for all terms, including array primitives.
* `array_type_safety`: a well-typed closed program, run from the empty store, never
  gets stuck.
* `writeReadProg_hasType` and `writeReadProg_eval`: an example program is well-typed,
  and its read sees the preceding destructive write.

**Caveat.** In this semantics `deleteArray` does not free memory. Safe deallocation
needs the uniqueness guarantee (Theorem 5), and this semantics does not prove it.
