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
| `Common/DeBruijn.lean` | `DeBruijn.Ren.up` (lifting a renaming of variables under a binder) and its laws | renaming of terms (`Sec3_CoreCalculus/RenameSubst.lean`), the renaming lemma (`Sec6_3_Theorems/Renaming.lean`), the substitution lemmas | renaming and weakening |
| `Common/Grades/PreorderedSemiring.lean` | the class `Grades.PreorderedSemiring R` (semiring, preorder, monotone `+` and `*`), with the instance for `ℕ` | the parameter `R` of the whole calculus (§3) | the `{0, 1, ω}` semiring of §4.1 is an instance |

Two proof techniques are also reused from the first paper (the code is separate because
the rule sets differ), as noted in the module docstrings: the dereliction-free typing
judgment (`TypingD.lean`), and the structure of the general substitution lemma
(`Substitution.lean`).

## Conventions you need first

* **Grades.** Everything is parameterised by a type `R` of grades with
  `[Grades.PreorderedSemiring R]`. The semiring need not be commutative. The paper's
  examples use the natural numbers (`ℕ`), and so do ours.
* **De Bruijn terms.** `Term R n` is the type of terms with `n` free variables, and
  `Term.var : Fin n → Term R n`. `Term R 0` is the type of closed terms. A binder binds
  index `0`. In `letPair t₁ t₂` (`let (x, y) = t₁ in t₂`), `y` is index `0` and `x` is
  index `1`.
* **De Bruijn identifiers.** Identifiers (type variables of kind `Name`) are de Bruijn
  too. `Ty R k` is the type of types with `k` bound identifiers, and `∃ id. A` is
  `Ty.ex A` with `A : Ty R (k + 1)`. Runtime identifiers of resources are `Ident.rt a`.
  `pack` and `unpack` are Curry-style: the identifiers only appear in types.
* **Contexts.** `Ctx R k n` gives every variable an optional assumption, linear
  (`Assm.lin A`, `x : A`) or graded (`Assm.grd A r`, `x : [A]_r`), and every runtime
  reference an optional `Res_id A`. Context addition `Γ₁ + Γ₂ = Γ` and scaling
  `r · Γ = Γ'` are partial, so they are relations, `CtxAdd Γ₁ Γ₂ Γ` and
  `CtxScale r Γ Γ'`. "`0 · Γ`" is the predicate `Γ.IsZero`.
* **One syntax for all sections.** The paper extends types and terms section by section.
  A Lean inductive type cannot be extended later, so `Ty` and `Term` contain all
  constructors at once, and `HasType` contains the typing rules of all sections. Each
  constructor's docstring names its section.
* **`let x = t₁ in t₂`** (used in the Granule examples) is read as `(λx. t₂) t₁`.

## Directory layout

The directory names follow the sections of the paper.

| Directory | Paper | Contents |
| --- | --- | --- |
| `Sec3_CoreCalculus/` | §3 Core calculus | syntax, identifier substitution, renaming and substitution of terms, contexts and their algebra, the typing rules, the dereliction-free judgment, the example derivation |
| `Sec4_Uniqueness/` | §4 Uniqueness and sharing | `exampleMove`, `exampleShare` |
| `Sec5_Fractional/` | §5 Fractional uniqueness | permissions, resource interfaces, `copyable`/`cloneable`, `resourceAllocator`, the examples of §5 |
| `Sec5_1_Equational/` | §5.1 (and the axioms of §4) | the equational theory `≡` |
| `Sec5_2_Distributive/` | §5.2 Partial views | `examplePartial` |
| `Sec6_1_Preliminaries/` | §6.1 | values, heaps, the references of a typed term |
| `Sec6_2_Reduction/` | §6.2 | single-step and multi-step reduction |
| `Sec6_3_Theorems/` | §6.3 | heap compatibility, Example 6.5, Lemmas 6.2 and 6.3 and the lemmas they need, Theorems 6.6–6.11 as stated, and their counterexamples |

The permissions of §5 (`Permission.lean`) are imported by `Sec3_CoreCalculus/Syntax.lean`,
because the single type of types contains the borrowing modality.

## Where to find the items of the paper

| Paper | Lean | File (under `RequestProject/FOFU/`) |
| --- | --- | --- |
| Types and terms (§3–§6.1) | `Ty`, `Term`, `Ident`, `Prim` | `Sec3_CoreCalculus/Syntax.lean` |
| `A [ι / id]`, weakening by an identifier | `Ty.inst`, `Ty.shift`, `Ty.subst` | `Sec3_CoreCalculus/TypeSubst.lean` |
| `t [t' / x]` | `Term.subst1`, `Term.subst`, `Term.rename` | `Sec3_CoreCalculus/RenameSubst.lean` |
| Contexts, `Γ₁ + Γ₂`, `r · Γ`, `0 · Γ` | `Ctx`, `CtxAdd`, `CtxScale`, `Ctx.IsZero` | `Sec3_CoreCalculus/Context.lean` |
| Algebra of contexts | `CtxAdd.assoc`, `CtxAdd.interchange`, `CtxScale.add_scale`, `CtxLe` | `Sec3_CoreCalculus/CtxAlgebra.lean` |
| Typing rules (all sections) | `HasType` | `Sec3_CoreCalculus/Typing.lean` |
| Rule `(var')` | `HasType.var'` | `Sec3_CoreCalculus/TypingLemmas.lean` |
| Dereliction-free judgment | `HasTypeD`, `hasType_iff_hasTypeD`, `HasType.approxCtx` | `Sec3_CoreCalculus/TypingD.lean` |
| Example derivation of §3 (`exampleNat`) | `exampleNat_typing` | `Sec3_CoreCalculus/Example.lean` |
| `exampleMove`, `exampleShare` (§4) | `exampleMove_typing`, `exampleShare_typing` | `Sec4_Uniqueness/Examples.lean` |
| Permissions `p ::= * \| f` (§5) | `Frac`, `Perm` | `Sec5_Fractional/Permission.lean` |
| Resource interfaces, `copyable`, `cloneable`, `resourceAllocator` | `PrimTy`, `Copyable`, `Cloneable`, `Term.Allocates` | `Sec5_Fractional/Resources.lean` |
| `exampleBorrow`, `exampleReborrow`, `exampleArray`, `exampleClone`, `exampleReference` | `…_typing` | `Sec5_Fractional/Examples.lean` |
| Equational theory (§4, §5.1) | `EqAxiom`, `Equiv` (`≡`) | `Sec5_1_Equational/Equational.lean` |
| `examplePartial` (§5.2) | `examplePartial_typing` | `Sec5_2_Distributive/Examples.lean` |
| Values (§6.1) | `IsValue`, `PrimSpine` | `Sec6_1_Preliminaries/Values.lean` |
| Heaps (§6.1) | `Heap`, `ArrVal`, `ResVal` | `Sec6_1_Preliminaries/Heap.lean` |
| Reduction (§6.2) | `Step`, `Steps` | `Sec6_2_Reduction/Step.lean` |
| Definition 6.4 (heap compatibility) | `Compat gc` | `Sec6_3_Theorems/Compat.lean` |
| Example 6.5 | `example_6_5` | `Sec6_3_Theorems/Compat.lean` |
| **Lemma 6.2** (linear substitution) | `HasType.subst_lin` | `Sec6_3_Theorems/Substitution.lean` |
| **Lemma 6.3** (graded substitution) | `HasType.subst_grd` | `Sec6_3_Theorems/Substitution.lean` |
| Theorems 6.6–6.11 as stated | `Progress`, `Preservation`, `BorrowSafety`, `MultiBorrowSafety`, `Uniqueness`, `EqSoundness` | `Sec6_3_Theorems/Statements.lean` |
| Counterexamples | `not_progress`, `not_preservation_literal`, `not_preservation_gc`, `not_borrowSafety_gc`, `not_multiBorrowSafety_gc`, `not_uniqueness_gc`, `not_eqSoundness` | `Sec6_3_Theorems/Counter*.lean` |

## Results on the theorems of §6.3

**Lemmas 6.2 and 6.3 are proved.** `HasType.subst_lin`: if `Γ₁ ⊢ t₁ : A` and
`Γ₂, x : A ⊢ t₂ : B`, then `Γ ⊢ t₂[t₁/x] : B` for every `Γ` with `Γ₂ + Γ₁ = Γ`.
`HasType.subst_grd`: if `Γ₁ ⊢ t₁ : A`, `Γ₂, x : [A]_r ⊢ t₂ : B`, `¬ resourceAllocator(t₁)`,
`r · Γ₁ = Γ₁ʳ` and `Γ₂ + Γ₁ʳ = Γ`, then `Γ ⊢ t₂[t₁/x] : B`. The paper's hypothesis that
`Γ₁` has only graded assumptions follows from `r · Γ₁` being defined. The proof uses
these lemmas, all in `Sec6_3_Theorems/`:

* `HasTypeD.substNames` (`NameSubst.lean`): identifier substitution, needed for `unpack`;
* `HasTypeD.rename` and `HasTypeD.shift` (`Renaming.lean`): renaming and weakening by an
  absent variable;
* `HasTypeD.weakenZero` (`ZeroWeakening.lean`): weakening by zero-graded assumptions;
* `HasTypeD.occurs` and `Term.allocates_subst` (`Occurs.lean`): needed for the side
  condition of promotion;
* `HasTypeD.subst_gen` (`Substitution.lean`): the general lemma, substituting for any
  variable whose assumption may be absent, linear or graded.

**Theorems 6.6–6.11.** Definition 6.4 is formalised in two variants: `gc = false` is the
definition as printed, and `gc = true` adds a garbage-collection rule `gcRes` for
resource entries. The rule is needed because, as printed, no heap that contains a
resource entry `id ↦ v_r` is compatible with any context (`Compat.ress_eq_none`).

| Paper | `gc = false` (as printed) | `gc = true` (with `gcRes`) |
| --- | --- | --- |
| Theorem 6.6 (Progress) | false: `not_progress` | false: `not_progress` |
| Theorem 6.7 (Preservation) | false: `not_preservation_literal` | false: `not_preservation_gc` |
| Lemma 6.8 (Borrow safety) | open | false: `not_borrowSafety_gc` |
| Theorem 6.9 (Multi-reduction borrow safety) | open | false: `not_multiBorrowSafety_gc` |
| Corollary 6.10 (Uniqueness) | true, vacuously: `uniqueness_literal` | false: `not_uniqueness_gc` |
| Theorem 6.11 (Soundness w.r.t. `≡`) | false: `not_eqSoundness` | false: `not_eqSoundness` |

The counterexamples (details in the docstrings of the `Counter*.lean` files):

* **Progress, Soundness:** `split (*())` is well typed (`nec` gives `*()` every
  permission, and `split` does not require a resource type), is not a value, and
  cannot reduce.
* **Preservation (printed):** `newArray 3` steps to a heap with a resource entry, which
  is compatible with no context.
* **Preservation (repaired):** `(λz. (z, *ref₀)) (split (*ref₀))`: `split` removes
  `ref₀` from the heap, but the function still mentions it.
* **Borrow safety:** `clone [ref₀]₁ as x in x` creates a new identifier whose
  reference only occurs in the heap, so its permissions in the term sum to `0`.
* **Multi-reduction borrow safety:** `split (*ref₀)` ends with two references of
  permission `1/2` and none of permission `1`.
* **Uniqueness:** after `split` and `join` the original reference `ref₀` has been
  replaced by a new one.

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
* `exampleGraded` is not formalised. It reads a `Float [4]` out of a reference that
  holds a `Float [6]`, and afterwards uses the reference at type `Ref id (Float [2])`.
  The printed interface of `readRef` keeps the type of the reference unchanged, so the
  example does not type-check against it.
* `exampleConcurrent`, `exampleDeriving` and the parallel-sum example use Granule
  features (`par`, `Maybe`/`Either`, length-indexed vectors) that are outside the
  calculus, so they are not formalised.

## Suggested reading order

1. `Sec3_CoreCalculus/Syntax.lean`, `Context.lean`, `Typing.lean`: the calculus.
2. `Sec3_CoreCalculus/Example.lean` and the examples of §4, §5 and §5.2: concrete
   derivations, built with the tactics `ctx_add` and `zero_rest` of `TypingLemmas.lean`.
3. `Sec6_1_Preliminaries/`, `Sec6_2_Reduction/Step.lean`, `Sec6_3_Theorems/Compat.lean`:
   the semantics and heap compatibility.
4. `Sec6_3_Theorems/Statements.lean`, then the `Counter*.lean` files.
5. `Sec6_3_Theorems/Substitution.lean` for Lemmas 6.2 and 6.3, going back to
   `Sec3_CoreCalculus/CtxAlgebra.lean`, `TypingD.lean` and the other `Sec6_3_Theorems/`
   files for the lemmas they use.
