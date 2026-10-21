# Reading guide

This guide explains how the Lean formalisation of *Linearity and Uniqueness: An Entente
Cordiale* (`paper.typ`) is organised and suggests an order for reading it. All Lean files
live in `RequestProject/LCU/`, in the namespace `LCU`. `RequestProject/LCU.lean` imports
everything, so `import RequestProject.LCU` gives access to the whole development.

The project builds with no `sorry`. For the overall results (including which theorems of
the paper turned out to be false as stated), see `README.md`.

## Conventions you need first

* **De Bruijn terms.** `Term n` is the type of terms with `n` free variables, and
  `Term.var : Fin n → Term n`. `Term 0` is the type of closed terms. A binder binds
  index `0` and shifts all other indices by one. In `letPair t₁ t₂`
  (`let (x, y) = t₁ in t₂`), `y` is index `0` and `x` is index `1`.
* **Contexts.** `Ctx n` gives every variable (`.inl i`) and every runtime array
  reference (`.inr a`) an optional hypothesis: `none` (absent), `some (.lin A)`
  (`x : A`), or `some (.nonlin A)` (`x : [A]`). Context addition `Γ₁ + Γ₂ = Γ` is
  partial, so it is the relation `Γ₁.Add Γ₂ Γ`. The paper's `[Γ]` is the predicate
  `Γ.AllNonLin`.
* **Two typing judgments.** `HasType` is the paper's judgment (Figure 1). `HasTypeD`
  is an equivalent version without a separate dereliction rule, which is more
  convenient for induction (`hasType_iff_hasTypeD`). Most proofs are about `HasTypeD`
  and are transferred to `HasType` at the end.
* **Grammars as types.** Sub-grammars such as values are inductive types (`Value n`,
  `CoreTerm n`, ...) that embed into `Term n`. A predicate like `IsValue t` just says
  that `t` is in the image of the embedding.

## Directory layout

The directory names follow the sections of the paper. The `Ext…` directories contain
material that goes beyond the paper.

| Directory | Paper | Contents |
| --- | --- | --- |
| `Sec2_KeyIdeas/` | §2 Key Ideas | the cake/coffee examples, `sip`, dereliction, borrowing, `uniqueBind` |
| `Sec3_1_Calculus/` | §3.1 (and Figure 1) | syntax, contexts, typing, weakening, substitution (Lemmas 1–3), values |
| `Sec3_2_Equational/` | §3.2 | the equational theory and the typability of its axioms |
| `Sec3_4_HeapModel/` | §3.4 | heaps, the reduction rules, compatibility (Definition 3) |
| `Sec3_5_Metatheory/` | §3.5 | Theorems 4–7 as stated, and their disproofs |
| `Sec4_Implementation/` | §4.1 | the `{0, 1, ω}` semiring used by Granule |
| `Ext1_CallByName/` | beyond the paper | a repaired, substitution-based call-by-name semantics: type safety and termination |
| `Ext2_MutableArrays/` | §3.3 + beyond | a store-based semantics with mutable arrays: type safety |

§3.3 (array primitives) has no directory of its own. Its typing rules are part of
`Sec3_1_Calculus/Typing.lean`, and its operational semantics is in `Ext2_MutableArrays/`.

## Where to find the numbered items of the paper

| Paper | Lean | File |
| --- | --- | --- |
| Types and terms (§3.1) | `Ty`, `Term`, `CoreTy`, `CoreTerm` | `Sec3_1_Calculus/Syntax.lean` |
| Definition 1 (`[Γ]`) | `Ctx.AllNonLin` | `Sec3_1_Calculus/Context.lean` |
| Definition 2 (context addition) | `HypAdd`, `Ctx.Add` | `Sec3_1_Calculus/Context.lean` |
| Figure 1 (typing rules), array primitives (§3.3) | `HasType`, `Prim.ty` | `Sec3_1_Calculus/Typing.lean` |
| Lemma 1 (linear substitution) | `HasType.subst_lin` | `Sec3_1_Calculus/Substitution.lean` |
| Lemma 2 (non-linear substitution) | `HasType.subst_nonlin` | `Sec3_1_Calculus/Substitution.lean` |
| Lemma 3 (weakening) | `HasType.weaken` | `Sec3_1_Calculus/Weakening.lean` |
| Equational theory (§3.2) | `EqAxiom`, `Equiv` (`≡ₗ`) | `Sec3_2_Equational/Equational.lean` |
| Typability of the axioms | `EqAxiom.preserves` | `Sec3_2_Equational/EqAxiomTyping.lean` |
| Values (Theorem 6) | `Value`, `PrimFun`, `IsValue` | `Sec3_1_Calculus/Values.lean` |
| Heaps and reduction (§3.4) | `Heap`, `Step`, `Steps`, `FullStep`, `FullSteps` | `Sec3_4_HeapModel/Heap.lean` |
| Definition 3 (compatibility `H ⋈ Γ`) | `Compat` | `Sec3_4_HeapModel/Heap.lean` |
| Theorem 4 (Conservation) | `Conservation`, refuted by `not_conservation` | `Sec3_5_Metatheory/Metatheory.lean`, `CounterConservation.lean` |
| Theorem 5 (Uniqueness) | `Uniqueness`, refuted by `not_uniqueness` | `Sec3_5_Metatheory/Metatheory.lean`, `CounterUniqueness.lean` |
| Theorem 6 (Progress) | `Progress`, refuted by `not_progress` | `Sec3_5_Metatheory/Metatheory.lean`, `CounterProgress.lean` |
| Theorem 7 (Equational soundness) | `EqSoundness`, refuted by `not_eqSoundness` | `Sec3_5_Metatheory/Metatheory.lean`, `CounterEqSoundness.lean` |
| §2 examples | `impossible_cake`, `impossible_coffee`, `possible_cake`, `sip_hasType`, ... | `Sec2_KeyIdeas/KeyIdeas.lean` |
| §4.1 grades `{0, 1, ω}` | `NOT` and its `CommSemiring`/`PartialOrder` instances | `Sec4_Implementation/Granule.lean` |

## Suggested reading paths

### Path A: the statements only

Read only the module docstrings, definitions and theorem statements. You can skip
every proof.

1. `Sec3_1_Calculus/Syntax.lean`: types, terms, and the core grammars.
2. `Sec3_1_Calculus/Context.lean`: hypotheses, contexts, context addition.
3. `Sec3_1_Calculus/Typing.lean`: the typing rules. Compare them side by side with
   Figure 1 of the paper; the docstring of `HasType` explains the encoding.
4. `Sec2_KeyIdeas/KeyIdeas.lean`: the examples of §2, as typing facts.
5. `Sec3_1_Calculus/Weakening.lean` and `Substitution.lean`: the statements of
   Lemmas 1–3 (`HasType.weaken`, `HasType.subst_lin`, `HasType.subst_nonlin`).
6. `Sec3_2_Equational/Equational.lean`: the equational axioms.
7. `Sec3_4_HeapModel/Heap.lean`: heaps and the reduction rules. The docstring lists
   the rules that were missing from the text and how they were reconstructed.
8. `Sec3_5_Metatheory/Metatheory.lean`: Theorems 4–7 stated literally. Then read the
   module docstrings of the four `Counter*.lean` files, which describe each
   counterexample in words.
9. `Ext1_CallByName/CbnSemantics.lean`: the repaired semantics and its type safety
   theorem `cbn_type_safety`; then `CbnNormalization.lean` for `cbn_normalization`
   and `cbn_eval_core`.
10. `Ext2_MutableArrays/ArraySemantics.lean` (definitions) and `ArrayProgress.lean`
    (`array_type_safety`).

### Path B: the full development, in dependency order

Files marked *(technical)* are infrastructure. On a first reading it is enough to
look at their docstrings.

**§3.1: the calculus** (`Sec3_1_Calculus/`)

1. `Syntax.lean`: `Ty`, `Prim`, `Term n`, `CoreTy`, `CoreTerm n`.
2. `RenameSubst.lean` *(technical)*: parallel renaming and substitution, `subst1`,
   `subst2`, `renameRefs`, and their composition laws.
3. `Context.lean`: `Hyp`, `Ctx n`, `HypAdd`, `Ctx.Add`, `Ctx.AllNonLin`, `Ctx.cons`.
4. `Typing.lean`: `HasType` (notation `Γ ⊢ t ∶ A`).
5. `CtxAlgebra.lean` *(technical)*: context addition is a partial commutative monoid
   (commutativity, associativity, interchange, and so on).
6. `TypingD.lean`: the dereliction-free judgment `HasTypeD`, admissibility of
   dereliction, and `hasType_iff_hasTypeD`. It also defines the `split_rule` tactic,
   which handles all rules that split their context in one case.
7. `Weakening.lean`: renaming of derivations and Lemma 3.
8. `Substitution.lean`: the general substitution lemma `HasTypeD.subst_gen`, and
   Lemmas 1 and 2. The docstring explains why the lemma is generalised to substitution
   for an arbitrary variable.
9. `Values.lean`: the value grammar `Value n`/`PrimFun n` and the induction principle
   `IsValue.induction`.
10. `FreeVars.lean`: `FreeIn`, the fact that linear variables must occur
    (`HasTypeD.freeIn_of_lin`), and strengthening (`HasTypeD.unrename`).

**§2: the examples** (`Sec2_KeyIdeas/KeyIdeas.lean`). This file uses `FreeVars.lean`
to show that `λx. (t₁, t₂)` is ill-typed when `x` occurs in both components.

**§3.2: equational theory** (`Sec3_2_Equational/`)

11. `Equational.lean`: `EqAxiom`, `Equiv`.
12. `EqAxiomTyping.lean`: `EqAxiom.preserves` (every axiom preserves typing from left
    to right), and the `…_expand` lemmas (the axioms without substitution also
    preserve typing from right to left).

**§3.4: heap model** (`Sec3_4_HeapModel/Heap.lean`)

13. Usage annotations, heaps (whose entries store their typing derivations), `Step`,
    `Steps`, `FullStep`, `FullSteps`, `Compat`.

**§3.5: metatheory** (`Sec3_5_Metatheory/`)

14. `Metatheory.lean`: the four statements, and a table pointing to their disproofs.
15. `CounterProgress.lean`: the shortest counterexample (a stuck term). A good first
    example of how the counterexamples are built.
16. `CounterConservation.lean`: one step whose reduct cannot be typed in any
    compatible context.
17. `CounterEqSoundness.lean`: an `η!` instance whose two sides can never reach the
    same final heap.
18. `CounterUniqueness.lean`: a six-step reduction, with every intermediate heap
    spelled out, that ends in a unique value pointing to a shared array.

These four files are independent of each other.

**Beyond the paper: a repaired call-by-name semantics** (`Ext1_CallByName/`)

19. `CbnSemantics.lean`: `CbnStep` replaces heap bindings with substitution. Results:
    subject reduction (`CbnStep.preserves`), progress for terms without array
    primitives (`cbn_progress`), type safety (`cbn_type_safety`), determinism. It also
    shows (`not_cbnStep_preserves_open`) that subject reduction fails for open terms.
20. `CbnExamples.lean`: the progress and conservation counterexamples evaluate
    correctly under `CbnStep`.
21. `CbnNormalization.lean`: termination via a logical relation `Reducible`. The
    fundamental lemma is `HasTypeD.reducible`, and the corollaries are
    `cbn_normalization`, `cbn_eval`, `cbn_value_unique` and `cbn_eval_core`.

**Beyond the paper: mutable arrays** (`Ext2_MutableArrays/`)

22. `RefShift.lean` *(technical)*: renaming array references (the `θ` of `copy_β`)
    preserves typing; weakening into larger non-linear contexts (`Ctx.Sub`,
    `HasTypeD.mono`).
23. `ArraySemantics.lean`: stores, the reduction `AStep`, and well-typed
    configurations `ConfOK`.
24. `ArrayPreservation.lean`: subject reduction `AStep.preserves`.
25. `ArrayProgress.lean`: progress `astep_progress` and type safety
    `array_type_safety`.
26. `ArrayExamples.lean`: `readArray (writeArray (newArray 3) 0 x) 0` evaluates to
    `(x, *a)`, so the read sees the destructive write.

**§4.1** (`Sec4_Implementation/Granule.lean`). This file is independent of everything
else and can be read at any point.

## Dependency overview

```
Syntax ─ RenameSubst ─┬─ Context ─ Typing ─ CtxAlgebra ─ TypingD ─ Weakening ─ Substitution ─┐
                      └─ Values ────────────────────────────────────────────────────────────┤
                                                                                            │
     Substitution ─ FreeVars ─┐                                                             │
     Equational (+ Values) ───┴─ EqAxiomTyping ─┬─ KeyIdeas                                 │
                                                ├─ Heap ─ Metatheory ─ Counter* (×4)        │
                                                └─ CbnSemantics ─┬─ CbnNormalization        │
                                                                 ├─ CbnExamples (+ Counter*)│
                                                                 └─ RefShift ─ ArraySemantics
                                                                     ─ ArrayPreservation ─ ArrayProgress ─ ArrayExamples
Granule (standalone)
```

## Tips for browsing in an editor

* Every file starts with a module docstring (`/-! … -/`) that lists its main
  definitions and results. Section headers (`/-! ## … -/`) divide the longer files.
* Hover over a name to see its docstring, or use `#check @LCU.HasType.subst_lin`
  in a scratch file that has `import RequestProject.LCU`.
* `#print axioms LCU.array_type_safety` (or any other result) shows that only the
  standard axioms are used.
