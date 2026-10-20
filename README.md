# Formalisation of *Linearity and Uniqueness: An Entente Cordiale* (LCU calculus)

This is a Lean 4 / Mathlib formalisation of the paper in `paper.typ`. All files live in
`RequestProject/LCU/` under the namespace `LCU`. The whole project builds with no `sorry`,
and the only axioms used are the standard `propext`, `Classical.choice` and `Quot.sound`.

## Representation

Terms use de Bruijn indices and are intrinsically scoped: `Term n` is the type of terms
with `n` free variables, `Term.var : Fin n → Term n`, and `Term 0` is the type of closed
terms. Binders bind index `0`. In `letPair t₁ t₂` (`let (x, y) = t₁ in t₂`), `y` is index
`0` and `x` is index `1`. A context `Ctx n` gives each variable (and each runtime array
reference) an optional linear hypothesis `x : A` or non-linear hypothesis `x : [A]`.
Context addition (Definition 2) and `[Γ]` (Definition 1) are defined pointwise.

## Files

| File | Contents |
| --- | --- |
| `Syntax.lean` | types `Ty`, primitives, terms `Term n`, renaming and substitution |
| `Context.lean`, `CtxAlgebra.lean` | contexts, context addition and its algebra |
| `Typing.lean` | the typing judgment `HasType` (Figure 1 plus the array primitives of §3.3) |
| `TypingD.lean` | an equivalent system with no separate dereliction rule (`hasType_iff_hasTypeD`) |
| `Weakening.lean` | **Lemma 3** (weakening) `HasType.weaken`, plus renaming/shifting |
| `Substitution.lean` | **Lemma 1** `HasType.subst_lin`, **Lemma 2** `HasType.subst_nonlin` |
| `Values.lean` | values |
| `Equational.lean` | the equational theory `≡ₗ` (§3.2); every axiom preserves typing (`EqAxiom.preserves`) |
| `Heap.lean` | the heap model (§3.4): heaps, single-step reduction `Step`, multi-step `Steps`, full β-reduction, compatibility `Compat` (**Definition 3**) |
| `Metatheory.lean` | **Theorems 4–7** stated literally as propositions `Conservation`, `Uniqueness`, `Progress`, `EqSoundness` |
| `Counter*.lean` | formal disproofs of these four statements (see below) |
| `CbnSemantics.lean` | a repaired, substitution-based call-by-name reduction `CbnStep` with subject reduction, progress, type safety and determinism (see below) |
| `CbnExamples.lean` | the progress and conservation counterexamples reduce to values under `CbnStep` |
| `CbnNormalization.lean` | termination of `CbnStep` evaluation on well-typed closed terms (logical relation) |
| `KeyIdeas.lean` | the examples of Section 2 (impossible/possible cake and coffee programs, `sip`, dereliction, borrowing, `uniqueReturn`/`uniqueBind`) |
| `RefShift.lean` | renaming of array references (for `copy_β`) and weakening into larger non-linear contexts |
| `ArraySemantics.lean` | a store-based semantics with mutable arrays, `AStep`, with subject reduction, progress and type safety |
| `ArrayExamples.lean` | an example run: `readArray (writeArray (newArray 3) 0 x) 0` evaluates to `(x, *a)` |
| `Granule.lean` | the `{0, 1, ω}` semiring of §4.1: a commutative semiring and partial order with monotone `+` and `*` |

## Reconstruction choices

The provided text leaves out a few rules: the runtime typing rule for array references
(found in the paper's appendix) and some heap-model rules. We reconstructed them as
follows. Array references are typed by `[Γ], a : Array A ⊢ a : Array A`, and `nec`
passes the array references of its conclusion to its premise. For source programs (no
array references), the typing rules are exactly the paper's. The heap-model rules we
reconstructed are documented in the docstring of `Heap.lean`.

## Results on Theorems 4–7

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

## A repaired call-by-name semantics with type safety

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

## Termination of call-by-name evaluation

`CbnNormalization.lean` proves that `CbnStep` evaluation terminates. It uses a unary
logical relation `Reducible A t`, and the fundamental lemma `HasTypeD.reducible`.

* `cbn_normalization`: every well-typed closed term without array primitives reduces
  to a value;
* `cbn_eval`: the value has the same type (in a context whose array references are
  non-linear);
* `cbn_value_unique`: the value is unique.

## The examples of Section 2

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

## Mutable arrays: a store-based semantics with type safety

`ArraySemantics.lean` extends the call-by-name semantics with a store of mutable float
arrays. The reduction `σ ⊢ t ⟶ σ' ⊢ t'` (`AStep`) uses these rules:

* `newArray k` allocates a fresh array;
* `readArray (*a) k` reads from the store;
* `writeArray (*a) k x` updates the store destructively;
* `copy !u as x in t ⟶ [*θ(u)/x]t` copies every array referenced by `u` to a fresh
  reference (`θ(a) = N + a`), as in the paper's `copy_β`;
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
