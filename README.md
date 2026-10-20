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
