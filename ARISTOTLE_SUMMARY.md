# Summary of changes for run 519ff1b3-d28a-43a2-846f-cf92c732c074
I formalised the LCU calculus from `paper.typ` in Lean 4 with Mathlib. Read literally against the rules in the provided text, all four of the paper's main metatheorems (Theorems 4–7) are false, and I proved each negation in Lean. The project builds with no `sorry`; the only axioms used are `propext`, `Classical.choice` and `Quot.sound`. Everything is in `RequestProject/LCU/` (namespace `LCU`), and `README.md` gives an overview.

**Representation (as you asked):** terms use de Bruijn indices with no named variables. `Term n` has `Term.var : Fin n → Term n`, so `Term 0` is the type of closed terms. Contexts give each variable a linear \(x : A\), non-linear \(x : [A]\), or no hypothesis, and context addition is defined pointwise.

**Proved:**
- **Syntax and typing:** renaming and substitution (`Syntax.lean`), and the typing rules of Figure 1 plus the array primitives (`Typing.lean`). `TypingD.lean` gives an equivalent system without a separate dereliction rule.
- **Lemma 1** (linear substitution) and **Lemma 2** (non-linear substitution) in `Substitution.lean`; **Lemma 3** (weakening) in `Weakening.lean`.
- **Equational theory** (`Equational.lean`): every axiom preserves typing left to right, and the axioms that don't involve substitution also preserve it right to left.
- **Section 4's \(\{0,1,\omega\}\) semiring** (`Granule.lean`): it is a commutative semiring, the order \(0 \sqsubseteq \omega\), \(1 \sqsubseteq \omega\) is a partial order, and \(+\) and \(\times\) are monotone.

**Heap model** (`Heap.lean`): heaps, single-step and multi-step reduction, full β-reduction, and heap–context compatibility (Definition 3). `Metatheory.lean` states Theorems 4–7 exactly as written in the paper.

**Theorems 4–7 are false as written:**
- **Theorem 4 (Conservation)**, `not_conservation`: `copy !((λz.z) unit) as x in &x : !1` steps to a term that has no valid typing.
- **Theorem 5 (Uniqueness)**, `not_uniqueness`: `let! z = (copy !(newArray 1) as x in &x) in z` ends with a fresh array that is not uniquely owned.
- **Theorem 6 (Progress)**, `not_progress`: `&(*((λz.z) unit))` is well-typed, not a value, and stuck.
- **Theorem 7 (Equational soundness)**, `not_eqSoundness`: the two sides of the η! instance `let! x = !unit in !x ≡ !unit` can never reach the same final heap.

**Caveat:** the provided text leaves out some rules, including the runtime typing rule for array references (which is in the paper's appendix) and some heap-model rules. I reconstructed these; the choices are documented in `Typing.lean`, `Heap.lean` and the README. So the counterexamples refute the theorems for the rules as given in the text plus these reconstructions, not necessarily for the full rule set in the appendix. The progress counterexample in particular relies on the text having no rule that reduces under `*`.

The Properties table lists all of these results with their final status.