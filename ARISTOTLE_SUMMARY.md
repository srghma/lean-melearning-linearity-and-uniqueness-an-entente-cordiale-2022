# Summary of changes for run b62d5b9a-0c58-402d-bfa0-4ff420488967
I replaced the places where the formalisation used a larger type plus a side condition with types that only contain valid objects. The project still builds with no `sorry`, and the only axioms are `propext`, `Classical.choice` and `Quot.sound`. All previous results still hold, including the four disproofs of Theorems 4–7.

**What changed**
- **Values (`Values.lean`).** The value grammar \(v ::= (t_1,t_2) \mid \mathsf{unit} \mid {*t} \mid {!t} \mid \lambda x.t \mid i \mid a \mid p\) is now a type `Value n`. Its partially applied primitives are a separate type `PrimFun n`: a primitive can only be applied to fewer arguments than it takes, and each argument must be a value. `IsValue t` now just says `t` comes from some `Value`. `IsValue.induction` lets proofs go case by case over values.
- **Core grammars (`Syntax.lean`).** The calculus of Section 3.1, without literals, primitives or array references, is now its own pair of types: `CoreTy` and `CoreTerm n`. Both embed one-to-one into the extended `Ty` and `Term n`. A new theorem, `cbn_eval_core`, says every well-typed closed `CoreTerm` evaluates to a `Value` of the same type. It needs no "contains no primitives" side condition.
- **Heaps (`Heap.lean`).**
  - Each heap entry \(x \mapsto_r (\Gamma \vdash t : A)\) now stores a proof that \(\Gamma \vdash t : A\) holds, so a heap can only record judgments that are actually derivable.
  - Heaps can only have finitely many arrays.
  - Arrays are finite lists of floats, so they can't have gaps.
  - The usage markers \(1 \le \omega\) form a proper decidable partial order.
  - Definition 3 (heap–context compatibility, `Compat`) now refers to the typing stored in the entry rather than a separate premise.
- **Array semantics (`ArraySemantics.lean`).**
  - Stores now carry a proof that they are finite, so the finiteness hypotheses are gone from `astep_progress` and `ASteps.preserves`.
  - Its values (`StoreValue`) and partially applied primitives (`ReadyPrim`) are also types now, and they embed into `Value` and `PrimFun`.

**A side effect on the paper's `copy_β` rule.** Requiring heap typings to hold showed a gap. The paper's rule assumes \(\Gamma \vdash v : A\) but records \(\Gamma \vdash *\theta(v) : *A\) in the new heap entry. In general the first does not imply the second, because \(\theta\) renames the array references to fresh copies that \(\Gamma\) doesn't mention. The rule now asks directly for the recorded judgment to hold. The Uniqueness counterexample used exactly such an unjustified entry, so I gave it a correct typing context, and its disproof still goes through.

**Not changed.** Typing contexts still allow infinitely many array references, and terms still include runtime array references. Making contexts finite would mean rewriting most of the development.

`README.md` has a new "Grammars by construction" section mapping each grammar in the paper to its Lean type. In the Properties table I added the value grammar, the core grammars, heaps and `cbn_eval_core` (marked proved), and updated the comments on entries these changes affect.