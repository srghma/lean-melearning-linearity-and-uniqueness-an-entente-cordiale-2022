# Summary of changes for run b3621db2-dbce-49a8-a9e3-ce0d7e6b7bf1
You don't need to send the *Functional Ownership through Fractional Uniqueness* file again. `paper.typ` in the project already contains it, and I continued from it.

The last open items were Lemma 6.8 and Theorem 6.9 of §6.3 under heap compatibility as printed (Definition 6.4). Both are now settled. The whole project builds with no `sorry`, and the two new results use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Lemma 6.8 (Borrow safety) holds with the printed rules.** It is `borrowSafety_literal`, in `RequestProject/FOFU/Sec6_3_Theorems/BorrowSafetyLiteral.lean`.
- The part about identifiers already in the heap is vacuous: under the printed rules, a compatible heap contains no identifiers.
- The part about newly created identifiers holds for real. `Step.new_ident` shows that when a step starts from a heap with no resource entries, every identifier it creates has exactly one reference, with permission 1, and that reference appears in the reduced term. So the permissions sum to 1. This part doesn't depend on typing.

**Theorem 6.9 (Multi-reduction borrow safety) is false with the printed rules.** It is `not_multiBorrowSafety_literal`, in `RequestProject/FOFU/Sec6_3_Theorems/CounterMultiBorrowLiteral.lean`. Starting from the empty heap and context, this closed term is well typed:

`(unpack ⟨id, x⟩ = newArray 3 in withBorrow (λb. unpack ⟨id', c⟩ = newRef (split b) in let [d] = share₀ c in *()) x, newArray 3)`

It reduces in 13 steps to the value `(*(), pack ⟨id₂, *ref₄⟩)`. Along the way:
- the borrowed array is split into two halves;
- the halves are stored in a new reference cell;
- that cell is thrown away with `share` at grade 0.

At the end, the first array's identifier is new, but only two references of permission 1/2 point to it, and none of permission 1. One caveat: the paper doesn't define `[H]_0`, so this reduction uses my earlier reading of the `share` rule, where the heap is left unchanged. Any reading that discards the cell without joining the halves gives the same result.

So every theorem in §6.3 is now settled for both versions of heap compatibility (as printed, and with the extra clean-up rule for resource entries):

| | As printed | With extra rule |
|---|---|---|
| 6.6 Progress | false | false |
| 6.7 Preservation | false | false |
| 6.8 Borrow safety | **true** | false |
| 6.9 Multi-reduction borrow safety | **false** | false |
| 6.10 Uniqueness | true, but only vacuously | false |
| 6.11 Equational soundness | false | false |

I updated the summary table in `Statements.lean`, the notes in `CounterBorrowSafety.lean`, `README.md`, the reading guide for this paper, and the two Properties table rows (now proved and disproved). One item from the earlier work is still not formalized: `exampleGraded`, which doesn't type-check against the `readRef` interface as printed in the paper.