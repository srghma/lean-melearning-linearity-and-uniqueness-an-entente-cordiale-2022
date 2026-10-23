# Proposal: making the formalisation more correct-by-construction

This document reviews the current formalisation of both papers (`RequestProject/FOFU/`
and `RequestProject/LCU/`) and suggests improvements. The main theme is
*correct by construction*: invariants should be guaranteed by the types, not stated as
side conditions that every rule and theorem has to carry around. Each item gives

* **Now**: what the code currently does (with file references);
* **Problem**: what can go wrong, or what it costs in proofs;
* **Proposal**: the suggested change;
* **Cost / benefit**: rough size of the change and what it buys.

A small prototype of items 1, 3 and 4 was originally written as a separate file. It was
never used by the formalisations and has been removed now that the proposal is
implemented in `RequestProject/Common/`, `RequestProject/FOFU/` and `RequestProject/LCU/`;
mentions of "the prototype" below refer to that removed sketch.

The items are ordered by the ratio of benefit to cost, as I estimate it. Items 1–5 change
the core representation. Items 6–11 are local changes. Items 12–14 are about process and
trust.

## Implementation status

The proposal has been implemented for both papers, with the review decisions "use a
custom `Var n` instead of `Fin2`", "a generic binding layer: yes" and "floats as
`Lean.JsonNumber`":

| Item | Status |
| --- | --- |
| 1. Length-indexed contexts and heaps | done: `Ctx α n` (`Common/Ctx.lean`) with variables `Var n` (`Common/Var.lean`); contexts, heaps and stores of both papers are built from it; `0 · Γ, x : A` is `Ctx.Pick` |
| 2. Generic binding layer | done: `Binding.Tm S n` (`Common/Syntax.lean`); the terms of both papers are instances |
| 3. Scoped runtime names, `Frac` permissions | done: `Term R n ρ` with `ref : Var ρ → _`, `Heap R n ρ ι` with `refs : Ctx (Option (Frac × Var ι)) ρ`; allocation creates the name `Var.zero`; no freshness premises, and the references of a term are in the scope of its heap by construction (deallocated references have entry `none`) |
| 4. Values as a separate type | LCU already had `Value n ρ`; FOFU keeps the `IsValue` predicate |
| 5. Steps indexed by growth | done: `Step H t s d e f H' t'` (FOFU) and `Step H t d e H' t'` (LCU); in FOFU configurations grow at index `0`, so β-rules continue with the body itself |
| 6. Restricted grammars | partly: `Ty.copyable`, `Ty.cloneable`, `Ty.funFree`, `Ty.refsFunFree` are `Bool`-valued and `Term.Allocates` is decidable; the context restriction `TCtx.RefsFunFree` is stated with `Ctx.All`; the restriction of Theorem 6.7 is still a hypothesis rather than a separate grammar of ground types |
| 7. Permission algebra, grade class | partly: `Grades.PreorderedSemiring` provides Mathlib's `AddLeftMono` / `AddRightMono` / `MulLeftMono` / `MulRightMono` instances (and `PreorderedSemiring.ofMono` builds the class from them), so Mathlib's order lemmas apply to grades; `Frac.add` has its partial commutative monoid laws (`add_comm`, `add_assoc`, `add_left_cancel`); the typing rules still take the definedness proof `f + g ≤ 1` directly |
| 8. Floats | done: `FloatLit := Lean.JsonNumber` in both papers |
| 11. Small clean-ups | done (`Step.appL`, `weakenTo`, lookup-based context restriction, `ArrTy` for LCU references) |
| 9, 10, 12–14 | not done (process and tooling items) |

The text below is the original proposal; its "Now" paragraphs describe the code before
the change.

---

## 1. Contexts and heaps as length-indexed lists, variables as `Fin2`

**Now.** Contexts are functions: `Ctx.vars : Fin n → Option (Assm R k)` and
`Ctx.refs : ℕ → Option (RefTy R k)` (`FOFU/Sec3_CoreCalculus/Context.lean`). In LCU,
`Ctx n := Fin n ⊕ ℕ → Option Hyp`. The previous step made the *judgments* structural
(`FinLookup` with `here` / `there` over `Fin.cons`), but the data is still a function.

**Problem.**
* Equality of contexts is function extensionality. In `FOFU/` and `LCU/` there are about
  50 uses of `funext` and about 50 of `Function.update`, and about 110 places convert a
  lookup judgment back into an equation (`.eq`, `…_iff`).
* `FinLookup` matches on `Fin.cons b f`. A context that is not syntactically a `Fin.cons`
  has to be rewritten first (`Fin.cons_self_tail`).
* Variables are `Fin n`. `Fin.succ` is not a constructor, so `cases` on a derivation whose
  index is `i.succ` fails with "dependent elimination failed". I hit this error in the
  prototype. The current code works around it by going through `finLookup_iff`, back to
  equations.
* The typing rule `var` needs two premises:
  `Γ.VarAt i (.lin A)` and `∀ j, j ≠ i → ZeroAssm (Γ.vars j)`. Many proofs then do case
  analysis on `j = i`.
* Contexts are extended at the front (`Ctx.cons`, for binders) and at the back
  (`Ctx.snoc`, for heap growth). Both have to be maintained.

**Proposal.**
```lean
inductive Ctx (α : Type) : ℕ → Type
  | nil  : Ctx α 0
  | snoc : Ctx α n → α → Ctx α (n + 1)

-- variables: Mathlib's `Fin2 n` (constructors `fz`, `fs`), or a custom `Var n`
inductive LinVar : Ctx (Option (Assm T R)) n → Fin2 n → T → Prop
  | here  : ZeroCtx Γ → LinVar (Γ.snoc (some (.lin A))) .fz A
  | there : LinVar Γ i A → ZeroAssm a → LinVar (Γ.snoc a) (.fs i) A
```
* Context addition and scaling become `Forall₃` / `Forall₂` relations defined by
  recursion on the lists (`nil` / `snoc`).
* `0 · Γ, x : A` becomes the single judgment `LinVar Γ i A`. The rule
  `var : LinVar Γ i A → HasType Γ (.var i) A` has one premise.
* Use `Fin2` (or a custom `Var n`) for term variables, so that `cases` / `induction` on
  lookup derivations works without detours.

In the prototype, `LinVar.unique` (the variable of a `var` rule is determined by the
context) and `CtxAdd.comm` are each a few lines of structural induction.

**Cost / benefit.** This is the largest change: most of the context algebra
(`CtxAlgebra.lean`, roughly 680 lines in both developments together) and the renaming
lemmas would have to be redone. The result is shorter proofs, no `funext` / `Function.update`
reasoning, and a single source of truth for the rule `var`. I would do it together with
item 2.

---

## 2. A generic binding layer (one renaming / substitution library)

**Now.** FOFU and LCU each define `rename`, `subst`, `up` and their composition laws for
their own `Term` (`FOFU/Sec3_CoreCalculus/RenameSubst.lean`, `LCU/Sec3_1_Calculus/RenameSubst.lean`,
plus `TypeSubst.lean` for identifiers). Only `Ren.up` is shared (`Common/DeBruijn.lean`).

**Problem.** The same σ-calculus lemmas (`rename_rename`, `subst_rename`, `subst_id`, …)
are proved several times, once for each syntax. Every new constructor needs new cases.

**Proposal.**
* Describe each syntax by a *signature*: a list of constructors, each with its binding
  arities, e.g. `letPair : [0, 2]` means one argument with no binders and one with two.
  Define a generic `Tm Sig n` with `var : Fin2 n → Tm Sig n`. Then `rename`, `subst`
  and all σ-calculus laws are proved **once**.
* A lighter alternative: keep the hand-written inductives, but define a typeclass
  `Syntax T` (`var`, `rename`, `subst`) with law fields. Give the laws as a `simp` set in
  the style of Autosubst (`up_comp`, `subst_comp`, …), so that the composition lemmas can
  be proved by `simp`.

**Cost / benefit.** Medium cost. It removes duplicated code, and new extensions (arrays,
call-by-name, references) get renaming and substitution for free.

---

## 3. Make runtime names scoped and heap invariants hold by construction

**Now.**
* Runtime references and identifiers are bare naturals: `Term.ref : ℕ → Term R n`,
  `Ident.rt : ℕ → Ident k`.
* Heaps are total functions `Heap.refs : ℕ → Option (ℚ × ℕ)` and
  `Heap.ress : ℕ → Option (ResVal R n)` (`FOFU/Sec6_1_Preliminaries/Heap.lean`).
* **Heap permissions are unconstrained rationals.** `ref ↦_p id` can store `p = 0`,
  `p < 0` or `p > 1`. Also, `Compat.extRes` and `Compat.gcArr` accept any `p : ℚ`.
* Freshness (`H.RefFree a`, `H.IdFresh id`) is a premise of the allocation rules.

**Problem.**
* Nothing in the types says that a reference in a term is in the heap. This is a
  separate theorem (`HasType.refs_ne_none`), and every heap theorem has to quantify over
  "`H.ress id ≠ none`".
* A heap value of type `Heap R n` may have infinite domain. Nothing guarantees that a
  fresh name exists. Allocation can be blocked for reasons unrelated to the paper.
  Compatible heaps happen to be finite, but that is a fact that has to be proved.
* Permissions outside `(0, 1]` are meaningless in the paper, but they are allowed in heaps
  and in `Compat`. The paper's borrow-safety statements talk about sums of permissions.
  An unconstrained `ℚ` makes such statements easier to break, or to satisfy, by accident.

**Proposal.**
* Store `Frac` (already defined in `Permission.lean`, `0 < p ≤ 1`) in heaps instead of
  `ℚ`. This is the cheapest item in the list. The prototype's `HeapPerm` shows the type.
* Index the runtime syntax by the number of references and identifiers in scope, in the
  same way as term variables: `Term R n ρ` with `ref : Fin2 ρ → Term R n ρ`, and
  `Heap R n ρ ι` with `refs : Ctx (Frac × Fin2 ι) ρ`. Then "`refs(t) ⊆ dom(H)`" holds by
  construction, and allocation *creates* a fresh name: the new name is `Fin2.fz` and
  everything else is weakened. There are no freshness premises.
* If full scoping is too invasive, use finite maps (`Finmap` / `AList`) for heaps. Then
  a fresh name always exists (a lemma, `exists_fresh`), and `dom(H)` is a `Finset`.

**Cost / benefit.** Switching to `Frac` is small. Scoped runtime names is medium to large.
It removes `refs_ne_none`, the `RefFree` / `IdFresh` side conditions and all
"`≠ none`" hypotheses in §6.3.

---

## 4. Values, runtime terms and source terms as separate types

**Now.**
* Values are a predicate `IsValue : Term R n → Prop`, defined together with `PrimSpine`
  by mutual induction (`FOFU/Sec6_1_Preliminaries/Values.lean`). Reduction rules carry
  premises `IsValue v`.
* The source term type contains the runtime-only forms `star`, `unborrow` and `ref`
  (§6.1). Source programs can therefore mention references.
* `Prim` primitives are applied with ordinary `app`, and `PrimSpine` counts arguments
  against `Prim.arity`.

**Problem.** Every rule that consumes a value needs an `IsValue` premise, and inversion
lemmas on `IsValue` are needed in progress proofs. "Source program" versus "runtime
configuration" is not visible in the types. For example, the examples of §3–§5 could use
`ref` by mistake.

**Proposal.**
* `inductive Val R n` with an embedding `Val.toTerm` (prototype: `Val`, `Val.toTm`,
  `Val.toTm_injective`). Reduction rules take `v : Val R n`. Alternatively, keep
  `IsValue`, but bundle it as `{t // IsValue t}` in the rule signatures.
* Index terms by a phase: `Term R (φ : Phase) n` with `Phase := source | runtime`. The
  constructors `star`, `unborrow` and `ref` would have `φ = runtime`, with an embedding
  from source to runtime. LCU already does something similar for its core grammar
  (`CoreTerm` / `CoreTerm.toTerm`). FOFU could follow the same pattern.
* Saturated primitives: `primApp (p : Prim) (args : Vector (Term R n) p.arity)`.
  Partially applied primitives stay values by construction, which makes `PrimSpine`
  unnecessary.

**Cost / benefit.** Medium cost. It removes a family of premises and inversion lemmas, and
makes the source/runtime distinction of the paper visible.

---

## 5. Index reduction by the heap growth, not by an arbitrary `m`

**Now.** `Step : Heap R n → Term R n → R → Heap R m → Term R m → Prop` allows arbitrary
`m`. Congruence rules take an explicit premise `(h : n ≤ m)` and weaken with
`Term.weaken h` (`FOFU/Sec6_2_Reduction/Step.lean`). The statements of §6.3 use
`Ctx.weakenTo m`, which is defined with `if hj : j.1 < n then … else none` and has no
`n ≤ m` hypothesis (`Statements.lean`).

**Problem.** "The heap only grows" is not part of the type. Each congruence rule repeats
it, and `weakenTo` silently does something meaningless if `m < n`.

**Proposal.** Index steps by the number of new variables:
`Step : Heap R n → Term R n → R → (d : ℕ) → Heap R (n + d) → Term R (n + d) → Prop`.
Weakening is then `Fin.castAdd` / `Fin2` lifting, `weakenTo` becomes a total and obvious
operation, and the `(h : n ≤ m)` premises disappear. Better still, in the style of item 1,
represent "the heap extends the old heap" as a relation `HeapExt H H'`, built from `snoc`.

Related cleanup: heap variables are added at the *end* (`Heap.snoc`, `Fin.last`), while
binders bind index `0`. This is why `Term.openLast` / `openLast2` renamings are needed in
the β-rules. If the heap uses de Bruijn *levels*, or the configuration grows at index `0`,
the opened body is literally `t`, with no renaming.

**Cost / benefit.** Small to medium. It removes about a dozen explicit premises from
`Step` and makes the statements of §6.3 simpler.

---

## 6. Restricted type grammars as types, not predicates

**Now.** Theorem 6.7 restricts references to function-free contents with the recursive
predicates `Ty.FunFree` and `Ty.RefsFunFree`, and `Ctx.RefsFunFree` adds three
`∀`-clauses (`Statements.lean`). `Cloneable A` is a premise of `clone`.
`Term.Allocates` (`resourceAllocator`) is a recursive `Prop` with `∨`.

**Proposal.**
* A grammar of *ground* types `GTy R k` (no `⊸`) with an embedding into `Ty R k`, and
  `Ty.res : ResKind → Ident k → GTy R k → Ty R k` for references. The restriction of
  Theorem 6.7 then holds by construction and its hypotheses disappear from the statement.
  This is the same pattern as LCU's `CoreTy`. If the unrestricted calculus should be
  kept, use an index `Ty R k (allowFun : Bool)` instead.
* `Allocates` and `Cloneable`: make them `Bool`-valued functions with a `decide`
  bridge, or inductive predicates. Then side conditions in examples are closed by
  `decide` and the definitions are executable.

---

## 7. Permissions and grades

* `Perm` is `star | frac (f : Frac)`. `join` takes a proof `f.1 + g.1 ≤ 1`. A partial
  commutative monoid structure on `Perm`, with a relation `PermAdd p q r` and lemmas for
  associativity, commutativity and cancellation, would let `join`, `split` and heap
  compatibility share one algebra. The same structure can serve as the "sum of
  permissions" in the statements of §6.3 (`permSum`), instead of a `match` inside a
  `Finset.sum`.
* `Common/Grades/PreorderedSemiring.lean` defines its own class. Check whether Mathlib's
  `OrderedSemiring` / `IsOrderedRing` (or a minimal `Preorder` + `Semiring` +
  monotonicity mixin) can replace it. This would give `simp`, `ring` and the order
  tactics for free.

---

## 8. Floats

`Term.float : Float → Term R n` uses Lean's built-in `Float`. Its equality is not lawful
(for example, `NaN`), and nothing can be proved about its arithmetic. The paper treats
floats as an opaque base type. Proposal: parameterise by an abstract type of literals,
`(F : Type)`, or use `ℚ` in proofs and `Float` only in examples meant to be executed.

---

## 9. Typing derivations as data, and a verified type checker

**Now.** Typing is a `Prop`. The examples (`Example.lean`, `Sec5_Fractional/Examples.lean`,
226 lines) are long, hand-written derivations, including explicit context additions.

**Proposal.**
* A checker `infer : Ctx … → Term … → Option (…)` for a bidirectional or annotated
  fragment, with a soundness theorem `infer Γ t = some A → HasType Γ t A`. Examples then
  become `by decide` or `by rfl`, and new examples cost nothing. Context splitting can be
  done algorithmically with input/output contexts ("leftover" typing), with a proof that
  this is equivalent to the declarative rules.
* Alternatively, a `Type`-valued derivation `Deriv Γ t A` lets one compute with
  derivations (count uses, extract the split) and recover `HasType` by truncation.

**Cost / benefit.** Medium. It mainly improves examples and regression tests.

---

## 10. Non-vacuity checks for every definition and theorem hypothesis

The previous runs found that Definition 6.4 as printed makes *no* heap with a resource
entry compatible (`Compat.ress_eq_none`). As a consequence, `uniqueness_literal` holds only
vacuously. Such problems are invisible in a correct-by-construction encoding if no one
checks that the hypotheses can be satisfied.

**Proposal.** Add a file `Sanity.lean` with one *inhabitation* example for each
judgment and each theorem hypothesis. For instance: there exist `H`, `Γ` with a resource
entry and `Compat gc H Γ`; there exists a well-typed `t` with a heap for which a step
exists. Treat a failing sanity example as a bug in the encoding.

---

## 11. Small clean-ups noticed while reviewing

* `Step.appL` binds an unused implicit `t₁'`.
* `Ctx.weakenTo` should take `(h : n ≤ m)` and use `Fin.castLE` (see item 5).
* `Ctx.RefsFunFree` uses equations `Γ.vars i = some …`. These could use the existing
  lookup judgments `VarAt` / `RefAt`, for consistency with the README's stated
  convention.
* `Heap` documentation still mentions `H.refs a = some (p, id)` as the reading of
  `RefAt`. This is fine as an explanation, but item 3 would make it obsolete.
* LCU stores the element type for array references in `Hyp` (`a ↦ lin A` means
  `a : Array A`), and the rule `ref` returns `.array h.ty`. A dedicated `RefHyp` type
  for references would make this explicit.

---

## 12. Process: statements first, frozen and reviewed

* Keep a single `Statements.lean` per paper. It should contain only definitions needed to
  *read* the theorems, and it should be the file a reviewer checks against the paper.
  FOFU already does this for §6.3. Extend the practice to Lemmas 6.2/6.3 and the LCU
  theorems.
* For every place where the formalisation deviates from the printed paper (for example,
  the direction of `approx`, the argument order of `withBorrow`, `readRefSplit`, `gcRes`),
  keep a machine-checked "printed version" alongside the repaired one, as is already done
  for `Compat gc` and `readRef`. Then each deviation is justified by a theorem, not only by
  a comment.

## 13. Suggested order of work

1. Item 3, `Frac` in heaps; item 11 clean-ups; item 10 sanity file (small, independent).
2. Item 5 (step indexing) and item 4 (values as a type).
3. Items 1 and 2 together (list contexts with `Fin2` and a generic binding layer). This
   is the big refactor and should be done on a branch, one paper at a time, starting with
   LCU, which is smaller.
4. Item 3, scoped runtime names, on top of the new context type.
5. Item 9 (type checker) once the representation is stable.

## 14. What should *not* change

* Intrinsic scoping by `n` (`Term R n`, `Term R 0` closed), as requested originally. All
  the proposals above extend this idea to the remaining unscoped parts: runtime names,
  heap growth and value-ness.
* Partial operations (context addition, scaling) as relations. This is the right choice.
  Making them total with `Option` would bring back equation premises.
