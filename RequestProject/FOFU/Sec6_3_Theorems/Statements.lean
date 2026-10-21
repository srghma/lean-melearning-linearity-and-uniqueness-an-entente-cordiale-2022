module
public import RequestProject.FOFU.Sec6_3_Theorems.Compat
public import RequestProject.FOFU.Sec6_2_Reduction.Step
public import RequestProject.FOFU.Sec5_1_Equational.Equational
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# The theorems of §6.3, stated as in the paper

Each of Theorem 6.6 – Theorem 6.11 is stated here as a proposition, literally following
the paper, over the formalised typing (`HasType`), reduction (`Step`, `Steps`) and heap
compatibility (`Compat gc`).  The flag `gc` selects Definition 6.4 as printed
(`gc = false`) or with the repair `gcRes` (`gc = true`); see `Compat.lean`.

| paper | statement | result |
| --- | --- | --- |
| Lemma 6.2 (Linear substitution) | `HasType.subst_lin` | proved (`Substitution.lean`) |
| Lemma 6.3 (Graded substitution) | `HasType.subst_grd` | proved (`Substitution.lean`) |
| Theorem 6.6 (Progress) | `Progress gc` | false for both `gc` (`CounterProgress.lean`) |
| Theorem 6.7 (Type preservation) | `Preservation gc` | false for both `gc` (`CounterPreservation.lean`) |
| Lemma 6.8 (Borrow safety) | `BorrowSafety gc` | false for `gc = true` (`CounterBorrowSafety.lean`) |
| Theorem 6.9 (Multi-reduction borrow safety) | `MultiBorrowSafety gc` | false for `gc = true` (`CounterBorrowSafety.lean`) |
| Corollary 6.10 (Uniqueness) | `Uniqueness gc` | vacuously true for `gc = false`, false for `gc = true` |
| Theorem 6.11 (Soundness w.r.t. `≡`) | `EqSoundness gc heapEq` | false for both `gc` and every `heapEq` (`CounterEqSoundness.lean`) |

## Formalisation choices

* "`H ⋈ (Γ₀ + s · Γ)` for all `s`, `Γ₀`": since addition and scaling are partial, this is
  `CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ`.
* After a step the heap may have grown (from `n` to `m` variables), so `Γ₀` is weakened to
  the larger scope (`Ctx.weakenTo`).
* `id ∈ dom(H)` for an identifier means `H.ress id ≠ none` (an entry `id ↦ v_r`).
* `∑_{ref ∈ refs(t), ref ↦_p id ∈ H} p` is `permSum H t id`.
* The restriction of Theorem 6.7 ("reference resources are restricted to non-function
  types") is the hypothesis that every type `Ref_id B` occurring in the context or in the
  result type has a function-free `B` (`Ty.RefsFunFree`).
* In Theorem 6.11 the relation "`H'(v₁) ≡ H''(v₂)`" (equality of the values with the heap
  substituted in, under full β-reduction) is not defined in the paper; it is a parameter
  `heapEq` of the statement.  The disproof works for every such relation.  The paper also
  says the semantics is "extended to full β-reduction" there; the term used in the
  disproof contains no redex at all, so the disproof is unaffected by this extension.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- Moving a context into the scope of `m` variables (in practice `n ≤ m`): variables
beyond the first `n` have no assumption. -/
def Ctx.weakenTo {k n : ℕ} (m : ℕ) (Γ : Ctx R k n) : Ctx R k m :=
  ⟨fun j => if hj : j.1 < n then Γ.vars ⟨j.1, hj⟩ else Option.none, Γ.refs⟩

/-- `Ty.FunFree A`: `A` contains no function type. -/
def Ty.FunFree {k : ℕ} : Ty R k → Prop
  | .lolli _ _ => False
  | .tensor A B => A.FunFree ∧ B.FunFree
  | .unit => True
  | .box _ A => A.FunFree
  | .ex A => A.FunFree
  | .borrow _ A => A.FunFree
  | .res _ _ A => A.FunFree
  | .nat => True
  | .float => True

/-- `Ty.RefsFunFree A`: every reference type `Ref_id B` occurring in `A` has a
function-free `B`. -/
def Ty.RefsFunFree {k : ℕ} : Ty R k → Prop
  | .lolli A B => A.RefsFunFree ∧ B.RefsFunFree
  | .tensor A B => A.RefsFunFree ∧ B.RefsFunFree
  | .unit => True
  | .box _ A => A.RefsFunFree
  | .ex A => A.RefsFunFree
  | .borrow _ A => A.RefsFunFree
  | .res κ _ A => (κ = .ref → A.FunFree) ∧ A.RefsFunFree
  | .nat => True
  | .float => True

/-- The restriction of Theorem 6.7 on a context: all types occurring in it satisfy
`Ty.RefsFunFree`. -/
def Ctx.RefsFunFree {k n : ℕ} (Γ : Ctx R k n) : Prop :=
  (∀ i A, Γ.vars i = some (.lin A) → A.RefsFunFree) ∧
  (∀ i A r, Γ.vars i = some (.grd A r) → A.RefsFunFree) ∧
  (∀ a T, Γ.refs a = some T → T.toTy.RefsFunFree)

/-- `∑_{ref ∈ refs(t), ref ↦_p id ∈ H} p`. -/
noncomputable def permSum {n m : ℕ} (H : Heap R n) (t : Term R m) (id : ℕ) : ℚ :=
  ∑ a ∈ t.refs, match H.refs a with
    | some (p, id') => if id' = id then p else 0
    | none => 0

/-- **Theorem 6.6 (Progress)**: given `Γ ⊢ t : A`, `t` is a value, or for all `s` and
`Γ₀`, if `H ⋈ (Γ₀ + s · Γ)` then `H ⊢ t ⤳_s H' ⊢ t'` for some `H'`, `t'`. -/
def Progress (gc : Bool) : Prop :=
  ∀ {n : ℕ} (Γ : Ctx R 0 n) (t : Term R n) (A : Ty R 0), HasType Γ t A →
    IsValue t ∨
    ∀ (s : R) (Γ₀ Γs Δ : Ctx R 0 n) (H : Heap R n),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ →
      ∃ (m : ℕ) (H' : Heap R m) (t' : Term R m), Step H t s H' t'

/-- **Theorem 6.7 (Type preservation)**: for `Γ ⊢ t : A` (with reference contents
restricted to non-function types), `H ⋈ (Γ₀ + s · Γ)` and `H ⊢ t ⤳_s H' ⊢ t'`, there is
`Γ'` with `Γ' ⊢ t' : A` and `H' ⋈ (Γ₀ + s · Γ')`. -/
def Preservation (gc : Bool) : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx R 0 n) (t : Term R n) (A : Ty R 0), HasType Γ t A →
    Γ.RefsFunFree → A.RefsFunFree →
    ∀ (s : R) (Γ₀ Γs Δ : Ctx R 0 n) (H : Heap R n) (H' : Heap R m) (t' : Term R m),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Step H t s H' t' →
      ∃ (Γ' Γs' Δ' : Ctx R 0 m),
        HasType Γ' t' A ∧ CtxScale s Γ' Γs' ∧ CtxAdd (Γ₀.weakenTo m) Γs' Δ' ∧ Compat gc H' Δ'

/-- **Lemma 6.8 (Borrow safety)**: for `Γ ⊢ t : A`, `H ⋈ (Γ₀ + s · Γ)` and
`H ⊢ t ⤳_s H' ⊢ t'`, every `id ∈ dom(H)` whose permissions in `t` sum to `1` has
permissions in `t'` summing to `0` or `1`, and every new `id' ∈ dom(H') \ dom(H)` has
permissions in `t'` summing to `1`. -/
def BorrowSafety (gc : Bool) : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx R 0 n) (t : Term R n) (A : Ty R 0), HasType Γ t A →
    ∀ (s : R) (Γ₀ Γs Δ : Ctx R 0 n) (H : Heap R n) (H' : Heap R m) (t' : Term R m),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Step H t s H' t' →
      (∀ id, H.ress id ≠ none → permSum H t id = 1 →
        permSum H' t' id = 0 ∨ permSum H' t' id = 1) ∧
      (∀ id', H'.ress id' ≠ none → H.ress id' = none → permSum H' t' id' = 1)

/-- **Theorem 6.9 (Multi-reduction borrow safety)**: for `Γ ⊢ t : A`,
`H ⋈ (Γ₀ + s · Γ)` and `H ⊢ t ⇒_s H' ⊢ v`, every `id ∈ dom(H)` whose permissions in `t`
sum to `1` has exactly one reference `ref' ↦_1 id` in `H'`, and for every new
`id' ∈ dom(H') \ dom(H)` and every `ref ∈ refs(v)` there is exactly one
`ref' ↦_1 id'` in `H'`. -/
def MultiBorrowSafety (gc : Bool) : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx R 0 n) (t : Term R n) (A : Ty R 0), HasType Γ t A →
    ∀ (s : R) (Γ₀ Γs Δ : Ctx R 0 n) (H : Heap R n) (H' : Heap R m) (v : Term R m),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Steps H t s H' v → IsValue v →
      (∀ id, H.ress id ≠ none → permSum H t id = 1 → ∃! a, H'.refs a = some (1, id)) ∧
      (∀ id', H'.ress id' ≠ none → H.ress id' = none →
        ∀ a ∈ v.refs, ∃! a', H'.refs a' = some (1, id'))

/-- **Corollary 6.10 (Uniqueness)**: for `Γ ⊢ t : *A`, `H ⋈ (Γ₀ + s · Γ)` and
`H ⊢ t ⇒_s H' ⊢ *v`, for all `id ∈ dom(H)`: every `ref ∈ refs(t)` with `ref ↦_1 id` in
`H` still has `ref ↦_1 id` in `H'`, and for every new `id' ∈ dom(H') \ dom(H)` and every
`ref ∈ refs(v)` there is exactly one `ref' ↦_1 id'` in `H'`. -/
def Uniqueness (gc : Bool) : Prop :=
  ∀ {n m : ℕ} (Γ : Ctx R 0 n) (t : Term R n) (A : Ty R 0), HasType Γ t (Ty.star A) →
    ∀ (s : R) (Γ₀ Γs Δ : Ctx R 0 n) (H : Heap R n) (H' : Heap R m) (v : Term R m),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Steps H t s H' (.star v) → IsValue v →
      ∀ id, H.ress id ≠ none →
        (∀ a ∈ t.refs, H.refs a = some (1, id) → H'.refs a = some (1, id)) ∧
        (∀ id', H'.ress id' ≠ none → H.ress id' = none →
          ∀ a ∈ v.refs, ∃! a', H'.refs a' = some (1, id'))

/-- **Theorem 6.11 (Soundness with respect to the equational theory)**: for
`Γ ⊢ t₁ : A`, `Γ ⊢ t₂ : A`, `t₁ ≡ t₂` and `H ⋈ Γ`, there are multi-reductions
`H ⊢ t₁ ⇒_1 H' ⊢ v₁` and `H ⊢ t₂ ⇒_1 H'' ⊢ v₂` to values with `H'(v₁) ≡ H''(v₂)`
(the relation `heapEq`). -/
def EqSoundness (gc : Bool)
    (heapEq : ∀ {m₁ m₂ : ℕ}, Heap R m₁ → Term R m₁ → Heap R m₂ → Term R m₂ → Prop) : Prop :=
  ∀ {n : ℕ} (Γ : Ctx R 0 n) (t₁ t₂ : Term R n) (A : Ty R 0) (H : Heap R n),
    HasType Γ t₁ A → HasType Γ t₂ A → t₁ ≡ t₂ → Compat gc H Γ →
    ∃ (m₁ : ℕ) (H₁ : Heap R m₁) (v₁ : Term R m₁) (m₂ : ℕ) (H₂ : Heap R m₂) (v₂ : Term R m₂),
      Steps H t₁ 1 H₁ v₁ ∧ IsValue v₁ ∧ Steps H t₂ 1 H₂ v₂ ∧ IsValue v₂ ∧ heapEq H₁ v₁ H₂ v₂

end FOFU
