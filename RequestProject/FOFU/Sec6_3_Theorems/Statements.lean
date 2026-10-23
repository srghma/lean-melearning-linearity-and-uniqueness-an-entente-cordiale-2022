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
| Lemma 6.8 (Borrow safety) | `BorrowSafety gc` | true for `gc = false` (`BorrowSafetyLiteral.lean`), false for `gc = true` (`CounterBorrowSafety.lean`) |
| Theorem 6.9 (Multi-reduction borrow safety) | `MultiBorrowSafety gc` | false for both `gc` (`CounterMultiBorrowLiteral.lean`, `CounterBorrowSafety.lean`) |
| Corollary 6.10 (Uniqueness) | `Uniqueness gc` | vacuously true for `gc = false`, false for `gc = true` |
| Theorem 6.11 (Soundness w.r.t. `≡`) | `EqSoundness gc heapEq` | false for both `gc` and every `heapEq` (`CounterEqSoundness.lean`) |

## Formalisation choices

* A configuration is a heap `H : Heap R n ρ ι` and a term `t : Term R n ρ`, typed in a
  context `Γ : TCtx R ι n ρ` (the identifiers of the types are those of the heap).
* "`H ⋈ (Γ₀ + s · Γ)` for all `s`, `Γ₀`": since addition and scaling are partial, this is
  `CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ`.
* After a step `H ⊢ t ⤳_s H' ⊢ t'` the configuration has grown by `d` variables, `e`
  references and `f` identifiers.  The type `A` and the frame `Γ₀` are moved into the
  larger scope (`Ty.ren (Var.shiftN f)`, `TCtx.lift`); the new names get no assumption.
* `id ∈ dom(H)` for an identifier means `H.ress.get id ≠ none` (an entry `id ↦ v_r`).
  After a step, the old identifier `id` is called `Var.shiftN f id`; after a reduction
  sequence (`Steps`) the old references and identifiers are mapped by `θr` and `θi`.
  An identifier `id' ∈ dom(H') \ dom(H)` is one with an entry in `H'` that is not the
  image of an identifier with an entry in `H`.
* `∑_{ref ∈ refs(t), ref ↦_p id ∈ H} p` is `permSum H t id`.
* The restriction of Theorem 6.7 ("reference resources are restricted to non-function
  types") is the hypothesis that every type `Ref_id B` occurring in the context or in the
  result type has a function-free `B` (`Ty.refsFunFree`, `TCtx.RefsFunFree`).
* In Theorem 6.11 the relation "`H'(v₁) ≡ H''(v₂)`" (equality of the values with the heap
  substituted in, under full β-reduction) is not defined in the paper; it is a parameter
  `heapEq` of the statement.  The disproof works for every such relation.  The paper also
  says the semantics is "extended to full β-reduction" there; the term used in the
  disproof contains no redex at all, so the disproof is unaffected by this extension.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- Moving a context into a scope with `d` more variables, `e` more references and `f`
more identifiers; the new variables and references have no assumption. -/
def TCtx.lift {k n ρ : ℕ} (d e f : ℕ) (Γ : TCtx R k n ρ) : TCtx R (k + f) (n + d) (ρ + e) :=
  ⟨(Γ.refs.map (Option.map (RefTy.ren (Var.shiftN f)))).pad none e,
    (Γ.vars.map (Option.map (Assm.ren (Var.shiftN f)))).pad none d⟩

/-- `Ty.funFree A`: `A` contains no function type. -/
def Ty.funFree {k : ℕ} : Ty R k → Bool
  | .lolli _ _ => false
  | .tensor A B => A.funFree && B.funFree
  | .unit => true
  | .box _ A => A.funFree
  | .ex A => A.funFree
  | .borrow _ A => A.funFree
  | .res _ _ A => A.funFree
  | .nat => true
  | .float => true

/-- `Ty.refsFunFree A`: every reference type `Ref_id B` occurring in `A` has a
function-free `B`. -/
def Ty.refsFunFree {k : ℕ} : Ty R k → Bool
  | .lolli A B => A.refsFunFree && B.refsFunFree
  | .tensor A B => A.refsFunFree && B.refsFunFree
  | .unit => true
  | .box _ A => A.refsFunFree
  | .ex A => A.refsFunFree
  | .borrow _ A => A.refsFunFree
  | .res .ref _ A => A.funFree && A.refsFunFree
  | .res _ _ A => A.refsFunFree
  | .nat => true
  | .float => true

/-- The type of an assumption (`x : A` or `x : [A]_r`). -/
def Assm.ty {k : ℕ} : Assm R k → Ty R k
  | .lin A => A
  | .grd A _ => A

/-- The restriction of Theorem 6.7 on a context: all types occurring in it satisfy
`Ty.refsFunFree`. -/
def TCtx.RefsFunFree {k n ρ : ℕ} (Γ : TCtx R k n ρ) : Prop :=
  Γ.vars.All (fun o => ∀ a ∈ o, a.ty.refsFunFree) ∧
    Γ.refs.All (fun o => ∀ T ∈ o, T.toTy.refsFunFree)

/-- The permission `p` of an entry `ref ↦_p id'` on the identifier `id` (`0` if the entry
is absent or points to another identifier). -/
def permOf {ι : ℕ} (id : Var ι) : Option (Frac × Var ι) → ℚ
  | some (p, id') => if id' = id then p.1 else 0
  | none => 0

/-- `∑_{ref ∈ refs(t), ref ↦_p id ∈ H} p`. -/
def permSum {n ρ ι : ℕ} (H : Heap R n ρ ι) (t : Term R n ρ) (id : Var ι) : ℚ :=
  ∑ a ∈ t.refs, permOf id (H.refs.get a)

/-- **Theorem 6.6 (Progress)**: given `Γ ⊢ t : A`, `t` is a value, or for all `s` and
`Γ₀`, if `H ⋈ (Γ₀ + s · Γ)` then `H ⊢ t ⤳_s H' ⊢ t'` for some `H'`, `t'`. -/
def Progress (gc : Bool) : Prop :=
  ∀ {n ρ ι : ℕ} (Γ : TCtx R ι n ρ) (t : Term R n ρ) (A : Ty R ι), HasType Γ t A →
    IsValue t ∨
    ∀ (s : R) (Γ₀ Γs Δ : TCtx R ι n ρ) (H : Heap R n ρ ι),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ →
      ∃ (d e f : ℕ) (H' : Heap R (n + d) (ρ + e) (ι + f)) (t' : Term R (n + d) (ρ + e)),
        Step H t s d e f H' t'

/-- **Theorem 6.7 (Type preservation)**: for `Γ ⊢ t : A` (with reference contents
restricted to non-function types), `H ⋈ (Γ₀ + s · Γ)` and `H ⊢ t ⤳_s H' ⊢ t'`, there is
`Γ'` with `Γ' ⊢ t' : A` and `H' ⋈ (Γ₀ + s · Γ')`. -/
def Preservation (gc : Bool) : Prop :=
  ∀ {n ρ ι d e f : ℕ} (Γ : TCtx R ι n ρ) (t : Term R n ρ) (A : Ty R ι), HasType Γ t A →
    Γ.RefsFunFree → A.refsFunFree →
    ∀ (s : R) (Γ₀ Γs Δ : TCtx R ι n ρ) (H : Heap R n ρ ι)
      (H' : Heap R (n + d) (ρ + e) (ι + f)) (t' : Term R (n + d) (ρ + e)),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Step H t s d e f H' t' →
      ∃ (Γ' Γs' Δ' : TCtx R (ι + f) (n + d) (ρ + e)),
        HasType Γ' t' (A.ren (Var.shiftN f)) ∧ CtxScale s Γ' Γs' ∧
          CtxAdd (Γ₀.lift d e f) Γs' Δ' ∧ Compat gc H' Δ'

/-- **Lemma 6.8 (Borrow safety)**: for `Γ ⊢ t : A`, `H ⋈ (Γ₀ + s · Γ)` and
`H ⊢ t ⤳_s H' ⊢ t'`, every `id ∈ dom(H)` whose permissions in `t` sum to `1` has
permissions in `t'` summing to `0` or `1`, and every new `id' ∈ dom(H') \ dom(H)` has
permissions in `t'` summing to `1`. -/
def BorrowSafety (gc : Bool) : Prop :=
  ∀ {n ρ ι d e f : ℕ} (Γ : TCtx R ι n ρ) (t : Term R n ρ) (A : Ty R ι), HasType Γ t A →
    ∀ (s : R) (Γ₀ Γs Δ : TCtx R ι n ρ) (H : Heap R n ρ ι)
      (H' : Heap R (n + d) (ρ + e) (ι + f)) (t' : Term R (n + d) (ρ + e)),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Step H t s d e f H' t' →
      (∀ id, H.ress.get id ≠ none → permSum H t id = 1 →
        permSum H' t' (Var.shiftN f id) = 0 ∨ permSum H' t' (Var.shiftN f id) = 1) ∧
      (∀ id', H'.ress.get id' ≠ none → (∀ id, Var.shiftN f id = id' → H.ress.get id = none) →
        permSum H' t' id' = 1)

/-- **Theorem 6.9 (Multi-reduction borrow safety)**: for `Γ ⊢ t : A`,
`H ⋈ (Γ₀ + s · Γ)` and `H ⊢ t ⇒_s H' ⊢ v`, every `id ∈ dom(H)` whose permissions in `t`
sum to `1` has exactly one reference `ref' ↦_1 id` in `H'`, and for every new
`id' ∈ dom(H') \ dom(H)` and every `ref ∈ refs(v)` there is exactly one
`ref' ↦_1 id'` in `H'`. -/
def MultiBorrowSafety (gc : Bool) : Prop :=
  ∀ {n ρ ι n' ρ' ι' : ℕ} (Γ : TCtx R ι n ρ) (t : Term R n ρ) (A : Ty R ι), HasType Γ t A →
    ∀ (s : R) (Γ₀ Γs Δ : TCtx R ι n ρ) (H : Heap R n ρ ι) (H' : Heap R n' ρ' ι')
      (v : Term R n' ρ') (θr : Var ρ → Var ρ') (θi : Var ι → Var ι'),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Steps H t s H' v θr θi → IsValue v →
      (∀ id, H.ress.get id ≠ none → permSum H t id = 1 →
        ∃! a, H'.refs.get a = some (Frac.one, θi id)) ∧
      (∀ id', H'.ress.get id' ≠ none → (∀ id, θi id = id' → H.ress.get id = none) →
        ∀ a ∈ v.refs, ∃! a', H'.refs.get a' = some (Frac.one, id'))

/-- **Corollary 6.10 (Uniqueness)**: for `Γ ⊢ t : *A`, `H ⋈ (Γ₀ + s · Γ)` and
`H ⊢ t ⇒_s H' ⊢ *v`, for all `id ∈ dom(H)`: every `ref ∈ refs(t)` with `ref ↦_1 id` in
`H` still has `ref ↦_1 id` in `H'`, and for every new `id' ∈ dom(H') \ dom(H)` and every
`ref ∈ refs(v)` there is exactly one `ref' ↦_1 id'` in `H'`. -/
def Uniqueness (gc : Bool) : Prop :=
  ∀ {n ρ ι n' ρ' ι' : ℕ} (Γ : TCtx R ι n ρ) (t : Term R n ρ) (A : Ty R ι),
    HasType Γ t (Ty.star A) →
    ∀ (s : R) (Γ₀ Γs Δ : TCtx R ι n ρ) (H : Heap R n ρ ι) (H' : Heap R n' ρ' ι')
      (v : Term R n' ρ') (θr : Var ρ → Var ρ') (θi : Var ι → Var ι'),
      CtxScale s Γ Γs → CtxAdd Γ₀ Γs Δ → Compat gc H Δ → Steps H t s H' (.star v) θr θi →
      IsValue v →
      ∀ id, H.ress.get id ≠ none →
        (∀ a ∈ t.refs, H.refs.get a = some (Frac.one, id) →
          H'.refs.get (θr a) = some (Frac.one, θi id)) ∧
        (∀ id', H'.ress.get id' ≠ none → (∀ id, θi id = id' → H.ress.get id = none) →
          ∀ a ∈ v.refs, ∃! a', H'.refs.get a' = some (Frac.one, id'))

/-- **Theorem 6.11 (Soundness with respect to the equational theory)**: for
`Γ ⊢ t₁ : A`, `Γ ⊢ t₂ : A`, `t₁ ≡ t₂` and `H ⋈ Γ`, there are multi-reductions
`H ⊢ t₁ ⇒_1 H' ⊢ v₁` and `H ⊢ t₂ ⇒_1 H'' ⊢ v₂` to values with `H'(v₁) ≡ H''(v₂)`
(the relation `heapEq`). -/
def EqSoundness (gc : Bool)
    (heapEq : ∀ {n₁ ρ₁ ι₁ n₂ ρ₂ ι₂ : ℕ}, Heap R n₁ ρ₁ ι₁ → Term R n₁ ρ₁ →
      Heap R n₂ ρ₂ ι₂ → Term R n₂ ρ₂ → Prop) : Prop :=
  ∀ {n ρ ι : ℕ} (Γ : TCtx R ι n ρ) (t₁ t₂ : Term R n ρ) (A : Ty R ι) (H : Heap R n ρ ι),
    HasType Γ t₁ A → HasType Γ t₂ A → t₁ ≡ t₂ → Compat gc H Γ →
    ∃ (n₁ ρ₁ ι₁ : ℕ) (H₁ : Heap R n₁ ρ₁ ι₁) (v₁ : Term R n₁ ρ₁) (θr₁ : Var ρ → Var ρ₁)
      (θi₁ : Var ι → Var ι₁) (n₂ ρ₂ ι₂ : ℕ) (H₂ : Heap R n₂ ρ₂ ι₂) (v₂ : Term R n₂ ρ₂)
      (θr₂ : Var ρ → Var ρ₂) (θi₂ : Var ι → Var ι₂),
      Steps H t₁ 1 H₁ v₁ θr₁ θi₁ ∧ IsValue v₁ ∧ Steps H t₂ 1 H₂ v₂ θr₂ θi₂ ∧ IsValue v₂ ∧
        heapEq H₁ v₁ H₂ v₂

end FOFU
