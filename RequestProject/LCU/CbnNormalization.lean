module
public import RequestProject.LCU.CbnSemantics

/-!
# Termination of call-by-name evaluation

We prove that the call-by-name reduction `CbnStep` of `CbnSemantics.lean` terminates
on well-typed closed primitive-free terms: every such term reduces to a value
(`cbn_normalization`).  Together with subject reduction this gives that evaluation of a
well-typed closed term always ends in a value of the same type (`cbn_eval`), and by
determinism this value is unique (`cbn_value_unique`).

The proof is by a (unary) logical relation `Reducible A t` ("`t` is reducible at type
`A`") on closed terms, defined by recursion on `A`, and the fundamental lemma
`HasTypeD.reducible`: a well-typed term, closed by a substitution of reducible terms
for its free variables, is reducible.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Congruence for multi-step reduction -/

namespace CbnSteps

variable {n : ℕ}

/-- Multi-step reduction is closed under any one-step congruence `f`. -/
lemma congr {t t' : Term n} (f : Term n → Term n) (hf : ∀ a b, CbnStep a b → CbnStep (f a) (f b))
    (h : CbnSteps t t') : CbnSteps (f t) (f t') :=
  Relation.ReflTransGen.lift f hf h

lemma trans {t₁ t₂ t₃ : Term n} (h₁ : CbnSteps t₁ t₂) (h₂ : CbnSteps t₂ t₃) :
    CbnSteps t₁ t₃ := Relation.ReflTransGen.trans h₁ h₂

lemma single {t₁ t₂ : Term n} (h : CbnStep t₁ t₂) : CbnSteps t₁ t₂ :=
  Relation.ReflTransGen.single h

lemma refl' (t : Term n) : CbnSteps t t := Relation.ReflTransGen.refl

end CbnSteps

/-! ## The logical relation -/

/-- `Reducible A t`: the closed term `t` evaluates to a value of the shape of `A` whose
components are again reducible. -/
def Reducible : Ty → Term 0 → Prop
  | .lolli A B, t => ∃ b, CbnSteps t (lam b) ∧ ∀ u, Reducible A u → Reducible B (subst1 u b)
  | .tensor A B, t => ∃ t₁ t₂, CbnSteps t (pair t₁ t₂) ∧ Reducible A t₁ ∧ Reducible B t₂
  | .unit, t => CbnSteps t unit
  | .bang A, t => ∃ u, CbnSteps t (bang u) ∧ Reducible A u
  | .star A, t => ∃ u, CbnSteps t (star u) ∧ Reducible A u
  | .array _, t => ∃ a, CbnSteps t (ref a)
  | .nat, t => ∃ k, CbnSteps t (nat k)
  | .float, t => ∃ x, CbnSteps t (float x)

/-- Reducibility is closed under backwards reduction. -/
lemma Reducible.of_steps {A : Ty} {t t' : Term 0} (h : Reducible A t') (hs : CbnSteps t t') :
    Reducible A t := by
  cases A with
  | lolli A B => obtain ⟨b, h₁, h₂⟩ := h; exact ⟨b, hs.trans h₁, h₂⟩
  | tensor A B => obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h; exact ⟨t₁, t₂, hs.trans h₁, h₂, h₃⟩
  | unit => exact CbnSteps.trans hs h
  | bang A => obtain ⟨u, h₁, h₂⟩ := h; exact ⟨u, hs.trans h₁, h₂⟩
  | star A => obtain ⟨u, h₁, h₂⟩ := h; exact ⟨u, hs.trans h₁, h₂⟩
  | array _ => obtain ⟨a, h₁⟩ := h; exact ⟨a, hs.trans h₁⟩
  | nat => obtain ⟨k, h₁⟩ := h; exact ⟨k, hs.trans h₁⟩
  | float => obtain ⟨x, h₁⟩ := h; exact ⟨x, hs.trans h₁⟩

/-- A reducible term evaluates to a value. -/
lemma Reducible.eval {A : Ty} {t : Term 0} (h : Reducible A t) :
    ∃ v, CbnSteps t v ∧ IsValue v := by
  cases A with
  | lolli A B => obtain ⟨b, h₁, -⟩ := h; exact ⟨_, h₁, .lam _⟩
  | tensor A B => obtain ⟨t₁, t₂, h₁, -⟩ := h; exact ⟨_, h₁, .pair _ _⟩
  | unit => exact ⟨_, h, .unit⟩
  | bang A => obtain ⟨u, h₁, -⟩ := h; exact ⟨_, h₁, .bang _⟩
  | star A => obtain ⟨u, h₁, -⟩ := h; exact ⟨_, h₁, .star _⟩
  | array _ => obtain ⟨a, h₁⟩ := h; exact ⟨_, h₁, .ref _⟩
  | nat => obtain ⟨k, h₁⟩ := h; exact ⟨_, h₁, .nat _⟩
  | float => obtain ⟨x, h₁⟩ := h; exact ⟨_, h₁, .float _⟩

/-! ## Substitution lemmas for closing substitutions -/

lemma subst1_subst_up {n : ℕ} (σ : Fin n → Term 0) (u : Term 0) (t : Term (n + 1)) :
    subst1 u (subst (Subst.up σ) t) = subst (Fin.cons u σ) t := by
  simp only [subst1, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact subst1_rename_succ u (σ i)

lemma subst2_subst_up_up {n : ℕ} (σ : Fin n → Term 0) (u₁ u₂ : Term 0) (t : Term (n + 2)) :
    subst2 u₁ u₂ (subst (Subst.up (Subst.up σ)) t) =
      subst (Fin.cons u₂ (Fin.cons u₁ σ)) t := by
  simp only [subst2, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      show _ = σ i
      simp only [Function.comp, Subst.up_succ, subst_rename]
      conv_rhs => rw [← subst_var (σ i)]
      rfl

/-! ## The fundamental lemma -/

/-- A closing substitution `σ` is reducible for `Γ` if it maps each variable with an
assumption `x : A` or `x : [A]` in `Γ` to a term reducible at `A`. -/
def RedSubst {n : ℕ} (Γ : Ctx n) (σ : Fin n → Term 0) : Prop :=
  ∀ i h, Γ (.inl i) = some h → Reducible h.ty (σ i)

lemma RedSubst.left {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {σ : Fin n → Term 0} (hσ : RedSubst Γ σ)
    (hadd : Γ₁.Add Γ₂ Γ) : RedSubst Γ₁ σ := by
  intro i h hi
  have := hadd (.inl i)
  rw [hi] at this
  generalize Γ₂ (.inl i) = b at this
  generalize hc : Γ (.inl i) = c at this
  cases this <;> exact hσ i _ hc

lemma RedSubst.right {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {σ : Fin n → Term 0} (hσ : RedSubst Γ σ)
    (hadd : Γ₁.Add Γ₂ Γ) : RedSubst Γ₂ σ := hσ.left hadd.comm

lemma RedSubst.cons {n : ℕ} {Γ : Ctx n} {σ : Fin n → Term 0} (hσ : RedSubst Γ σ) {h : Hyp}
    {u : Term 0} (hu : Reducible h.ty u) : RedSubst (Γ.cons (some h)) (Fin.cons u σ) := by
  intro i h' hi
  cases i using Fin.cases with
  | zero => cases hi; exact hu
  | succ i => exact hσ i h' hi

lemma RedSubst.refsOnly {n : ℕ} (Γ : Ctx n) (σ : Fin n → Term 0) :
    RedSubst Γ.refsOnly σ := by
  intro i h hi; simp at hi

/-- **Fundamental lemma** of the logical relation. -/
theorem HasTypeD.reducible {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A)
    (hp : t.PrimFree) {σ : Fin n → Term 0} (hσ : RedSubst Γ σ) :
    Reducible A (subst σ t) := by
  induction ht with
  | var hi _ => exact hσ _ _ hi
  | abs _ ih =>
    refine ⟨_, CbnSteps.refl' _, fun u hu => ?_⟩
    rw [subst1_subst_up]
    exact ih hp (hσ.cons (h := .lin _) hu)
  | app _ _ hadd ih₁ ih₂ =>
    obtain ⟨b, hs, hb⟩ := ih₁ hp.1 (hσ.left hadd)
    exact (hb _ (ih₂ hp.2 (hσ.right hadd))).of_steps
      ((hs.congr _ fun _ _ => .app _).trans (CbnSteps.single (.betaLolli _ _)))
  | tensorI _ _ hadd ih₁ ih₂ =>
    exact ⟨_, _, CbnSteps.refl' _, ih₁ hp.1 (hσ.left hadd), ih₂ hp.2 (hσ.right hadd)⟩
  | tensorE _ _ hadd ih₁ ih₂ =>
    obtain ⟨u₁, u₂, hs, hu₁, hu₂⟩ := ih₁ hp.1 (hσ.left hadd)
    have := ih₂ hp.2 (((hσ.right hadd).cons (h := .lin _) hu₁).cons (h := .lin _) hu₂)
    rw [← subst2_subst_up_up] at this
    exact this.of_steps ((hs.congr _ fun _ _ => .letPair _).trans (CbnSteps.single (.betaTensor _ _ _)))
  | unitI _ => exact CbnSteps.refl' _
  | unitE _ _ hadd ih₁ ih₂ =>
    have hs : CbnSteps _ unit := ih₁ hp.1 (hσ.left hadd)
    exact (ih₂ hp.2 (hσ.right hadd)).of_steps
      ((hs.congr _ fun _ _ => .letUnit _).trans (CbnSteps.single (.betaUnit _)))
  | bangI _ _ ih => exact ⟨_, CbnSteps.refl' _, ih hp hσ⟩
  | bangE _ _ hadd ih₁ ih₂ =>
    obtain ⟨u, hs, hu⟩ := ih₁ hp.1 (hσ.left hadd)
    have := ih₂ hp.2 ((hσ.right hadd).cons (h := .nonlin _) hu)
    rw [← subst1_subst_up] at this
    exact this.of_steps ((hs.congr _ fun _ _ => .letBang _).trans (CbnSteps.single (.betaBang _ _)))
  | borrow _ ih =>
    obtain ⟨u, hs, hu⟩ := ih hp hσ
    exact ⟨u, (hs.congr _ fun _ _ => .borrow).trans (CbnSteps.single (.betaBorrow _)), hu⟩
  | copy _ _ hadd ih₁ ih₂ =>
    obtain ⟨u, hs, hu⟩ := ih₁ hp.1 (hσ.left hadd)
    have := ih₂ hp.2 ((hσ.right hadd).cons (h := .lin (.star _))
      (u := star u) ⟨u, CbnSteps.refl' _, hu⟩)
    rw [← subst1_subst_up] at this
    exact this.of_steps ((hs.congr _ fun _ _ => .copy _).trans (CbnSteps.single (.betaCopy _ _)))
  | nec _ _ ih => exact ⟨_, CbnSteps.refl' _, ih hp (RedSubst.refsOnly _ σ)⟩
  | natI _ => exact ⟨_, CbnSteps.refl' _⟩
  | floatI _ => exact ⟨_, CbnSteps.refl' _⟩
  | prim _ => exact hp.elim
  | ref _ _ => exact ⟨_, CbnSteps.refl' _⟩

/-! ## Termination -/

/-- **Termination of evaluation.** Every well-typed closed primitive-free term reduces
(in the call-by-name semantics `CbnStep`) to a value. -/
theorem cbn_normalization {Γ : Ctx 0} {t : Term 0} {A : Ty} (ht : HasType Γ t A)
    (hp : t.PrimFree) : ∃ v, CbnSteps t v ∧ IsValue v := by
  have h := (hasType_iff_hasTypeD.1 ht).reducible hp (σ := Term.var)
    (fun i => i.elim0)
  rw [subst_var] at h
  exact h.eval

/-- **Evaluation.** A well-typed closed primitive-free term (in a context whose runtime
array references are non-linear, e.g. the empty context) evaluates to a value of the
same type. -/
theorem cbn_eval {Γ : Ctx 0} {t : Term 0} {A : Ty} (hr : Γ.RefsNonLin) (ht : HasType Γ t A)
    (hp : t.PrimFree) : ∃ v, CbnSteps t v ∧ IsValue v ∧ HasType Γ v A := by
  obtain ⟨v, hs, hv⟩ := cbn_normalization ht hp
  exact ⟨v, hs, hv, hs.preserves (Ctx.noVars_zero Γ) hr ht⟩

/-- Reduction sequences ending in values are unique: the value a term evaluates to is
uniquely determined. -/
theorem cbn_value_unique {n : ℕ} {t v₁ v₂ : Term n} (h₁ : CbnSteps t v₁) (hv₁ : IsValue v₁)
    (h₂ : CbnSteps t v₂) (hv₂ : IsValue v₂) : v₁ = v₂ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on generalizing v₂ with
  | refl =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hs _ _ => exact (hv₁.not_cbnStep hs).elim
  | head hs hrest ih =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl => exact (hv₂.not_cbnStep hs).elim
    | head hs' hrest' _ =>
      rw [CbnStep.deterministic hs hs'] at ih
      exact ih hrest' hv₂

/-! ## The core calculus -/

/-- Terms of the core grammar of Section 3.1 contain no array primitives. -/
lemma CoreTerm.primFree {n : ℕ} (t : CoreTerm n) : t.toTerm.PrimFree := by
  induction t <;> simp_all [Term.PrimFree]

/-- **Termination for the core calculus.** Every well-typed closed term of the core grammar
(Section 3.1) evaluates, in the call-by-name semantics `CbnStep`, to (the embedding of) an
element of the value grammar `Value 0`, of the same type. -/
theorem cbn_eval_core {Γ : Ctx 0} {t : CoreTerm 0} {A : Ty} (hr : Γ.RefsNonLin)
    (ht : HasType Γ t.toTerm A) :
    ∃ v : Value 0, CbnSteps t.toTerm v.toTerm ∧ HasType Γ v.toTerm A := by
  obtain ⟨_, hs, ⟨v, rfl⟩, hv⟩ := cbn_eval hr ht t.primFree
  exact ⟨v, hs, hv⟩

end LCU
