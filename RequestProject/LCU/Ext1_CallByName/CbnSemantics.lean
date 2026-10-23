module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping

/-!
# A substitution-based call-by-name semantics and syntactic type safety

The heap model of Section 3.4 is call-by-name.  As shown in `Counter*.lean`, the
metatheorems of Section 3.5 fail for the heap rules as given in the text.  Here we
give a *repaired*, substitution-based call-by-name reduction `CbnStep` for the
array-free fragment, which mirrors the heap rules with heap bindings replaced by
substitution:

* `(λx. t) u ⟶ [u/x]t`
* `let (x, y) = (t₁, t₂) in t ⟶ [t₁/x, t₂/y]t`
* `let unit = unit in t ⟶ t`
* `let! x = !u in t ⟶ [u/x]t`
* `&(*t) ⟶ !t` (with no value restriction on `t`: this is the repair of the
  progress counterexample `not_progress`)
* `copy !u as x in t ⟶ [*u/x]t`

plus congruence rules reducing the eliminated term of every elimination form.

We prove for terms without free variables (in particular for closed terms `Term 0 ρ`)
in contexts whose runtime array references are non-linear:

* **subject reduction** (`CbnStep.preserves`, `CbnSteps.preserves`);
* **progress** for primitive-free terms (`cbn_progress`);
* hence **syntactic type safety** (`cbn_type_safety`): a well-typed closed
  primitive-free term never reduces to a stuck term;
* determinism of the reduction (`CbnStep.deterministic`) and that values are normal
  forms (`IsValue.not_cbnStep`).

The restriction to terms without free variables is necessary: `copy !x as y in *y`
is typable with `x : [A]`, but its reduct `*x` is not, since `nec` forbids
variable assumptions.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Primitive-free terms -/

/-- The operators that are array primitives. -/
def Op.IsPrim {ρ : ℕ} (o : Op ρ) : Prop := ∃ p, o = Op.prim p

/-- A term is primitive-free if it contains no array primitive `newArray`,
`readArray`, `writeArray`, `deleteArray`. -/
def Term.PrimFree {n ρ : ℕ} (t : Term n ρ) : Prop := ¬ Binding.Tm.HasOp Op.IsPrim t

section PrimFree

variable {n ρ : ℕ}

open Binding in
/-- Unfolding `PrimFree` on an operator application. -/
lemma Term.primFree_op {o : Op ρ} {as : Args (sig ρ) n (Op.arity o)} :
    Term.PrimFree (Tm.op o as : Term n ρ) ↔ ¬ o.IsPrim ∧ ¬ Args.HasOp Op.IsPrim as := by
  simp [Term.PrimFree, Tm.hasOp_op_iff]

open Binding in
lemma Term.primFree_args {k : ℕ} {ks : List ℕ} {t : Tm (sig ρ) (n + k)}
    {as : Args (sig ρ) n ks} :
    ¬ Args.HasOp Op.IsPrim (.cons t as) ↔ Term.PrimFree t ∧ ¬ Args.HasOp Op.IsPrim as := by
  simp [Term.PrimFree, Args.hasOp_cons_iff]

@[simp] lemma Term.primFree_var (i : Var n) : (var i : Term n ρ).PrimFree := nofun

@[simp] lemma Term.primFree_lam (t : Term (n + 1) ρ) : (lam t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_app (t₁ t₂ : Term n ρ) :
    (app t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_pair (t₁ t₂ : Term n ρ) :
    (pair t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) :
    (letPair t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_unit : (unit : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_letUnit (t₁ t₂ : Term n ρ) :
    (letUnit t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_bang (t : Term n ρ) : (bang t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (letBang t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_borrow (t : Term n ρ) : (borrow t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (copy t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_star (t : Term n ρ) : (star t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_nat (k : ℕ) : (nat k : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_float (x : FloatLit) : (float x : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_ref (a : Var ρ) : (ref a : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.not_primFree_prim (p : Prim) : ¬ (prim p : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]

end PrimFree

/-- Renaming preserves being primitive-free. -/
lemma Term.PrimFree.rename {n m ρ : ℕ} {t : Term n ρ} (ht : t.PrimFree) (r : Var n → Var m) :
    (t.rename r).PrimFree := fun h => ht (Binding.Tm.HasOp.of_ren h)

/-- Substituting primitive-free terms preserves being primitive-free. -/
lemma Term.PrimFree.subst {n m ρ : ℕ} {t : Term n ρ} (ht : t.PrimFree) {σ : Var n → Term m ρ}
    (hσ : ∀ i, (σ i).PrimFree) : (t.subst σ).PrimFree := fun h =>
  (Binding.Tm.HasOp.of_subst h).elim ht fun ⟨i, hi⟩ => hσ i hi

lemma Term.PrimFree.subst1 {n ρ : ℕ} {s : Term n ρ} {t : Term (n + 1) ρ} (ht : t.PrimFree)
    (hs : s.PrimFree) : (t.subst1 s).PrimFree :=
  ht.subst fun i => by cases i with | zero => exact hs | succ i => exact Term.primFree_var i

lemma Term.PrimFree.subst2 {n ρ : ℕ} {s₁ s₂ : Term n ρ} {t : Term (n + 2) ρ} (ht : t.PrimFree)
    (hs₁ : s₁.PrimFree) (hs₂ : s₂.PrimFree) : (t.subst2 s₁ s₂).PrimFree :=
  ht.subst fun i => by
    cases i with
    | zero => exact hs₂
    | succ i =>
      cases i with
      | zero => exact hs₁
      | succ i => exact Term.primFree_var i

/-! ## The reduction relation -/

/-- Call-by-name single-step reduction `t ⟶ t'` (substitution-based). -/
inductive CbnStep : {n ρ : ℕ} → Term n ρ → Term n ρ → Prop where
  | betaLolli {n ρ : ℕ} (t : Term (n + 1) ρ) (u : Term n ρ) : CbnStep (app (lam t) u) (t.subst1 u)
  | betaTensor {n ρ : ℕ} (t₁ t₂ : Term n ρ) (t : Term (n + 2) ρ) :
      CbnStep (letPair (pair t₁ t₂) t) (t.subst2 t₁ t₂)
  | betaUnit {n ρ : ℕ} (t : Term n ρ) : CbnStep (letUnit unit t) t
  | betaBang {n ρ : ℕ} (u : Term n ρ) (t : Term (n + 1) ρ) :
      CbnStep (letBang (bang u) t) (t.subst1 u)
  | betaBorrow {n ρ : ℕ} (t : Term n ρ) : CbnStep (borrow (star t)) (bang t)
  | betaCopy {n ρ : ℕ} (u : Term n ρ) (t : Term (n + 1) ρ) :
      CbnStep (copy (bang u) t) (t.subst1 (star u))
  | app {n ρ : ℕ} {t t' : Term n ρ} (u : Term n ρ) : CbnStep t t' → CbnStep (app t u) (app t' u)
  | letPair {n ρ : ℕ} {t t' : Term n ρ} (u : Term (n + 2) ρ) :
      CbnStep t t' → CbnStep (letPair t u) (letPair t' u)
  | letUnit {n ρ : ℕ} {t t' : Term n ρ} (u : Term n ρ) :
      CbnStep t t' → CbnStep (letUnit t u) (letUnit t' u)
  | letBang {n ρ : ℕ} {t t' : Term n ρ} (u : Term (n + 1) ρ) :
      CbnStep t t' → CbnStep (letBang t u) (letBang t' u)
  | borrow {n ρ : ℕ} {t t' : Term n ρ} : CbnStep t t' → CbnStep (borrow t) (borrow t')
  | copy {n ρ : ℕ} {t t' : Term n ρ} (u : Term (n + 1) ρ) :
      CbnStep t t' → CbnStep (copy t u) (copy t' u)

/-- Multi-step reduction `t ⟶* t'`: the reflexive-transitive closure of `CbnStep`. -/
def CbnSteps {n ρ : ℕ} : Term n ρ → Term n ρ → Prop := Relation.ReflTransGen CbnStep

/-! ## Contexts without variables -/

/-- The context has no assumptions for (de Bruijn) variables. -/
def TCtx.NoVars {n ρ : ℕ} (Γ : TCtx n ρ) : Prop := Γ.vars = .replicate n none

/-- All runtime array references of the context are non-linear. -/
def TCtx.RefsNonLin {n ρ : ℕ} (Γ : TCtx n ρ) : Prop := Γ.refs.All NonLin

/-- Every context for closed terms has no variables. -/
lemma TCtx.noVars_zero {ρ : ℕ} (Γ : TCtx 0 ρ) : Γ.NoVars := Ctx.eq_nil _

/-- Both summands of a context without variables have no variables. -/
lemma TCtx.NoVars.left {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.NoVars) :
    Γ₁.NoVars := by
  have := h.vars; rw [hΓ] at this
  exact Ctx.ext fun i => by
    have h' := this.get i
    rw [Ctx.get_replicate] at h'
    simpa using h'.eq_none.1

lemma TCtx.NoVars.right {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.NoVars) :
    Γ₂.NoVars := hΓ.left h.comm

lemma TCtx.RefsNonLin.left {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : Γ₁.Add Γ₂ Γ)
    (hΓ : Γ.RefsNonLin) : Γ₁.RefsNonLin :=
  Ctx.all_iff.2 fun a => (h.refs.get a).nonLin_left (hΓ.get a)

lemma TCtx.NoVars.refsOnly_eq {n ρ : ℕ} {Γ : TCtx n ρ} (hΓ : Γ.NoVars) : Γ.refsOnly = Γ :=
  TCtx.ext rfl hΓ.symm

/-- A context without variables whose references are non-linear is non-linear. -/
lemma TCtx.NoVars.allNonLin {n ρ : ℕ} {Γ : TCtx n ρ} (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) :
    Γ.AllNonLin :=
  ⟨hr, by rw [show Γ.vars = _ from hΓ]; exact TCtx.allNonLin_replicate _⟩

/-! ## Subject reduction -/

/-- **Subject reduction.** Reduction preserves typing for terms in a context without
variable assumptions whose array references are non-linear. -/
theorem CbnStep.preserves {n ρ : ℕ} {t t' : Term n ρ} (hs : CbnStep t t') {Γ : TCtx n ρ}
    {A : Ty} (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) (ht : HasType Γ t A) : HasType Γ t' A := by
  -- reducing the eliminated subterm `u` of an elimination form `Γ₁ + Γ₂ ⊢ E[u]`
  have cong : ∀ {Γ Γ₁ Γ₂ : TCtx n ρ} {u u' : Term n ρ} {B : Ty}, Γ.NoVars → Γ.RefsNonLin →
      (∀ {Γ : TCtx n ρ} {A : Ty}, Γ.NoVars → Γ.RefsNonLin → HasType Γ u A → HasType Γ u' A) →
      HasTypeD Γ₁ u B → Γ₁.Add Γ₂ Γ → HasTypeD Γ₁ u' B := fun hΓ hr ih h hadd =>
    hasType_iff_hasTypeD.1 (ih (hΓ.left hadd) (hr.left hadd) (hasType_iff_hasTypeD.2 h))
  induction hs generalizing Γ A with
  | betaLolli t u => exact EqAxiom.preserves (.betaLolli t u) ht
  | betaTensor t₁ t₂ t => exact EqAxiom.preserves (.betaTensor t₁ t₂ t) ht
  | betaUnit t => exact EqAxiom.preserves (.betaUnit t) ht
  | betaBang u t => exact EqAxiom.preserves (.betaBang u t) ht
  | betaBorrow t =>
    rw [hasType_iff_hasTypeD] at *
    cases ht with
    | borrow h =>
      cases h with
      | nec h _ =>
        rw [hΓ.refsOnly_eq] at h
        exact .bangI (hΓ.allNonLin hr) h
  | betaCopy u t =>
    rw [hasType_iff_hasTypeD] at ht
    cases ht with
    | copy h₁ h₂ hadd =>
      cases h₁ with
      | bangI _ hu =>
        have hΓ₁ := hΓ.left hadd
        have hstar : HasType _ (star u) _ :=
          hasType_iff_hasTypeD.2 (.nec (by rw [hΓ₁.refsOnly_eq]; exact hu)
            (show Ctx.All _ _ by rw [show _ = _ from hΓ₁]; exact TCtx.allNonLin_replicate _))
        exact hstar.subst_lin (hasType_iff_hasTypeD.2 h₂) hadd
  | app _ _ ih =>
    rw [hasType_iff_hasTypeD] at ht ⊢
    cases ht with | app h₁ h₂ hadd => exact .app (cong hΓ hr ih h₁ hadd) h₂ hadd
  | letPair _ _ ih =>
    rw [hasType_iff_hasTypeD] at ht ⊢
    cases ht with | tensorE h₁ h₂ hadd => exact .tensorE (cong hΓ hr ih h₁ hadd) h₂ hadd
  | letUnit _ _ ih =>
    rw [hasType_iff_hasTypeD] at ht ⊢
    cases ht with | unitE h₁ h₂ hadd => exact .unitE (cong hΓ hr ih h₁ hadd) h₂ hadd
  | letBang _ _ ih =>
    rw [hasType_iff_hasTypeD] at ht ⊢
    cases ht with | bangE h₁ h₂ hadd => exact .bangE (cong hΓ hr ih h₁ hadd) h₂ hadd
  | copy _ _ ih =>
    rw [hasType_iff_hasTypeD] at ht ⊢
    cases ht with | copy h₁ h₂ hadd => exact .copy (cong hΓ hr ih h₁ hadd) h₂ hadd
  | borrow _ ih =>
    rw [hasType_iff_hasTypeD] at *
    cases ht with
    | borrow h =>
      exact .borrow (hasType_iff_hasTypeD.1 (ih hΓ hr (hasType_iff_hasTypeD.2 h)))

/-- Reduction preserves primitive-freeness. -/
theorem CbnStep.primFree {n ρ : ℕ} {t t' : Term n ρ} (hs : CbnStep t t') (ht : t.PrimFree) :
    t'.PrimFree := by
  induction hs with
  | betaLolli t u => simp only [Term.primFree_app, Term.primFree_lam] at ht; exact ht.1.subst1 ht.2
  | betaTensor t₁ t₂ t =>
    simp only [Term.primFree_letPair, Term.primFree_pair] at ht; exact ht.2.subst2 ht.1.1 ht.1.2
  | betaUnit t => exact ((Term.primFree_letUnit _ _).1 ht).2
  | betaBang u t =>
    simp only [Term.primFree_letBang, Term.primFree_bang] at ht; exact ht.2.subst1 ht.1
  | betaBorrow t => simpa using ht
  | betaCopy u t =>
    simp only [Term.primFree_copy, Term.primFree_bang] at ht
    exact ht.2.subst1 ((Term.primFree_star _).2 ht.1)
  | app _ _ ih | letPair _ _ ih | letUnit _ _ ih | letBang _ _ ih | copy _ _ ih =>
    simp only [Term.primFree_app, Term.primFree_letPair, Term.primFree_letUnit,
      Term.primFree_letBang, Term.primFree_copy] at ht ⊢
    exact ⟨ih ht.1, ht.2⟩
  | borrow _ ih => simp only [Term.primFree_borrow] at ht ⊢; exact ih ht

/-- Subject reduction for many steps. -/
theorem CbnSteps.preserves {n ρ : ℕ} {t t' : Term n ρ} (hs : CbnSteps t t') {Γ : TCtx n ρ}
    {A : Ty} (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) (ht : HasType Γ t A) : HasType Γ t' A := by
  induction hs with
  | refl => exact ht
  | tail _ h ih => exact h.preserves hΓ hr ih

/-- Many steps preserve being primitive-free. -/
theorem CbnSteps.primFree {n ρ : ℕ} {t t' : Term n ρ} (hs : CbnSteps t t') (ht : t.PrimFree) :
    t'.PrimFree := by
  induction hs with
  | refl => exact ht
  | tail _ h ih => exact h.primFree ih

/-- The restriction of subject reduction to contexts without variable assumptions is
necessary: with `x : [1]`, the term `copy !x as y in &y : !1` reduces to `&(*x)`,
which is not typable since `nec` forbids variable assumptions. -/
theorem not_cbnStep_preserves_open :
    ∃ (Γ : TCtx 1 0) (t t' : Term 1 0) (A : Ty),
      HasType Γ t A ∧ CbnStep t t' ∧ ¬ HasType Γ t' A := by
  refine ⟨(TCtx.empty : TCtx 0 0).cons (some (.nonlin .unit)),
    copy (bang (var 0)) (borrow (var 0)), borrow (star (var 0)), .bang .unit, ?_,
    .betaCopy _ _, ?_⟩
  · rw [hasType_iff_hasTypeD]
    exact .copy (.bangI (TCtx.AllNonLin.cons TCtx.AllNonLin.empty (nonLin_nonlin _))
      (HasTypeD.var_zero_single (.nonlin .unit)))
      (.borrow (HasTypeD.var_zero_single (.lin (.star .unit)))) (TCtx.Add.empty_right _)
  · rw [hasType_iff_hasTypeD]
    intro h
    cases h with
    | borrow h =>
      cases h with
      | nec h _ =>
        revert h
        generalize Ty.unit = B
        intro h
        cases h with
        | var hi _ => cases hi.get

/-! ## Progress -/

/-- **Progress.** A well-typed primitive-free term without free variables is either a
value or can take a reduction step. -/
theorem cbn_progress {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasType Γ t A)
    (hΓ : Γ.NoVars) (hp : t.PrimFree) : IsValue t ∨ ∃ t', CbnStep t t' := by
  rw [hasType_iff_hasTypeD] at ht
  induction ht with
  | var hi _ => have := hi.get; rw [show _ = _ from hΓ, Ctx.get_replicate] at this; cases this
  | abs _ _ => exact .inl (.lam _)
  | tensorI _ _ _ _ _ => exact .inl (.pair _ _)
  | unitI _ => exact .inl .unit
  | bangI _ _ _ => exact .inl (.bang _)
  | nec _ _ _ => exact .inl (.star _)
  | natI _ => exact .inl (.nat _)
  | floatI _ => exact .inl (.float _)
  | ref _ _ => exact .inl (.ref _)
  | prim _ => exact (Term.not_primFree_prim _ hp).elim
  | app h₁ _ hadd ih₁ _ | tensorE h₁ _ hadd ih₁ _ | unitE h₁ _ hadd ih₁ _
  | bangE h₁ _ hadd ih₁ _ | copy h₁ _ hadd ih₁ _ =>
    right
    simp only [Term.primFree_app, Term.primFree_letPair, Term.primFree_letUnit,
      Term.primFree_letBang, Term.primFree_copy] at hp
    rcases ih₁ (hΓ.left hadd) hp.1 with hv | ⟨t', hs⟩
    · have hp1 := hp.1
      induction hv using IsValue.induction with
      | prim => simp at hp1
      | readArray₁ _ => simp at hp1
      | writeArray₁ _ => simp at hp1
      | writeArray₂ _ _ => simp at hp1
      | _ => first | (cases h₁; done) | exact ⟨_, by constructor⟩
    · exact ⟨_, by constructor; exact hs⟩
  | borrow h₁ ih₁ =>
    right
    rw [Term.primFree_borrow] at hp
    rcases ih₁ hΓ hp with hv | ⟨t', hs⟩
    · induction hv using IsValue.induction with
      | prim => simp at hp
      | readArray₁ _ => simp at hp
      | writeArray₁ _ => simp at hp
      | writeArray₂ _ _ => simp at hp
      | _ => first | (cases h₁; done) | exact ⟨_, by constructor⟩
    · exact ⟨_, .borrow hs⟩

/-- **Syntactic type safety** for closed terms: a well-typed closed primitive-free term
(in a context whose runtime array references are non-linear, e.g. the empty context)
never reduces to a stuck term, and every reduct has the same type. -/
theorem cbn_type_safety {ρ : ℕ} {Γ : TCtx 0 ρ} {t t' : Term 0 ρ} {A : Ty} (hr : Γ.RefsNonLin)
    (ht : HasType Γ t A) (hp : t.PrimFree) (hs : CbnSteps t t') :
    HasType Γ t' A ∧ (IsValue t' ∨ ∃ t'', CbnStep t' t'') := by
  have ht' := hs.preserves (TCtx.noVars_zero Γ) hr ht
  exact ⟨ht', cbn_progress ht' (TCtx.noVars_zero Γ) (hs.primFree hp)⟩

/-! ## Determinism -/

/-- Values are normal forms. -/
theorem IsValue.not_cbnStep {n ρ : ℕ} {v t : Term n ρ} (hv : IsValue v) : ¬ CbnStep v t := by
  intro hs
  induction hv using IsValue.induction generalizing t with
  | readArray₁ _ _ ih =>
    cases hs with
    | app _ h => cases h
  | writeArray₁ _ _ ih =>
    cases hs with
    | app _ h => cases h
  | writeArray₂ _ _ _ _ ih₁ ih₂ =>
    cases hs with
    | app _ h =>
      cases h with
      | app _ h => cases h
  | _ => cases hs

/-- The call-by-name reduction is deterministic. -/
theorem CbnStep.deterministic {n ρ : ℕ} {t t₁ t₂ : Term n ρ} (h₁ : CbnStep t t₁)
    (h₂ : CbnStep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | app _ h ih | letPair _ h ih | letUnit _ h ih | letBang _ h ih | borrow h ih | copy _ h ih =>
    cases h₂ <;> first | (cases h; done) | (rename_i h'; rw [ih h'])
  | _ => cases h₂ <;> first | rfl | (rename_i h; cases h)

end LCU
