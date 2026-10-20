module
public import RequestProject.LCU.Equational

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

We prove for terms without free variables (in particular for closed terms `Term 0`)
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

/-- A term is primitive-free if it contains no array primitive `newArray`,
`readArray`, `writeArray`, `deleteArray`. -/
def Term.PrimFree : {n : ℕ} → Term n → Prop
  | _, var _ => True
  | _, lam t => t.PrimFree
  | _, app t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, pair t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, letPair t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, unit => True
  | _, letUnit t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, bang t => t.PrimFree
  | _, letBang t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, borrow t => t.PrimFree
  | _, copy t₁ t₂ => t₁.PrimFree ∧ t₂.PrimFree
  | _, star t => t.PrimFree
  | _, nat _ => True
  | _, float _ => True
  | _, prim _ => False
  | _, ref _ => True

lemma Term.PrimFree.rename {n m : ℕ} {t : Term n} (ht : t.PrimFree) (ρ : Fin n → Fin m) :
    (t.rename ρ).PrimFree := by
  induction t generalizing m with
  | prim => exact ht.elim
  | lam _ ih | bang _ ih | borrow _ ih | star _ ih => exact ih ht _
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | letPair _ _ ih₁ ih₂ | letUnit _ _ ih₁ ih₂
  | letBang _ _ ih₁ ih₂ | copy _ _ ih₁ ih₂ => exact ⟨ih₁ ht.1 _, ih₂ ht.2 _⟩
  | _ => trivial

lemma Term.PrimFree.subst {n m : ℕ} {t : Term n} (ht : t.PrimFree) {σ : Fin n → Term m}
    (hσ : ∀ i, (σ i).PrimFree) : (t.subst σ).PrimFree := by
  have hup : ∀ {n m : ℕ} {σ : Fin n → Term m}, (∀ i, (σ i).PrimFree) →
      ∀ i, (Subst.up σ i).PrimFree := fun hσ i => Fin.cases trivial (fun i => (hσ i).rename _) i
  induction t generalizing m with
  | var i => exact hσ i
  | prim => exact ht.elim
  | lam t ih => exact ih ht (hup hσ)
  | bang _ ih | borrow _ ih | star _ ih => exact ih ht hσ
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | letPair _ _ ih₁ ih₂ | letUnit _ _ ih₁ ih₂
  | letBang _ _ ih₁ ih₂ | copy _ _ ih₁ ih₂ =>
    exact ⟨ih₁ ht.1 hσ, ih₂ ht.2 (by first | exact hσ | exact hup hσ | exact hup (hup hσ))⟩
  | _ => trivial

lemma Term.PrimFree.subst1 {n : ℕ} {s : Term n} {t : Term (n + 1)} (hs : s.PrimFree)
    (ht : t.PrimFree) : (Term.subst1 s t).PrimFree :=
  ht.subst (Fin.cases hs fun _ => trivial)

lemma Term.PrimFree.subst2 {n : ℕ} {s₁ s₂ : Term n} {t : Term (n + 2)} (hs₁ : s₁.PrimFree)
    (hs₂ : s₂.PrimFree) (ht : t.PrimFree) : (Term.subst2 s₁ s₂ t).PrimFree :=
  ht.subst (Fin.cases hs₂ (Fin.cases hs₁ fun _ => trivial))

/-! ## The reduction relation -/

/-- Call-by-name single-step reduction `t ⟶ t'` (substitution-based). -/
inductive CbnStep : {n : ℕ} → Term n → Term n → Prop where
  | betaLolli {n : ℕ} (t : Term (n + 1)) (u : Term n) : CbnStep (app (lam t) u) (subst1 u t)
  | betaTensor {n : ℕ} (t₁ t₂ : Term n) (t : Term (n + 2)) :
      CbnStep (letPair (pair t₁ t₂) t) (subst2 t₁ t₂ t)
  | betaUnit {n : ℕ} (t : Term n) : CbnStep (letUnit unit t) t
  | betaBang {n : ℕ} (u : Term n) (t : Term (n + 1)) : CbnStep (letBang (bang u) t) (subst1 u t)
  | betaBorrow {n : ℕ} (t : Term n) : CbnStep (borrow (star t)) (bang t)
  | betaCopy {n : ℕ} (u : Term n) (t : Term (n + 1)) :
      CbnStep (copy (bang u) t) (subst1 (star u) t)
  | app {n : ℕ} {t t' : Term n} (u : Term n) : CbnStep t t' → CbnStep (app t u) (app t' u)
  | letPair {n : ℕ} {t t' : Term n} (u : Term (n + 2)) :
      CbnStep t t' → CbnStep (letPair t u) (letPair t' u)
  | letUnit {n : ℕ} {t t' : Term n} (u : Term n) :
      CbnStep t t' → CbnStep (letUnit t u) (letUnit t' u)
  | letBang {n : ℕ} {t t' : Term n} (u : Term (n + 1)) :
      CbnStep t t' → CbnStep (letBang t u) (letBang t' u)
  | borrow {n : ℕ} {t t' : Term n} : CbnStep t t' → CbnStep (borrow t) (borrow t')
  | copy {n : ℕ} {t t' : Term n} (u : Term (n + 1)) :
      CbnStep t t' → CbnStep (copy t u) (copy t' u)

/-- Multi-step reduction `t ⟶* t'`: the reflexive-transitive closure of `CbnStep`. -/
def CbnSteps {n : ℕ} : Term n → Term n → Prop := Relation.ReflTransGen CbnStep

/-! ## Contexts without variables -/

/-- The context has no assumptions for (de Bruijn) variables. -/
def Ctx.NoVars {n : ℕ} (Γ : Ctx n) : Prop := ∀ i, Γ (.inl i) = none

/-- All runtime array references of the context are non-linear. -/
def Ctx.RefsNonLin {n : ℕ} (Γ : Ctx n) : Prop := ∀ a, NonLin (Γ (.inr a))

lemma Ctx.noVars_zero (Γ : Ctx 0) : Γ.NoVars := fun i => i.elim0

lemma Ctx.NoVars.left {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.NoVars) :
    Γ₁.NoVars := fun i => by
  have := h (.inl i); rw [hΓ i] at this; exact this.eq_none.1

lemma Ctx.NoVars.right {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.NoVars) :
    Γ₂.NoVars := fun i => by
  have := h (.inl i); rw [hΓ i] at this; exact this.eq_none.2

lemma Ctx.RefsNonLin.left {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.RefsNonLin) :
    Γ₁.RefsNonLin := fun a => (h (.inr a)).nonLin_left (hΓ a)

lemma Ctx.NoVars.refsOnly_eq {n : ℕ} {Γ : Ctx n} (hΓ : Γ.NoVars) : Γ.refsOnly = Γ := by
  funext x
  rcases x with i | a
  · rw [Ctx.refsOnly_inl, hΓ i]
  · rfl

lemma Ctx.NoVars.allNonLin {n : ℕ} {Γ : Ctx n} (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) :
    Γ.AllNonLin := by
  rintro (i | a)
  · rw [hΓ i]; trivial
  · exact hr a

/-! ## Subject reduction -/

/-- **Subject reduction.** Reduction preserves typing for terms in a context without
variable assumptions whose array references are non-linear. -/
theorem CbnStep.preserves {n : ℕ} {t t' : Term n} (hs : CbnStep t t') {Γ : Ctx n} {A : Ty}
    (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) (ht : HasType Γ t A) : HasType Γ t' A := by
  -- reducing the eliminated subterm `u` of an elimination form `Γ₁ + Γ₂ ⊢ E[u]`
  have cong : ∀ {Γ Γ₁ Γ₂ : Ctx n} {u u' : Term n} {B : Ty}, Γ.NoVars → Γ.RefsNonLin →
      (∀ {Γ : Ctx n} {A : Ty}, Γ.NoVars → Γ.RefsNonLin → HasType Γ u A → HasType Γ u' A) →
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
            (fun i => by rw [hΓ₁ i]; trivial))
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
theorem CbnStep.primFree {n : ℕ} {t t' : Term n} (hs : CbnStep t t') (ht : t.PrimFree) :
    t'.PrimFree := by
  induction hs with
  | betaLolli t u => exact Term.PrimFree.subst1 (s := u) ht.2 ht.1
  | betaTensor t₁ t₂ t => exact ht.1.1.subst2 ht.1.2 ht.2
  | betaUnit t => exact ht.2
  | betaBang u t => exact Term.PrimFree.subst1 (s := u) ht.1 ht.2
  | betaBorrow t => exact ht
  | betaCopy u t => exact Term.PrimFree.subst1 (s := star u) ht.1 ht.2
  | app _ _ ih | letPair _ _ ih | letUnit _ _ ih | letBang _ _ ih | copy _ _ ih =>
    exact ⟨ih ht.1, ht.2⟩
  | borrow _ ih => exact ih ht

theorem CbnSteps.preserves {n : ℕ} {t t' : Term n} (hs : CbnSteps t t') {Γ : Ctx n} {A : Ty}
    (hΓ : Γ.NoVars) (hr : Γ.RefsNonLin) (ht : HasType Γ t A) : HasType Γ t' A := by
  induction hs with
  | refl => exact ht
  | tail _ h ih => exact h.preserves hΓ hr ih

theorem CbnSteps.primFree {n : ℕ} {t t' : Term n} (hs : CbnSteps t t') (ht : t.PrimFree) :
    t'.PrimFree := by
  induction hs with
  | refl => exact ht
  | tail _ h ih => exact h.primFree ih

/-- The restriction of subject reduction to contexts without variable assumptions is
necessary: with `x : [1]`, the term `copy !x as y in &y : !1` reduces to `&(*x)`,
which is not typable since `nec` forbids variable assumptions. -/
theorem not_cbnStep_preserves_open :
    ∃ (Γ : Ctx 1) (t t' : Term 1) (A : Ty),
      HasType Γ t A ∧ CbnStep t t' ∧ ¬ HasType Γ t' A := by
  refine ⟨(Ctx.empty : Ctx 0).cons (some (.nonlin .unit)), copy (bang (var 0)) (borrow (var 0)),
    borrow (star (var 0)), .bang .unit, ?_, .betaCopy _ _, ?_⟩
  · rw [hasType_iff_hasTypeD]
    exact .copy (.bangI (Ctx.AllNonLin.cons Ctx.AllNonLin.empty (nonLin_nonlin _))
      (HasTypeD.var_zero_single (.nonlin .unit)))
      (.borrow (HasTypeD.var_zero_single (.lin (.star .unit)))) (Ctx.Add.empty_right _)
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
        | var hi _ => simp at hi

/-! ## Progress -/

/-- **Progress.** A well-typed primitive-free term without free variables is either a
value or can take a reduction step. -/
theorem cbn_progress {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasType Γ t A)
    (hΓ : Γ.NoVars) (hp : t.PrimFree) : IsValue t ∨ ∃ t', CbnStep t t' := by
  rw [hasType_iff_hasTypeD] at ht
  induction ht with
  | var hi _ => rw [hΓ] at hi; cases hi
  | abs _ _ => exact .inl (.lam _)
  | tensorI _ _ _ _ _ => exact .inl (.pair _ _)
  | unitI _ => exact .inl .unit
  | bangI _ _ _ => exact .inl (.bang _)
  | nec _ _ _ => exact .inl (.star _)
  | natI _ => exact .inl (.nat _)
  | floatI _ => exact .inl (.float _)
  | ref _ _ => exact .inl (.ref _)
  | prim _ => exact hp.elim
  | app h₁ _ hadd ih₁ _ | tensorE h₁ _ hadd ih₁ _ | unitE h₁ _ hadd ih₁ _
  | bangE h₁ _ hadd ih₁ _ | copy h₁ _ hadd ih₁ _ =>
    right
    rcases ih₁ (hΓ.left hadd) hp.1 with hv | ⟨t', hs⟩
    · induction hv using IsValue.induction with
      | prim => exact hp.1.elim
      | readArray₁ _ => exact hp.1.1.elim
      | writeArray₁ _ => exact hp.1.1.elim
      | writeArray₂ _ _ => exact hp.1.1.1.elim
      | _ => first | (cases h₁; done) | exact ⟨_, by constructor⟩
    · exact ⟨_, by constructor; exact hs⟩
  | borrow h₁ ih₁ =>
    right
    rcases ih₁ hΓ hp with hv | ⟨t', hs⟩
    · induction hv using IsValue.induction with
      | prim => exact hp.elim
      | readArray₁ _ => exact hp.1.elim
      | writeArray₁ _ => exact hp.1.elim
      | writeArray₂ _ _ => exact hp.1.1.elim
      | _ => first | (cases h₁; done) | exact ⟨_, by constructor⟩
    · exact ⟨_, .borrow hs⟩

/-- **Syntactic type safety** for closed terms: a well-typed closed primitive-free term
(in a context whose runtime array references are non-linear, e.g. the empty context)
never reduces to a stuck term, and every reduct has the same type. -/
theorem cbn_type_safety {Γ : Ctx 0} {t t' : Term 0} {A : Ty} (hr : Γ.RefsNonLin)
    (ht : HasType Γ t A) (hp : t.PrimFree) (hs : CbnSteps t t') :
    HasType Γ t' A ∧ (IsValue t' ∨ ∃ t'', CbnStep t' t'') := by
  have ht' := hs.preserves (Ctx.noVars_zero Γ) hr ht
  exact ⟨ht', cbn_progress ht' (Ctx.noVars_zero Γ) (hs.primFree hp)⟩

/-! ## Determinism -/

/-- Values are normal forms. -/
theorem IsValue.not_cbnStep {n : ℕ} {v t : Term n} (hv : IsValue v) : ¬ CbnStep v t := by
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
theorem CbnStep.deterministic {n : ℕ} {t t₁ t₂ : Term n} (h₁ : CbnStep t t₁)
    (h₂ : CbnStep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | app _ h ih | letPair _ h ih | letUnit _ h ih | letBang _ h ih | borrow h ih | copy _ h ih =>
    cases h₂ <;> first | (cases h; done) | (rename_i h'; rw [ih h'])
  | _ => cases h₂ <;> first | rfl | (rename_i h; cases h)

end LCU
