module
public import RequestProject.LCU.Sec3_2_Equational.Equational
public import RequestProject.LCU.Sec3_1_Calculus.FreeVars

/-!
# Typability of the equational axioms (Section 3.2)

The paper notes that "the typability of these axioms relies on the admissibility of
linear and non-linear substitution".  This file makes that remark precise.

## Main results

* `EqAxiom.preserves`: every axiom `l ≡ r`, oriented from left to right, preserves
  typing: `Γ ⊢ l : A` implies `Γ ⊢ r : A`.  The `β`-axioms use the substitution
  lemmas (Lemmas 1 and 2); the `η⊸`/`assoc` axioms use strengthening
  (`HasTypeD.unrename`).
* `HasType.etaLolli_expand`, `HasType.etaTensor_expand`, `HasType.betaUnit_expand`,
  `HasType.etaUnit_expand`, `HasType.etaBang_expand`, `HasType.unitR_expand`,
  `HasType.assoc_expand`: the axioms that do not involve a substitution also preserve
  typing from right to left.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Typability of the axioms -/

namespace HasTypeD

/-- Weakening with the non-linear context added on the left. -/
lemma weaken' {n ρ : ℕ} {Γ Δ Γ' : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasTypeD Γ t A)
    (hΔ : Δ.AllNonLin) (hadd : Δ.Add Γ Γ') : HasTypeD Γ' t A := ht.weaken hΔ hadd.comm

end HasTypeD

/-- Typing of the variable `Var.zero` in the dereliction-free system. -/
lemma HasTypeD.var_zero_inv {n ρ : ℕ} {Γ : TCtx n ρ} {h : Option (Hyp Ty)} {B : Ty}
    (ht : HasTypeD (Γ.cons h) (Term.var .zero) B) :
    ∃ h', h = some h' ∧ h'.ty = B ∧ Γ.AllNonLin := by
  cases ht with
  | var hi hr =>
    cases hi with
    | here hΓ => exact ⟨_, rfl, rfl, hr, hΓ⟩

/-- Inversion for variables: `Δ ⊢ x : B` means `x` has a hypothesis of type `B` in `Δ`
and all other assumptions are non-linear. -/
lemma HasTypeD.var_inv {n ρ : ℕ} {Δ : TCtx n ρ} {i : Var n} {B : Ty}
    (h : HasTypeD Δ (Term.var i) B) :
    ∃ h', Δ.vars.Pick NonLin i (some h') ∧ h'.ty = B ∧ Δ.refs.All NonLin := by
  cases h with
  | var hi hr => exact ⟨_, hi, rfl, hr⟩

/-- The `η⊸` case: from a typing of `λx. t x` (with `t` not mentioning `x`, i.e. a
weakening `t.rename Var.succ`), recover a typing of `t`. -/
lemma etaLolli_aux {n ρ : ℕ} {Γ : TCtx n ρ} {Δ₁ Δ₂ : TCtx (n + 1) ρ} {t : Term n ρ}
    {A A' B : Ty} (h₁ : HasTypeD Δ₁ (t.rename Var.succ) (A ⊸ B))
    (h₂ : HasTypeD Δ₂ (Term.var .zero) A)
    (hadd : Δ₁.Add Δ₂ (Γ.cons (some (.lin A')))) : HasTypeD Γ t (A' ⊸ B) := by
  obtain ⟨Θ₁, a, rfl⟩ := TCtx.eq_cons Δ₁
  obtain ⟨Θ₂, b, rfl⟩ := TCtx.eq_cons Δ₂
  obtain ⟨h', rfl, ty, hΘ₂⟩ := h₂.var_zero_inv
  obtain ⟨hΘ, h0⟩ := TCtx.Add.of_cons hadd
  rcases h0.eq_lin with ⟨_, hc⟩ | ⟨rfl, hc⟩
  · cases hc
  · cases hc
    simp only [Hyp.ty] at ty
    subst ty
    have h1 := h₁.unrename (SubstSetup.zero Term.unit) rfl
    rw [TCtx.remove_succ_cons] at h1
    exact h1.weaken hΘ₂ hΘ

/-- The `η⊗` case: from a typing of `let (x, y) = t in (x, y)`, recover a typing of
`t`. -/
lemma etaTensor_aux {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {Δ₁ Δ₂ : TCtx (n + 2) ρ} {t : Term n ρ}
    {A B A' B' : Ty} (h₁ : HasTypeD Γ₁ t (A ⊗ B))
    (g₁ : HasTypeD Δ₁ (Term.var (.succ .zero)) A') (g₂ : HasTypeD Δ₂ (Term.var .zero) B')
    (gadd : Δ₁.Add Δ₂ ((Γ₂.cons (some (.lin A))).cons (some (.lin B))))
    (hadd : Γ₁.Add Γ₂ Γ) : HasTypeD Γ t (A' ⊗ B') := by
  obtain ⟨Θ₁', b₁, rfl⟩ := TCtx.eq_cons Δ₁
  obtain ⟨Θ₁, a₁, rfl⟩ := TCtx.eq_cons Θ₁'
  obtain ⟨Θ₂', b₂, rfl⟩ := TCtx.eq_cons Δ₂
  obtain ⟨Θ₂, a₂, rfl⟩ := TCtx.eq_cons Θ₂'
  obtain ⟨k1, p1, ty1, _⟩ := g₁.var_inv
  obtain ⟨k0, rfl, ty0, hΘ₂'⟩ := g₂.var_zero_inv
  obtain ⟨hΘ₂, ha₂⟩ := TCtx.AllNonLin.of_cons hΘ₂'
  simp only [TCtx.cons_vars] at p1
  cases p1 with
  | there p1 hb₁ =>
    cases p1 with
    | here hΘ₁v =>
      obtain ⟨gadd', e0⟩ := TCtx.Add.of_cons gadd
      obtain ⟨gadd'', e1⟩ := TCtx.Add.of_cons gadd'
      have := e0.some_of_nonLin' hb₁
      simp only [Option.some.injEq] at this
      subst this
      have := e1.some_of_nonLin ha₂
      simp only [Option.some.injEq] at this
      subst this
      simp only [Hyp.ty] at ty0 ty1
      subst ty0 ty1
      have hΘ₁r : Θ₁.refs.All NonLin := by
        obtain ⟨_, _, _, h⟩ := g₁.var_inv; exact h
      exact h₁.weaken (TCtx.AllNonLin.of_add gadd'' ⟨hΘ₁r, hΘ₁v⟩ hΘ₂) hadd

/-- The `assoc` case: re-associate the two `copy`s.  The side condition that `x` is
not free in `t₃` appears as `t₃` being a weakening. -/
lemma assoc_aux {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {Δ₁ Δ₂ : TCtx (n + 1) ρ} {t₁ : Term n ρ}
    {t₂ t₃ : Term (n + 1) ρ} {A B C : Ty}
    (h₁ : HasTypeD Γ₁ t₁ (.bang A)) (g₁ : HasTypeD Δ₁ t₂ (.bang B))
    (g₂ : HasTypeD (Δ₂.cons (some (.lin (.star B)))) (t₃.rename (Ren.up Var.succ)) (.bang C))
    (gadd : Δ₁.Add Δ₂ (Γ₂.cons (some (.lin (.star A))))) (hadd : Γ₁.Add Γ₂ Γ) :
    HasTypeD Γ (copy (copy t₁ t₂) t₃) (.bang C) := by
  obtain ⟨Θ₁, a, rfl⟩ := TCtx.eq_cons Δ₁
  obtain ⟨Θ₂, b, rfl⟩ := TCtx.eq_cons Δ₂
  obtain ⟨hΘ, h0⟩ := TCtx.Add.of_cons gadd
  rcases h0.eq_lin with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
  · have g₂' := g₂.unrename (SubstSetup.zero Term.unit).up rfl
    rw [TCtx.remove_cons, TCtx.remove_succ_cons] at g₂'
    obtain ⟨Θ, hΘ₁, hΘ₂⟩ := TCtx.Add.assoc' hΘ hadd
    exact HasTypeD.copy (HasTypeD.copy h₁ g₁ hΘ₁) g₂' hΘ₂
  · exfalso
    have hf := g₂.freeIn_of_lin (i := .succ .zero) rfl
    obtain ⟨i, hi⟩ := freeIn_rename _ _ _ hf
    cases i with
    | zero => cases hi
    | succ i => cases hi

/-- **Typability of the equational axioms (left to right).**  If `l ≡ r` is an axiom
of the equational theory and `Γ ⊢ l : A`, then `Γ ⊢ r : A`. -/
theorem EqAxiom.preserves {n ρ : ℕ} {l r : Term n ρ} (hax : EqAxiom l r) {Γ : TCtx n ρ} {A : Ty}
    (hl : HasType Γ l A) : HasType Γ r A := by
  rw [hasType_iff_hasTypeD] at *
  cases hax with
  | betaLolli t t' =>
    cases hl with
    | app h₁ h₂ hadd =>
      cases h₁ with
      | abs h₁ => exact h₂.subst_lin h₁ hadd.comm
  | etaLolli t =>
    cases hl with
    | abs h =>
      cases h with
      | app h₁ h₂ hadd => exact etaLolli_aux h₁ h₂ hadd
  | betaTensor t₁ t₂ t =>
    cases hl with
    | tensorE h₁ h₂ hadd =>
      cases h₁ with
      | tensorI g₁ g₂ gadd =>
        rw [subst2_eq]
        obtain ⟨Θ, hΘ, hΘ'⟩ := TCtx.Add.assoc gadd hadd
        have inner := (g₂.shift nonLin_none).subst_lin h₂ (hΘ.cons (.noneLeft _))
        exact g₁.subst_lin inner hΘ'
  | etaTensor t =>
    cases hl with
    | tensorE h₁ h₂ hadd =>
      cases h₂ with
      | tensorI g₁ g₂ gadd => exact etaTensor_aux h₁ g₁ g₂ gadd hadd
  | betaUnit t =>
    cases hl with
    | unitE h₁ h₂ hadd =>
      cases h₁ with
      | unitI hΓ₁ => exact h₂.weaken' hΓ₁ hadd
  | etaUnit t =>
    cases hl with
    | unitE h₁ h₂ hadd =>
      cases h₂ with
      | unitI hΓ₂ => exact h₁.weaken hΓ₂ hadd
  | betaBang t t' =>
    cases hl with
    | bangE h₁ h₂ hadd =>
      cases h₁ with
      | bangI hΓ₁ h₁ => exact h₁.subst_nonlin hΓ₁ h₂ hadd
  | etaBang t =>
    cases hl with
    | bangE h₁ h₂ hadd =>
      cases h₂ with
      | bangI hΓ₂ h₂ =>
        obtain ⟨h', e, ty, _⟩ := h₂.var_zero_inv
        cases e
        subst ty
        exact h₁.weaken (TCtx.AllNonLin.of_cons hΓ₂).1 hadd
  | unitR t =>
    cases hl with
    | copy h₁ h₂ hadd =>
      cases h₂ with
      | borrow h₂ =>
        obtain ⟨h', e, ty, hΓ₂⟩ := h₂.var_zero_inv
        cases e
        cases ty
        exact h₁.weaken hΓ₂ hadd
  | unitL v t' _ =>
    cases hl with
    | copy h₁ h₂ hadd =>
      cases h₁ with
      | borrow h₁ => exact h₁.subst_lin h₂ hadd
  | assoc t₁ t₂ t₃ =>
    cases hl with
    | copy h₁ h₂ hadd =>
      cases h₂ with
      | copy g₁ g₂ gadd => exact assoc_aux h₁ g₁ g₂ gadd hadd

/-! ## Typability of the substitution-free axioms from right to left -/

/-- `x : h ⊢ x : h.ty`, for the variable `Var.zero` in an otherwise empty context. -/
lemma HasTypeD.var_zero_single {n ρ : ℕ} (h : Hyp Ty) :
    HasTypeD ((TCtx.empty : TCtx n ρ).cons (some h)) (Term.var .zero) h.ty :=
  HasTypeD.var (.here (TCtx.allNonLin_replicate _)) (TCtx.allNonLin_replicate _)

/-- Adding an empty context extended by `none` on the right. -/
lemma TCtx.Add.cons_empty_right {n ρ : ℕ} (Γ : TCtx n ρ) (h : Option (Hyp Ty)) :
    (Γ.cons none).Add ((TCtx.empty : TCtx n ρ).cons h) (Γ.cons h) :=
  (TCtx.Add.empty_right Γ).cons (.noneLeft _)

namespace HasType

variable {n ρ : ℕ} {Γ : TCtx n ρ} {A B : Ty}

/-- `(η⊸)` from right to left. -/
theorem etaLolli_expand {t : Term n ρ} (ht : HasType Γ t (A ⊸ B)) :
    HasType Γ (.lam (.app (t.rename Var.succ) (.var .zero))) (A ⊸ B) := by
  rw [hasType_iff_hasTypeD] at *
  exact .abs (.app (ht.shift nonLin_none) (HasTypeD.var_zero_single (.lin A))
    (TCtx.Add.cons_empty_right Γ _))

/-- `(η⊗)` from right to left. -/
theorem etaTensor_expand {t : Term n ρ} (ht : HasType Γ t (A ⊗ B)) :
    HasType Γ (.letPair t (.pair (.var (.succ .zero)) (.var .zero))) (A ⊗ B) := by
  rw [hasType_iff_hasTypeD] at *
  refine .tensorE ht (Γ₂ := TCtx.empty)
    (.tensorI (Γ₁ := (TCtx.empty.cons (some (.lin A))).cons none)
    ((HasTypeD.var_zero_single (.lin A)).shift nonLin_none)
    (HasTypeD.var_zero_single (n := n + 1) (.lin B)) ?_) (TCtx.Add.empty_right _)
  exact (TCtx.Add.empty_right _).cons (.noneLeft _)

/-- `(β1)` from right to left. -/
theorem betaUnit_expand {t : Term n ρ} (ht : HasType Γ t A) :
    HasType Γ (.letUnit .unit t) A := by
  rw [hasType_iff_hasTypeD] at *
  exact .unitE (.unitI TCtx.AllNonLin.empty) ht (TCtx.Add.empty_left _)

/-- `(η1)` from right to left. -/
theorem etaUnit_expand {t : Term n ρ} (ht : HasType Γ t .unit) :
    HasType Γ (.letUnit t .unit) .unit := by
  rw [hasType_iff_hasTypeD] at *
  exact .unitE ht (.unitI TCtx.AllNonLin.empty) (TCtx.Add.empty_right _)

/-- `(η!)` from right to left. -/
theorem etaBang_expand {t : Term n ρ} (ht : HasType Γ t (.bang A)) :
    HasType Γ (.letBang t (.bang (.var .zero))) (.bang A) := by
  rw [hasType_iff_hasTypeD] at *
  exact .bangE ht (Γ₂ := TCtx.empty)
    (.bangI (TCtx.AllNonLin.cons TCtx.AllNonLin.empty (nonLin_nonlin A))
      (HasTypeD.var_zero_single (.nonlin A))) (TCtx.Add.empty_right _)

/-- `(unitR)` from right to left. -/
theorem unitR_expand {t : Term n ρ} (ht : HasType Γ t (.bang A)) :
    HasType Γ (.copy t (.borrow (.var .zero))) (.bang A) := by
  rw [hasType_iff_hasTypeD] at *
  exact .copy ht (Γ₂ := TCtx.empty) (.borrow (HasTypeD.var_zero_single (.lin (.star A))))
    (TCtx.Add.empty_right _)

/-- `(assoc)` from right to left. -/
theorem assoc_expand {t₁ : Term n ρ} {t₂ t₃ : Term (n + 1) ρ} {C : Ty}
    (ht : HasType Γ (.copy (.copy t₁ t₂) t₃) (.bang C)) :
    HasType Γ (.copy t₁ (.copy t₂ (t₃.rename (Ren.up Var.succ)))) (.bang C) := by
  rw [hasType_iff_hasTypeD] at *
  cases ht with
  | copy h hc hadd =>
    cases h with
    | copy g₁ g₂ gadd =>
      obtain ⟨Θ, hΘ, hΘ'⟩ := TCtx.Add.assoc gadd hadd
      refine .copy g₁ (.copy g₂ (hc.rename ((TCtx.renCtx_succ _ nonLin_none).cons _))
        (hΘ.cons (HypAdd.none_right _))) hΘ'

end HasType

end LCU
