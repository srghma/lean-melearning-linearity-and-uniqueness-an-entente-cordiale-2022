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
lemma weaken' {n : ℕ} {Γ Δ Γ' : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A)
    (hΔ : Δ.AllNonLin) (hadd : Δ.Add Γ Γ') : HasTypeD Γ' t A := ht.weaken hΔ hadd.comm

end HasTypeD

/-- Typing of a variable `0` in the dereliction-free system. -/
lemma HasTypeD.var_zero_inv {n : ℕ} {Γ : Ctx n} {h : Option Hyp} {B : Ty}
    (ht : HasTypeD (Γ.cons h) (Term.var 0) B) :
    ∃ h', h = some h' ∧ h'.ty = B ∧ Γ.AllNonLin := by
  cases ht with
  | var hi hrest =>
    refine ⟨_, hi, rfl, ?_⟩
    rintro (j | a)
    · have := hrest (.inl j.succ); rwa [Ctx.set_ne _ _ (by simp)] at this
    · have := hrest (.inr a); rwa [Ctx.set_ne _ _ (by simp)] at this

/-- Inversion for variables: `Δ ⊢ x : B` means `x` has a hypothesis of type `B` in `Δ`
and all other assumptions are non-linear. -/
lemma HasTypeD.var_inv {n : ℕ} {Δ : Ctx n} {i : Fin n} {B : Ty}
    (h : HasTypeD Δ (Term.var i) B) :
    ∃ h', Δ (.inl i) = some h' ∧ h'.ty = B ∧ (Δ.set (.inl i) none).AllNonLin := by
  cases h with
  | var hi hrest => exact ⟨_, hi, rfl, hrest⟩

/-- Removing variable `0` is taking the tail. -/
lemma Ctx.remove_succ {n : ℕ} (Δ : Ctx (n + 1)) : Δ.remove Fin.succ = Δ.tail := by
  funext x; rcases x with j | a <;> rfl

/-- The `η⊸` case: from a typing of `λx. t x` (with `t` not mentioning `x`, i.e. a
weakening `t.rename Fin.succ`), recover a typing of `t`. -/
lemma etaLolli_aux {n : ℕ} {Γ : Ctx n} {Δ₁ Δ₂ : Ctx (n + 1)} {t : Term n} {A A' B : Ty}
    (h₁ : HasTypeD Δ₁ (t.rename Fin.succ) (A ⊸ B)) (h₂ : HasTypeD Δ₂ (Term.var 0) A)
    (hadd : Δ₁.Add Δ₂ (Γ.cons (some (.lin A')))) : HasTypeD Γ t (A' ⊸ B) := by
  obtain ⟨h', e, ty, hrest⟩ := h₂.var_inv
  have h0 := hadd (.inl 0)
  rw [e, Ctx.cons_inl_zero] at h0
  rcases h0.eq_lin with ⟨_, hc⟩ | ⟨hΔ₁0, hc⟩
  · cases hc
  · cases hc
    simp only [Hyp.ty] at ty
    subst ty
    have hΔ₂ : Δ₂.tail.AllNonLin := by
      rintro (j | a)
      · exact hrest.of_set (by simp)
      · exact hrest.of_set (by simp)
    have h1 := h₁.unrename (SubstSetup.zero Term.unit) hΔ₁0
    rw [Ctx.remove_succ] at h1
    rw [← Ctx.cons_tail Δ₁, ← Ctx.cons_tail Δ₂] at hadd
    exact h1.weaken hΔ₂ (Ctx.Add.of_cons hadd).1

/-- The `η⊗` case: from a typing of `let (x, y) = t in (x, y)`, recover a typing of
`t`. -/
lemma etaTensor_aux {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {Δ₁ Δ₂ : Ctx (n + 2)} {t : Term n}
    {A B A' B' : Ty} (h₁ : HasTypeD Γ₁ t (A ⊗ B)) (g₁ : HasTypeD Δ₁ (Term.var (Fin.succ 0)) A')
    (g₂ : HasTypeD Δ₂ (Term.var 0) B')
    (gadd : Δ₁.Add Δ₂ ((Γ₂.cons (some (.lin A))).cons (some (.lin B))))
    (hadd : Γ₁.Add Γ₂ Γ) : HasTypeD Γ t (A' ⊗ B') := by
  obtain ⟨k1, e1, ty1, r1⟩ := g₁.var_inv
  obtain ⟨k0, e0, ty0, r0⟩ := g₂.var_inv
  have a0 := gadd (.inl 0)
  rw [e0] at a0
  have := a0.some_of_nonLin' (r1.of_set fun h => (Fin.succ_ne_zero _).symm (Sum.inl_injective h))
  simp only [Ctx.cons_inl_zero, Option.some.injEq] at this
  subst this
  have a1 := gadd (.inl (Fin.succ 0))
  rw [e1] at a1
  have := a1.some_of_nonLin (r0.of_set fun h => Fin.succ_ne_zero _ (Sum.inl_injective h))
  rw [Ctx.cons_inl_succ, Ctx.cons_inl_zero, Option.some.injEq] at this
  subst this
  simp only [Hyp.ty] at ty0 ty1
  subst ty0 ty1
  refine h₁.weaken ?_ hadd
  rintro (j | a)
  · have := gadd (.inl j.succ.succ)
    exact this.nonLin_of
      (r1.of_set fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ (Sum.inl_injective h)))
      (r0.of_set fun h => Fin.succ_ne_zero _ (Sum.inl_injective h))
  · have := gadd (.inr a)
    exact this.nonLin_of (r1.of_set (by simp)) (r0.of_set (by simp))

/-- The `assoc` case: re-associate the two `copy`s.  The side condition that `x` is
not free in `t₃` appears as `t₃` being a weakening. -/
lemma assoc_aux {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {Δ₁ Δ₂ : Ctx (n + 1)} {t₁ : Term n}
    {t₂ t₃ : Term (n + 1)} {A B C : Ty}
    (h₁ : HasTypeD Γ₁ t₁ (.bang A)) (g₁ : HasTypeD Δ₁ t₂ (.bang B))
    (g₂ : HasTypeD (Δ₂.cons (some (.lin (.star B)))) (t₃.rename (Ren.up Fin.succ)) (.bang C))
    (gadd : Δ₁.Add Δ₂ (Γ₂.cons (some (.lin (.star A))))) (hadd : Γ₁.Add Γ₂ Γ) :
    HasTypeD Γ (copy (copy t₁ t₂) t₃) (.bang C) := by
  have a0 := gadd (.inl 0)
  rw [Ctx.cons_inl_zero] at a0
  rcases a0.eq_lin with ⟨e1, e2⟩ | ⟨_, e2⟩
  · have g₂' := g₂.unrename (SubstSetup.zero Term.unit).up e2
    rw [Ctx.remove_cons, Ctx.remove_succ] at g₂'
    rw [← Ctx.cons_tail Δ₁, e1] at g₁
    rw [← Ctx.cons_tail Δ₁, ← Ctx.cons_tail Δ₂] at gadd
    obtain ⟨Θ, hΘ, hΘ'⟩ := Ctx.Add.assoc' (Ctx.Add.of_cons gadd).1 hadd
    exact HasTypeD.copy (HasTypeD.copy h₁ g₁ hΘ) g₂' hΘ'
  · exfalso
    have hf := g₂.freeIn_of_lin (i := Fin.succ 0) (by rw [Ctx.cons_inl_succ]; exact e2)
    obtain ⟨i, hi⟩ := freeIn_rename _ _ _ hf
    cases i using Fin.cases with
    | zero => exact (Fin.succ_ne_zero 0).symm hi
    | succ i => exact Fin.succ_ne_zero _ (Fin.succ_injective _ hi)

/-- **Typability of the equational axioms (left to right).**  If `l ≡ r` is an axiom
of the equational theory and `Γ ⊢ l : A`, then `Γ ⊢ r : A`. -/
theorem EqAxiom.preserves {n : ℕ} {l r : Term n} (hax : EqAxiom l r) {Γ : Ctx n} {A : Ty}
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
        obtain ⟨Θ, hΘ, hΘ'⟩ := Ctx.Add.assoc gadd hadd
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
        exact h₁.weaken (Ctx.AllNonLin.of_cons hΓ₂).1 hadd
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

/-- `x : h ⊢ x : h.ty`, for the variable `0` in an otherwise empty context. -/
lemma HasTypeD.var_zero_single {n : ℕ} (h : Hyp) :
    HasTypeD ((Ctx.empty : Ctx n).cons (some h)) (Term.var 0) h.ty := by
  refine HasTypeD.var rfl ?_
  rintro (j | a)
  · cases j using Fin.cases
    · simp
    · rw [Ctx.set_ne _ _ (fun e => Fin.succ_ne_zero _ (Sum.inl_injective e))]; trivial
  · rw [Ctx.set_ne _ _ (by simp)]; trivial

/-- Adding an empty context extended by `none` on the right. -/
lemma Ctx.Add.cons_empty_right {n : ℕ} (Γ : Ctx n) (h : Option Hyp) :
    (Γ.cons none).Add ((Ctx.empty : Ctx n).cons h) (Γ.cons h) :=
  (Ctx.Add.empty_right Γ).cons (.noneLeft _)

namespace HasType

variable {n : ℕ} {Γ : Ctx n} {A B : Ty}

/-- `(η⊸)` from right to left. -/
theorem etaLolli_expand {t : Term n} (ht : HasType Γ t (A ⊸ B)) :
    HasType Γ (.lam (.app (t.rename Fin.succ) (.var 0))) (A ⊸ B) := by
  rw [hasType_iff_hasTypeD] at *
  exact .abs (.app (ht.shift nonLin_none) (HasTypeD.var_zero_single (.lin A))
    (Ctx.Add.cons_empty_right Γ _))

/-- `(η⊗)` from right to left. -/
theorem etaTensor_expand {t : Term n} (ht : HasType Γ t (A ⊗ B)) :
    HasType Γ (.letPair t (.pair (.var (Fin.succ 0)) (.var 0))) (A ⊗ B) := by
  rw [hasType_iff_hasTypeD] at *
  refine .tensorE ht (Γ₂ := Ctx.empty) (.tensorI (Γ₁ := (Ctx.empty.cons (some (.lin A))).cons none)
    ((HasTypeD.var_zero_single (.lin A)).shift nonLin_none)
    (HasTypeD.var_zero_single (n := n + 1) (.lin B)) ?_) (Ctx.Add.empty_right _)
  exact (Ctx.Add.empty_right _).cons (.noneLeft _)

/-- `(β1)` from right to left. -/
theorem betaUnit_expand {t : Term n} (ht : HasType Γ t A) :
    HasType Γ (.letUnit .unit t) A := by
  rw [hasType_iff_hasTypeD] at *
  exact .unitE (.unitI Ctx.AllNonLin.empty) ht (Ctx.Add.empty_left _)

/-- `(η1)` from right to left. -/
theorem etaUnit_expand {t : Term n} (ht : HasType Γ t .unit) :
    HasType Γ (.letUnit t .unit) .unit := by
  rw [hasType_iff_hasTypeD] at *
  exact .unitE ht (.unitI Ctx.AllNonLin.empty) (Ctx.Add.empty_right _)

/-- `(η!)` from right to left. -/
theorem etaBang_expand {t : Term n} (ht : HasType Γ t (.bang A)) :
    HasType Γ (.letBang t (.bang (.var 0))) (.bang A) := by
  rw [hasType_iff_hasTypeD] at *
  exact .bangE ht (Γ₂ := Ctx.empty)
    (.bangI (Ctx.AllNonLin.cons Ctx.AllNonLin.empty (nonLin_nonlin A))
      (HasTypeD.var_zero_single (.nonlin A))) (Ctx.Add.empty_right _)

/-- `(unitR)` from right to left. -/
theorem unitR_expand {t : Term n} (ht : HasType Γ t (.bang A)) :
    HasType Γ (.copy t (.borrow (.var 0))) (.bang A) := by
  rw [hasType_iff_hasTypeD] at *
  exact .copy ht (Γ₂ := Ctx.empty) (.borrow (HasTypeD.var_zero_single (.lin (.star A))))
    (Ctx.Add.empty_right _)

/-- `(assoc)` from right to left. -/
theorem assoc_expand {t₁ : Term n} {t₂ t₃ : Term (n + 1)} {C : Ty}
    (ht : HasType Γ (.copy (.copy t₁ t₂) t₃) (.bang C)) :
    HasType Γ (.copy t₁ (.copy t₂ (t₃.rename (Ren.up Fin.succ)))) (.bang C) := by
  rw [hasType_iff_hasTypeD] at *
  cases ht with
  | copy h hc hadd =>
    cases h with
    | copy g₁ g₂ gadd =>
      obtain ⟨Θ, hΘ, hΘ'⟩ := Ctx.Add.assoc gadd hadd
      refine .copy g₁ (.copy g₂ (hc.rename ((Ctx.renCtx_succ _ nonLin_none).cons _))
        (hΘ.cons (HypAdd.none_right _))) hΘ'

end HasType

end LCU
