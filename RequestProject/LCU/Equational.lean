module
public import RequestProject.LCU.Substitution
public import RequestProject.LCU.Values

/-!
# Equational theory (Section 3.2)

The equational theory `t₁ ≡ t₂` of the LCU calculus: the standard `βη`-equalities of
the multiplicative linear λ-calculus fragment, `β!`/`η!`, and the relative monad
laws `unitR`, `unitL`, `assoc` for the uniqueness fragment, closed under
equivalence and congruence.

The paper notes that "the typability of these axioms relies on the admissibility of
linear and non-linear substitution".  We prove (`EqAxiom.preserves`) that every
axiom, oriented from left to right, preserves typing, and (`HasType.etaLolli_expand`,
`HasType.assoc_expand`, ...) that the axioms not involving a substitution also
preserve typing from right to left.
-/

@[expose] public section

namespace LCU

open Term

/-- The axioms of the equational theory, `l ≡ r`. In de Bruijn notation:

* `(β⊸)` `(λx. t) t' ≡ [t'/x]t` and `(η⊸)` `λx. t x ≡ t` (`x` not free in `t`);
* `(β⊗)` `let (x, y) = (t₁, t₂) in t ≡ [t₁/x, t₂/y]t` and
  `(η⊗)` `let (x, y) = t in (x, y) ≡ t`;
* `(β1)` `let unit = unit in t ≡ t` and `(η1)` `let unit = t in unit ≡ t`;
* `(β!)` `let! x = !t in t' ≡ [t/x]t'` and `(η!)` `let! x = t in !x ≡ t`;
* `(unitR)` `copy t as x in &x ≡ t`;
* `(unitL)` `copy &v as x in t' ≡ [v/x]t'` for values `v`;
* `(assoc)` `copy t₁ as x in (copy t₂ as y in t₃) ≡ copy (copy t₁ as x in t₂) as y in t₃`
  where `x` is not free in `t₃` (in de Bruijn form, the left-hand `t₃` is a weakening
  of the right-hand one). -/
inductive EqAxiom : {n : ℕ} → Term n → Term n → Prop where
  | betaLolli {n : ℕ} (t : Term (n + 1)) (t' : Term n) : EqAxiom (app (lam t) t') (subst1 t' t)
  | etaLolli {n : ℕ} (t : Term n) :
      EqAxiom (lam (app (t.rename Fin.succ) (var 0))) t
  | betaTensor {n : ℕ} (t₁ t₂ : Term n) (t : Term (n + 2)) :
      EqAxiom (letPair (pair t₁ t₂) t) (subst2 t₁ t₂ t)
  | etaTensor {n : ℕ} (t : Term n) :
      EqAxiom (letPair t (pair (var (Fin.succ 0)) (var 0))) t
  | betaUnit {n : ℕ} (t : Term n) : EqAxiom (letUnit unit t) t
  | etaUnit {n : ℕ} (t : Term n) : EqAxiom (letUnit t unit) t
  | betaBang {n : ℕ} (t : Term n) (t' : Term (n + 1)) : EqAxiom (letBang (bang t) t') (subst1 t t')
  | etaBang {n : ℕ} (t : Term n) : EqAxiom (letBang t (bang (var 0))) t
  | unitR {n : ℕ} (t : Term n) : EqAxiom (copy t (borrow (var 0))) t
  | unitL {n : ℕ} (v : Term n) (t' : Term (n + 1)) :
      IsValue v → EqAxiom (copy (borrow v) t') (subst1 v t')
  | assoc {n : ℕ} (t₁ : Term n) (t₂ : Term (n + 1)) (t₃ : Term (n + 1)) :
      EqAxiom (copy t₁ (copy t₂ (t₃.rename (Ren.up Fin.succ)))) (copy (copy t₁ t₂) t₃)

/-- The equational theory `≡`: the congruence closure of `EqAxiom`. -/
inductive Equiv : {n : ℕ} → Term n → Term n → Prop where
  | ax {n : ℕ} {t t' : Term n} : EqAxiom t t' → Equiv t t'
  | refl {n : ℕ} (t : Term n) : Equiv t t
  | symm {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv t' t
  | trans {n : ℕ} {t t' t'' : Term n} : Equiv t t' → Equiv t' t'' → Equiv t t''
  | lam {n : ℕ} {t t' : Term (n + 1)} : Equiv t t' → Equiv (lam t) (lam t')
  | app {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (app t₁ t₂) (app t₁' t₂')
  | pair {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (pair t₁ t₂) (pair t₁' t₂')
  | letPair {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 2)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letPair t₁ t₂) (letPair t₁' t₂')
  | letUnit {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letUnit t₁ t₂) (letUnit t₁' t₂')
  | bang {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (bang t) (bang t')
  | letBang {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 1)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letBang t₁ t₂) (letBang t₁' t₂')
  | borrow {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (borrow t) (borrow t')
  | copy {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 1)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (copy t₁ t₂) (copy t₁' t₂')
  | star {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (star t) (star t')

@[inherit_doc] infix:50 " ≡ₗ " => Equiv

/-! ## Free variables and linear occurrence -/

/-- `FreeIn i t`: the variable `i` occurs free in `t`. -/
def FreeIn : {n : ℕ} → Fin n → Term n → Prop
  | _, i, .var j => i = j
  | _, i, .lam t => FreeIn i.succ t
  | _, i, .app t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .pair t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .letPair t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ.succ t₂
  | _, _, .unit => False
  | _, i, .letUnit t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .bang t => FreeIn i t
  | _, i, .letBang t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ t₂
  | _, i, .borrow t => FreeIn i t
  | _, i, .copy t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ t₂
  | _, i, .star t => FreeIn i t
  | _, _, .nat _ => False
  | _, _, .float _ => False
  | _, _, .prim _ => False
  | _, _, .ref _ => False

lemma Ren.exists_of_up {n m : ℕ} {ρ : Fin n → Fin m} {j : Fin m} :
    (∃ i, Ren.up ρ i = j.succ) → ∃ i, ρ i = j
  | ⟨i, hi⟩ => by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.succ_ne_zero j).symm
    | succ i => exact ⟨i, by simpa using hi⟩

lemma freeIn_rename {n m : ℕ} (ρ : Fin n → Fin m) (t : Term n) :
    ∀ j, FreeIn j (t.rename ρ) → ∃ i, ρ i = j := by
  induction t generalizing m with
  | var i => intro j h; exact ⟨i, (h : j = ρ i).symm⟩
  | lam _ ih => intro j h; exact Ren.exists_of_up (ih _ _ h)
  | bang _ ih | borrow _ ih | star _ ih => intro j h; exact ih _ _ h
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | letPair _ _ ih₁ ih₂ | letUnit _ _ ih₁ ih₂
  | letBang _ _ ih₁ ih₂ | copy _ _ ih₁ ih₂ =>
    intro j h
    rcases h with h | h
    · exact ih₁ _ _ h
    · first
        | exact ih₂ _ _ h
        | exact Ren.exists_of_up (ih₂ _ _ h)
        | exact Ren.exists_of_up (Ren.exists_of_up (ih₂ _ _ h))
  | _ => intro j h; exact h.elim

/-- Linear variables occur free in well-typed terms. -/
theorem HasTypeD.freeIn_of_lin {n : ℕ} {Γ : Ctx n} {t : Term n} {B : Ty}
    (ht : HasTypeD Γ t B) : ∀ {i : Fin n} {A : Ty}, Γ (.inl i) = some (.lin A) → FreeIn i t := by
  induction ht with
  | var hi hrest =>
    intro i A h
    simpa using Ctx.AllNonLin.set_not_lin hrest h
  | abs _ ih => intro i A h; exact ih (i := i.succ) h
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro i A h
    have := hadd (.inl i); rw [h] at this
    rcases this.eq_lin with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro i A h; exact (hΓ.not_lin h).elim
  | borrow _ ih => intro i A h; exact ih h
  | nec _ hΓ _ => intro i A h; have := hΓ i; rw [h] at this; exact this.elim
  | ref _ hrest =>
    intro i A h
    have := Ctx.AllNonLin.set_not_lin hrest h
    simp at this

/-- Strengthening: removing an absent variable from a renamed term. -/
theorem HasTypeD.unrename {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n}
    (hs : SubstSetup ρ i σ) {Δ : Ctx m} {t : Term n} {B : Ty}
    (ht : HasTypeD Δ (t.rename ρ) B) (hi : Δ (.inl i) = none) :
    HasTypeD (Δ.remove ρ) t B := by
  have := ht.subst_gen hs (Γ' := Ctx.empty) (by rw [hi]; exact Ctx.AllNonLin.empty)
    (Ctx.Add.empty_left _)
  rwa [subst_rename, show σ ∘ ρ = Term.var from funext hs.var, subst_var] at this

/-! ## Typability of the axioms -/

namespace HasTypeD

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

lemma HasTypeD.var_inv {n : ℕ} {Δ : Ctx n} {i : Fin n} {B : Ty}
    (h : HasTypeD Δ (Term.var i) B) :
    ∃ h', Δ (.inl i) = some h' ∧ h'.ty = B ∧ (Δ.set (.inl i) none).AllNonLin := by
  cases h with
  | var hi hrest => exact ⟨_, hi, rfl, hrest⟩

lemma Ctx.remove_succ {n : ℕ} (Δ : Ctx (n + 1)) : Δ.remove Fin.succ = Δ.tail := by
  funext x; rcases x with j | a <;> rfl

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

lemma HasTypeD.var_zero_single {n : ℕ} (h : Hyp) :
    HasTypeD ((Ctx.empty : Ctx n).cons (some h)) (Term.var 0) h.ty := by
  refine HasTypeD.var rfl ?_
  rintro (j | a)
  · cases j using Fin.cases
    · simp
    · rw [Ctx.set_ne _ _ (fun e => Fin.succ_ne_zero _ (Sum.inl_injective e))]; trivial
  · rw [Ctx.set_ne _ _ (by simp)]; trivial

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
