module
public import RequestProject.Common.Ctx.Pointwise

/-!
# Length-indexed contexts: algebra of pointwise relations

Laws of a relation `R a b c` (read `a + b = c`) on entries lift to `Ctx.Forall₃ R`
(functionality, associativity, interchange, units).
-/

@[expose] public section

namespace Ctx

variable {α β γ δ : Type} {n m : ℕ}

/-! ## Algebra of pointwise relations

Laws of a relation `R a b c` (read `a + b = c`) on entries lift to the pointwise relation
`Forall₃ R` on contexts.  These are used for context addition in both papers. -/

section Forall₃Algebra

variable {R : α → α → α → Prop}

/-- A functional relation lifts to a functional relation. -/
lemma Forall₃.func {Γ₁ Γ₂ Γ Γ' : Ctx α n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) (h' : Forall₃ R Γ₁ Γ₂ Γ')
    (hR : ∀ {a b c c'}, R a b c → R a b c' → c = c') : Γ = Γ' := by
  induction h with
  | nil => cases h'; rfl
  | snoc _ habc ih => cases h' with | snoc h' habc' => rw [ih h', hR habc habc']

/-- Associativity lifts. -/
lemma Forall₃.assoc
    {Γ₁ Γ₂ Γ₃ Γ₁₂ Γ : Ctx α n} (h₁ : Forall₃ R Γ₁ Γ₂ Γ₁₂) (h₂ : Forall₃ R Γ₁₂ Γ₃ Γ)
    (hR : ∀ {a b ab c abc}, R a b ab → R ab c abc → ∃ bc, R b c bc ∧ R a bc abc) :
    ∃ Γ₂₃, Forall₃ R Γ₂ Γ₃ Γ₂₃ ∧ Forall₃ R Γ₁ Γ₂₃ Γ := by
  induction h₁ with
  | nil => cases Γ₃; cases Γ; exact ⟨Ctx.nil, .nil, .nil⟩
  | snoc _ habc ih =>
    cases h₂ with
    | snoc h₂ h' =>
      obtain ⟨Δ, hΔ₁, hΔ₂⟩ := ih h₂
      obtain ⟨x, hx₁, hx₂⟩ := hR habc h'
      exact ⟨Δ ,, x, .snoc hΔ₁ hx₁, .snoc hΔ₂ hx₂⟩

/-- The interchange law lifts. -/
lemma Forall₃.interchange
    {A₁ A₂ A B₁ B₂ B C : Ctx α n} (h₁ : Forall₃ R A₁ A₂ A) (h₂ : Forall₃ R B₁ B₂ B)
    (h : Forall₃ R A B C)
    (hR : ∀ {a₁ a₂ a b₁ b₂ b c}, R a₁ a₂ a → R b₁ b₂ b → R a b c →
      ∃ c₁ c₂, R a₁ b₁ c₁ ∧ R a₂ b₂ c₂ ∧ R c₁ c₂ c) :
    ∃ C₁ C₂, Forall₃ R A₁ B₁ C₁ ∧ Forall₃ R A₂ B₂ C₂ ∧ Forall₃ R C₁ C₂ C := by
  induction h₁ with
  | nil => cases h₂; cases h; exact ⟨Ctx.nil, Ctx.nil, .nil, .nil, .nil⟩
  | snoc _ ha ih =>
    cases h₂ with
    | snoc h₂ hb =>
      cases h with
      | snoc h hc =>
        obtain ⟨C₁, C₂, h₁', h₂', h'⟩ := ih h₂ h
        obtain ⟨c₁, c₂, hc₁, hc₂, hc'⟩ := hR ha hb hc
        exact ⟨C₁ ,, c₁, C₂ ,, c₂, .snoc h₁' hc₁, .snoc h₂' hc₂, .snoc h' hc'⟩

/-- A property preserved by the relation lifts. -/
lemma Forall₃.all {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P a → P b → P c) (h₁ : All P Γ₁) (h₂ : All P Γ₂) : All P Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih =>
    rw [all_snoc] at h₁ h₂
    exact .snoc (ih h₁.1 h₂.1) (hR habc h₁.2 h₂.2)

/-- A property reflected by the relation (on the left) lifts. -/
lemma Forall₃.all_left {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P c → P a) (hΓ : All P Γ) : All P Γ₁ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => rw [all_snoc] at hΓ; exact .snoc (ih hΓ.1) (hR habc hΓ.2)

/-- A property reflected by the relation (on the right) lifts. -/
lemma Forall₃.all_right {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P c → P b) (hΓ : All P Γ) : All P Γ₂ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => rw [all_snoc] at hΓ; exact .snoc (ih hΓ.1) (hR habc hΓ.2)

/-- A relation that is reflexive on entries satisfying `P` is reflexive on contexts whose
entries satisfy `P`. -/
lemma Forall₃.of_all {P : α → Prop} (hR : ∀ {a}, P a → R a a a) {Γ : Ctx α n} (h : All P Γ) :
    Forall₃ R Γ Γ Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ ha ih => exact .snoc ih (hR ha)

/-- A unit on entries gives a unit on contexts. -/
lemma Forall₃.replicate_left {e : α} (hR : ∀ a, R e a a) (Γ : Ctx α n) :
    Forall₃ R (replicate n e) Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ a ih => exact .snoc ih (hR a)

lemma Forall₃.replicate_right {e : α} (hR : ∀ a, R a e a) (Γ : Ctx α n) :
    Forall₃ R Γ (replicate n e) Γ := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ a ih => exact .snoc ih (hR a)

lemma Forall₃.eq_of_replicate_left {e : α} {Γ Γ' : Ctx α n}
    (h : Forall₃ R (replicate n e) Γ Γ') (hR : ∀ {a c}, R e a c → a = c) : Γ = Γ' := by
  induction Γ with
  | nil => cases Γ'; rfl
  | snoc Γ a ih =>
    cases Γ' with
    | snoc Γ' c =>
      rw [replicate, forall₃_snoc] at h
      rw [ih h.1, hR h.2]

lemma Forall₃.eq_of_replicate_right {e : α} {Γ Γ' : Ctx α n}
    (h : Forall₃ R Γ (replicate n e) Γ') (hR : ∀ {a c}, R a e c → a = c) : Γ = Γ' := by
  induction Γ with
  | nil => cases Γ'; rfl
  | snoc Γ a ih =>
    cases Γ' with
    | snoc Γ' c =>
      rw [replicate, forall₃_snoc] at h
      rw [ih h.1, hR h.2]

end Forall₃Algebra

end Ctx
