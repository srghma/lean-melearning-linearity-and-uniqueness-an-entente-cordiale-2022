module
public import RequestProject.LCU.Sec3_1_Calculus.CtxAlgebra

/-!
# A dereliction-free presentation of the typing rules

To streamline the metatheory we use an equivalent presentation of the typing
judgment without the dereliction rule `der`, in which instead the variable rule
also accepts non-linear assumptions: `[Γ], x : [A] ⊢ x : A`.
We show that `der` is admissible in this system, so the two systems are equivalent
(`hasType_iff_hasTypeD`).

## Why a second system?

In `HasType`, dereliction `der` can be applied anywhere in a derivation, so every
induction on typing derivations would need a case for it, and inversion lemmas
("if `Γ ⊢ λx. t : C` then ...") would have to look through arbitrarily many `der`
steps.  In `HasTypeD`, every derivation is syntax-directed.  Almost all metatheory
(weakening, substitution, subject reduction, progress, ...) is therefore proved for
`HasTypeD` and transported to `HasType` with `hasType_iff_hasTypeD`.

## Main results

* `HasTypeD.der`: dereliction is admissible in `HasTypeD`.
* `hasType_iff_hasTypeD`: `HasType Γ t A ↔ HasTypeD Γ t A`.
-/

@[expose] public section

namespace LCU

open Term

/-- Typing without dereliction (an auxiliary, equivalent presentation of `HasType`). -/
inductive HasTypeD : {n : ℕ} → Ctx n → Term n → Ty → Prop where
  | var {n : ℕ} {Γ : Ctx n} {i : Fin n} {h : Hyp} :
      Γ (.inl i) = some h → (Γ.set (.inl i) none).AllNonLin →
      HasTypeD Γ (var i) h.ty
  | abs {n : ℕ} {Γ : Ctx n} {t : Term (n + 1)} {A B : Ty} :
      HasTypeD (Γ.cons (some (.lin A))) t B → HasTypeD Γ (lam t) (A ⊸ B)
  | app {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ t₂ : Term n} {A B : Ty} :
      HasTypeD Γ₁ t₁ (A ⊸ B) → HasTypeD Γ₂ t₂ A → Γ₁.Add Γ₂ Γ → HasTypeD Γ (app t₁ t₂) B
  | tensorI {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ t₂ : Term n} {A B : Ty} :
      HasTypeD Γ₁ t₁ A → HasTypeD Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasTypeD Γ (pair t₁ t₂) (A ⊗ B)
  | tensorE {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ : Term n} {t₂ : Term (n + 2)} {A B C : Ty} :
      HasTypeD Γ₁ t₁ (A ⊗ B) →
      HasTypeD ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (letPair t₁ t₂) C
  | unitI {n : ℕ} {Γ : Ctx n} : Γ.AllNonLin → HasTypeD Γ unit .unit
  | unitE {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ t₂ : Term n} {B : Ty} :
      HasTypeD Γ₁ t₁ .unit → HasTypeD Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasTypeD Γ (letUnit t₁ t₂) B
  | bangI {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} :
      Γ.AllNonLin → HasTypeD Γ t A → HasTypeD Γ (bang t) (.bang A)
  | bangE {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ : Term n} {t₂ : Term (n + 1)} {A B : Ty} :
      HasTypeD Γ₁ t₁ (.bang A) → HasTypeD (Γ₂.cons (some (.nonlin A))) t₂ B →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (letBang t₁ t₂) B
  | borrow {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} :
      HasTypeD Γ t (.star A) → HasTypeD Γ (borrow t) (.bang A)
  | copy {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} {t₁ : Term n} {t₂ : Term (n + 1)} {A B : Ty} :
      HasTypeD Γ₁ t₁ (.bang A) → HasTypeD (Γ₂.cons (some (.lin (.star A)))) t₂ (.bang B) →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (copy t₁ t₂) (.bang B)
  | nec {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} :
      HasTypeD Γ.refsOnly t A → Γ.VarsNonLin → HasTypeD Γ (star t) (.star A)
  | natI {n : ℕ} {Γ : Ctx n} {k : ℕ} : Γ.AllNonLin → HasTypeD Γ (nat k) .nat
  | floatI {n : ℕ} {Γ : Ctx n} {x : Float} : Γ.AllNonLin → HasTypeD Γ (float x) .float
  | prim {n : ℕ} {Γ : Ctx n} {p : Prim} : Γ.AllNonLin → HasTypeD Γ (prim p) p.ty
  | ref {n : ℕ} {Γ : Ctx n} {a : ℕ} {h : Hyp} :
      Γ (.inr a) = some h → (Γ.set (.inr a) none).AllNonLin →
      HasTypeD Γ (ref a) (.array h.ty)

/-! ## Auxiliary context lemmas -/

namespace Ctx

variable {n : ℕ}

/-- Lifting a name under a variable binder. -/
def liftName : Fin n ⊕ ℕ → Fin (n + 1) ⊕ ℕ := Sum.map Fin.succ id

@[simp] lemma liftName_inl (i : Fin n) : liftName (.inl i) = .inl i.succ := rfl
@[simp] lemma liftName_inr (a : ℕ) : liftName (n := n) (.inr a) = .inr a := rfl

/-- Looking up a lifted name in an extended context. -/
lemma cons_liftName (Γ : Ctx n) (h : Option Hyp) (x : Fin n ⊕ ℕ) :
    Γ.cons h (liftName x) = Γ x := by
  rcases x with i | a <;> rfl

/-- Updating a name commutes with extending the context. -/
lemma cons_set (Γ : Ctx n) (h : Option Hyp) (x : Fin n ⊕ ℕ) (h' : Option Hyp) :
    (Γ.set x h').cons h = (Γ.cons h).set (liftName x) h' := by
  rcases x with i | a
  · exact cons_set_succ Γ h i h'
  · funext y; rcases y with j | b
    · cases j using Fin.cases <;> rfl
    · by_cases hb : b = a
      · subst hb; simp
      · rw [cons_inr, set_ne _ _ (by simpa using hb), set_ne _ _ (by simpa using hb)]; rfl

lemma refsOnly_set_inr (Γ : Ctx n) (a : ℕ) (h : Option Hyp) :
    (Γ.set (.inr a) h).refsOnly = Γ.refsOnly.set (.inr a) h := by
  funext y; rcases y with j | b
  · simp [set]
  · by_cases hb : b = a
    · subst hb; simp
    · rw [refsOnly_inr, set_ne _ _ (by simpa using hb), set_ne _ _ (by simpa using hb)]; rfl

lemma VarsNonLin.set_inr {Γ : Ctx n} (hΓ : Γ.VarsNonLin) (a : ℕ) (h : Option Hyp) :
    (Γ.set (.inr a) h).VarsNonLin := by
  intro i; rw [set_ne _ _ (by simp)]; exact hΓ i

/-- A non-linear context contains no linear assumption. -/
lemma AllNonLin.not_lin {Γ : Ctx n} (hΓ : Γ.AllNonLin) {x : Fin n ⊕ ℕ} {A : Ty}
    (hx : Γ x = some (.lin A)) : False := by
  have := hΓ x; rw [hx] at this; exact this

lemma AllNonLin.set_not_lin {Γ : Ctx n} {x y : Fin n ⊕ ℕ} {h : Option Hyp}
    (hΓ : (Γ.set x h).AllNonLin) {A : Ty} (hy : Γ y = some (.lin A)) : y = x := by
  by_contra hne
  have := hΓ y; rw [set_ne _ _ hne, hy] at this; exact this

/-- Dereliction distributes over a sum: turning the linear assumption `x : A` of
`Γ₁ + Γ₂` into `x : [A]` can be done in whichever summand contains `x : A`. -/
lemma Add.der {Γ₁ Γ₂ Γ : Ctx n} (hadd : Γ₁.Add Γ₂ Γ) {x : Fin n ⊕ ℕ} {A : Ty}
    (hx : Γ x = some (.lin A)) :
    (Γ₁ x = some (.lin A) ∧ (Γ₁.set x (some (.nonlin A))).Add Γ₂ (Γ.set x (some (.nonlin A)))) ∨
    (Γ₂ x = some (.lin A) ∧ Γ₁.Add (Γ₂.set x (some (.nonlin A))) (Γ.set x (some (.nonlin A)))) := by
  have := hadd x; rw [hx] at this
  rcases this.der with ⟨hd, hl⟩ | ⟨hd, hl⟩
  · left; refine ⟨hl, ?_⟩
    have := hadd.set (x := x) hd; rwa [Ctx.set_eq_self rfl] at this
  · right; refine ⟨hl, ?_⟩
    have := hadd.set (x := x) hd; rwa [Ctx.set_eq_self rfl] at this

end Ctx

/-! ## Admissibility of dereliction and equivalence with `HasType` -/

/-- Internal tactic: `split_rule h₁ h₂ hadd` applies whichever of the context-splitting
rules `app`, `tensorI`, `tensorE`, `unitE`, `bangE`, `copy` fits the goal. -/
macro "split_rule " h₁:term:max h₂:term:max hadd:term:max : tactic => `(tactic| first
  | exact HasTypeD.app $h₁ $h₂ $hadd | exact HasTypeD.tensorI $h₁ $h₂ $hadd
  | exact HasTypeD.tensorE $h₁ $h₂ $hadd | exact HasTypeD.unitE $h₁ $h₂ $hadd
  | exact HasTypeD.bangE $h₁ $h₂ $hadd | exact HasTypeD.copy $h₁ $h₂ $hadd)

namespace HasTypeD

/-- Dereliction is admissible in the dereliction-free system, for variables and
array references alike. -/
theorem der {n : ℕ} {Γ : Ctx n} {t : Term n} {B : Ty} (ht : HasTypeD Γ t B) :
    ∀ {x : Fin n ⊕ ℕ} {A : Ty}, Γ x = some (.lin A) →
      HasTypeD (Γ.set x (some (.nonlin A))) t B := by
  induction ht with
  | var hi hrest | ref hi hrest =>
    intro x A hx
    obtain rfl := Ctx.AllNonLin.set_not_lin hrest hx
    rw [hi] at hx; cases hx
    first
    | exact HasTypeD.var (h := .nonlin A) (by simp) (by rw [Ctx.set_set]; exact hrest)
    | exact HasTypeD.ref (h := .nonlin A) (by simp) (by rw [Ctx.set_set]; exact hrest)
  | abs _ ih =>
    intro x A hx
    refine HasTypeD.abs ?_
    rw [Ctx.cons_set]
    exact ih (by rw [Ctx.cons_liftName]; exact hx)
  | app h₁ h₂ hadd ih₁ ih₂ | tensorI h₁ h₂ hadd ih₁ ih₂ | tensorE h₁ h₂ hadd ih₁ ih₂
  | unitE h₁ h₂ hadd ih₁ ih₂ | bangE h₁ h₂ hadd ih₁ ih₂ | copy h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · split_rule (ih₁ hl) h₂ hd
    · split_rule h₁
        (by (try simp only [Ctx.cons_set]); exact ih₂ (by simpa only [Ctx.cons_liftName])) hd
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro x A hx; exact (hΓ.not_lin hx).elim
  | borrow _ ih => intro x A hx; exact HasTypeD.borrow (ih hx)
  | @nec n Γ t A' _ hΓ ih =>
    intro x A hx
    rcases x with i | a
    · have := hΓ i; rw [hx] at this; exact this.elim
    · refine HasTypeD.nec ?_ (hΓ.set_inr a _)
      rw [Ctx.refsOnly_set_inr]
      exact ih (by simpa using hx)

end HasTypeD

/-- The paper's typing judgment and the dereliction-free one coincide. -/
theorem hasType_iff_hasTypeD {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} :
    HasType Γ t A ↔ HasTypeD Γ t A := by
  constructor
  · intro h
    induction h with
    | var hi hrest => exact HasTypeD.var (h := .lin _) hi hrest
    | der _ hi ih => exact ih.der hi
    | _ => constructor <;> assumption
  · intro h
    induction h with
    | @var n Γ i h hi hrest =>
      cases h with
      | lin A => exact HasType.var hi hrest
      | nonlin A =>
        have e : Γ = (Γ.set (.inl i) (some (.lin A))).set (.inl i) (some (.nonlin A)) := by
          rw [Ctx.set_set, Ctx.set_eq_self hi]
        rw [e]
        show HasType _ _ A
        exact HasType.der (HasType.var (by simp) (by rw [Ctx.set_set]; exact hrest)) (by simp)
    | _ => constructor <;> assumption

end LCU
