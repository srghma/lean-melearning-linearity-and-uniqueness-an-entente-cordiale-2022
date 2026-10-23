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

* `HasTypeD.derVar`, `HasTypeD.derRef`: dereliction (for variables and for array
  references) is admissible in `HasTypeD`.
* `hasType_iff_hasTypeD`: `HasType Γ t A ↔ HasTypeD Γ t A`.
-/

@[expose] public section

namespace LCU

open Term

/-- Typing without dereliction (an auxiliary, equivalent presentation of `HasType`). -/
inductive HasTypeD : {n ρ : ℕ} → TCtx n ρ → Term n ρ → Ty → Prop where
  | var {n ρ : ℕ} {Γ : TCtx n ρ} {i : Var n} {h : Hyp Ty} :
      Γ.vars.Pick NonLin i (some h) → Γ.refs.All NonLin → HasTypeD Γ (var i) h.ty
  | abs {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term (n + 1) ρ} {A B : Ty} :
      HasTypeD (Γ.cons (some (.lin A))) t B → HasTypeD Γ (lam t) (A ⊸ B)
  | app {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {A B : Ty} :
      HasTypeD Γ₁ t₁ (A ⊸ B) → HasTypeD Γ₂ t₂ A → Γ₁.Add Γ₂ Γ → HasTypeD Γ (app t₁ t₂) B
  | tensorI {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {A B : Ty} :
      HasTypeD Γ₁ t₁ A → HasTypeD Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasTypeD Γ (pair t₁ t₂) (A ⊗ B)
  | tensorE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 2) ρ} {A B C : Ty} :
      HasTypeD Γ₁ t₁ (A ⊗ B) →
      HasTypeD ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (letPair t₁ t₂) C
  | unitI {n ρ : ℕ} {Γ : TCtx n ρ} : Γ.AllNonLin → HasTypeD Γ unit .unit
  | unitE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {B : Ty} :
      HasTypeD Γ₁ t₁ .unit → HasTypeD Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasTypeD Γ (letUnit t₁ t₂) B
  | bangI {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      Γ.AllNonLin → HasTypeD Γ t A → HasTypeD Γ (bang t) (.bang A)
  | bangE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 1) ρ} {A B : Ty} :
      HasTypeD Γ₁ t₁ (.bang A) → HasTypeD (Γ₂.cons (some (.nonlin A))) t₂ B →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (letBang t₁ t₂) B
  | borrow {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      HasTypeD Γ t (.star A) → HasTypeD Γ (borrow t) (.bang A)
  | copy {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 1) ρ} {A B : Ty} :
      HasTypeD Γ₁ t₁ (.bang A) → HasTypeD (Γ₂.cons (some (.lin (.star A)))) t₂ (.bang B) →
      Γ₁.Add Γ₂ Γ → HasTypeD Γ (copy t₁ t₂) (.bang B)
  | nec {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      HasTypeD Γ.refsOnly t A → Γ.VarsNonLin → HasTypeD Γ (star t) (.star A)
  | natI {n ρ : ℕ} {Γ : TCtx n ρ} {k : ℕ} : Γ.AllNonLin → HasTypeD Γ (nat k) .nat
  | floatI {n ρ : ℕ} {Γ : TCtx n ρ} {x : FloatLit} : Γ.AllNonLin → HasTypeD Γ (float x) .float
  | prim {n ρ : ℕ} {Γ : TCtx n ρ} {p : Prim} : Γ.AllNonLin → HasTypeD Γ (prim p) p.ty
  | ref {n ρ : ℕ} {Γ : TCtx n ρ} {a : Var ρ} {h : Hyp ArrTy} :
      Γ.refs.Pick NonLin a (some h) → Γ.vars.All NonLin → HasTypeD Γ (ref a) h.ty.toTy

/-! ## Auxiliary context lemmas -/

namespace TCtx

variable {n ρ : ℕ}

/-- Dereliction distributes over a sum: turning the linear assumption `x : A` of
`Γ₁ + Γ₂` into `x : [A]` can be done in whichever summand contains `x : A`. -/
lemma Add.derVar {Γ₁ Γ₂ Γ : TCtx n ρ} (hadd : Γ₁.Add Γ₂ Γ) {i : Var n} {A : Ty}
    (hx : Γ.vars.get i = some (.lin A)) :
    (Γ₁.vars.get i = some (.lin A) ∧
      (Γ₁.setVar i (some (.nonlin A))).Add Γ₂ (Γ.setVar i (some (.nonlin A)))) ∨
    (Γ₂.vars.get i = some (.lin A) ∧
      Γ₁.Add (Γ₂.setVar i (some (.nonlin A))) (Γ.setVar i (some (.nonlin A)))) := by
  have := hadd.vars.get i; rw [hx] at this
  rcases this.der with ⟨hd, hl⟩ | ⟨hd, hl⟩
  · left; refine ⟨hl, ?_⟩
    have := hadd.setVar (i := i) hd
    rwa [setVar_get] at this
  · right; refine ⟨hl, ?_⟩
    have := hadd.setVar (i := i) hd
    rwa [setVar_get] at this

/-- Dereliction of an array reference distributes over a sum. -/
lemma Add.derRef {Γ₁ Γ₂ Γ : TCtx n ρ} (hadd : Γ₁.Add Γ₂ Γ) {a : Var ρ} {A : ArrTy}
    (hx : Γ.refs.get a = some (.lin A)) :
    (Γ₁.refs.get a = some (.lin A) ∧
      (Γ₁.setRef a (some (.nonlin A))).Add Γ₂ (Γ.setRef a (some (.nonlin A)))) ∨
    (Γ₂.refs.get a = some (.lin A) ∧
      Γ₁.Add (Γ₂.setRef a (some (.nonlin A))) (Γ.setRef a (some (.nonlin A)))) := by
  have := hadd.refs.get a; rw [hx] at this
  rcases this.der with ⟨hd, hl⟩ | ⟨hd, hl⟩
  · left; refine ⟨hl, ?_⟩
    have := hadd.setRef (a := a) hd
    rwa [setRef_get] at this
  · right; refine ⟨hl, ?_⟩
    have := hadd.setRef (a := a) hd
    rwa [setRef_get] at this

end TCtx

/-! ## Admissibility of dereliction and equivalence with `HasType` -/

/-- Internal tactic: `split_rule h₁ h₂ hadd` applies whichever of the context-splitting
rules `app`, `tensorI`, `tensorE`, `unitE`, `bangE`, `copy` fits the goal. -/
macro "split_rule " h₁:term:max h₂:term:max hadd:term:max : tactic => `(tactic| first
  | exact HasTypeD.app $h₁ $h₂ $hadd | exact HasTypeD.tensorI $h₁ $h₂ $hadd
  | exact HasTypeD.tensorE $h₁ $h₂ $hadd | exact HasTypeD.unitE $h₁ $h₂ $hadd
  | exact HasTypeD.bangE $h₁ $h₂ $hadd | exact HasTypeD.copy $h₁ $h₂ $hadd)

namespace HasTypeD

/-- Dereliction of a variable is admissible in the dereliction-free system. -/
theorem derVar {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {B : Ty} (ht : HasTypeD Γ t B) :
    ∀ {i : Var n} {A : Ty}, Γ.vars.get i = some (.lin A) →
      HasTypeD (Γ.setVar i (some (.nonlin A))) t B := by
  induction ht with
  | var hi hr =>
    intro x A hx
    obtain rfl := hi.eq_of_not (by rw [hx]; exact not_nonLin_lin A)
    rw [hi.get] at hx; cases hx
    exact HasTypeD.var (h := .nonlin A) (hi.set _) hr
  | ref hi hv =>
    intro x A hx; exact (not_lin_of_all hv hx).elim
  | abs _ ih =>
    intro x A hx
    exact HasTypeD.abs (ih (i := .succ x) hx)
  | app h₁ h₂ hadd ih₁ ih₂ | tensorI h₁ h₂ hadd ih₁ ih₂ | tensorE h₁ h₂ hadd ih₁ ih₂
  | unitE h₁ h₂ hadd ih₁ ih₂ | bangE h₁ h₂ hadd ih₁ ih₂ | copy h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.derVar hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · split_rule (ih₁ hl) h₂ hd
    · first
      | have h2 := ih₂ (i := x) hl; split_rule h₁ h2 hd
      | have h2 := ih₂ (i := .succ x) hl
        simp only [← TCtx.cons_setVar_succ] at h2; split_rule h₁ h2 hd
      | have h2 := ih₂ (i := .succ (.succ x)) hl
        simp only [← TCtx.cons_setVar_succ] at h2; split_rule h₁ h2 hd
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro x A hx; exact (not_lin_of_all hΓ.vars hx).elim
  | borrow _ ih => intro x A hx; exact HasTypeD.borrow (ih hx)
  | nec _ hΓ _ => intro x A hx; exact (not_lin_of_all hΓ hx).elim

/-- Dereliction of an array reference is admissible in the dereliction-free system. -/
theorem derRef {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {B : Ty} (ht : HasTypeD Γ t B) :
    ∀ {a : Var ρ} {A : ArrTy}, Γ.refs.get a = some (.lin A) →
      HasTypeD (Γ.setRef a (some (.nonlin A))) t B := by
  induction ht with
  | var hi hr =>
    intro x A hx; exact (not_lin_of_all hr hx).elim
  | ref hi hv =>
    intro x A hx
    obtain rfl := hi.eq_of_not (by rw [hx]; exact not_nonLin_lin A)
    rw [hi.get] at hx; cases hx
    exact HasTypeD.ref (h := .nonlin A) (hi.set _) hv
  | abs _ ih =>
    intro x A hx
    have h := ih hx
    simp only [← TCtx.cons_setRef] at h
    exact HasTypeD.abs h
  | app h₁ h₂ hadd ih₁ ih₂ | tensorI h₁ h₂ hadd ih₁ ih₂ | tensorE h₁ h₂ hadd ih₁ ih₂
  | unitE h₁ h₂ hadd ih₁ ih₂ | bangE h₁ h₂ hadd ih₁ ih₂ | copy h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.derRef hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · split_rule (ih₁ hl) h₂ hd
    · have h2 := ih₂ hl
      simp only [← TCtx.cons_setRef] at h2; split_rule h₁ h2 hd
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro x A hx; exact (not_lin_of_all hΓ.refs hx).elim
  | borrow _ ih => intro x A hx; exact HasTypeD.borrow (ih hx)
  | nec _ hΓ ih =>
    intro x A hx
    exact HasTypeD.nec (ih hx) hΓ

end HasTypeD

/-- The paper's typing judgment and the dereliction-free one coincide. -/
theorem hasType_iff_hasTypeD {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
    HasType Γ t A ↔ HasTypeD Γ t A := by
  constructor
  · intro h
    induction h with
    | var hi hrest => exact HasTypeD.var (h := .lin _) hi hrest
    | der _ hi ih => exact ih.derVar hi.eq
    | _ => constructor <;> assumption
  · intro h
    induction h with
    | @var n ρ Γ i h hi hrest =>
      cases h with
      | lin A => exact HasType.var hi hrest
      | nonlin A =>
        have e : Γ = (Γ.setVar i (some (.lin A))).setVar i (some (.nonlin A)) := by
          rw [TCtx.setVar_setVar, ← hi.get, TCtx.setVar_get]
        rw [e]
        exact HasType.der (HasType.var (hi.set _) hrest) (by simp [TCtx.setVar])
    | _ => constructor <;> assumption

end LCU
