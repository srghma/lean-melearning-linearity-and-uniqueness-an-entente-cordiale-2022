module
public import RequestProject.LCU.CtxAlgebra

/-!
# A dereliction-free presentation of the typing rules

To streamline the metatheory we use an equivalent presentation of the typing
judgment without the dereliction rule `der`, in which instead the variable rule
also accepts non-linear assumptions: `[Γ], x : [A] ⊢ x : A`.
We show that `der` is admissible in this system, so the two systems are equivalent
(`hasType_iff_hasTypeD`).
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

namespace Ctx

variable {n : ℕ}

/-- Lifting a name under a variable binder. -/
def liftName : Fin n ⊕ ℕ → Fin (n + 1) ⊕ ℕ := Sum.map Fin.succ id

@[simp] lemma liftName_inl (i : Fin n) : liftName (.inl i) = .inl i.succ := rfl
@[simp] lemma liftName_inr (a : ℕ) : liftName (n := n) (.inr a) = .inr a := rfl

lemma cons_liftName (Γ : Ctx n) (h : Option Hyp) (x : Fin n ⊕ ℕ) :
    Γ.cons h (liftName x) = Γ x := by
  rcases x with i | a <;> rfl

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

lemma AllNonLin.not_lin {Γ : Ctx n} (hΓ : Γ.AllNonLin) {x : Fin n ⊕ ℕ} {A : Ty}
    (hx : Γ x = some (.lin A)) : False := by
  have := hΓ x; rw [hx] at this; exact this

lemma AllNonLin.set_not_lin {Γ : Ctx n} {x y : Fin n ⊕ ℕ} {h : Option Hyp}
    (hΓ : (Γ.set x h).AllNonLin) {A : Ty} (hy : Γ y = some (.lin A)) : y = x := by
  by_contra hne
  have := hΓ y; rw [set_ne _ _ hne, hy] at this; exact this

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

namespace HasTypeD

/-- Dereliction is admissible in the dereliction-free system, for variables and
array references alike. -/
theorem der {n : ℕ} {Γ : Ctx n} {t : Term n} {B : Ty} (ht : HasTypeD Γ t B) :
    ∀ {x : Fin n ⊕ ℕ} {A : Ty}, Γ x = some (.lin A) →
      HasTypeD (Γ.set x (some (.nonlin A))) t B := by
  induction ht with
  | @var n Γ i h hi hrest =>
    intro x A hx
    have := Ctx.AllNonLin.set_not_lin hrest hx
    subst this
    rw [hi] at hx; cases hx
    exact HasTypeD.var (h := .nonlin A) (by simp) (by rw [Ctx.set_set]; exact hrest)
  | @abs n Γ t A' B ht ih =>
    intro x A hx
    refine HasTypeD.abs ?_
    rw [Ctx.cons_set]
    exact ih (by rw [Ctx.cons_liftName]; exact hx)
  | app h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.app (ih₁ hl) h₂ hd
    · exact HasTypeD.app h₁ (ih₂ hl) hd
  | tensorI h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.tensorI (ih₁ hl) h₂ hd
    · exact HasTypeD.tensorI h₁ (ih₂ hl) hd
  | tensorE h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.tensorE (ih₁ hl) h₂ hd
    · refine HasTypeD.tensorE h₁ ?_ hd
      rw [Ctx.cons_set, Ctx.cons_set]
      exact ih₂ (by rw [Ctx.cons_liftName, Ctx.cons_liftName]; exact hl)
  | unitI hΓ => intro x A hx; exact (hΓ.not_lin hx).elim
  | unitE h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.unitE (ih₁ hl) h₂ hd
    · exact HasTypeD.unitE h₁ (ih₂ hl) hd
  | bangI hΓ _ _ => intro x A hx; exact (hΓ.not_lin hx).elim
  | bangE h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.bangE (ih₁ hl) h₂ hd
    · refine HasTypeD.bangE h₁ ?_ hd
      rw [Ctx.cons_set]
      exact ih₂ (by rw [Ctx.cons_liftName]; exact hl)
  | borrow _ ih => intro x A hx; exact HasTypeD.borrow (ih hx)
  | copy h₁ h₂ hadd ih₁ ih₂ =>
    intro x A hx
    rcases hadd.der hx with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · exact HasTypeD.copy (ih₁ hl) h₂ hd
    · refine HasTypeD.copy h₁ ?_ hd
      rw [Ctx.cons_set]
      exact ih₂ (by rw [Ctx.cons_liftName]; exact hl)
  | @nec n Γ t A' _ hΓ ih =>
    intro x A hx
    rcases x with i | a
    · have := hΓ i; rw [hx] at this; exact this.elim
    · refine HasTypeD.nec ?_ (hΓ.set_inr a _)
      rw [Ctx.refsOnly_set_inr]
      exact ih (by simpa using hx)
  | natI hΓ => intro x A hx; exact (hΓ.not_lin hx).elim
  | floatI hΓ => intro x A hx; exact (hΓ.not_lin hx).elim
  | prim hΓ => intro x A hx; exact (hΓ.not_lin hx).elim
  | @ref n Γ a h ha hrest =>
    intro x A hx
    have := Ctx.AllNonLin.set_not_lin hrest hx
    subst this
    rw [ha] at hx; cases hx
    exact HasTypeD.ref (h := .nonlin A) (by simp) (by rw [Ctx.set_set]; exact hrest)

end HasTypeD

/-- The paper's typing judgment and the dereliction-free one coincide. -/
theorem hasType_iff_hasTypeD {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} :
    HasType Γ t A ↔ HasTypeD Γ t A := by
  constructor
  · intro h
    induction h with
    | var hi hrest => exact HasTypeD.var (h := .lin _) hi hrest
    | abs _ ih => exact .abs ih
    | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
    | tensorI _ _ hadd ih₁ ih₂ => exact .tensorI ih₁ ih₂ hadd
    | tensorE _ _ hadd ih₁ ih₂ => exact .tensorE ih₁ ih₂ hadd
    | unitI hΓ => exact .unitI hΓ
    | unitE _ _ hadd ih₁ ih₂ => exact .unitE ih₁ ih₂ hadd
    | der _ hi ih => exact ih.der hi
    | bangI hΓ _ ih => exact .bangI hΓ ih
    | bangE _ _ hadd ih₁ ih₂ => exact .bangE ih₁ ih₂ hadd
    | borrow _ ih => exact .borrow ih
    | copy _ _ hadd ih₁ ih₂ => exact .copy ih₁ ih₂ hadd
    | nec _ hΓ ih => exact .nec ih hΓ
    | natI hΓ => exact .natI hΓ
    | floatI hΓ => exact .floatI hΓ
    | prim hΓ => exact .prim hΓ
    | ref ha hrest => exact .ref ha hrest
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
    | abs _ ih => exact .abs ih
    | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
    | tensorI _ _ hadd ih₁ ih₂ => exact .tensorI ih₁ ih₂ hadd
    | tensorE _ _ hadd ih₁ ih₂ => exact .tensorE ih₁ ih₂ hadd
    | unitI hΓ => exact .unitI hΓ
    | unitE _ _ hadd ih₁ ih₂ => exact .unitE ih₁ ih₂ hadd
    | bangI hΓ _ ih => exact .bangI hΓ ih
    | bangE _ _ hadd ih₁ ih₂ => exact .bangE ih₁ ih₂ hadd
    | borrow _ ih => exact .borrow ih
    | copy _ _ hadd ih₁ ih₂ => exact .copy ih₁ ih₂ hadd
    | nec _ hΓ ih => exact .nec ih hΓ
    | natI hΓ => exact .natI hΓ
    | floatI hΓ => exact .floatI hΓ
    | prim hΓ => exact .prim hΓ
    | ref ha hrest => exact .ref ha hrest

end LCU
