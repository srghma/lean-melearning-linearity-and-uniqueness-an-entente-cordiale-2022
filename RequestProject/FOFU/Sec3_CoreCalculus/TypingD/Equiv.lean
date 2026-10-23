module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD.Basic

/-!
# Equivalence of `HasTypeD` and `HasType`

* `HasTypeD.approxCtx`: approximation extends to whole contexts;
* `HasTypeD.der`: dereliction is admissible for `HasTypeD`;
* `HasType.toD`, `HasTypeD.toHasType`, `hasType_iff_hasTypeD`: the two judgments are
  equivalent; `HasType.approxCtx` follows.
-/

@[expose] public section

namespace FOFU

open Ty

variable {R : Type} [Grades.PreorderedSemiring R]

/-! ## Approximation of whole contexts -/

namespace HasTypeD

theorem approxCtx {k n ρ : ℕ} {Γ Γ' : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasTypeD Γ t B) (hle : CtxLe Γ Γ') : HasTypeD Γ' t B := by
  classical
  suffices H : ∀ S : Finset (Var n), ∀ Γ' : TCtx R k n ρ, CtxLe Γ Γ' →
      (∀ j, j ∉ S → Γ'.vars.get j = Γ.vars.get j) → HasTypeD Γ' t B from
    H Finset.univ Γ' hle (fun j hj => absurd (Finset.mem_univ j) hj)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Γ' hle hS
    have e : Γ' = Γ := TCtx.ext hle.refs (Ctx.ext fun j => hS j (Finset.notMem_empty j))
    rw [e]; exact h
  | insert j S hj ih =>
    intro Γ' hle hS
    have h₁ : HasTypeD (Γ'.setVar j (Γ.vars.get j)) t B := by
      refine ih _ ⟨hle.refs, Ctx.forall₂_iff.2 fun i => ?_⟩ (fun i hi => ?_)
      · simp only [TCtx.setVar_vars, Ctx.get_set]
        split_ifs with hij
        · subst hij; exact .refl _
        · exact hle.vars.get i
      · simp only [TCtx.setVar_vars, Ctx.get_set]
        split_ifs with hij
        · subst hij; rfl
        · exact hS i (by simp [hij, hi])
    rcases (hle.vars.get j).cases' with e | ⟨A, r, s, e₁, e₂, hrs⟩
    · rw [← e, TCtx.setVar_get] at h₁; exact h₁
    · rw [e₁] at h₁
      have := HasTypeD.approx (i := j) (A := A) (r := r) (Ctx.Lookup.of_eq (by simp)) hrs h₁
      rw [TCtx.setVar_setVar, ← e₂, TCtx.setVar_get] at this
      exact this

/-! ## Dereliction is admissible -/

theorem der {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} (h : HasTypeD Γ t B) :
    ∀ {i : Var n} {A : Ty R k}, Γ.vars.get i = some (.lin A) →
      HasTypeD (Γ.setVar i (some (.grd A 1))) t B := by
  induction h with
  | @var k n ρ Γ j C hj =>
    intro i A hi
    have hji : i = j := hj.eq_of_not (by rw [hi]; exact not_zeroAssm_lin A)
    subst hji
    rw [hj.get] at hi; cases hi
    exact .varG (hj.set _)
  | @varG k n ρ Γ j C hj =>
    intro i A hi
    have hji : i = j := hj.eq_of_not (by rw [hi]; exact not_zeroAssm_lin A)
    subst hji
    rw [hj.get] at hi; cases hi
  | abs _ ih =>
    intro i A hi
    exact .abs (ih (i := .succ i) hi)
  | app hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .app h (ih₁ h1) ‹_›
    · exact .app h ‹_› (ih₂ h2)
  | tensorI hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .tensorI h (ih₁ h1) ‹_›
    · exact .tensorI h ‹_› (ih₂ h2)
  | unitE hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .unitE h (ih₁ h1) ‹_›
    · exact .unitE h ‹_› (ih₂ h2)
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .withBorrow h (ih₁ h1) ‹_›
    · exact .withBorrow h ‹_› (ih₂ h2)
  | join hfg hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .join hfg h (ih₁ h1) ‹_›
    · exact .join hfg h ‹_› (ih₂ h2)
  | elim hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .elim h (ih₁ h1) ‹_›
    · exact .elim h ‹_› (ih₂ (i := .succ i) h2)
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .tensorE h (ih₁ h1) ‹_›
    · exact .tensorE h ‹_› (ih₂ (i := .succ (.succ i)) h2)
  | unpack hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .unpack h (ih₁ h1) ‹_›
    · have := ih₂ (i := .succ i) (A := A.shift) (by
        simp [TCtx.shiftNames, h2, Ty.shift])
      refine .unpack h ‹_› ?_
      rw [TCtx.shiftNames, TCtx.renNames_setVar]
      exact this
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .clone ι h (ih₁ h1) hr hc hA ‹_›
    · exact .clone ι h ‹_› hr hc hA (ih₂ (i := .succ i) h2)
  | pr hs _ _ _ =>
    intro i A hi
    have := hs.vars.get i; rw [hi] at this; exact this.not_lin_right.elim
  | @approx k n ρ Γ t B j C r s hj hrs _ ih =>
    intro i A hi
    by_cases hji : j = i
    · subst hji; simp at hi
    · rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ (Ne.symm hji)] at hi
      have := HasTypeD.approx (i := j)
        (Ctx.Lookup.of_eq (by rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ hji]; exact hj.eq)) hrs
        (ih hi)
      rwa [TCtx.setVar_comm _ (Ne.symm hji)] at this
  | pack ι _ ih => intro i A hi; exact .pack ι (ih hi)
  | share r _ ih => intro i A hi; exact .share r (ih hi)
  | split _ ih => intro i A hi; exact .split (ih hi)
  | push _ ih => intro i A hi; exact .push (ih hi)
  | pull _ ih => intro i A hi; exact .pull (ih hi)
  | unborrow _ ih => intro i A hi; exact .unborrow (ih hi)
  | unitI hz | nat _ hz | float _ hz | prim hz _ | nec _ hz _ _ | ref hz _ =>
    intro i A hi
    have := hz.get i; rw [hi] at this; exact this.elim

end HasTypeD

/-! ## Equivalence with `HasType` -/

theorem HasType.toD {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasType Γ t B) : HasTypeD Γ t B := by
  induction h with
  | der hi _ ih => exact ih.der hi.eq
  | var hi => exact .var hi
  | abs _ ih => exact .abs ih
  | app hadd _ _ ih₁ ih₂ => exact .app hadd ih₁ ih₂
  | pr hs _ hna ih => exact .pr hs ih hna
  | elim hadd _ _ ih₁ ih₂ => exact .elim hadd ih₁ ih₂
  | approx hi hrs _ ih => exact .approx hi hrs ih
  | tensorI hadd _ _ ih₁ ih₂ => exact .tensorI hadd ih₁ ih₂
  | tensorE hadd _ _ ih₁ ih₂ => exact .tensorE hadd ih₁ ih₂
  | unitI hz => exact .unitI hz
  | unitE hadd _ _ ih₁ ih₂ => exact .unitE hadd ih₁ ih₂
  | pack ι _ ih => exact .pack ι ih
  | unpack hadd _ _ ih₁ ih₂ => exact .unpack hadd ih₁ ih₂
  | share r _ ih => exact .share r ih
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ => exact .clone ι hadd ih₁ hr hc hA ih₂
  | withBorrow hadd _ _ ih₁ ih₂ => exact .withBorrow hadd ih₁ ih₂
  | split _ ih => exact .split ih
  | join hfg hadd _ _ ih₁ ih₂ => exact .join hfg hadd ih₁ ih₂
  | push _ ih => exact .push ih
  | pull _ ih => exact .pull ih
  | nat m hz => exact .nat m hz
  | float x hz => exact .float x hz
  | prim hz hp => exact .prim hz hp
  | nec p hz _ ih => exact .nec p hz ih
  | unborrow _ ih => exact .unborrow ih
  | ref hz ha => exact .ref hz ha

theorem HasTypeD.toHasType {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasTypeD Γ t B) : HasType Γ t B := by
  induction h with
  | varG hi => exact .var' hi
  | var hi => exact .var hi
  | abs _ ih => exact .abs ih
  | app hadd _ _ ih₁ ih₂ => exact .app hadd ih₁ ih₂
  | pr hs _ hna ih => exact .pr hs ih hna
  | elim hadd _ _ ih₁ ih₂ => exact .elim hadd ih₁ ih₂
  | approx hi hrs _ ih => exact .approx hi hrs ih
  | tensorI hadd _ _ ih₁ ih₂ => exact .tensorI hadd ih₁ ih₂
  | tensorE hadd _ _ ih₁ ih₂ => exact .tensorE hadd ih₁ ih₂
  | unitI hz => exact .unitI hz
  | unitE hadd _ _ ih₁ ih₂ => exact .unitE hadd ih₁ ih₂
  | pack ι _ ih => exact .pack ι ih
  | unpack hadd _ _ ih₁ ih₂ => exact .unpack hadd ih₁ ih₂
  | share r _ ih => exact .share r ih
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ => exact .clone ι hadd ih₁ hr hc hA ih₂
  | withBorrow hadd _ _ ih₁ ih₂ => exact .withBorrow hadd ih₁ ih₂
  | split _ ih => exact .split ih
  | join hfg hadd _ _ ih₁ ih₂ => exact .join hfg hadd ih₁ ih₂
  | push _ ih => exact .push ih
  | pull _ ih => exact .pull ih
  | nat m hz => exact .nat m hz
  | float x hz => exact .float x hz
  | prim hz hp => exact .prim hz hp
  | nec p hz _ ih => exact .nec p hz ih
  | unborrow _ ih => exact .unborrow ih
  | ref hz ha => exact .ref hz ha

/-- The dereliction-free judgment is equivalent to the paper's. -/
theorem hasType_iff_hasTypeD {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} :
    HasType Γ t B ↔ HasTypeD Γ t B := ⟨HasType.toD, HasTypeD.toHasType⟩

/-- Approximation of whole contexts, for the paper's judgment. -/
theorem HasType.approxCtx {k n ρ : ℕ} {Γ Γ' : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasType Γ t B) (hle : CtxLe Γ Γ') : HasType Γ' t B :=
  (h.toD.approxCtx hle).toHasType

end FOFU
