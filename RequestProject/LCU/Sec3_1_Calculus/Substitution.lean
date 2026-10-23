module
public import RequestProject.LCU.Sec3_1_Calculus.Weakening

/-!
# Substitution lemmas (Lemmas 1 and 2)

We prove a general substitution lemma for substituting a term for an arbitrary
variable `i` (which may be absent, linear or non-linear in the context), and derive
Lemma 1 (linear substitution) and Lemma 2 (non-linear substitution) from it.

## Main results

* `HasTypeD.subst_gen`: if `Δ ⊢ t : B`, `σ` substitutes the term `σ i` for the
  variable `i` and renames the other variables (`SubstSetup r i σ`), and `σ i`
  satisfies the side condition `SubstHyp (Δ i) Γ' (σ i)` determined by the
  hypothesis of `i` in `Δ`, then `Γ' + Δ∖i ⊢ t[σ] : B`.
* `HasType.subst_lin` (**Lemma 1**): if `Γ' ⊢ t' : A` and `Γ, x : A ⊢ t : B`, then
  `Γ' + Γ ⊢ [t'/x]t : B`.
* `HasType.subst_nonlin` (**Lemma 2**): if `[Γ'] ⊢ t' : A` and `Γ, x : [A] ⊢ t : B`,
  then `[Γ'] + Γ ⊢ [t'/x]t : B`.
* `HasType.subst_none`: substituting for a variable that is absent from the context.

## Implementation notes

The generalisation from "variable `0`" to "any variable `i`" is needed because going
under a binder shifts the substituted variable (`SubstSetup.up`).  Allowing the
hypothesis of `i` to be absent, linear or non-linear lets one induction handle
Lemmas 1 and 2 (and strengthening) at once: at a context split, the hypothesis of `i`
moves into one or both premises, and `SubstHyp.split` splits the substituted term's
context accordingly.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Substitution data -/

/-- Data describing the substitution of a term for the variable `i : Var m`:
`r : Var n → Var m` enumerates the other variables and `σ` maps them back to
variables, while `σ i` is the substituted term. -/
structure SubstSetup {n m ρ : ℕ} (r : Var n → Var m) (i : Var m) (σ : Var m → Term n ρ) :
    Prop where
  inj : Function.Injective r
  ne : ∀ j, r j ≠ i
  surj : ∀ k, k ≠ i → ∃ j, r j = k
  var : ∀ j, σ (r j) = .var j

namespace SubstSetup

variable {n m ρ : ℕ} {r : Var n → Var m} {i : Var m} {σ : Var m → Term n ρ}

/-- Substitution data can be pushed under a binder. -/
lemma up (hs : SubstSetup r i σ) : SubstSetup (Ren.up r) (.succ i) (Subst.up σ) where
  inj := Ren.up_injective hs.inj
  ne j := by
    cases j with
    | zero => exact Var.zero_ne_succ i
    | succ j => simpa using hs.ne j
  surj k hk := by
    cases k with
    | zero => exact ⟨.zero, rfl⟩
    | succ k =>
      obtain ⟨j, hj⟩ := hs.surj k (fun e => hk (by rw [e]))
      exact ⟨.succ j, by simp [hj]⟩
  var j := by
    cases j with
    | zero => rfl
    | succ j => simp [hs.var]

/-- The substitution `[s/x]` for the variable `Var.zero`, as used by `Term.subst1`. -/
lemma zero (s : Term n ρ) : SubstSetup Var.succ .zero (Var.cons s Term.var) where
  inj := Var.succ_injective
  ne := Var.succ_ne_zero
  surj k hk := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k => exact ⟨k, rfl⟩
  var _ := rfl

end SubstSetup

/-! ## Removing the substituted variable from a context -/

namespace TCtx

variable {n m ρ : ℕ}

/-- The context `Δ` restricted along `r` (removing the substituted variable). -/
def remove (r : Var n → Var m) (Δ : TCtx m ρ) : TCtx n ρ :=
  ⟨Δ.refs, Ctx.ofFn (fun j => Δ.vars.get (r j))⟩

@[simp] lemma remove_refs (r : Var n → Var m) (Δ : TCtx m ρ) : (Δ.remove r).refs = Δ.refs := rfl
@[simp] lemma remove_vars_get (r : Var n → Var m) (Δ : TCtx m ρ) (j : Var n) :
    (Δ.remove r).vars.get j = Δ.vars.get (r j) := Ctx.get_ofFn _ _

lemma remove_cons (r : Var n → Var m) (Δ : TCtx m ρ) (h : Option (Hyp Ty)) :
    (Δ.cons h).remove (Ren.up r) = (Δ.remove r).cons h :=
  ext rfl (Ctx.ext fun j => by cases j <;> simp [remove])

lemma remove_succ_cons (Δ : TCtx n ρ) (h : Option (Hyp Ty)) : (Δ.cons h).remove Var.succ = Δ :=
  ext rfl (Ctx.ext fun j => by simp [remove])

/-- Removing a variable commutes with context addition. -/
lemma Add.remove (r : Var n → Var m) {Δ₁ Δ₂ Δ : TCtx m ρ} (h : Δ₁.Add Δ₂ Δ) :
    (Δ₁.remove r).Add (Δ₂.remove r) (Δ.remove r) :=
  ⟨h.refs, Ctx.forall₃_iff.2 fun j => by simp only [remove_vars_get]; exact h.vars.get (r j)⟩

lemma remove_refsOnly (r : Var n → Var m) (Δ : TCtx m ρ) :
    Δ.refsOnly.remove r = (Δ.remove r).refsOnly :=
  ext rfl (Ctx.ext fun j => by simp [remove, refsOnly])

lemma AllNonLin.remove {r : Var n → Var m} {Δ : TCtx m ρ} (hΔ : Δ.AllNonLin) :
    (Δ.remove r).AllNonLin :=
  ⟨hΔ.refs, Ctx.all_iff.2 fun j => by simp only [remove_vars_get]; exact hΔ.vars.get _⟩

lemma VarsNonLin.remove {r : Var n → Var m} {Δ : TCtx m ρ} (hΔ : Δ.VarsNonLin) :
    (Δ.remove r).VarsNonLin :=
  Ctx.all_iff.2 fun j => by simp only [remove_vars_get]; exact hΔ.get _

end TCtx

/-! ## The side condition on the substituted term -/

/-- The condition on the substituted term, depending on the hypothesis of the
substituted variable: nothing (but a non-linear context) if it is absent, a typing
if it is linear, and a typing in a non-linear context if it is non-linear. -/
def SubstHyp {n ρ : ℕ} : Option (Hyp Ty) → TCtx n ρ → Term n ρ → Prop
  | none, Γ', _ => Γ'.AllNonLin
  | some (.lin A), Γ', s => HasTypeD Γ' s A
  | some (.nonlin A), Γ', s => Γ'.AllNonLin ∧ HasTypeD Γ' s A

namespace SubstHyp

variable {n ρ : ℕ}

lemma allNonLin {h : Option (Hyp Ty)} {Γ' : TCtx n ρ} {s : Term n ρ} (hh : NonLin h)
    (hs : SubstHyp h Γ' s) : Γ'.AllNonLin := by
  cases hh
  · exact hs
  · exact hs.1

lemma shift {h : Option (Hyp Ty)} {Γ' : TCtx n ρ} {s : Term n ρ} (hs : SubstHyp h Γ' s) :
    SubstHyp h (Γ'.cons none) (s.rename Var.succ) := by
  rcases h with _ | ⟨A | A⟩
  · exact TCtx.AllNonLin.cons hs nonLin_none
  · exact HasTypeD.shift hs nonLin_none
  · exact ⟨TCtx.AllNonLin.cons hs.1 nonLin_none, HasTypeD.shift hs.2 nonLin_none⟩

/-- If the hypothesis of the substituted variable is split between two premises,
the term and its context can be split accordingly (a non-linear term is shared). -/
lemma split {h₁ h₂ h : Option (Hyp Ty)} {Γ' : TCtx n ρ} {s : Term n ρ} (hh : HypAdd h₁ h₂ h)
    (hs : SubstHyp h Γ' s) :
    ∃ Γ₁ Γ₂, SubstHyp h₁ Γ₁ s ∧ SubstHyp h₂ Γ₂ s ∧ Γ₁.Add Γ₂ Γ' := by
  match h₁, h₂, h, hh with
  | _, _, _, .noneLeft none => exact ⟨Γ', Γ', hs, hs, TCtx.Add.idem hs⟩
  | _, _, _, .noneLeft (some (.lin _)) =>
    exact ⟨TCtx.empty, Γ', TCtx.AllNonLin.empty, hs, TCtx.Add.empty_left _⟩
  | _, _, _, .noneLeft (some (.nonlin _)) => exact ⟨Γ', Γ', hs.1, hs, TCtx.Add.idem hs.1⟩
  | _, _, _, .noneRight (.lin _) =>
    exact ⟨Γ', TCtx.empty, hs, TCtx.AllNonLin.empty, TCtx.Add.empty_right _⟩
  | _, _, _, .noneRight (.nonlin _) => exact ⟨Γ', Γ', hs, hs.1, TCtx.Add.idem hs.1⟩
  | _, _, _, .nonlin _ => exact ⟨Γ', Γ', hs, hs, TCtx.Add.idem hs.1⟩

end SubstHyp

/-- Combining the splitting of the substitution with the splitting of the context. -/
lemma subst_split {n m ρ : ℕ} {r : Var n → Var m} {i : Var m} {Δ₁ Δ₂ Δ : TCtx m ρ}
    (hadd : Δ₁.Add Δ₂ Δ) {Γ' Γ'' : TCtx n ρ} {s : Term n ρ} (hs : SubstHyp (Δ.vars.get i) Γ' s)
    (hadd' : Γ'.Add (Δ.remove r) Γ'') :
    ∃ Γ₁' Γ₂' Γ₁'' Γ₂'', SubstHyp (Δ₁.vars.get i) Γ₁' s ∧ SubstHyp (Δ₂.vars.get i) Γ₂' s ∧
      Γ₁'.Add (Δ₁.remove r) Γ₁'' ∧ Γ₂'.Add (Δ₂.remove r) Γ₂'' ∧ Γ₁''.Add Γ₂'' Γ'' := by
  obtain ⟨Γ₁', Γ₂', h₁, h₂, h₁₂⟩ := hs.split (hadd.vars.get i)
  obtain ⟨C₁, C₂, hc₁, hc₂, hc⟩ := TCtx.Add.interchange h₁₂ (hadd.remove r) hadd'
  exact ⟨Γ₁', Γ₂', C₁, C₂, h₁, h₂, hc₁, hc₂, hc⟩

/-! ## The substitution lemmas -/

namespace HasTypeD

/-- The general substitution lemma. -/
theorem subst_gen {m ρ : ℕ} {Δ : TCtx m ρ} {t : Term m ρ} {B : Ty} (ht : HasTypeD Δ t B) :
    ∀ {n : ℕ} {r : Var n → Var m} {i : Var m} {σ : Var m → Term n ρ} {Γ' Γ'' : TCtx n ρ},
      SubstSetup r i σ → SubstHyp (Δ.vars.get i) Γ' (σ i) → Γ'.Add (Δ.remove r) Γ'' →
      HasTypeD Γ'' (t.subst σ) B := by
  induction ht with
  | @var m ρ Δ k h hk hr =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    simp only [Term.subst_var]
    by_cases hki : k = i
    · subst hki
      rw [hk.get] at hsub
      have hrem : (Δ.remove r).AllNonLin := ⟨hr, Ctx.all_iff.2 fun j => by
        simp only [TCtx.remove_vars_get]; exact hk.other (hs.ne j)⟩
      rcases h with A | A
      · exact hsub.weaken hrem hadd
      · exact hsub.2.weaken hrem hadd
    · obtain ⟨j, rfl⟩ := hs.surj k hki
      rw [hs.var]
      have hΓ' := hsub.allNonLin (hk.other (Ne.symm hki))
      have hpick : (Δ.remove r).vars.Pick NonLin j (some h) := by
        have := hk.comp hs.inj; exact this
      exact .var (pick_of_add hadd.comm.vars hΓ'.vars hpick)
        (hadd.refs.all HypAdd.nonLin_of hΓ'.refs hr)
  | abs _ ih =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    refine HasTypeD.abs (ih hs.up hsub.shift ?_)
    rw [TCtx.remove_cons]
    exact hadd.cons (.noneLeft _)
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro n r i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    split_rule (ih₁ hs h₁ a₁)
      (ih₂ (by first | exact hs | exact hs.up | exact hs.up.up)
        (by first | exact h₂ | exact h₂.shift | exact h₂.shift.shift)
        (by (try simp only [TCtx.remove_cons])
            first | exact a₂ | exact a₂.cons (.noneLeft _)
                  | exact (a₂.cons (.noneLeft _)).cons (.noneLeft _))) a
  | unitI hΔ | natI hΔ | floatI hΔ | prim hΔ =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    constructor; exact TCtx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ.vars.get _)) hΔ.remove
  | bangI hΔ _ ih =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    exact .bangI (TCtx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ.vars.get _)) hΔ.remove)
      (ih hs hsub hadd)
  | borrow _ ih =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    exact .borrow (ih hs hsub hadd)
  | nec _ hΔ ih =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    have hΓ' := hsub.allNonLin (hΔ.get i)
    refine .nec (ih hs (Γ' := Γ'.refsOnly)
      (by simp only [TCtx.refsOnly_vars, Ctx.get_replicate]; exact hΓ'.refsOnly) ?_) ?_
    · rw [TCtx.remove_refsOnly]; exact hadd.refsOnly
    · exact TCtx.VarsNonLin.of_add hadd hΓ'.varsNonLin hΔ.remove
  | ref ha hv =>
    intro n r i σ Γ' Γ'' hs hsub hadd
    have hΓ' := hsub.allNonLin (hv.get i)
    exact .ref (pick_of_add hadd.comm.refs hΓ'.refs ha)
      (hadd.vars.all HypAdd.nonLin_of hΓ'.vars (TCtx.VarsNonLin.remove hv))

/-- Lemma 1 (linear substitution), dereliction-free version. -/
lemma subst_lin {n ρ : ℕ} {Γ' Γ Γ'' : TCtx n ρ} {t' : Term n ρ} {t : Term (n + 1) ρ} {A B : Ty}
    (ht' : HasTypeD Γ' t' A) (ht : HasTypeD (Γ.cons (some (.lin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasTypeD Γ'' (t.subst1 t') B :=
  ht.subst_gen (SubstSetup.zero t') ht' (by rwa [TCtx.remove_succ_cons])

/-- Lemma 2 (non-linear substitution), dereliction-free version. -/
lemma subst_nonlin {n ρ : ℕ} {Γ' Γ Γ'' : TCtx n ρ} {t' : Term n ρ} {t : Term (n + 1) ρ}
    {A B : Ty} (hΓ' : Γ'.AllNonLin) (ht' : HasTypeD Γ' t' A)
    (ht : HasTypeD (Γ.cons (some (.nonlin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasTypeD Γ'' (t.subst1 t') B :=
  ht.subst_gen (SubstSetup.zero t') ⟨hΓ', ht'⟩ (by rwa [TCtx.remove_succ_cons])

/-- Substitution for an absent variable, dereliction-free version. -/
lemma subst_none {n ρ : ℕ} {Γ : TCtx n ρ} {s : Term n ρ} {t : Term (n + 1) ρ} {B : Ty}
    (ht : HasTypeD (Γ.cons none) t B) : HasTypeD Γ (t.subst1 s) B :=
  ht.subst_gen (SubstSetup.zero s) (Γ' := TCtx.empty) TCtx.AllNonLin.empty
    (by rw [TCtx.remove_succ_cons]; exact TCtx.Add.empty_left _)

end HasTypeD

namespace HasType

/-- **Lemma 1 (Linear substitution).** If `Γ' ⊢ t' : A` and `Γ, x : A ⊢ t : B` then
`Γ' + Γ ⊢ [t'/x]t : B`. -/
theorem subst_lin {n ρ : ℕ} {Γ' Γ Γ'' : TCtx n ρ} {t' : Term n ρ} {t : Term (n + 1) ρ}
    {A B : Ty} (ht' : HasType Γ' t' A) (ht : HasType (Γ.cons (some (.lin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (t.subst1 t') B := by
  rw [hasType_iff_hasTypeD] at *
  exact ht'.subst_lin ht hadd

/-- **Lemma 2 (Non-linear substitution).** If `[Γ'] ⊢ t' : A` and `Γ, x : [A] ⊢ t : B`
then `[Γ'] + Γ ⊢ [t'/x]t : B`. -/
theorem subst_nonlin {n ρ : ℕ} {Γ' Γ Γ'' : TCtx n ρ} {t' : Term n ρ} {t : Term (n + 1) ρ}
    {A B : Ty} (hΓ' : Γ'.AllNonLin) (ht' : HasType Γ' t' A)
    (ht : HasType (Γ.cons (some (.nonlin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (t.subst1 t') B := by
  rw [hasType_iff_hasTypeD] at *
  exact HasTypeD.subst_nonlin hΓ' ht' ht hadd

/-- Substitution for a variable which does not occur in the context (strengthening). -/
theorem subst_none {n ρ : ℕ} {Γ : TCtx n ρ} {s : Term n ρ} {t : Term (n + 1) ρ} {B : Ty}
    (ht : HasType (Γ.cons none) t B) : HasType Γ (t.subst1 s) B := by
  rw [hasType_iff_hasTypeD] at *
  exact ht.subst_none

end HasType

end LCU
