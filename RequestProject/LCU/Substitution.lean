module
public import RequestProject.LCU.Weakening

/-!
# Substitution lemmas (Lemmas 1 and 2)

We prove a general substitution lemma for substituting a term for an arbitrary
variable `i` (which may be absent, linear or non-linear in the context), and derive
Lemma 1 (linear substitution) and Lemma 2 (non-linear substitution) from it.
-/

@[expose] public section

namespace LCU

open Term

/-- Data describing the substitution of a term for the variable `i : Fin m`:
`ρ : Fin n → Fin m` enumerates the other variables and `σ` maps them back to
variables, while `σ i` is the substituted term. -/
structure SubstSetup {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin m) (σ : Fin m → Term n) : Prop where
  inj : Function.Injective ρ
  ne : ∀ j, ρ j ≠ i
  surj : ∀ k, k ≠ i → ∃ j, ρ j = k
  var : ∀ j, σ (ρ j) = .var j

namespace SubstSetup

variable {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n}

lemma up (hs : SubstSetup ρ i σ) : SubstSetup (Ren.up ρ) i.succ (Subst.up σ) where
  inj := (Ctx.RenCtx.cons ⟨hs.inj, fun _ => rfl, fun _ _ => trivial, fun _ => rfl⟩
    (Γ := (Ctx.empty : Ctx n)) (Γ' := (Ctx.empty : Ctx m)) none).inj
  ne := by
    intro j; cases j using Fin.cases
    · exact (Fin.succ_ne_zero i).symm
    · simpa using hs.ne _
  surj := by
    intro k hk
    cases k using Fin.cases with
    | zero => exact ⟨0, rfl⟩
    | succ k =>
      obtain ⟨j, hj⟩ := hs.surj k (fun e => hk (by rw [e]))
      exact ⟨j.succ, by simp [hj]⟩
  var := by
    intro j; cases j using Fin.cases
    · rfl
    · simp [hs.var, rename]

lemma zero (s : Term n) : SubstSetup Fin.succ 0 (Fin.cons s Term.var) where
  inj := Fin.succ_injective _
  ne := Fin.succ_ne_zero
  surj := fun k hk => ⟨k.pred hk, by simp⟩
  var := fun _ => rfl

end SubstSetup

namespace Ctx

variable {n m : ℕ}

/-- The context `Δ` restricted along `ρ` (removing the substituted variable). -/
def remove (ρ : Fin n → Fin m) (Δ : Ctx m) : Ctx n :=
  Sum.elim (fun j => Δ (.inl (ρ j))) (fun a => Δ (.inr a))

lemma remove_cons (ρ : Fin n → Fin m) (Δ : Ctx m) (h : Option Hyp) :
    (Δ.cons h).remove (Ren.up ρ) = (Δ.remove ρ).cons h := by
  funext x; rcases x with j | a
  · cases j using Fin.cases <;> rfl
  · rfl

lemma remove_succ_cons (Δ : Ctx n) (h : Option Hyp) : (Δ.cons h).remove Fin.succ = Δ := by
  funext x; rcases x with j | a <;> rfl

lemma Add.remove (ρ : Fin n → Fin m) {Δ₁ Δ₂ Δ : Ctx m} (h : Δ₁.Add Δ₂ Δ) :
    (Δ₁.remove ρ).Add (Δ₂.remove ρ) (Δ.remove ρ) := by
  rintro (j | a)
  · exact h _
  · exact h _

lemma remove_refsOnly (ρ : Fin n → Fin m) (Δ : Ctx m) :
    Δ.refsOnly.remove ρ = (Δ.remove ρ).refsOnly := by
  funext x; rcases x with j | a <;> rfl

end Ctx

/-- The condition on the substituted term, depending on the hypothesis of the
substituted variable: nothing (but a non-linear context) if it is absent, a typing
if it is linear, and a typing in a non-linear context if it is non-linear. -/
def SubstHyp {n : ℕ} : Option Hyp → Ctx n → Term n → Prop
  | none, Γ', _ => Γ'.AllNonLin
  | some (.lin A), Γ', s => HasTypeD Γ' s A
  | some (.nonlin A), Γ', s => Γ'.AllNonLin ∧ HasTypeD Γ' s A

namespace SubstHyp

variable {n : ℕ}

lemma allNonLin {h : Option Hyp} {Γ' : Ctx n} {s : Term n} (hh : NonLin h)
    (hs : SubstHyp h Γ' s) : Γ'.AllNonLin := by
  rcases h with _ | ⟨A | A⟩
  · exact hs
  · exact absurd hh (not_nonLin_lin A)
  · exact hs.1

lemma shift {h : Option Hyp} {Γ' : Ctx n} {s : Term n} (hs : SubstHyp h Γ' s) :
    SubstHyp h (Γ'.cons none) (s.rename Fin.succ) := by
  rcases h with _ | ⟨A | A⟩
  · exact Ctx.AllNonLin.cons hs nonLin_none
  · exact HasTypeD.shift hs nonLin_none
  · exact ⟨Ctx.AllNonLin.cons hs.1 nonLin_none, HasTypeD.shift hs.2 nonLin_none⟩

lemma split {h₁ h₂ h : Option Hyp} {Γ' : Ctx n} {s : Term n} (hh : HypAdd h₁ h₂ h)
    (hs : SubstHyp h Γ' s) :
    ∃ Γ₁ Γ₂, SubstHyp h₁ Γ₁ s ∧ SubstHyp h₂ Γ₂ s ∧ Γ₁.Add Γ₂ Γ' := by
  match h₁, h₂, h, hh with
  | _, _, _, .noneLeft none => exact ⟨Γ', Γ', hs, hs, Ctx.Add.idem hs⟩
  | _, _, _, .noneLeft (some (.lin _)) =>
    exact ⟨Ctx.empty, Γ', Ctx.AllNonLin.empty, hs, Ctx.Add.empty_left _⟩
  | _, _, _, .noneLeft (some (.nonlin _)) => exact ⟨Γ', Γ', hs.1, hs, Ctx.Add.idem hs.1⟩
  | _, _, _, .noneRight (.lin _) =>
    exact ⟨Γ', Ctx.empty, hs, Ctx.AllNonLin.empty, Ctx.Add.empty_right _⟩
  | _, _, _, .noneRight (.nonlin _) => exact ⟨Γ', Γ', hs, hs.1, Ctx.Add.idem hs.1⟩
  | _, _, _, .nonlin _ => exact ⟨Γ', Γ', hs, hs, Ctx.Add.idem hs.1⟩

end SubstHyp

/-- Combining the splitting of the substitution with the splitting of the context. -/
lemma subst_split {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {Δ₁ Δ₂ Δ : Ctx m}
    (hadd : Δ₁.Add Δ₂ Δ) {Γ' Γ'' : Ctx n} {s : Term n} (hs : SubstHyp (Δ (.inl i)) Γ' s)
    (hadd' : Γ'.Add (Δ.remove ρ) Γ'') :
    ∃ Γ₁' Γ₂' Γ₁'' Γ₂'', SubstHyp (Δ₁ (.inl i)) Γ₁' s ∧ SubstHyp (Δ₂ (.inl i)) Γ₂' s ∧
      Γ₁'.Add (Δ₁.remove ρ) Γ₁'' ∧ Γ₂'.Add (Δ₂.remove ρ) Γ₂'' ∧ Γ₁''.Add Γ₂'' Γ'' := by
  obtain ⟨Γ₁', Γ₂', h₁, h₂, h₁₂⟩ := hs.split (hadd (.inl i))
  obtain ⟨C₁, C₂, hc₁, hc₂, hc⟩ := Ctx.Add.interchange h₁₂ (hadd.remove ρ) hadd'
  exact ⟨Γ₁', Γ₂', C₁, C₂, h₁, h₂, hc₁, hc₂, hc⟩

/-- Removing a variable from a context whose other assumptions are non-linear. -/
lemma Ctx.remove_allNonLin {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n}
    (hs : SubstSetup ρ i σ) {Δ : Ctx m} (hΔ : (Δ.set (.inl i) none).AllNonLin) :
    (Δ.remove ρ).AllNonLin := by
  rintro (j | a)
  · have := hΔ (.inl (ρ j))
    rwa [Ctx.set_ne _ _ (by simpa using hs.ne j)] at this
  · have := hΔ (.inr a)
    rwa [Ctx.set_ne _ _ (by simp)] at this

/-- Removing a variable from a context whose other assumptions are non-linear, keeping
the assumption of one name. -/
lemma Ctx.remove_set_allNonLin {n m : ℕ} {ρ : Fin n → Fin m} (hinj : Function.Injective ρ)
    {Δ : Ctx m} {y : Fin n ⊕ ℕ} {h : Option Hyp} (hΔ : (Δ.set (Sum.map ρ id y) h).AllNonLin) :
    ((Δ.remove ρ).set y h).AllNonLin := by
  have e : ∀ z, Δ.remove ρ z = Δ (Sum.map ρ id z) := by rintro (j | a) <;> rfl
  refine Ctx.AllNonLin.set' (fun z hz => ?_) (by simpa using hΔ (Sum.map ρ id y))
  rw [e]
  exact hΔ.of_set ((Sum.map_injective.2 ⟨hinj, Function.injective_id⟩).ne hz)

lemma Ctx.AllNonLin.remove {n m : ℕ} {ρ : Fin n → Fin m} {Δ : Ctx m} (hΔ : Δ.AllNonLin) :
    (Δ.remove ρ).AllNonLin := by
  rintro (j | a)
  · exact hΔ _
  · exact hΔ _

namespace HasTypeD

/-- The general substitution lemma. -/
theorem subst_gen {m : ℕ} {Δ : Ctx m} {t : Term m} {B : Ty} (ht : HasTypeD Δ t B) :
    ∀ {n : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n} {Γ' Γ'' : Ctx n},
      SubstSetup ρ i σ → SubstHyp (Δ (.inl i)) Γ' (σ i) → Γ'.Add (Δ.remove ρ) Γ'' →
      HasTypeD Γ'' (t.subst σ) B := by
  induction ht with
  | @var m Δ k h hk hrest =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    simp only [Term.subst]
    by_cases hki : k = i
    · subst hki
      rw [hk] at hsub
      have hrem := Ctx.remove_allNonLin hs hrest
      rcases h with A | A
      · exact hsub.weaken hrem hadd
      · exact hsub.2.weaken hrem hadd
    · obtain ⟨j, rfl⟩ := hs.surj k hki
      rw [hs.var]
      have hΓ' := hsub.allNonLin (hrest.of_set (by simpa using Ne.symm hki))
      obtain ⟨h₁, h₂⟩ :=
        hadd.comm.weaken_name hΓ' (x := .inl j) hk (Ctx.remove_set_allNonLin hs.inj hrest)
      exact .var h₁ h₂
  | abs _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    refine HasTypeD.abs (ih hs.up hsub.shift ?_)
    rw [Ctx.remove_cons]
    exact hadd.cons (.noneLeft _)
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    split_rule (ih₁ hs h₁ a₁)
      (ih₂ (by first | exact hs | exact hs.up | exact hs.up.up)
        (by first | exact h₂ | exact h₂.shift | exact h₂.shift.shift)
        (by (try simp only [Ctx.remove_cons])
            first | exact a₂ | exact a₂.cons (.noneLeft _)
                  | exact (a₂.cons (.noneLeft _)).cons (.noneLeft _))) a
  | unitI hΔ | natI hΔ | floatI hΔ | prim hΔ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    constructor; exact Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove
  | bangI hΔ _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .bangI (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
      (ih hs hsub hadd)
  | borrow _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .borrow (ih hs hsub hadd)
  | @nec m Δ t A _ hΔ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    have hΓ' := hsub.allNonLin (hΔ i)
    refine .nec (ih hs (Γ' := Γ'.refsOnly) hΓ'.refsOnly ?_) ?_
    · rw [Ctx.remove_refsOnly]; exact hadd.refsOnly
    · refine Ctx.VarsNonLin.of_add hadd hΓ'.varsNonLin (fun j => hΔ _)
  | @ref m Δ a h ha hrest =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    have hΓ' := hsub.allNonLin (hrest.of_set (by simp))
    obtain ⟨h₁, h₂⟩ :=
      hadd.comm.weaken_name hΓ' (x := .inr a) ha (Ctx.remove_set_allNonLin hs.inj hrest)
    exact .ref h₁ h₂

lemma subst_lin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (ht' : HasTypeD Γ' t' A) (ht : HasTypeD (Γ.cons (some (.lin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasTypeD Γ'' (Term.subst1 t' t) B :=
  ht.subst_gen (SubstSetup.zero t') ht' (by rwa [Ctx.remove_succ_cons])

lemma subst_nonlin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (hΓ' : Γ'.AllNonLin) (ht' : HasTypeD Γ' t' A)
    (ht : HasTypeD (Γ.cons (some (.nonlin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasTypeD Γ'' (Term.subst1 t' t) B :=
  ht.subst_gen (SubstSetup.zero t') ⟨hΓ', ht'⟩ (by rwa [Ctx.remove_succ_cons])

lemma subst_none {n : ℕ} {Γ : Ctx n} {s : Term n} {t : Term (n + 1)} {B : Ty}
    (ht : HasTypeD (Γ.cons none) t B) : HasTypeD Γ (Term.subst1 s t) B :=
  ht.subst_gen (SubstSetup.zero s) (Γ' := Ctx.empty) Ctx.AllNonLin.empty
    (by rw [Ctx.remove_succ_cons]; exact Ctx.Add.empty_left _)

end HasTypeD

namespace HasType

/-- **Lemma 1 (Linear substitution).** If `Γ' ⊢ t' : A` and `Γ, x : A ⊢ t : B` then
`Γ' + Γ ⊢ [t'/x]t : B`. -/
theorem subst_lin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (ht' : HasType Γ' t' A) (ht : HasType (Γ.cons (some (.lin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (Term.subst1 t' t) B := by
  rw [hasType_iff_hasTypeD] at *
  exact ht'.subst_lin ht hadd

/-- **Lemma 2 (Non-linear substitution).** If `[Γ'] ⊢ t' : A` and `Γ, x : [A] ⊢ t : B`
then `[Γ'] + Γ ⊢ [t'/x]t : B`. -/
theorem subst_nonlin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (hΓ' : Γ'.AllNonLin) (ht' : HasType Γ' t' A) (ht : HasType (Γ.cons (some (.nonlin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (Term.subst1 t' t) B := by
  rw [hasType_iff_hasTypeD] at *
  exact HasTypeD.subst_nonlin hΓ' ht' ht hadd

/-- Substitution for a variable which does not occur in the context (strengthening). -/
theorem subst_none {n : ℕ} {Γ : Ctx n} {s : Term n} {t : Term (n + 1)} {B : Ty}
    (ht : HasType (Γ.cons none) t B) : HasType Γ (Term.subst1 s t) B := by
  rw [hasType_iff_hasTypeD] at *
  exact ht.subst_none

end HasType

end LCU
