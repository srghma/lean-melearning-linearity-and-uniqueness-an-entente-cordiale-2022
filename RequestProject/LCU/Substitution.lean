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

lemma HypAdd.some_of_nonLin' {h : Hyp} {d c : Option Hyp} (hx : HypAdd d (some h) c)
    (hd : NonLin d) : c = some h := hx.comm.some_of_nonLin hd

/-- Removing a variable from a context whose other assumptions are non-linear. -/
lemma Ctx.remove_allNonLin {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n}
    (hs : SubstSetup ρ i σ) {Δ : Ctx m} (hΔ : (Δ.set (.inl i) none).AllNonLin) :
    (Δ.remove ρ).AllNonLin := by
  rintro (j | a)
  · have := hΔ (.inl (ρ j))
    rwa [Ctx.set_ne _ _ (by simpa using hs.ne j)] at this
  · have := hΔ (.inr a)
    rwa [Ctx.set_ne _ _ (by simp)] at this

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
      have hi : NonLin (Δ (.inl i)) := by
        have := hrest (.inl i); rwa [Ctx.set_ne _ _ (by simpa using (Ne.symm hki))] at this
      have hΓ' := hsub.allNonLin hi
      refine HasTypeD.var (h := h) ?_ ?_
      · have e : Δ.remove ρ (.inl j) = some h := hk
        have := hadd (.inl j); rw [e] at this
        exact this.some_of_nonLin' (hΓ' _)
      · intro y
        by_cases hy : y = .inl j
        · subst hy; simp
        · rw [Ctx.set_ne _ _ hy]
          refine (hadd y).nonLin_of (hΓ' y) ?_
          rcases y with y | a
          · have := hrest (.inl (ρ y))
            rwa [Ctx.set_ne _ _ (by simpa [hs.inj.eq_iff] using hy)] at this
          · have := hrest (.inr a)
            rwa [Ctx.set_ne _ _ (by simp)] at this
  | abs _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    refine HasTypeD.abs (ih hs.up hsub.shift ?_)
    rw [Ctx.remove_cons]
    exact hadd.cons (.noneLeft _)
  | app _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    exact .app (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂) a
  | tensorI _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    exact .tensorI (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂) a
  | tensorE _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    refine .tensorE (ih₁ hs h₁ a₁) (ih₂ hs.up.up h₂.shift.shift ?_) a
    rw [Ctx.remove_cons, Ctx.remove_cons]
    exact (a₂.cons (.noneLeft _)).cons (.noneLeft _)
  | unitI hΔ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .unitI (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
  | unitE _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    exact .unitE (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂) a
  | bangI hΔ _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .bangI (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
      (ih hs hsub hadd)
  | bangE _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    refine .bangE (ih₁ hs h₁ a₁) (ih₂ hs.up h₂.shift ?_) a
    rw [Ctx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | borrow _ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .borrow (ih hs hsub hadd)
  | copy _ _ hadd ih₁ ih₂ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd'
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd hsub hadd'
    refine .copy (ih₁ hs h₁ a₁) (ih₂ hs.up h₂.shift ?_) a
    rw [Ctx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | @nec m Δ t A _ hΔ ih =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    have hΓ' := hsub.allNonLin (hΔ i)
    refine .nec (ih hs (Γ' := Γ'.refsOnly) hΓ'.refsOnly ?_) ?_
    · rw [Ctx.remove_refsOnly]; exact hadd.refsOnly
    · refine Ctx.VarsNonLin.of_add hadd hΓ'.varsNonLin (fun j => hΔ _)
  | natI hΔ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .natI (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
  | floatI hΔ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .floatI (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
  | prim hΔ =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    exact .prim (Ctx.AllNonLin.of_add hadd (hsub.allNonLin (hΔ _)) hΔ.remove)
  | @ref m Δ a h ha hrest =>
    intro n ρ i σ Γ' Γ'' hs hsub hadd
    have hi : NonLin (Δ (.inl i)) := by
      have := hrest (.inl i); rwa [Ctx.set_ne _ _ (by simp)] at this
    have hΓ' := hsub.allNonLin hi
    have e : Δ.remove ρ (.inr a) = some h := ha
    have hx := hadd (.inr a); rw [e] at hx
    refine HasTypeD.ref (h := h) (hx.some_of_nonLin' (hΓ' _)) ?_
    intro y
    by_cases hy : y = .inr a
    · subst hy; simp
    · rw [Ctx.set_ne _ _ hy]
      refine (hadd y).nonLin_of (hΓ' y) ?_
      rcases y with y | b
      · have := hrest (.inl (ρ y))
        rwa [Ctx.set_ne _ _ (by simp)] at this
      · have := hrest (.inr b)
        rwa [Ctx.set_ne _ _ (by simpa using hy)] at this

end HasTypeD

namespace HasType

/-- **Lemma 1 (Linear substitution).** If `Γ' ⊢ t' : A` and `Γ, x : A ⊢ t : B` then
`Γ' + Γ ⊢ [t'/x]t : B`. -/
theorem subst_lin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (ht' : HasType Γ' t' A) (ht : HasType (Γ.cons (some (.lin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (Term.subst1 t' t) B := by
  rw [hasType_iff_hasTypeD] at *
  refine ht.subst_gen (SubstSetup.zero t') (Γ' := Γ') ht' ?_
  rwa [Ctx.remove_succ_cons]

/-- **Lemma 2 (Non-linear substitution).** If `[Γ'] ⊢ t' : A` and `Γ, x : [A] ⊢ t : B`
then `[Γ'] + Γ ⊢ [t'/x]t : B`. -/
theorem subst_nonlin {n : ℕ} {Γ' Γ Γ'' : Ctx n} {t' : Term n} {t : Term (n + 1)} {A B : Ty}
    (hΓ' : Γ'.AllNonLin) (ht' : HasType Γ' t' A) (ht : HasType (Γ.cons (some (.nonlin A))) t B)
    (hadd : Γ'.Add Γ Γ'') : HasType Γ'' (Term.subst1 t' t) B := by
  rw [hasType_iff_hasTypeD] at *
  refine ht.subst_gen (SubstSetup.zero t') (Γ' := Γ') ⟨hΓ', ht'⟩ ?_
  rwa [Ctx.remove_succ_cons]

/-- Substitution for a variable which does not occur in the context (strengthening). -/
theorem subst_none {n : ℕ} {Γ : Ctx n} {s : Term n} {t : Term (n + 1)} {B : Ty}
    (ht : HasType (Γ.cons none) t B) : HasType Γ (Term.subst1 s t) B := by
  rw [hasType_iff_hasTypeD] at *
  refine ht.subst_gen (SubstSetup.zero s) (Γ' := Ctx.empty) Ctx.AllNonLin.empty ?_
  rw [Ctx.remove_succ_cons]; exact Ctx.Add.empty_left _

end HasType

end LCU
