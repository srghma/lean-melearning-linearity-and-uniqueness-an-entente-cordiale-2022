module
public import RequestProject.FOFU.Sec6_3_Theorems.NameSubst
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst

/-!
# Renaming (and weakening by absent variables) in typing derivations

`HasTypeD.rename`: if `Γ ⊢ t : A` and `ρ` is an injective renaming of variables, then
`ρ(Γ) ⊢ ρ(t) : A`, where `ρ(Γ)` (`Ctx.ren ρ Γ`) gives `ρ j` the assumption of `j` and
no assumption to variables outside the image of `ρ`.  In particular a derivation can be
moved under a binder (`HasTypeD.shift`: `Γ, x : − ⊢ t↑ : A`).

The renaming `DeBruijn.Ren.up` on variables is shared with *Linearity and Uniqueness*
(`RequestProject/Common/DeBruijn.lean`).
-/

@[expose] public section

namespace FOFU

open DeBruijn Ty

variable {R : Type} [Grades.PreorderedSemiring R]

namespace Ctx

section
omit [Grades.PreorderedSemiring R]

variable {k n m : ℕ}

/-- Renaming a context along `ρ : Fin n → Fin m`. -/
noncomputable def ren (ρ : Fin n → Fin m) (Γ : Ctx R k n) : Ctx R k m :=
  ⟨Function.extend ρ Γ.vars (fun _ => Option.none), Γ.refs⟩

@[simp] lemma ren_refs (ρ : Fin n → Fin m) (Γ : Ctx R k n) : (Γ.ren ρ).refs = Γ.refs := rfl

lemma ren_vars_apply {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx R k n)
    (j : Fin n) : (Γ.ren ρ).vars (ρ j) = Γ.vars j :=
  hρ.extend_apply Γ.vars (fun _ => Option.none) j

lemma ren_vars_of_notMem {ρ : Fin n → Fin m} (Γ : Ctx R k n) {l : Fin m}
    (hl : ∀ j, ρ j ≠ l) : (Γ.ren ρ).vars l = Option.none :=
  Function.extend_apply' Γ.vars (fun _ => Option.none) l (fun ⟨j, hj⟩ => hl j hj)

/-- Every variable of the target is either the image of a variable, or outside the image
(and then has no assumption in any renamed context). -/
lemma ren_cases {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (l : Fin m) :
    (∃ j, ρ j = l ∧ ∀ Δ : Ctx R k n, (Δ.ren ρ).vars l = Δ.vars j) ∨
    (∀ Δ : Ctx R k n, (Δ.ren ρ).vars l = Option.none) := by
  by_cases h : ∃ j, ρ j = l
  · obtain ⟨j, rfl⟩ := h
    exact Or.inl ⟨j, rfl, fun Δ => ren_vars_apply hρ Δ j⟩
  · exact Or.inr fun Δ => ren_vars_of_notMem Δ (fun j hj => h ⟨j, hj⟩)

lemma cons_ren_up {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx R k n)
    (a : Option (Assm R k)) : (Γ.cons a).ren (Ren.up ρ) = (Γ.ren ρ).cons a := by
  ext1
  · funext l
    cases l using Fin.cases with
    | zero => exact ren_vars_apply (Ren.up_injective hρ) _ 0
    | succ l =>
      rcases ren_cases hρ (k := k) l with ⟨j, rfl, -⟩ | h
      · rw [cons_vars_succ, ren_vars_apply hρ]
        exact ren_vars_apply (Ren.up_injective hρ) (Γ.cons a) j.succ
      · rw [cons_vars_succ, h]
        apply ren_vars_of_notMem
        intro j hj
        obtain ⟨i, hi⟩ := Ren.exists_of_up ⟨j, hj⟩
        have := h ((Ctx.none n : Ctx R k n).update i (some (.lin .unit)))
        rw [← hi, ren_vars_apply hρ] at this
        simp [Ctx.update] at this
  · rfl

lemma update_ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx R k n) (i : Fin n)
    (a : Option (Assm R k)) : (Γ.update i a).ren ρ = (Γ.ren ρ).update (ρ i) a := by
  ext1
  · funext l
    rcases ren_cases hρ (k := k) l with ⟨j, rfl, h⟩ | h
    · rw [h]
      by_cases hj : j = i
      · subst hj; simp [Ctx.update]
      · rw [update_vars_ne _ hj, update_vars_ne _ (hρ.ne hj), ren_vars_apply hρ]
    · rw [h, update_vars_ne, h]
      intro e; subst e
      have := h ((Ctx.none n : Ctx R k n).update i (some (.lin .unit)))
      rw [ren_vars_apply hρ] at this
      simp [Ctx.update] at this
  · rfl

lemma refsOnly_ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx R k n) :
    Γ.refsOnly.ren ρ = (Γ.ren ρ).refsOnly := by
  ext1
  · funext l
    rcases ren_cases hρ (k := k) l with ⟨j, rfl, h⟩ | h
    · rw [h]; rfl
    · rw [h]; rfl
  · rfl

lemma substNames_ren {k' : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    (σ : Fin k → Ident k') (Γ : Ctx R k n) :
    (Γ.ren ρ).substNames σ = (Γ.substNames σ).ren ρ := by
  ext1
  · funext l
    rcases ren_cases hρ (k := k) l with ⟨j, rfl, h⟩ | h
    · simp only [substNames]; rw [h, ren_vars_apply hρ]
    · simp only [substNames]; rw [h, ren_vars_of_notMem]
      · rfl
      intro j hj; subst hj
      have := h ((Ctx.none n : Ctx R k n).update j (some (.lin .unit)))
      rw [ren_vars_apply hρ] at this
      simp [Ctx.update] at this
  · rfl

lemma shiftNames_ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : Ctx R k n) :
    (Γ.ren ρ).shiftNames = Γ.shiftNames.ren ρ := substNames_ren hρ _ Γ

/-- Renaming along `Fin.succ` adds an absent variable `0`. -/
lemma ren_succ (Γ : Ctx R k n) : Γ.ren Fin.succ = Γ.cons Option.none := by
  ext1
  · funext l
    cases l using Fin.cases with
    | zero => exact ren_vars_of_notMem Γ (fun j => Fin.succ_ne_zero j)
    | succ l => exact ren_vars_apply (Fin.succ_injective _) Γ l
  · rfl

end

end Ctx

variable {k n m : ℕ}

lemma CtxAdd.ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ₁ Γ₂ Γ : Ctx R k n}
    (h : CtxAdd Γ₁ Γ₂ Γ) : CtxAdd (Γ₁.ren ρ) (Γ₂.ren ρ) (Γ.ren ρ) := by
  refine ⟨fun l => ?_, h.refs⟩
  rcases Ctx.ren_cases hρ (k := k) l with ⟨j, rfl, e⟩ | e
  · rw [e, e, e]; exact h.vars j
  · rw [e, e, e]; exact .noneLeft _

lemma CtxScale.ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {r : R} {Γ Γ' : Ctx R k n}
    (h : CtxScale r Γ Γ') : CtxScale r (Γ.ren ρ) (Γ'.ren ρ) := by
  refine ⟨fun l => ?_, h.refs⟩
  rcases Ctx.ren_cases hρ (k := k) l with ⟨j, rfl, e⟩ | e
  · rw [e, e]; exact h.vars j
  · rw [e, e]; exact .none

lemma Ctx.IsZero.ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ : Ctx R k n}
    (h : Γ.IsZero) : (Γ.ren ρ).IsZero := by
  intro l
  rcases Ctx.ren_cases hρ (k := k) l with ⟨j, rfl, e⟩ | e
  · rw [e]; exact h j
  · rw [e]; trivial

lemma zeroRest_ren {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ : Ctx R k n} {i : Fin n}
    (h : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
    ∀ l, l ≠ ρ i → ZeroAssm ((Γ.ren ρ).vars l) := by
  intro l hl
  rcases Ctx.ren_cases hρ (k := k) l with ⟨j, rfl, e⟩ | e
  · rw [e]; exact h j (fun hj => hl (hj ▸ rfl))
  · rw [e]; trivial

omit [Grades.PreorderedSemiring R] in
/-- Renaming does not change whether a term allocates resources. -/
lemma Term.allocates_rename {n m : ℕ} {ρ : Fin n → Fin m} {t : Term R n} :
    (t.rename ρ).Allocates ↔ t.Allocates := by
  induction t generalizing m with
  | var => simp [Term.rename, Term.Allocates]
  | _ => simp_all [Term.rename, Term.Allocates]

/-! ## The renaming lemma -/

theorem HasTypeD.rename {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} (h : HasTypeD Γ t A) :
    ∀ {m : ℕ} {ρ : Fin n → Fin m}, Function.Injective ρ →
      HasTypeD (Γ.ren ρ) (t.rename ρ) A := by
  induction h with
  | var hi hz =>
    intro m ρ hρ
    exact .var (by rw [Ctx.ren_vars_apply hρ]; exact hi) (zeroRest_ren hρ hz)
  | varG hi hz =>
    intro m ρ hρ
    exact .varG (by rw [Ctx.ren_vars_apply hρ]; exact hi) (zeroRest_ren hρ hz)
  | abs _ ih =>
    intro m ρ hρ
    have := ih (Ren.up_injective hρ)
    rw [Ctx.cons_ren_up hρ] at this
    exact .abs this
  | app hadd _ _ ih₁ ih₂ => intro m ρ hρ; exact .app (hadd.ren hρ) (ih₁ hρ) (ih₂ hρ)
  | pr hs _ hna ih =>
    intro m ρ hρ
    refine .pr (hs.ren hρ) (ih hρ) ?_
    intro h'; exact hna (Term.allocates_rename.mp h')
  | elim hadd _ _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (Ren.up_injective hρ)
    rw [Ctx.cons_ren_up hρ] at this
    exact .elim (hadd.ren hρ) (ih₁ hρ) this
  | approx hi hrs _ ih =>
    intro m ρ hρ
    have := HasTypeD.approx (by rw [Ctx.ren_vars_apply hρ]; exact hi) hrs (ih hρ)
    rw [Ctx.update_ren hρ]
    exact this
  | tensorI hadd _ _ ih₁ ih₂ => intro m ρ hρ; exact .tensorI (hadd.ren hρ) (ih₁ hρ) (ih₂ hρ)
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (Ren.up_injective (Ren.up_injective hρ))
    rw [Ctx.cons_ren_up (Ren.up_injective hρ), Ctx.cons_ren_up hρ] at this
    exact .tensorE (hadd.ren hρ) (ih₁ hρ) this
  | unitI hz => intro m ρ hρ; exact .unitI (hz.ren hρ)
  | unitE hadd _ _ ih₁ ih₂ => intro m ρ hρ; exact .unitE (hadd.ren hρ) (ih₁ hρ) (ih₂ hρ)
  | pack ι _ ih => intro m ρ hρ; exact .pack ι (ih hρ)
  | unpack hadd _ _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (Ren.up_injective hρ)
    rw [Ctx.cons_ren_up hρ, ← Ctx.shiftNames_ren hρ] at this
    exact .unpack (hadd.ren hρ) (ih₁ hρ) this
  | share r _ ih => intro m ρ hρ; exact .share r (ih hρ)
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (Ren.up_injective hρ)
    rw [Ctx.cons_ren_up hρ] at this
    exact .clone ι (hadd.ren hρ) (ih₁ hρ) hr hc hA this
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro m ρ hρ; exact .withBorrow (hadd.ren hρ) (ih₁ hρ) (ih₂ hρ)
  | split _ ih => intro m ρ hρ; exact .split (ih hρ)
  | join hfg hadd _ _ ih₁ ih₂ => intro m ρ hρ; exact .join hfg (hadd.ren hρ) (ih₁ hρ) (ih₂ hρ)
  | push _ ih => intro m ρ hρ; exact .push (ih hρ)
  | pull _ ih => intro m ρ hρ; exact .pull (ih hρ)
  | nat x hz => intro m ρ hρ; exact .nat x (hz.ren hρ)
  | float x hz => intro m ρ hρ; exact .float x (hz.ren hρ)
  | prim hz hp => intro m ρ hρ; exact .prim (hz.ren hρ) hp
  | nec p hz _ ih =>
    intro m ρ hρ
    have := ih hρ
    rw [Ctx.refsOnly_ren hρ] at this
    exact .nec p (hz.ren hρ) this
  | unborrow _ ih => intro m ρ hρ; exact .unborrow (ih hρ)
  | ref hz ha => intro m ρ hρ; exact .ref (hz.ren hρ) ha

/-- Moving a derivation under a binder: `Γ ⊢ t : A` implies `Γ, x : − ⊢ t↑ : A`. -/
theorem HasTypeD.shift {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} (h : HasTypeD Γ t A) :
    HasTypeD (Γ.cons none) (t.rename Fin.succ) A := by
  have := h.rename (Fin.succ_injective n)
  rwa [Ctx.ren_succ] at this

end FOFU
