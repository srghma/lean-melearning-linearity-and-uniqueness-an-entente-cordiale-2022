module
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.SubstSetup

/-!
# The substitution lemmas (Lemmas 6.2 and 6.3)

* `HasType.subst_lin` (**Lemma 6.2**, linear substitution): if `Γ₁ ⊢ t₁ : A` and
  `Γ₂, x : A ⊢ t₂ : B`, then `Γ₂ + Γ₁ ⊢ t₂[t₁/x] : B`.
* `HasType.subst_grd` (**Lemma 6.3**, graded substitution): if `[Γ₁] ⊢ t₁ : A`,
  `Γ₂, x : [A]_r ⊢ t₂ : B` and `¬ resourceAllocator(t₁)`, then
  `Γ₂ + r · Γ₁ ⊢ t₂[t₁/x] : B`.  That `Γ₁` contains only graded assumptions is implied by
  the existence of `r · Γ₁` (scaling is undefined on linear assumptions), so it is not a
  separate hypothesis.

As everywhere, `+` and `·` are partial, so "`Γ₂ + Γ₁`" means: for every `Γ` with
`CtxAdd Γ₂ Γ₁ Γ`.

## Proof

Both lemmas are instances of one substitution lemma for the dereliction-free judgment
`HasTypeD` (`HasTypeD.subst_gen`), which substitutes a term for an arbitrary variable `i`
whose assumption may be absent, linear or graded; the condition on the substituted term
and its context is `SubstHyp`.  This is the same structure as the proof of the
substitution lemmas of *Linearity and Uniqueness*
(`RequestProject/LCU/Sec3_1_Calculus/Substitution.lean`), generalised to grades:

* at a context split, the assumption `x : [A]_(r + s)` is split as `x : [A]_r` and
  `x : [A]_s`, and `(r + s) · Γ₁` as `r · Γ₁ + s · Γ₁` (`SubstHyp.split`);
* under the promotion rule `pr` the assumption `x : [A]_(r * q)` comes from `x : [A]_q`,
  and `(r * q) · Γ₁ = r · (q · Γ₁)` (`SubstHyp.scale`);
* approximation `x : [A]_r ⟶ x : [A]_s` is handled by approximating the whole of
  `r · Γ₁` to `s · Γ₁` (`HasTypeD.approxCtx`);
* in a variable rule for another variable, `x` has grade `0`, so it is replaced by the
  zero context `0 · Γ₁`, which can be weakened in (`HasTypeD.weakenZero`);
* the side condition `¬ resourceAllocator` of `pr` is preserved because `t₁` only
  occurs in `t₂[t₁/x]` if `x` occurs in `t₂` (`Term.allocates_subst`, `HasTypeD.occurs`).
-/

@[expose] public section

namespace FOFU

open Binding

variable {R : Type} [Grades.PreorderedSemiring R]

variable {k n m ρ : ℕ}

/-! ## The general substitution lemma -/

/-- Combining the splitting of the substitution with the splitting of the context. -/
lemma subst_split {r : Var n → Var m} {i : Var m} {Δ₁ Δ₂ Δ : TCtx R k m ρ}
    (hadd : CtxAdd Δ₁ Δ₂ Δ) {Γx Γ' : TCtx R k n ρ} {s : Term R n ρ}
    (hs : SubstHyp (Δ.vars.get i) Γx s) (hadd' : CtxAdd Γx (Δ.remove r) Γ') :
    ∃ Γx₁ Γx₂ C₁ C₂, SubstHyp (Δ₁.vars.get i) Γx₁ s ∧ SubstHyp (Δ₂.vars.get i) Γx₂ s ∧
      CtxAdd Γx₁ (Δ₁.remove r) C₁ ∧ CtxAdd Γx₂ (Δ₂.remove r) C₂ ∧ CtxAdd C₁ C₂ Γ' := by
  obtain ⟨Γx₁, Γx₂, h₁, h₂, h₁₂⟩ := hs.split (hadd.vars.get i)
  obtain ⟨C₁, C₂, hc₁, hc₂, hc⟩ := h₁₂.interchange (hadd.remove r) hadd'
  exact ⟨Γx₁, Γx₂, C₁, C₂, h₁, h₂, hc₁, hc₂, hc⟩

/-- The removed context of a variable rule for another variable. -/
lemma pick_remove {r : Var n → Var m} (hr : Function.Injective r) {Δ : TCtx R k m ρ} {j : Var n}
    {a : Option (Assm R k)} (h : Δ.vars.Pick ZeroAssm (r j) a) :
    (Δ.remove r).vars.Pick ZeroAssm j a := h.comp hr

theorem HasTypeD.subst_gen {Δ : TCtx R k m ρ} {t : Term R m ρ} {B : Ty R k}
    (ht : HasTypeD Δ t B) :
    ∀ {n : ℕ} {r : Var n → Var m} {i : Var m} {σ : Var m → Term R n ρ} {Γx Γ' : TCtx R k n ρ},
      SubstSetup r i σ → SubstHyp (Δ.vars.get i) Γx (σ i) → CtxAdd Γx (Δ.remove r) Γ' →
      HasTypeD Γ' (t.subst σ) B := by
  induction ht with
  | @var _ m _ Δ l C hl =>
    intro n r i σ Γx Γ' hs hsub hadd
    by_cases hli : l = i
    · subst hli
      rw [hl.get] at hsub
      exact (hsub : HasTypeD Γx (σ l) C).weakenZero
        (Ctx.all_iff.2 fun j => by simpa using hl.other (hs.ne j)) hadd.comm
    · obtain ⟨j, rfl⟩ := hs.surj l hli
      change HasTypeD Γ' (σ (r j)) C
      rw [hs.var]
      have hΓx := hsub.isZero (hl.other (Ne.symm hli))
      exact HasTypeD.weakenZero (.var (pick_remove hs.inj hl)) hΓx hadd
  | @varG _ m _ Δ l C hl =>
    intro n r i σ Γx Γ' hs hsub hadd
    by_cases hli : l = i
    · subst hli
      rw [hl.get] at hsub
      obtain ⟨Γ₁, h₁, -, hsc⟩ := hsub
      rw [hsc.one_eq] at hadd
      exact h₁.weakenZero (Ctx.all_iff.2 fun j => by simpa using hl.other (hs.ne j)) hadd.comm
    · obtain ⟨j, rfl⟩ := hs.surj l hli
      change HasTypeD Γ' (σ (r j)) C
      rw [hs.var]
      have hΓx := hsub.isZero (hl.other (Ne.symm hli))
      exact HasTypeD.weakenZero (.varG (pick_remove hs.inj hl)) hΓx hadd
  | abs _ ih =>
    intro n r i σ Γx Γ' hs hsub hadd
    refine HasTypeD.abs (ih hs.up hsub.shift ?_)
    rw [TCtx.remove_cons]
    exact hadd.cons (.noneLeft _)
  | app hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .app a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | tensorI hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .tensorI a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | unitE hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .unitE a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | withBorrow hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .withBorrow a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | join hfg hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .join hfg a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | elim hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .elim a (ih₁ hs h₁ a₁) (ih₂ hs.up h₂.shift ?_)
    rw [TCtx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | clone ι hadd₀ _ hq hc hA _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .clone ι a (ih₁ hs h₁ a₁) hq hc hA (ih₂ hs.up h₂.shift ?_)
    rw [TCtx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | tensorE hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .tensorE a (ih₁ hs h₁ a₁) (ih₂ hs.up.up h₂.shift.shift ?_)
    rw [TCtx.remove_cons, TCtx.remove_cons]
    exact (a₂.cons (.noneLeft _)).cons (.noneLeft _)
  | unpack hadd₀ _ _ ih₁ ih₂ =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .unpack a (ih₁ hs h₁ a₁) (ih₂ hs.up (by
      rw [TCtx.cons_vars, Ctx.get_snoc_succ, TCtx.shiftNames, TCtx.renNames_vars, Ctx.get_map]
      exact (h₂.renNames _).shift) ?_)
    rw [TCtx.remove_cons, TCtx.shiftNames, TCtx.remove_renNames]
    exact (a₂.renNames _).cons (.noneLeft _)
  | @pr _ m _ Δ₀ Δ t C q hsc _ hna ih =>
    intro n r i σ Γx Γ' hs hsub hadd
    obtain ⟨Γx₀, h₀, hx₀⟩ := hsub.scale (hsc.vars.get i)
    obtain ⟨C₀, hc₀, hsc₀⟩ := hx₀.add_exists (hsc.remove r) hadd
    refine .pr hsc₀ (ih hs h₀ hc₀) ?_
    intro hall
    rcases Term.allocates_subst hall with h | ⟨j, hj, ha⟩
    · exact hna h
    · by_cases hji : j = i
      · subst hji
        have hne := ‹HasTypeD Δ₀ t C›.occurs hj
        have e := hsc.vars.get j
        rcases e' : Δ₀.vars.get j with _ | ⟨A | ⟨A, q'⟩⟩
        · exact absurd e' hne
        · rw [e'] at e; exact e.not_lin_left.elim
        · rw [e'] at e
          rw [e.grd_eq] at hsub
          obtain ⟨_, _, hna', _⟩ := hsub
          exact hna' ha
      · exact hs.not_allocates hji ha
  | @approx _ m _ Δ₀ t C j A q q' hj hrq _ ih =>
    intro n r i σ Γx Γ' hs hsub hadd
    replace hj := hj.eq
    by_cases hji : j = i
    · subst hji
      rw [TCtx.setVar_vars, Ctx.get_set_same] at hsub
      obtain ⟨Γx₀, h₀, hle⟩ := hsub.le hrq
      rw [TCtx.remove_setVar_ne hs.ne] at hadd
      obtain ⟨C₀, hc₀, hle₀⟩ := hle.add_exists hadd
      rw [← hj] at h₀
      exact (ih hs h₀ hc₀).approxCtx hle₀
    · rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ (Ne.symm hji)] at hsub
      obtain ⟨j', rfl⟩ := hs.surj j hji
      rw [TCtx.remove_setVar hs.inj] at hadd
      obtain ⟨C₀, hc₀, hle₀⟩ :=
        (CtxLe.setVar (Γ := Δ₀.remove r) (i := j') (by simpa using hj) hrq).add_exists' hadd
      exact (ih hs hsub hc₀).approxCtx hle₀
  | pack ι _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .pack ι (ih hs hsub hadd)
  | share q _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .share q (ih hs hsub hadd)
  | split _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .split (ih hs hsub hadd)
  | push _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .push (ih hs hsub hadd)
  | pull _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .pull (ih hs hsub hadd)
  | unborrow _ ih => intro n r i σ Γx Γ' hs hsub hadd; exact .unborrow (ih hs hsub hadd)
  | unitI hz =>
    intro n r i σ Γx Γ' hs hsub hadd
    exact .unitI ((hsub.isZero (hz.get i)).add hadd (hz.remove r))
  | nat x hz =>
    intro n r i σ Γx Γ' hs hsub hadd
    exact .nat x ((hsub.isZero (hz.get i)).add hadd (hz.remove r))
  | float x hz =>
    intro n r i σ Γx Γ' hs hsub hadd
    exact .float x ((hsub.isZero (hz.get i)).add hadd (hz.remove r))
  | prim hz hp =>
    intro n r i σ Γx Γ' hs hsub hadd
    exact .prim ((hsub.isZero (hz.get i)).add hadd (hz.remove r)) hp
  | @ref _ m _ Δ a T hz ha =>
    intro n r i σ Γx Γ' hs hsub hadd
    have := hadd.refs.get a
    rw [show (Δ.remove r).refs.get a = some T from ha.eq] at this
    exact .ref ((hsub.isZero (hz.get i)).add hadd (hz.remove r))
      (Ctx.Lookup.of_eq this.eq_of_right)
  | nec p hz _ ih =>
    intro n r i σ Γx Γ' hs hsub hadd
    have hΓx := hsub.isZero (hz.get i)
    refine .nec p (hΓx.add hadd (hz.remove r)) (ih hs (Γx := Γx.refsOnly)
      (by simpa using TCtx.IsZero.refsOnly Γx) ?_)
    rw [TCtx.remove_refsOnly]
    exact hadd.refsOnly

/-! ## Lemmas 6.2 and 6.3 -/

/-- **Lemma 6.2 (Linear substitution is admissible).** If `Γ₁ ⊢ t₁ : A` and
`Γ₂, x : A ⊢ t₂ : B`, then `Γ₂ + Γ₁ ⊢ t₂[t₁/x] : B`. -/
theorem HasType.subst_lin {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
    {A B : Ty R k} (h₁ : HasType Γ₁ t₁ A) (h₂ : HasType (Γ₂.cons (some (.lin A))) t₂ B)
    (hadd : CtxAdd Γ₂ Γ₁ Γ) : HasType Γ (t₂.subst1 t₁) B := by
  refine (h₂.toD.subst_gen (SubstSetup.zero t₁) (Γx := Γ₁) h₁.toD ?_).toHasType
  have : (Γ₂.cons (some (.lin A))).remove Var.succ = Γ₂ :=
    TCtx.ext rfl (Ctx.ext fun j => by simp)
  rw [this]; exact hadd.comm

/-- **Lemma 6.3 (Graded substitution is admissible).** If `[Γ₁] ⊢ t₁ : A`,
`Γ₂, x : [A]_r ⊢ t₂ : B` and `¬ resourceAllocator(t₁)`, then
`Γ₂ + r · Γ₁ ⊢ t₂[t₁/x] : B`.  (`Γ₁` has no linear assumptions because `r · Γ₁` is
defined.) -/
theorem HasType.subst_grd {Γ₁ Γ₁r Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ}
    {t₂ : Term R (n + 1) ρ} {A B : Ty R k} {r : R} (h₁ : HasType Γ₁ t₁ A)
    (h₂ : HasType (Γ₂.cons (some (.grd A r))) t₂ B)
    (hna : ¬ t₁.Allocates) (hsc : CtxScale r Γ₁ Γ₁r) (hadd : CtxAdd Γ₂ Γ₁r Γ) :
    HasType Γ (t₂.subst1 t₁) B := by
  refine (h₂.toD.subst_gen (SubstSetup.zero t₁) (Γx := Γ₁r) ⟨Γ₁, h₁.toD, hna, hsc⟩ ?_).toHasType
  have : (Γ₂.cons (some (.grd A r))).remove Var.succ = Γ₂ :=
    TCtx.ext rfl (Ctx.ext fun j => by simp)
  rw [this]; exact hadd.comm

/-- Substitution for a variable that has no assumption (strengthening). -/
theorem HasType.subst_none {Γ : TCtx R k n ρ} {s : Term R n ρ} {t : Term R (n + 1) ρ}
    {B : Ty R k} (h : HasType (Γ.cons none) t B) : HasType Γ (t.subst1 s) B := by
  refine (h.toD.subst_gen (SubstSetup.zero s) (Γx := Γ.refsOnly)
    (TCtx.IsZero.refsOnly Γ) ?_).toHasType
  have : (Γ.cons none).remove Var.succ = Γ := TCtx.ext rfl (Ctx.ext fun j => by simp)
  rw [this]; exact CtxAdd.refsOnly_left Γ

end FOFU
