module
public import RequestProject.FOFU.Sec6_3_Theorems.Occurs

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

open DeBruijn

variable {R : Type} [Grades.PreorderedSemiring R]

/-! ## Substitution data -/

/-- Data describing the substitution of a term for the variable `i : Fin m`:
`ρ : Fin n → Fin m` enumerates the other variables and `σ` maps them back to
variables, while `σ i` is the substituted term. -/
structure SubstSetup {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin m) (σ : Fin m → Term R n) :
    Prop where
  inj : Function.Injective ρ
  ne : ∀ j, ρ j ≠ i
  surj : ∀ l, l ≠ i → ∃ j, ρ j = l
  var : ∀ j, σ (ρ j) = .var j

namespace SubstSetup

variable {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term R n}

omit [Grades.PreorderedSemiring R] in
/-- Substitution data can be pushed under a binder. -/
lemma up (hs : SubstSetup ρ i σ) :
    SubstSetup (Ren.up ρ) i.succ (Term.Subst.up σ) where
  inj := Ren.up_injective hs.inj
  ne := by
    intro j; cases j using Fin.cases
    · exact (Fin.succ_ne_zero i).symm
    · simpa using hs.ne _
  surj := by
    intro l hl
    cases l using Fin.cases with
    | zero => exact ⟨0, rfl⟩
    | succ l =>
      obtain ⟨j, hj⟩ := hs.surj l (fun e => hl (by rw [e]))
      exact ⟨j.succ, by simp [hj]⟩
  var := by
    intro j; cases j using Fin.cases
    · rfl
    · simp [hs.var, Term.rename]

omit [Grades.PreorderedSemiring R] in
/-- The substitution `[s/x]` for the variable `0`, as used by `Term.subst1`. -/
lemma zero (s : Term R n) : SubstSetup Fin.succ 0 (Fin.cons s Term.var) where
  inj := Fin.succ_injective _
  ne := Fin.succ_ne_zero
  surj := fun l hl => ⟨l.pred hl, by simp⟩
  var := fun _ => rfl

omit [Grades.PreorderedSemiring R] in
lemma not_allocates (hs : SubstSetup ρ i σ) {j : Fin m} (hj : j ≠ i) : ¬ (σ j).Allocates := by
  obtain ⟨l, rfl⟩ := hs.surj j hj
  rw [hs.var]; exact id

end SubstSetup

/-! ## Removing the substituted variable from a context -/

namespace Ctx

variable {k n m : ℕ}

/-- The context `Δ` restricted along `ρ` (removing the substituted variable). -/
def remove (ρ : Fin n → Fin m) (Δ : Ctx R k m) : Ctx R k n := ⟨fun j => Δ.vars (ρ j), Δ.refs⟩

omit [Grades.PreorderedSemiring R] in
lemma remove_cons (ρ : Fin n → Fin m) (Δ : Ctx R k m) (a : Option (Assm R k)) :
    (Δ.cons a).remove (Ren.up ρ) = (Δ.remove ρ).cons a := by
  ext1
  · funext j; cases j using Fin.cases <;> rfl
  · rfl

omit [Grades.PreorderedSemiring R] in
lemma remove_succ_cons (Δ : Ctx R k n) (a : Option (Assm R k)) :
    (Δ.cons a).remove Fin.succ = Δ := rfl

omit [Grades.PreorderedSemiring R] in
lemma remove_refsOnly (ρ : Fin n → Fin m) (Δ : Ctx R k m) :
    Δ.refsOnly.remove ρ = (Δ.remove ρ).refsOnly := rfl

omit [Grades.PreorderedSemiring R] in
lemma remove_substNames {k' : ℕ} (ρ : Fin n → Fin m) (τ : Fin k → Ident k') (Δ : Ctx R k m) :
    (Δ.substNames τ).remove ρ = (Δ.remove ρ).substNames τ := rfl

omit [Grades.PreorderedSemiring R] in
lemma remove_update_ne {ρ : Fin n → Fin m} {i : Fin m} (hne : ∀ j, ρ j ≠ i) (Δ : Ctx R k m)
    (a : Option (Assm R k)) : (Δ.update i a).remove ρ = Δ.remove ρ := by
  ext1
  · funext j; exact update_vars_ne _ (hne j) _
  · rfl

omit [Grades.PreorderedSemiring R] in
lemma remove_update {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Δ : Ctx R k m) (j : Fin n)
    (a : Option (Assm R k)) : (Δ.update (ρ j) a).remove ρ = (Δ.remove ρ).update j a := by
  ext1
  · funext l
    by_cases hl : l = j
    · subst hl; simp [remove, update]
    · simp only [remove, update]
      rw [Function.update_of_ne (hρ.ne hl), Function.update_of_ne hl]
  · rfl

lemma IsZero.remove {Δ : Ctx R k m} (h : Δ.IsZero) (ρ : Fin n → Fin m) :
    (Δ.remove ρ).IsZero := fun j => h (ρ j)

end Ctx

variable {k n m : ℕ}

lemma CtxAdd.remove (ρ : Fin n → Fin m) {Δ₁ Δ₂ Δ : Ctx R k m} (h : CtxAdd Δ₁ Δ₂ Δ) :
    CtxAdd (Δ₁.remove ρ) (Δ₂.remove ρ) (Δ.remove ρ) :=
  ⟨fun j => h.vars (ρ j), h.refs⟩

lemma CtxScale.remove (ρ : Fin n → Fin m) {r : R} {Δ Δ' : Ctx R k m} (h : CtxScale r Δ Δ') :
    CtxScale r (Δ.remove ρ) (Δ'.remove ρ) :=
  ⟨fun j => h.vars (ρ j), h.refs⟩

lemma CtxScale.cons {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ') :
    CtxScale r (Γ.cons none) (Γ'.cons none) :=
  ⟨fun j => Fin.cases .none (fun j => h.vars j) j, h.refs⟩

lemma AssmScale.unique {r : R} {a b c : Option (Assm R k)} (h₁ : AssmScale r a b)
    (h₂ : AssmScale r a c) : b = c := by
  cases h₁ <;> cases h₂ <;> rfl

lemma AssmScale.grd_eq {r q : R} {A : Ty R k} {b : Option (Assm R k)}
    (h : AssmScale r (some (.grd A q)) b) : b = some (.grd A (r * q)) := by
  cases h; rfl

lemma CtxScale.unique {r : R} {Γ Γ₁ Γ₂ : Ctx R k n} (h₁ : CtxScale r Γ Γ₁)
    (h₂ : CtxScale r Γ Γ₂) : Γ₁ = Γ₂ := by
  ext1
  · funext i; exact (h₁.vars i).unique (h₂.vars i)
  · rw [h₁.refs, h₂.refs]

/-! ## The side condition on the substituted term -/

/-- The condition on the substituted term `s` and its context `Γx`, depending on the
assumption on the substituted variable:
* absent: `Γx` is a zero context (and `s` is arbitrary);
* linear `x : A`: `Γx ⊢ s : A`;
* graded `x : [A]_r`: `Γx = r · Γ₁` for some `Γ₁ ⊢ s : A`, and `s` does not allocate. -/
def SubstHyp : Option (Assm R k) → Ctx R k n → Term R n → Prop
  | none, Γx, _ => Γx.IsZero
  | some (.lin A), Γx, s => HasTypeD Γx s A
  | some (.grd A r), Γx, s => ∃ Γ₁, HasTypeD Γ₁ s A ∧ ¬ s.Allocates ∧ CtxScale r Γ₁ Γx

namespace SubstHyp

variable {a : Option (Assm R k)} {Γx : Ctx R k n} {s : Term R n}

lemma isZero (hz : ZeroAssm a) (h : SubstHyp a Γx s) : Γx.IsZero := by
  rcases a with _ | ⟨A | ⟨A, r⟩⟩
  · exact h
  · exact hz.elim
  · simp only [ZeroAssm] at hz; subst hz
    obtain ⟨Γ₁, -, -, hsc⟩ := h
    exact hsc.isZero_zero

lemma shift (h : SubstHyp a Γx s) : SubstHyp a (Γx.cons none) (s.rename Fin.succ) := by
  rcases a with _ | ⟨A | ⟨A, r⟩⟩
  · exact Ctx.IsZero.cons (a := none) trivial h
  · exact HasTypeD.shift h
  · obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
    exact ⟨Γ₁.cons none, h₁.shift, fun h' => hna (Term.allocates_rename.mp h'), hsc.cons⟩

lemma substNames {k' : ℕ} (τ : Fin k → Ident k') (h : SubstHyp a Γx s) :
    SubstHyp (a.map (Assm.subst τ)) (Γx.substNames τ) s := by
  rcases a with _ | ⟨A | ⟨A, r⟩⟩
  · exact Ctx.IsZero.substNames h τ
  · exact HasTypeD.substNames h τ
  · obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
    exact ⟨Γ₁.substNames τ, h₁.substNames τ, hna, hsc.substNames τ⟩

/-- Splitting the substitution along a split of the substituted variable. -/
lemma split {a₁ a₂ : Option (Assm R k)} (hadd : AssmAdd a₁ a₂ a) (h : SubstHyp a Γx s) :
    ∃ Γ₁ Γ₂, SubstHyp a₁ Γ₁ s ∧ SubstHyp a₂ Γ₂ s ∧ CtxAdd Γ₁ Γ₂ Γx := by
  cases hadd with
  | noneLeft a => exact ⟨Ctx.none n, Γx, Ctx.IsZero.none, h, CtxAdd.none_left _⟩
  | noneRight a => exact ⟨Γx, Ctx.none n, h, Ctx.IsZero.none, CtxAdd.none_right _⟩
  | grd A r q =>
    obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
    obtain ⟨Γr, hr⟩ := CtxScale.exists_of_graded hsc.graded r
    obtain ⟨Γq, hq⟩ := CtxScale.exists_of_graded hsc.graded q
    exact ⟨Γr, Γq, ⟨Γ₁, h₁, hna, hr⟩, ⟨Γ₁, h₁, hna, hq⟩, hr.add_scale hq hsc⟩

/-- The substitution under the promotion rule `pr`. -/
lemma scale {r : R} {a₀ : Option (Assm R k)} (hsc : AssmScale r a₀ a) (h : SubstHyp a Γx s) :
    ∃ Γx₀, SubstHyp a₀ Γx₀ s ∧ CtxScale r Γx₀ Γx := by
  cases hsc with
  | none => exact ⟨Γx, h, CtxScale.of_isZero h r⟩
  | grd A q =>
    obtain ⟨Γ₁, h₁, hna, hsc'⟩ := h
    obtain ⟨Γq, hq⟩ := CtxScale.exists_of_graded hsc'.graded q
    obtain ⟨Y, hY⟩ := CtxScale.exists_of_graded hq.graded' r
    have := (hq.comp hY).unique hsc'
    subst this
    exact ⟨Γq, ⟨Γ₁, h₁, hna, hq⟩, hY⟩

/-- The substitution under an approximation `x : [A]_r ⟶ x : [A]_q`. -/
lemma le {A : Ty R k} {r q : R} (hrq : r ≤ q) (h : SubstHyp (some (.grd A q)) Γx s) :
    ∃ Γx₀, SubstHyp (some (.grd A r)) Γx₀ s ∧ CtxLe Γx₀ Γx := by
  obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
  obtain ⟨Γr, hr⟩ := CtxScale.exists_of_graded hsc.graded r
  exact ⟨Γr, ⟨Γ₁, h₁, hna, hr⟩, CtxLe.of_scale hr hsc hrq⟩

end SubstHyp

/-! ## The general substitution lemma -/

/-- Combining the splitting of the substitution with the splitting of the context. -/
lemma subst_split {ρ : Fin n → Fin m} {i : Fin m} {Δ₁ Δ₂ Δ : Ctx R k m}
    (hadd : CtxAdd Δ₁ Δ₂ Δ) {Γx Γ' : Ctx R k n} {s : Term R n}
    (hs : SubstHyp (Δ.vars i) Γx s) (hadd' : CtxAdd Γx (Δ.remove ρ) Γ') :
    ∃ Γx₁ Γx₂ C₁ C₂, SubstHyp (Δ₁.vars i) Γx₁ s ∧ SubstHyp (Δ₂.vars i) Γx₂ s ∧
      CtxAdd Γx₁ (Δ₁.remove ρ) C₁ ∧ CtxAdd Γx₂ (Δ₂.remove ρ) C₂ ∧ CtxAdd C₁ C₂ Γ' := by
  obtain ⟨Γx₁, Γx₂, h₁, h₂, h₁₂⟩ := hs.split (hadd.vars i)
  obtain ⟨C₁, C₂, hc₁, hc₂, hc⟩ := h₁₂.interchange (hadd.remove ρ) hadd'
  exact ⟨Γx₁, Γx₂, C₁, C₂, h₁, h₂, hc₁, hc₂, hc⟩

theorem HasTypeD.subst_gen {Δ : Ctx R k m} {t : Term R m} {B : Ty R k} (ht : HasTypeD Δ t B) :
    ∀ {n : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term R n} {Γx Γ' : Ctx R k n},
      SubstSetup ρ i σ → SubstHyp (Δ.vars i) Γx (σ i) → CtxAdd Γx (Δ.remove ρ) Γ' →
      HasTypeD Γ' (t.subst σ) B := by
  induction ht with
  | @var _ m Δ l C hl hz =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    simp only [Term.subst]
    by_cases hli : l = i
    · subst hli
      rw [hl] at hsub
      exact (hsub : HasTypeD Γx (σ l) C).weakenZero
        (fun j => hz _ (hs.ne j)) hadd.comm
    · obtain ⟨j, rfl⟩ := hs.surj l hli
      rw [hs.var]
      have hΓx := hsub.isZero (hz i (Ne.symm hli))
      refine HasTypeD.weakenZero (Γ := Δ.remove ρ) (.var hl (fun j' hj' => hz _ ?_)) hΓx hadd
      exact hs.inj.ne hj'
  | @varG _ m Δ l C hl hz =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    simp only [Term.subst]
    by_cases hli : l = i
    · subst hli
      rw [hl] at hsub
      obtain ⟨Γ₁, h₁, -, hsc⟩ := hsub
      rw [hsc.one_eq] at hadd
      exact h₁.weakenZero (fun j => hz _ (hs.ne j)) hadd.comm
    · obtain ⟨j, rfl⟩ := hs.surj l hli
      rw [hs.var]
      have hΓx := hsub.isZero (hz i (Ne.symm hli))
      refine HasTypeD.weakenZero (Γ := Δ.remove ρ) (.varG hl (fun j' hj' => hz _ ?_)) hΓx hadd
      exact hs.inj.ne hj'
  | abs _ ih =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    refine HasTypeD.abs (ih hs.up hsub.shift ?_)
    rw [Ctx.remove_cons]
    exact hadd.cons (.noneLeft _)
  | app hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .app a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | tensorI hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .tensorI a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | unitE hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .unitE a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | withBorrow hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .withBorrow a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | join hfg hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    exact .join hfg a (ih₁ hs h₁ a₁) (ih₂ hs h₂ a₂)
  | elim hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .elim a (ih₁ hs h₁ a₁) (ih₂ hs.up h₂.shift ?_)
    rw [Ctx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | clone ι hadd₀ _ hr hc hA _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .clone ι a (ih₁ hs h₁ a₁) hr hc hA (ih₂ hs.up h₂.shift ?_)
    rw [Ctx.remove_cons]
    exact a₂.cons (.noneLeft _)
  | tensorE hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .tensorE a (ih₁ hs h₁ a₁) (ih₂ hs.up.up h₂.shift.shift ?_)
    rw [Ctx.remove_cons, Ctx.remove_cons]
    exact (a₂.cons (.noneLeft _)).cons (.noneLeft _)
  | unpack hadd₀ _ _ ih₁ ih₂ =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨_, _, _, _, h₁, h₂, a₁, a₂, a⟩ := subst_split hadd₀ hsub hadd
    refine .unpack a (ih₁ hs h₁ a₁) (ih₂ hs.up (h₂.substNames _).shift ?_)
    rw [Ctx.remove_cons, Ctx.shiftNames, Ctx.remove_substNames]
    exact (a₂.substNames _).cons (.noneLeft _)
  | @pr _ m Δ₀ Δ t C r hsc _ hna ih =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    obtain ⟨Γx₀, h₀, hx₀⟩ := hsub.scale (hsc.vars i)
    obtain ⟨C₀, hc₀, hsc₀⟩ := hx₀.add_exists (hsc.remove ρ) hadd
    refine .pr hsc₀ (ih hs h₀ hc₀) ?_
    intro hall
    rcases Term.allocates_subst hall with h | ⟨j, hj, ha⟩
    · exact hna h
    · by_cases hji : j = i
      · subst hji
        have hne := ‹HasTypeD Δ₀ t C›.occurs hj
        have e := hsc.vars j
        rcases e' : Δ₀.vars j with _ | ⟨A | ⟨A, q⟩⟩
        · exact absurd e' hne
        · rw [e'] at e; exact e.not_lin_left.elim
        · rw [e'] at e
          rw [e.grd_eq] at hsub
          obtain ⟨_, _, hna', _⟩ := hsub
          exact hna' ha
      · exact hs.not_allocates hji ha
  | @approx _ m Δ₀ t C j A r q hj hrq _ ih =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    by_cases hji : j = i
    · subst hji
      rw [Ctx.update_vars_self] at hsub
      obtain ⟨Γx₀, h₀, hle⟩ := hsub.le hrq
      rw [Ctx.remove_update_ne hs.ne] at hadd
      obtain ⟨C₀, hc₀, hle₀⟩ := hle.add_exists hadd
      rw [← hj] at h₀
      exact (ih hs h₀ hc₀).approxCtx hle₀
    · rw [Ctx.update_vars_ne _ (Ne.symm hji)] at hsub
      obtain ⟨j', rfl⟩ := hs.surj j hji
      rw [Ctx.remove_update hs.inj] at hadd
      obtain ⟨C₀, hc₀, hle₀⟩ := (CtxLe.update (Γ := Δ₀.remove ρ) (i := j') hj hrq).add_exists' hadd
      exact (ih hs hsub hc₀).approxCtx hle₀
  | pack ι _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .pack ι (ih hs hsub hadd)
  | share r _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .share r (ih hs hsub hadd)
  | split _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .split (ih hs hsub hadd)
  | push _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .push (ih hs hsub hadd)
  | pull _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .pull (ih hs hsub hadd)
  | unborrow _ ih => intro n ρ i σ Γx Γ' hs hsub hadd; exact .unborrow (ih hs hsub hadd)
  | unitI hz =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    exact .unitI ((hsub.isZero (hz i)).add hadd (hz.remove ρ))
  | nat x hz =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    exact .nat x ((hsub.isZero (hz i)).add hadd (hz.remove ρ))
  | float x hz =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    exact .float x ((hsub.isZero (hz i)).add hadd (hz.remove ρ))
  | prim hz hp =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    exact .prim ((hsub.isZero (hz i)).add hadd (hz.remove ρ)) hp
  | @ref _ m Δ a T hz ha =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    have := hadd.refs a
    rw [show (Δ.remove ρ).refs a = some T from ha] at this
    exact .ref ((hsub.isZero (hz i)).add hadd (hz.remove ρ)) this.eq_of_right
  | nec p hz _ ih =>
    intro n ρ i σ Γx Γ' hs hsub hadd
    have hΓx := hsub.isZero (hz i)
    refine .nec p (hΓx.add hadd (hz.remove ρ)) (ih hs (Γx := Γx.refsOnly)
      (Ctx.IsZero.refsOnly Γx) ?_)
    rw [Ctx.remove_refsOnly]
    exact hadd.refsOnly

/-! ## Lemmas 6.2 and 6.3 -/

/-- **Lemma 6.2 (Linear substitution is admissible).** If `Γ₁ ⊢ t₁ : A` and
`Γ₂, x : A ⊢ t₂ : B`, then `Γ₂ + Γ₁ ⊢ t₂[t₁/x] : B`. -/
theorem HasType.subst_lin {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 1)}
    {A B : Ty R k} (h₁ : HasType Γ₁ t₁ A) (h₂ : HasType (Γ₂.cons (some (.lin A))) t₂ B)
    (hadd : CtxAdd Γ₂ Γ₁ Γ) : HasType Γ (Term.subst1 t₁ t₂) B :=
  (h₂.toD.subst_gen (SubstSetup.zero t₁) (Γx := Γ₁) h₁.toD hadd.comm).toHasType

/-- **Lemma 6.3 (Graded substitution is admissible).** If `[Γ₁] ⊢ t₁ : A`,
`Γ₂, x : [A]_r ⊢ t₂ : B` and `¬ resourceAllocator(t₁)`, then
`Γ₂ + r · Γ₁ ⊢ t₂[t₁/x] : B`.  (`Γ₁` has no linear assumptions because `r · Γ₁` is
defined.) -/
theorem HasType.subst_grd {Γ₁ Γ₁r Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 1)}
    {A B : Ty R k} {r : R} (h₁ : HasType Γ₁ t₁ A) (h₂ : HasType (Γ₂.cons (some (.grd A r))) t₂ B)
    (hna : ¬ t₁.Allocates) (hsc : CtxScale r Γ₁ Γ₁r) (hadd : CtxAdd Γ₂ Γ₁r Γ) :
    HasType Γ (Term.subst1 t₁ t₂) B :=
  (h₂.toD.subst_gen (SubstSetup.zero t₁) (Γx := Γ₁r) ⟨Γ₁, h₁.toD, hna, hsc⟩ hadd.comm).toHasType

/-- Substitution for a variable that has no assumption (strengthening). -/
theorem HasType.subst_none {Γ : Ctx R k n} {s : Term R n} {t : Term R (n + 1)} {B : Ty R k}
    (h : HasType (Γ.cons none) t B) : HasType Γ (Term.subst1 s t) B :=
  (h.toD.subst_gen (SubstSetup.zero s) (Γx := Ctx.none n) Ctx.IsZero.none
    (CtxAdd.none_left Γ)).toHasType

end FOFU
