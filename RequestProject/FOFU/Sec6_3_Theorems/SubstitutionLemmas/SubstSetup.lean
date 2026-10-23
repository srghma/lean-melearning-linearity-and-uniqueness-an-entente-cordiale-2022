module
public import RequestProject.FOFU.Sec6_3_Theorems.SubstitutionLemmas.Occurs

/-!
# Infrastructure for the substitution lemmas

* `SubstSetup ρ i σ`: the substitution `σ` replaces the variable `i` and renames the other
  variables along `ρ`;
* `TCtx.remove`: removing the substituted variable from a context, and how it interacts
  with context addition and scaling;
* `SubstHyp a Γx s`: the side condition on the substituted term `s`, in context `Γx`, for a
  variable whose assumption is `a` (absent, linear or graded), with its splitting and
  scaling laws.

These are used by the general substitution lemma `HasTypeD.subst_gen` in
`Substitution.lean`.
-/

@[expose] public section

namespace FOFU

open Binding

variable {R : Type} [Grades.PreorderedSemiring R]

/-! ## Substitution data -/

/-- Data describing the substitution of a term for the variable `i : Var m`:
`ρ : Var n → Var m` enumerates the other variables and `σ` maps them back to
variables, while `σ i` is the substituted term. -/
structure SubstSetup {n m ρ' : ℕ} (ρ : Var n → Var m) (i : Var m) (σ : Var m → Term R n ρ') :
    Prop where
  inj : Function.Injective ρ
  ne : ∀ j, ρ j ≠ i
  surj : ∀ l, l ≠ i → ∃ j, ρ j = l
  var : ∀ j, σ (ρ j) = .var j

namespace SubstSetup

variable {n m ρ' : ℕ} {ρ : Var n → Var m} {i : Var m} {σ : Var m → Term R n ρ'}

omit [Grades.PreorderedSemiring R] in
/-- Substitution data can be pushed under a binder. -/
lemma up (hs : SubstSetup ρ i σ) :
    SubstSetup (Ren.up ρ) (.succ i) (Term.Subst.up σ) where
  inj := Ren.up_injective hs.inj
  ne := by
    intro j; cases j with
    | zero => exact Var.zero_ne_succ i
    | succ j => simpa using hs.ne j
  surj := by
    intro l hl
    cases l with
    | zero => exact ⟨.zero, rfl⟩
    | succ l =>
      obtain ⟨j, hj⟩ := hs.surj l (fun e => hl (by rw [e]))
      exact ⟨.succ j, by simp [hj]⟩
  var := by
    intro j; cases j with
    | zero => rfl
    | succ j => simp [hs.var]

omit [Grades.PreorderedSemiring R] in
/-- The substitution `[s/x]` for the variable `Var.zero`, as used by `Term.subst1`. -/
lemma zero (s : Term R n ρ') : SubstSetup Var.succ .zero (Var.cons s Term.var) where
  inj := Var.succ_injective
  ne := Var.succ_ne_zero
  surj := fun l hl => by
    cases l with
    | zero => exact absurd rfl hl
    | succ l => exact ⟨l, rfl⟩
  var := fun _ => rfl

omit [Grades.PreorderedSemiring R] in
lemma not_allocates (hs : SubstSetup ρ i σ) {j : Var m} (hj : j ≠ i) : ¬ (σ j).Allocates := by
  obtain ⟨l, rfl⟩ := hs.surj j hj
  rw [hs.var]; exact Tm.not_hasOp_var

end SubstSetup

/-! ## Removing the substituted variable from a context -/

namespace TCtx

variable {k n m ρ : ℕ}

/-- The context `Δ` restricted along `r` (removing the substituted variable). -/
def remove (r : Var n → Var m) (Δ : TCtx R k m ρ) : TCtx R k n ρ :=
  ⟨Δ.refs, Ctx.ofFn fun j => Δ.vars.get (r j)⟩

omit [Grades.PreorderedSemiring R]

@[simp] lemma remove_refs (r : Var n → Var m) (Δ : TCtx R k m ρ) : (Δ.remove r).refs = Δ.refs :=
  rfl
@[simp] lemma remove_vars_get (r : Var n → Var m) (Δ : TCtx R k m ρ) (j : Var n) :
    (Δ.remove r).vars.get j = Δ.vars.get (r j) := by simp [remove]

lemma remove_cons (r : Var n → Var m) (Δ : TCtx R k m ρ) (a : Option (Assm R k)) :
    (Δ.cons a).remove (Ren.up r) = (Δ.remove r).cons a :=
  TCtx.ext rfl (Ctx.ext fun j => by cases j <;> simp)

lemma remove_refsOnly (r : Var n → Var m) (Δ : TCtx R k m ρ) :
    Δ.refsOnly.remove r = (Δ.remove r).refsOnly :=
  TCtx.ext rfl (Ctx.ext fun j => by simp)

lemma remove_renNames {k' : ℕ} (r : Var n → Var m) (τ : Var k → Var k') (Δ : TCtx R k m ρ) :
    (Δ.renNames τ).remove r = (Δ.remove r).renNames τ :=
  TCtx.ext rfl (Ctx.ext fun j => by simp)

lemma remove_setVar_ne {r : Var n → Var m} {i : Var m} (hne : ∀ j, r j ≠ i)
    (Δ : TCtx R k m ρ) (a : Option (Assm R k)) : (Δ.setVar i a).remove r = Δ.remove r :=
  TCtx.ext rfl (Ctx.ext fun j => by simp [Ctx.get_set_ne _ _ (hne j)])

lemma remove_setVar {r : Var n → Var m} (hr : Function.Injective r) (Δ : TCtx R k m ρ)
    (j : Var n) (a : Option (Assm R k)) :
    (Δ.setVar (r j) a).remove r = (Δ.remove r).setVar j a :=
  TCtx.ext rfl (Ctx.ext fun l => by
    by_cases h : l = j <;> simp [Ctx.get_set, hr.eq_iff, h])

end TCtx

variable {k n m ρ : ℕ}

lemma TCtx.IsZero.remove {Δ : TCtx R k m ρ} (h : Δ.IsZero) (r : Var n → Var m) :
    (Δ.remove r).IsZero := Ctx.all_iff.2 fun j => by simpa using h.get (r j)

lemma CtxAdd.remove (r : Var n → Var m) {Δ₁ Δ₂ Δ : TCtx R k m ρ} (h : CtxAdd Δ₁ Δ₂ Δ) :
    CtxAdd (Δ₁.remove r) (Δ₂.remove r) (Δ.remove r) :=
  ⟨h.refs, Ctx.forall₃_iff.2 fun j => by simpa using h.vars.get (r j)⟩

lemma CtxScale.remove (r : Var n → Var m) {q : R} {Δ Δ' : TCtx R k m ρ} (h : CtxScale q Δ Δ') :
    CtxScale q (Δ.remove r) (Δ'.remove r) :=
  ⟨h.refs, Ctx.forall₂_iff.2 fun j => by simpa using h.vars.get (r j)⟩

lemma AssmScale.grd_eq {r q : R} {A : Ty R k} {b : Option (Assm R k)}
    (h : AssmScale r (some (.grd A q)) b) : b = some (.grd A (r * q)) := by
  cases h; rfl

/-! ## The side condition on the substituted term -/

/-- The condition on the substituted term `s` and its context `Γx`, depending on the
assumption on the substituted variable:
* absent: `Γx` is a zero context (and `s` is arbitrary);
* linear `x : A`: `Γx ⊢ s : A`;
* graded `x : [A]_r`: `Γx = r · Γ₁` for some `Γ₁ ⊢ s : A`, and `s` does not allocate. -/
def SubstHyp : Option (Assm R k) → TCtx R k n ρ → Term R n ρ → Prop
  | none, Γx, _ => Γx.IsZero
  | some (.lin A), Γx, s => HasTypeD Γx s A
  | some (.grd A r), Γx, s => ∃ Γ₁, HasTypeD Γ₁ s A ∧ ¬ s.Allocates ∧ CtxScale r Γ₁ Γx

namespace SubstHyp

variable {a : Option (Assm R k)} {Γx : TCtx R k n ρ} {s : Term R n ρ}

lemma isZero (hz : ZeroAssm a) (h : SubstHyp a Γx s) : Γx.IsZero := by
  cases hz with
  | none => exact h
  | grd A =>
    obtain ⟨Γ₁, -, -, hsc⟩ := h
    exact hsc.isZero_zero

lemma shift (h : SubstHyp a Γx s) : SubstHyp a (Γx.cons none) (s.rename Var.succ) := by
  rcases a with _ | ⟨A | ⟨A, r⟩⟩
  · exact TCtx.IsZero.cons (a := none) h .none
  · exact HasTypeD.shift h
  · obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
    exact ⟨Γ₁.cons none, h₁.shift, by rwa [Term.allocates_ren], hsc.cons .none⟩

lemma renNames {k' : ℕ} (τ : Var k → Var k') (h : SubstHyp a Γx s) :
    SubstHyp (a.map (Assm.ren τ)) (Γx.renNames τ) s := by
  rcases a with _ | ⟨A | ⟨A, r⟩⟩
  · exact TCtx.IsZero.renNames h τ
  · exact HasTypeD.renNames h τ
  · obtain ⟨Γ₁, h₁, hna, hsc⟩ := h
    exact ⟨Γ₁.renNames τ, h₁.renNames τ, hna, hsc.renNames τ⟩

/-- Splitting the substitution along a split of the substituted variable. -/
lemma split {a₁ a₂ : Option (Assm R k)} (hadd : AssmAdd a₁ a₂ a) (h : SubstHyp a Γx s) :
    ∃ Γ₁ Γ₂, SubstHyp a₁ Γ₁ s ∧ SubstHyp a₂ Γ₂ s ∧ CtxAdd Γ₁ Γ₂ Γx := by
  cases hadd with
  | noneLeft a =>
    exact ⟨Γx.refsOnly, Γx, TCtx.IsZero.refsOnly Γx, h, CtxAdd.refsOnly_left _⟩
  | noneRight a =>
    exact ⟨Γx, Γx.refsOnly, h, TCtx.IsZero.refsOnly Γx, CtxAdd.refsOnly_right _⟩
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

end FOFU
