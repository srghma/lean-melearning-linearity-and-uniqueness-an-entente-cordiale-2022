module
public import RequestProject.FOFU.Sec6_3_Theorems.NameSubst
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst

/-!
# Renaming (and weakening by zero-graded variables) in typing derivations

`HasTypeD.rename`: if `Γ ⊢ t : A` and `Γ.RenCtx r Γ'`, i.e. `Γ'` is `Γ` renamed along an
injective renaming `r` of variables with absent or `0`-graded assumptions on the variables
outside the image of `r`, then `Γ' ⊢ r(t) : A`.  It is the generic context renaming
`Ctx.Ren ZeroAssm r` of `RequestProject/Common/Ctx.lean` on the variables; the references
are unchanged.  In particular a derivation can be moved under a binder
(`HasTypeD.shift`: `Γ, x : − ⊢ t↑ : A`).
-/

@[expose] public section

namespace FOFU

open Ty

variable {R : Type} [Grades.PreorderedSemiring R]

/-- A zero assumption is its own sum. -/
lemma ZeroAssm.add_self {k : ℕ} {a : Option (Assm R k)} (h : ZeroAssm a) : AssmAdd a a a := by
  cases h with
  | none => exact .noneLeft _
  | grd A => have := AssmAdd.grd A (0 : R) 0; rwa [add_zero] at this

namespace TCtx

variable {k n m ρ : ℕ}

/-- `RenCtx r Γ Γ'`: `Γ'` is `Γ` renamed along the injective `r`, with absent or
`0`-graded assumptions on the variables outside the image of `r`; the references are
unchanged. -/
structure RenCtx (r : Var n → Var m) (Γ : TCtx R k n ρ) (Γ' : TCtx R k m ρ) : Prop where
  refs : Γ'.refs = Γ.refs
  vars : Ctx.Ren ZeroAssm r Γ.vars Γ'.vars

namespace RenCtx

variable {r : Var n → Var m} {Γ : TCtx R k n ρ} {Γ' : TCtx R k m ρ}

lemma cons (hr : RenCtx r Γ Γ') (a : Option (Assm R k)) :
    RenCtx (Ren.up r) (Γ.cons a) (Γ'.cons a) := ⟨hr.refs, hr.vars.up a⟩

lemma isZero (hr : RenCtx r Γ Γ') (hΓ : Γ.IsZero) : Γ'.IsZero := hr.vars.all hΓ

lemma refsOnly (hr : RenCtx r Γ Γ') : RenCtx r Γ.refsOnly Γ'.refsOnly :=
  ⟨hr.refs, Ctx.Ren.replicate .none hr.vars.inj⟩

lemma setVar (hr : RenCtx r Γ Γ') (i : Var n) (a : Option (Assm R k)) :
    RenCtx r (Γ.setVar i a) (Γ'.setVar (r i) a) := ⟨hr.refs, hr.vars.set i a⟩

lemma shiftNames (hr : RenCtx r Γ Γ') : RenCtx r Γ.shiftNames Γ'.shiftNames :=
  ⟨by simp [TCtx.shiftNames, hr.refs],
    hr.vars.mapCtx _ fun _ ha => ha.renNames _⟩

lemma lookup (hr : RenCtx r Γ Γ') {i : Var n} {a : Option (Assm R k)}
    (h : Γ.vars.Lookup i a) : Γ'.vars.Lookup (r i) a :=
  Ctx.Lookup.of_eq (by rw [hr.vars.map, h.eq])

/-- A splitting `Γ₁ + Γ₂ = Γ` of the source context can be transported to a splitting of
the renamed context; the extra (zero) assumptions are given to both parts. -/
lemma split (hr : RenCtx r Γ Γ') {Γ₁ Γ₂ : TCtx R k n ρ} (hadd : CtxAdd Γ₁ Γ₂ Γ) :
    ∃ Γ₁' Γ₂', RenCtx r Γ₁ Γ₁' ∧ RenCtx r Γ₂ Γ₂' ∧ CtxAdd Γ₁' Γ₂' Γ' := by
  obtain ⟨Δ₁, Δ₂, h₁, h₂, h⟩ := hr.vars.split ZeroAssm.add_self hadd.vars
  exact ⟨⟨Γ₁.refs, Δ₁⟩, ⟨Γ₂.refs, Δ₂⟩, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩, ⟨hr.refs ▸ hadd.refs, h⟩⟩

/-- Scaling can be transported along renamings. -/
lemma scale (hr : RenCtx r Γ Γ') {q : R} {Γ₀ : TCtx R k n ρ} (hs : CtxScale q Γ₀ Γ) :
    ∃ Γ₀', RenCtx r Γ₀ Γ₀' ∧ CtxScale q Γ₀' Γ' := by
  classical
  let f : Var m → Option (Assm R k) := fun j =>
    if hj : ∃ i, r i = j then Γ₀.vars.get hj.choose else Γ'.vars.get j
  have hf : ∀ i, f (r i) = Γ₀.vars.get i := fun i => by
    have hex : ∃ i', r i' = r i := ⟨i, rfl⟩
    simp only [f, dif_pos hex]; rw [hr.vars.inj hex.choose_spec]
  have hf' : ∀ j, (∀ i, r i ≠ j) → f j = Γ'.vars.get j := fun j hj => by
    simp only [f, dif_neg (show ¬ ∃ i, r i = j from fun ⟨i, e⟩ => hj i e)]
  refine ⟨⟨Γ₀.refs, Ctx.ofFn f⟩, ⟨rfl, ⟨hr.vars.inj, fun i => by simp [hf], fun j hj => ?_⟩⟩,
    ⟨by rw [hr.refs, hs.refs], Ctx.forall₂_iff.2 fun j => ?_⟩⟩
  · rw [Ctx.get_ofFn, hf' j hj]; exact hr.vars.off j hj
  · rw [Ctx.get_ofFn]
    by_cases hj : ∃ i, r i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hf, hr.vars.map]; exact hs.vars.get i
    · have hj' : ∀ i, r i ≠ j := fun i e => hj ⟨i, e⟩
      rw [hf' j hj']; exact AssmScale.zero (hr.vars.off j hj') q

end RenCtx

/-- Renaming along `Var.succ`, adding a new variable with a zero assumption. -/
lemma renCtx_succ (Γ : TCtx R k n ρ) {a : Option (Assm R k)} (ha : ZeroAssm a) :
    RenCtx Var.succ Γ (Γ.cons a) := ⟨rfl, Ctx.Ren.succ Γ.vars ha⟩

end TCtx

/-! ## The renaming lemma -/

theorem HasTypeD.rename {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k}
    (h : HasTypeD Γ t A) :
    ∀ {m : ℕ} {r : Var n → Var m} {Γ' : TCtx R k m ρ}, Γ.RenCtx r Γ' →
      HasTypeD Γ' (t.rename r) A := by
  induction h with
  | var hi => intro m r Γ' hr; exact .var (hr.vars.pick hi)
  | varG hi => intro m r Γ' hr; exact .varG (hr.vars.pick hi)
  | abs _ ih => intro m r Γ' hr; exact .abs (ih (hr.cons _))
  | app hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .app hadd' (ih₁ h₁) (ih₂ h₂)
  | tensorI hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .tensorI hadd' (ih₁ h₁) (ih₂ h₂)
  | unitE hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .unitE hadd' (ih₁ h₁) (ih₂ h₂)
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .withBorrow hadd' (ih₁ h₁) (ih₂ h₂)
  | join hfg hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .join hfg hadd' (ih₁ h₁) (ih₂ h₂)
  | elim hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .elim hadd' (ih₁ h₁) (ih₂ (h₂.cons _))
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .tensorE hadd' (ih₁ h₁) (ih₂ ((h₂.cons _).cons _))
  | unpack hadd _ _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .unpack hadd' (ih₁ h₁) (ih₂ (h₂.shiftNames.cons _))
  | clone ι hadd _ hq hc hA _ ih₁ ih₂ =>
    intro m r Γ' hr
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hr.split hadd
    exact .clone ι hadd' (ih₁ h₁) hq hc hA (ih₂ (h₂.cons _))
  | pr hs _ hna ih =>
    intro m r Γ' hr
    obtain ⟨Γ₀', h₀, hs'⟩ := hr.scale hs
    exact .pr hs' (ih h₀) (by rwa [Term.allocates_ren])
  | @approx k n ρ Γ t B i C q s hi hrs _ ih =>
    intro m r Γ' hr
    have h₀ := hr.setVar i (Γ.vars.get i)
    rw [TCtx.setVar_setVar, TCtx.setVar_get] at h₀
    have hq : (Γ'.setVar (r i) (Γ.vars.get i)).vars.Lookup (r i) (some (.grd C q)) :=
      Ctx.Lookup.of_eq (by simp [hi.eq])
    have := HasTypeD.approx hq hrs (ih h₀)
    have hs : Γ'.vars.get (r i) = some (.grd C s) := by rw [hr.vars.map]; simp
    rwa [TCtx.setVar_setVar, ← hs, TCtx.setVar_get] at this
  | pack ι _ ih => intro m r Γ' hr; exact .pack ι (ih hr)
  | share q _ ih => intro m r Γ' hr; exact .share q (ih hr)
  | split _ ih => intro m r Γ' hr; exact .split (ih hr)
  | push _ ih => intro m r Γ' hr; exact .push (ih hr)
  | pull _ ih => intro m r Γ' hr; exact .pull (ih hr)
  | unborrow _ ih => intro m r Γ' hr; exact .unborrow (ih hr)
  | unitI hz => intro m r Γ' hr; exact .unitI (hr.isZero hz)
  | nat x hz => intro m r Γ' hr; exact .nat x (hr.isZero hz)
  | float x hz => intro m r Γ' hr; exact .float x (hr.isZero hz)
  | prim hz hp => intro m r Γ' hr; exact .prim (hr.isZero hz) hp
  | nec p hz _ ih => intro m r Γ' hr; exact .nec p (hr.isZero hz) (ih hr.refsOnly)
  | ref hz ha => intro m r Γ' hr; exact .ref (hr.isZero hz) (hr.refs ▸ ha)

/-- Moving a derivation under a binder: `Γ ⊢ t : A` implies `Γ, x : − ⊢ t↑ : A`. -/
theorem HasTypeD.shift {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k}
    (h : HasTypeD Γ t A) : HasTypeD (Γ.cons none) (t.rename Var.succ) A :=
  h.rename (TCtx.renCtx_succ Γ .none)

end FOFU
