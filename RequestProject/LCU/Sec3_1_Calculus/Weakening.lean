module
public import RequestProject.LCU.Sec3_1_Calculus.TypingD

/-!
# Structural properties: renaming and weakening (Lemma 3)

## Main definitions

* `TCtx.RenCtx r Γ Γ'`: `Γ'` is `Γ` renamed along an injective `r : Var n → Var m`, plus
  extra non-linear (or absent) assumptions for the variables outside the image of `r`.
  It is the generic context renaming `Ctx.Ren NonLin r` of
  `RequestProject/Common/Ctx.lean` on the variables; the array references are unchanged.

## Main results

* `HasTypeD.rename`, `HasType.rename`: typing is stable under such renamings.  This
  covers exchange, and weakening by fresh non-linear variables.
* `HasType.weaken` (**Lemma 3**): if `Γ ⊢ t : A` and `Δ` is non-linear, then
  `Γ + Δ ⊢ t : A`.
* `HasType.shift`, `HasTypeD.shift`: weakening by a fresh variable `Var.zero`, used
  whenever a term is moved under a binder.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Renaming contexts -/

namespace TCtx

variable {n m ρ : ℕ}

/-- `RenCtx r Γ Γ'`: the context `Γ'` is obtained from `Γ` by renaming its variables
along the injective map `r`, and adding non-linear (or absent) assumptions for the
variables outside the image of `r`.  The array references are unchanged. -/
structure RenCtx (r : Var n → Var m) (Γ : TCtx n ρ) (Γ' : TCtx m ρ) : Prop where
  refs : Γ'.refs = Γ.refs
  vars : Ctx.Ren NonLin r Γ.vars Γ'.vars

namespace RenCtx

variable {r : Var n → Var m} {Γ : TCtx n ρ} {Γ' : TCtx m ρ}

/-- Renamings extend under binders (along `Ren.up r`). -/
lemma cons (hr : RenCtx r Γ Γ') (h : Option (Hyp Ty)) :
    RenCtx (Ren.up r) (Γ.cons h) (Γ'.cons h) := ⟨hr.refs, hr.vars.up h⟩

/-- Renaming preserves non-linearity of contexts. -/
lemma allNonLin (hr : RenCtx r Γ Γ') (hΓ : Γ.AllNonLin) : Γ'.AllNonLin :=
  ⟨hr.refs ▸ hΓ.refs, hr.vars.all hΓ.vars⟩

lemma varsNonLin (hr : RenCtx r Γ Γ') (hΓ : Γ.VarsNonLin) : Γ'.VarsNonLin := hr.vars.all hΓ

lemma refsOnly (hr : RenCtx r Γ Γ') : RenCtx r Γ.refsOnly Γ'.refsOnly where
  refs := hr.refs
  vars := ⟨hr.vars.inj, fun _ => by simp, fun _ _ => by simp⟩

/-- A splitting `Γ₁ + Γ₂ = Γ` of the source context can be transported to a
splitting of the renamed context; the extra (non-linear) assumptions are given to both
parts. -/
lemma split (hr : RenCtx r Γ Γ') {Γ₁ Γ₂ : TCtx n ρ} (hadd : Γ₁.Add Γ₂ Γ) :
    ∃ Γ₁' Γ₂', RenCtx r Γ₁ Γ₁' ∧ RenCtx r Γ₂ Γ₂' ∧ Γ₁'.Add Γ₂' Γ' := by
  obtain ⟨Δ₁, Δ₂, h₁, h₂, h⟩ := hr.vars.split HypAdd.idem hadd.vars
  exact ⟨⟨Γ₁.refs, Δ₁⟩, ⟨Γ₂.refs, Δ₂⟩, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩, ⟨hr.refs ▸ hadd.refs, h⟩⟩

end RenCtx

/-- Renaming along `Var.succ`, adding a new variable with a non-linear hypothesis. -/
lemma renCtx_succ (Γ : TCtx n ρ) {h : Option (Hyp Ty)} (hh : NonLin h) :
    RenCtx Var.succ Γ (Γ.cons h) := ⟨rfl, Ctx.Ren.succ Γ.vars hh⟩

end TCtx

/-! ## Renaming and weakening of typing derivations -/

/-- Adding a non-linear context preserves the shape `[Γ], x : h` of the context of a
variable rule. -/
lemma pick_of_add {T : Type} {n : ℕ} {Γ Δ Γ' : Ctx (Option (Hyp T)) n}
    (hadd : Ctx.Forall₃ HypAdd Γ Δ Γ') (hΔ : Δ.All NonLin) {i : Var n} {h : Hyp T}
    (hi : Γ.Pick NonLin i (some h)) : Γ'.Pick NonLin i (some h) :=
  Ctx.pick_iff.2 ⟨by have := hadd.get i; rw [hi.get] at this; exact this.some_of_nonLin (hΔ.get i),
    fun j hj => (hadd.get j).nonLin_of (hi.other hj) (hΔ.get j)⟩

namespace HasTypeD

/-- Typing is preserved by renaming (exchange and non-linear weakening). -/
theorem rename {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasTypeD Γ t A) :
    ∀ {m : ℕ} {r : Var n → Var m} {Γ' : TCtx m ρ}, Γ.RenCtx r Γ' →
      HasTypeD Γ' (t.rename r) A := by
  induction ht with
  | var hi hr =>
    intro m r Γ' hρ
    exact .var (hρ.vars.pick hi) (hρ.refs ▸ hr)
  | ref ha hv =>
    intro m r Γ' hρ
    exact .ref (hρ.refs ▸ ha) (hρ.vars.all hv)
  | abs _ ih => intro m r Γ' hρ; exact .abs (ih (hρ.cons _))
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro m r Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    split_rule (ih₁ h₁) (ih₂ (by (repeat apply TCtx.RenCtx.cons); exact h₂)) hadd'
  | unitI hΓ | natI hΓ | floatI hΓ | prim hΓ =>
    intro m r Γ' hρ; constructor; exact hρ.allNonLin hΓ
  | bangI hΓ _ ih => intro m r Γ' hρ; exact .bangI (hρ.allNonLin hΓ) (ih hρ)
  | borrow _ ih => intro m r Γ' hρ; exact .borrow (ih hρ)
  | nec _ hΓ ih => intro m r Γ' hρ; exact .nec (ih hρ.refsOnly) (hρ.varsNonLin hΓ)

/-- Lemma 3 (weakening is admissible), dereliction-free version. -/
theorem weaken {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasTypeD Γ t A) :
    ∀ {Δ Γ' : TCtx n ρ}, Δ.AllNonLin → Γ.Add Δ Γ' → HasTypeD Γ' t A := by
  suffices ∀ {Δ Γ' : TCtx n ρ}, Γ.Add Δ Γ' → Δ.AllNonLin → HasTypeD Γ' t A from
    fun {_ _} hΔ hadd => this hadd hΔ
  induction ht with
  | var hi hr =>
    intro Δ Γ' hadd hΔ
    exact .var (pick_of_add hadd.vars hΔ.vars hi) (hadd.refs.all HypAdd.nonLin_of hr hΔ.refs)
  | ref hi hv =>
    intro Δ Γ' hadd hΔ
    exact .ref (pick_of_add hadd.refs hΔ.refs hi) (hadd.vars.all HypAdd.nonLin_of hv hΔ.vars)
  | abs _ ih =>
    intro Δ Γ' hadd hΔ
    exact .abs (ih (hadd.cons (HypAdd.none_right _)) (hΔ.cons nonLin_none))
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hadd' hΔ
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := TCtx.Add.interchange hadd (TCtx.Add.idem hΔ) hadd'
    split_rule (ih₁ h₁ hΔ)
      (ih₂ (by first | exact h₂ | exact h₂.cons_none _ | exact (h₂.cons_none _).cons_none _)
        (by first | exact hΔ | exact hΔ.cons_none | exact hΔ.cons_none.cons_none)) h
  | unitI hΓ | natI hΓ | floatI hΓ | prim hΓ =>
    intro Δ Γ' hadd hΔ; constructor; exact TCtx.AllNonLin.of_add hadd hΓ hΔ
  | bangI hΓ _ ih =>
    intro Δ Γ' hadd hΔ; exact .bangI (TCtx.AllNonLin.of_add hadd hΓ hΔ) (ih hadd hΔ)
  | borrow _ ih => intro Δ Γ' hadd hΔ; exact .borrow (ih hadd hΔ)
  | nec _ hΓ ih =>
    intro Δ Γ' hadd hΔ
    exact .nec (ih hadd.refsOnly hΔ.refsOnly) (TCtx.VarsNonLin.of_add hadd hΓ hΔ.varsNonLin)

end HasTypeD

namespace HasType

/-- Typing is preserved by renaming (exchange and non-linear weakening). -/
theorem rename {n m ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} {r : Var n → Var m}
    {Γ' : TCtx m ρ} (ht : HasType Γ t A) (hr : Γ.RenCtx r Γ') : HasType Γ' (t.rename r) A :=
  hasType_iff_hasTypeD.2 ((hasType_iff_hasTypeD.1 ht).rename hr)

/-- **Lemma 3 (Weakening is admissible).** If `Γ ⊢ t : A` then `Γ + [Δ] ⊢ t : A`.
(The paper writes `Γ, [Γ']`, i.e. the sum of disjoint contexts; we allow the
non-linear context `Δ` to overlap with `Γ` as long as the sum is defined.) -/
theorem weaken {n ρ : ℕ} {Γ Δ Γ' : TCtx n ρ} {t : Term n ρ} {A : Ty}
    (ht : HasType Γ t A) (hΔ : Δ.AllNonLin) (hadd : Γ.Add Δ Γ') : HasType Γ' t A :=
  hasType_iff_hasTypeD.2 ((hasType_iff_hasTypeD.1 ht).weaken hΔ hadd)

/-- Weakening by a fresh variable (`Var.zero`) which is absent or non-linear. -/
theorem shift {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasType Γ t A)
    {h : Option (Hyp Ty)} (hh : NonLin h) : HasType (Γ.cons h) (t.rename Var.succ) A :=
  ht.rename (TCtx.renCtx_succ Γ hh)

end HasType

lemma HasTypeD.shift {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} (ht : HasTypeD Γ t A)
    {h : Option (Hyp Ty)} (hh : NonLin h) : HasTypeD (Γ.cons h) (t.rename Var.succ) A :=
  ht.rename (TCtx.renCtx_succ Γ hh)

end LCU
