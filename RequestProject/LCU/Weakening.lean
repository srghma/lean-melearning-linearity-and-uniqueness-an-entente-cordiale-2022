module
public import RequestProject.LCU.TypingD

/-!
# Structural properties: renaming and weakening (Lemma 3)
-/

@[expose] public section

namespace LCU

open Term

namespace Ctx

variable {n m : ℕ}

/-- `RenCtx ρ Γ Γ'`: the context `Γ'` is obtained from `Γ` by renaming its variables
along the injective map `ρ`, and adding non-linear (or absent) assumptions for the
variables outside the image of `ρ`. -/
structure RenCtx (ρ : Fin n → Fin m) (Γ : Ctx n) (Γ' : Ctx m) : Prop where
  inj : Function.Injective ρ
  map : ∀ i, Γ' (.inl (ρ i)) = Γ (.inl i)
  off : ∀ j, (∀ i, ρ i ≠ j) → NonLin (Γ' (.inl j))
  refs : ∀ a, Γ' (.inr a) = Γ (.inr a)

namespace RenCtx

variable {ρ : Fin n → Fin m} {Γ : Ctx n} {Γ' : Ctx m}

lemma cons (hρ : RenCtx ρ Γ Γ') (h : Option Hyp) :
    RenCtx (Term.Ren.up ρ) (Γ.cons h) (Γ'.cons h) where
  inj := by
    intro i j e
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · exact absurd e.symm (Fin.succ_ne_zero _)
    · exact absurd e (Fin.succ_ne_zero _)
    · simp only [Ren.up_succ, Fin.succ_inj] at e
      rw [hρ.inj e]
  map := by
    intro i; cases i using Fin.cases
    · rfl
    · exact hρ.map _
  off := by
    intro j hj
    cases j using Fin.cases with
    | zero => exact absurd rfl (hj 0)
    | succ j =>
      exact hρ.off j (fun i e => hj i.succ (by simp [e]))
  refs := hρ.refs

lemma allNonLin (hρ : RenCtx ρ Γ Γ') (hΓ : Γ.AllNonLin) : Γ'.AllNonLin := by
  rintro (j | a)
  · by_cases hj : ∃ i, ρ i = j
    · obtain ⟨i, rfl⟩ := hj; rw [hρ.map]; exact hΓ _
    · exact hρ.off j (fun i e => hj ⟨i, e⟩)
  · rw [hρ.refs]; exact hΓ _

lemma varsNonLin (hρ : RenCtx ρ Γ Γ') (hΓ : Γ.VarsNonLin) : Γ'.VarsNonLin := by
  intro j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj; rw [hρ.map]; exact hΓ _
  · exact hρ.off j (fun i e => hj ⟨i, e⟩)

lemma refsOnly (hρ : RenCtx ρ Γ Γ') : RenCtx ρ Γ.refsOnly Γ'.refsOnly where
  inj := hρ.inj
  map := fun _ => rfl
  off := fun _ _ => trivial
  refs := hρ.refs

lemma set (hρ : RenCtx ρ Γ Γ') (i : Fin n) (h : Option Hyp) :
    RenCtx ρ (Γ.set (.inl i) h) (Γ'.set (.inl (ρ i)) h) where
  inj := hρ.inj
  map := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · rw [set_ne _ _ (by simpa using hρ.inj.ne hk), set_ne _ _ (by simpa using hk), hρ.map]
  off := by
    intro j hj
    rw [set_ne _ _ (by simpa using (hj i).symm)]
    exact hρ.off j hj
  refs := by
    intro a; rw [set_ne _ _ (by simp), set_ne _ _ (by simp), hρ.refs]

lemma set_inr (hρ : RenCtx ρ Γ Γ') (a : ℕ) (h : Option Hyp) :
    RenCtx ρ (Γ.set (.inr a) h) (Γ'.set (.inr a) h) where
  inj := hρ.inj
  map := by intro k; rw [set_ne _ _ (by simp), set_ne _ _ (by simp), hρ.map]
  off := by intro j hj; rw [set_ne _ _ (by simp)]; exact hρ.off j hj
  refs := by
    intro b
    by_cases hb : b = a
    · subst hb; simp
    · rw [set_ne _ _ (by simpa using hb), set_ne _ _ (by simpa using hb), hρ.refs]

open Classical in
lemma split (hρ : RenCtx ρ Γ Γ') {Γ₁ Γ₂ : Ctx n} (hadd : Γ₁.Add Γ₂ Γ) :
    ∃ Γ₁' Γ₂', RenCtx ρ Γ₁ Γ₁' ∧ RenCtx ρ Γ₂ Γ₂' ∧ Γ₁'.Add Γ₂' Γ' := by
  let mk : Ctx n → Ctx m := fun Δ =>
    Sum.elim (Function.extend ρ (fun i => Δ (.inl i)) (fun j => Γ' (.inl j)))
      (fun a => Δ (.inr a))
  have hmap : ∀ Δ i, mk Δ (.inl (ρ i)) = Δ (.inl i) := fun Δ i => by
    simp only [mk, Sum.elim_inl]; exact hρ.inj.extend_apply _ _ i
  have hoff : ∀ Δ j, (∀ i, ρ i ≠ j) → mk Δ (.inl j) = Γ' (.inl j) := fun Δ j hj => by
    simp only [mk, Sum.elim_inl]; exact Function.extend_apply' _ _ _ (fun ⟨i, e⟩ => hj i e)
  refine ⟨mk Γ₁, mk Γ₂, ⟨hρ.inj, hmap Γ₁, ?_, fun _ => rfl⟩,
    ⟨hρ.inj, hmap Γ₂, ?_, fun _ => rfl⟩, ?_⟩
  · intro j hj; rw [hoff _ j hj]; exact hρ.off j hj
  · intro j hj; rw [hoff _ j hj]; exact hρ.off j hj
  · rintro (j | a)
    · by_cases hj : ∃ i, ρ i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [hmap, hmap, hρ.map]; exact hadd _
      · have hj' : ∀ i, ρ i ≠ j := fun i e => hj ⟨i, e⟩
        rw [hoff _ j hj', hoff _ j hj']
        exact HypAdd.idem (hρ.off j hj')
    · show HypAdd (Γ₁ _) (Γ₂ _) _
      rw [hρ.refs]; exact hadd _

end RenCtx

/-- Renaming along `Fin.succ`, adding a new variable with a non-linear hypothesis. -/
lemma renCtx_succ (Γ : Ctx n) {h : Option Hyp} (hh : NonLin h) :
    RenCtx Fin.succ Γ (Γ.cons h) where
  inj := Fin.succ_injective _
  map := fun _ => rfl
  off := by
    intro j hj
    cases j using Fin.cases with
    | zero => exact hh
    | succ j => exact absurd rfl (hj j)
  refs := fun _ => rfl

end Ctx

lemma HypAdd.some_of_nonLin {h : Hyp} {d c : Option Hyp} (hx : HypAdd (some h) d c)
    (hd : NonLin d) : c = some h := by
  cases hx with
  | noneRight => rfl
  | nonlin => rfl

namespace HasTypeD

/-- Typing is preserved by renaming (exchange and non-linear weakening). -/
theorem rename {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A) :
    ∀ {m : ℕ} {ρ : Fin n → Fin m} {Γ' : Ctx m}, Ctx.RenCtx ρ Γ Γ' →
      HasTypeD Γ' (t.rename ρ) A := by
  induction ht with
  | @var n Γ i h hi hrest =>
    intro m ρ Γ' hρ
    refine HasTypeD.var (by rw [hρ.map]; exact hi) ?_
    exact (hρ.set i none).allNonLin hrest
  | abs _ ih => intro m ρ Γ' hρ; exact .abs (ih (hρ.cons _))
  | app _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .app (ih₁ h₁) (ih₂ h₂) hadd'
  | tensorI _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .tensorI (ih₁ h₁) (ih₂ h₂) hadd'
  | tensorE _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .tensorE (ih₁ h₁) (ih₂ ((h₂.cons _).cons _)) hadd'
  | unitI hΓ => intro m ρ Γ' hρ; exact .unitI (hρ.allNonLin hΓ)
  | unitE _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .unitE (ih₁ h₁) (ih₂ h₂) hadd'
  | bangI hΓ _ ih => intro m ρ Γ' hρ; exact .bangI (hρ.allNonLin hΓ) (ih hρ)
  | bangE _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .bangE (ih₁ h₁) (ih₂ (h₂.cons _)) hadd'
  | borrow _ ih => intro m ρ Γ' hρ; exact .borrow (ih hρ)
  | copy _ _ hadd ih₁ ih₂ =>
    intro m ρ Γ' hρ
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hρ.split hadd
    exact .copy (ih₁ h₁) (ih₂ (h₂.cons _)) hadd'
  | nec _ hΓ ih => intro m ρ Γ' hρ; exact .nec (ih hρ.refsOnly) (hρ.varsNonLin hΓ)
  | natI hΓ => intro m ρ Γ' hρ; exact .natI (hρ.allNonLin hΓ)
  | floatI hΓ => intro m ρ Γ' hρ; exact .floatI (hρ.allNonLin hΓ)
  | prim hΓ => intro m ρ Γ' hρ; exact .prim (hρ.allNonLin hΓ)
  | @ref n Γ a h ha hrest =>
    intro m ρ Γ' hρ
    refine HasTypeD.ref (by rw [hρ.refs]; exact ha) ?_
    exact (hρ.set_inr a none).allNonLin hrest

/-- Lemma 3 (weakening is admissible), dereliction-free version. -/
theorem weaken {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A) :
    ∀ {Δ Γ' : Ctx n}, Δ.AllNonLin → Γ.Add Δ Γ' → HasTypeD Γ' t A := by
  induction ht with
  | @var n Γ i h hi hrest =>
    intro Δ Γ' hΔ hadd
    have hx := hadd (.inl i)
    rw [hi] at hx
    have hΔi := hΔ (.inl i)
    refine HasTypeD.var (h := h) ?_ ?_
    · exact hx.some_of_nonLin (hΔ _)
    · have := hadd.set (x := .inl i) (h₁ := none) (h₂ := none) (h := none) (.noneLeft _)
      exact Ctx.AllNonLin.of_add this hrest (fun y => by
        by_cases hy : y = .inl i
        · subst hy; simp
        · rw [Ctx.set_ne _ _ hy]; exact hΔ y)
  | abs _ ih =>
    intro Δ Γ' hΔ hadd
    exact .abs (ih (hΔ.cons nonLin_none) (hadd.cons (HypAdd.none_right _)))
  | app _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    exact .app (ih₁ hΔ h₁) (ih₂ hΔ h₂) h
  | tensorI _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    exact .tensorI (ih₁ hΔ h₁) (ih₂ hΔ h₂) h
  | tensorE _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    refine .tensorE (ih₁ hΔ h₁) (ih₂ ((hΔ.cons nonLin_none).cons nonLin_none)
      ((h₂.cons (HypAdd.none_right _)).cons (HypAdd.none_right _))) h
  | unitI hΓ => intro Δ Γ' hΔ hadd; exact .unitI (Ctx.AllNonLin.of_add hadd hΓ hΔ)
  | unitE _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    exact .unitE (ih₁ hΔ h₁) (ih₂ hΔ h₂) h
  | bangI hΓ _ ih =>
    intro Δ Γ' hΔ hadd; exact .bangI (Ctx.AllNonLin.of_add hadd hΓ hΔ) (ih hΔ hadd)
  | bangE _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    exact .bangE (ih₁ hΔ h₁) (ih₂ (hΔ.cons nonLin_none) (h₂.cons (HypAdd.none_right _))) h
  | borrow _ ih => intro Δ Γ' hΔ hadd; exact .borrow (ih hΔ hadd)
  | copy _ _ hadd ih₁ ih₂ =>
    intro Δ Γ' hΔ hadd'
    obtain ⟨C₁, C₂, h₁, h₂, h⟩ := Ctx.Add.interchange hadd (Ctx.Add.idem hΔ) hadd'
    exact .copy (ih₁ hΔ h₁) (ih₂ (hΔ.cons nonLin_none) (h₂.cons (HypAdd.none_right _))) h
  | nec _ hΓ ih =>
    intro Δ Γ' hΔ hadd
    exact .nec (ih hΔ.refsOnly hadd.refsOnly) (Ctx.VarsNonLin.of_add hadd hΓ hΔ.varsNonLin)
  | natI hΓ => intro Δ Γ' hΔ hadd; exact .natI (Ctx.AllNonLin.of_add hadd hΓ hΔ)
  | floatI hΓ => intro Δ Γ' hΔ hadd; exact .floatI (Ctx.AllNonLin.of_add hadd hΓ hΔ)
  | prim hΓ => intro Δ Γ' hΔ hadd; exact .prim (Ctx.AllNonLin.of_add hadd hΓ hΔ)
  | @ref n Γ a h ha hrest =>
    intro Δ Γ' hΔ hadd
    have hx := hadd (.inr a)
    rw [ha] at hx
    refine HasTypeD.ref (h := h) ?_ ?_
    · exact hx.some_of_nonLin (hΔ _)
    · have := hadd.set (x := .inr a) (h₁ := none) (h₂ := none) (h := none) (.noneLeft _)
      exact Ctx.AllNonLin.of_add this hrest (fun y => by
        by_cases hy : y = .inr a
        · subst hy; simp
        · rw [Ctx.set_ne _ _ hy]; exact hΔ y)

end HasTypeD

namespace HasType

/-- Typing is preserved by renaming (exchange and non-linear weakening). -/
theorem rename {n m : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} {ρ : Fin n → Fin m} {Γ' : Ctx m}
    (ht : HasType Γ t A) (hρ : Ctx.RenCtx ρ Γ Γ') : HasType Γ' (t.rename ρ) A :=
  hasType_iff_hasTypeD.2 ((hasType_iff_hasTypeD.1 ht).rename hρ)

/-- **Lemma 3 (Weakening is admissible).** If `Γ ⊢ t : A` then `Γ + [Δ] ⊢ t : A`.
(The paper writes `Γ, [Γ']`, i.e. the sum of disjoint contexts; we allow the
non-linear context `Δ` to overlap with `Γ` as long as the sum is defined.) -/
theorem weaken {n : ℕ} {Γ Δ Γ' : Ctx n} {t : Term n} {A : Ty}
    (ht : HasType Γ t A) (hΔ : Δ.AllNonLin) (hadd : Γ.Add Δ Γ') : HasType Γ' t A :=
  hasType_iff_hasTypeD.2 ((hasType_iff_hasTypeD.1 ht).weaken hΔ hadd)

/-- Weakening by a fresh (de Bruijn index `0`) variable which is absent or non-linear. -/
theorem shift {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasType Γ t A)
    {h : Option Hyp} (hh : NonLin h) : HasType (Γ.cons h) (t.rename Fin.succ) A :=
  ht.rename (Ctx.renCtx_succ Γ hh)

end HasType

lemma HasTypeD.shift {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A)
    {h : Option Hyp} (hh : NonLin h) : HasTypeD (Γ.cons h) (t.rename Fin.succ) A :=
  ht.rename (Ctx.renCtx_succ Γ hh)

end LCU
