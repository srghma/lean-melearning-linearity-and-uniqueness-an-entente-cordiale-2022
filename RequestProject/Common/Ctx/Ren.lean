module
public import RequestProject.Common.Ctx.Pointwise

/-!
# Length-indexed contexts: renaming

`Ctx.Ren P r Γ Δ`: `Δ` is `Γ` renamed along the injective renaming `r`, with entries
satisfying `P` at the variables outside the image of `r`.
-/

@[expose] public section

namespace Ctx

variable {α β γ δ : Type} {n m : ℕ}

/-! ## Renaming contexts

`Ren P r Γ Δ` says that `Δ` is `Γ` renamed along the injective renaming `r`, with entries
satisfying `P` at the variables outside the image of `r`.  Typing is preserved by such
renamings when `P` describes the entries that can be weakened away (non-linear or absent
hypotheses, zero-graded assumptions, …). -/

/-- `Δ` is `Γ` renamed along the injective `r`, with `P`-entries elsewhere. -/
structure Ren (P : α → Prop) (r : Var n → Var m) (Γ : Ctx α n) (Δ : Ctx α m) : Prop where
  inj : Function.Injective r
  map : ∀ i, Δ.get (r i) = Γ.get i
  off : ∀ j, (∀ i, r i ≠ j) → P (Δ.get j)

namespace Ren

variable {P : α → Prop} {r : Var n → Var m} {Γ : Ctx α n} {Δ : Ctx α m}

/-- Renamings extend under binders. -/
lemma up (h : Ren P r Γ Δ) (a : α) : Ren P (Ren.up r) (Γ ,, a) (Δ ,, a) where
  inj := _root_.Ren.up_injective h.inj
  map i := by cases i with | zero => rfl | succ i => exact h.map i
  off j hj := by
    cases j with
    | zero => exact absurd rfl (hj .zero)
    | succ j => exact h.off j (fun i e => hj (.succ i) (by simp [e]))

/-- Weakening by a new variable `Var.zero` whose entry satisfies `P`. -/
lemma succ (Γ : Ctx α n) {a : α} (ha : P a) : Ren P Var.succ Γ (Γ ,, a) where
  inj := Var.succ_injective
  map _ := rfl
  off j hj := by
    cases j with
    | zero => exact ha
    | succ j => exact absurd rfl (hj j)

/-- The identity renaming. -/
lemma refl (Γ : Ctx α n) : Ren P id Γ Γ where
  inj := Function.injective_id
  map _ := rfl
  off j hj := absurd rfl (hj j)

lemma all (h : Ren P r Γ Δ) (hΓ : All P Γ) : All P Δ :=
  all_iff.2 fun j => by
    by_cases hj : ∃ i, r i = j
    · obtain ⟨i, rfl⟩ := hj; rw [h.map]; exact hΓ.get i
    · exact h.off j (fun i e => hj ⟨i, e⟩)

lemma set (h : Ren P r Γ Δ) (i : Var n) (a : α) : Ren P r (Γ.set i a) (Δ.set (r i) a) where
  inj := h.inj
  map k := by
    by_cases hk : k = i
    · subst hk; simp
    · rw [get_set_ne _ _ (h.inj.ne hk), get_set_ne _ _ hk, h.map]
  off j hj := by
    rw [get_set_ne _ _ (fun e => hj i e.symm)]
    exact h.off j hj

/-- Picked contexts are transported along renamings. -/
lemma pick (h : Ren P r Γ Δ) {i : Var n} {a : α} (hi : Pick P Γ i a) : Pick P Δ (r i) a :=
  pick_iff.2 ⟨by rw [h.map, hi.get], fun j hj => by
    by_cases hj' : ∃ k, r k = j
    · obtain ⟨k, rfl⟩ := hj'
      rw [h.map]; exact hi.other (fun e => hj (e ▸ rfl))
    · exact h.off j (fun k e => hj' ⟨k, e⟩)⟩

open Classical in
/-- A splitting `Γ₁ + Γ₂ = Γ` of the source context can be transported to a splitting of
the renamed context, when the relation is reflexive on `P`-entries: the extra entries are
given to both parts. -/
lemma split {R : α → α → α → Prop} (hR : ∀ {a}, P a → R a a a) (h : Ren P r Γ Δ)
    {Γ₁ Γ₂ : Ctx α n} (hadd : Forall₃ R Γ₁ Γ₂ Γ) :
    ∃ Δ₁ Δ₂, Ren P r Γ₁ Δ₁ ∧ Ren P r Γ₂ Δ₂ ∧ Forall₃ R Δ₁ Δ₂ Δ := by
  let mk : Ctx α n → Ctx α m := fun Θ =>
    ofFn (fun j => if hj : ∃ i, r i = j then Θ.get hj.choose else Δ.get j)
  have hmap : ∀ Θ i, (mk Θ).get (r i) = Θ.get i := fun Θ i => by
    have hex : ∃ i', r i' = r i := ⟨i, rfl⟩
    simp only [mk, get_ofFn, dif_pos hex]
    rw [h.inj hex.choose_spec]
  have hoff : ∀ Θ j, (∀ i, r i ≠ j) → (mk Θ).get j = Δ.get j := fun Θ j hj => by
    simp only [mk, get_ofFn, dif_neg (show ¬ ∃ i, r i = j from fun ⟨i, e⟩ => hj i e)]
  refine ⟨mk Γ₁, mk Γ₂, ⟨h.inj, hmap Γ₁, fun j hj => by rw [hoff _ j hj]; exact h.off j hj⟩,
    ⟨h.inj, hmap Γ₂, fun j hj => by rw [hoff _ j hj]; exact h.off j hj⟩, ?_⟩
  refine forall₃_iff.2 fun j => ?_
  by_cases hj : ∃ i, r i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [hmap, hmap, h.map]; exact hadd.get i
  · have hj' : ∀ i, r i ≠ j := fun i e => hj ⟨i, e⟩
    rw [hoff _ j hj', hoff _ j hj']
    exact hR (h.off j hj')

end Ren

end Ctx
