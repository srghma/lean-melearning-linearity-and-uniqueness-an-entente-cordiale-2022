module
public import RequestProject.LCU.CbnSemantics

/-!
# Renaming array references, and weakening into larger non-linear contexts

Auxiliary results for the store-based semantics of `ArraySemantics.lean`:

* `Term.shiftRefs N t` renames every array reference `a` in `t` to `N + a`.  This is the
  renaming `θ` of the paper's `copy_β` rule, which points a copied value to freshly
  copied arrays.  `HasTypeD.shiftRefs` shows that it preserves typing.
* `Ctx.Sub Γ Γ'` (`Γ ⊆ Γ'`) says that `Γ'` contains all assumptions of `Γ`;
  `HasTypeD.mono` weakens a typing into a larger context whose extra assumptions are
  non-linear.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Renaming array references -/

/-- Rename every array reference `a` to `N + a`. -/
abbrev Term.shiftRefs (N : ℕ) {n : ℕ} (t : Term n) : Term n := renameRefs (N + ·) t

namespace Ctx

variable {n : ℕ}

/-- `RefShift N Γ Γ'`: `Γ'` is `Γ` with each array reference `a` renamed to `N + a`,
and with arbitrary non-linear (or absent) assumptions for the references below `N`. -/
structure RefShift (N : ℕ) (Γ Γ' : Ctx n) : Prop where
  vars : ∀ i, Γ' (.inl i) = Γ (.inl i)
  map : ∀ a, Γ' (.inr (N + a)) = Γ (.inr a)
  low : ∀ b, b < N → NonLin (Γ' (.inr b))

namespace RefShift

variable {N : ℕ} {Γ Γ' : Ctx n}

lemma cons (hs : RefShift N Γ Γ') (h : Option Hyp) : RefShift N (Γ.cons h) (Γ'.cons h) where
  vars i := by cases i using Fin.cases <;> simp [hs.vars]
  map a := hs.map a
  low b hb := hs.low b hb

lemma apply_inr_of_le (hs : RefShift N Γ Γ') {b : ℕ} (hb : N ≤ b) :
    Γ' (.inr b) = Γ (.inr (b - N)) := by
  have := hs.map (b - N); rwa [Nat.add_sub_cancel' hb] at this

lemma allNonLin (hs : RefShift N Γ Γ') (hΓ : Γ.AllNonLin) : Γ'.AllNonLin := by
  rintro (i | b)
  · rw [hs.vars]; exact hΓ _
  · by_cases hb : b < N
    · exact hs.low b hb
    · rw [hs.apply_inr_of_le (not_lt.1 hb)]; exact hΓ _

lemma varsNonLin (hs : RefShift N Γ Γ') (hΓ : Γ.VarsNonLin) : Γ'.VarsNonLin := by
  intro i; rw [hs.vars]; exact hΓ i

lemma refsOnly (hs : RefShift N Γ Γ') : RefShift N Γ.refsOnly Γ'.refsOnly where
  vars _ := rfl
  map a := hs.map a
  low b hb := hs.low b hb

lemma set_inl (hs : RefShift N Γ Γ') (i : Fin n) (h : Option Hyp) :
    RefShift N (Γ.set (.inl i) h) (Γ'.set (.inl i) h) where
  vars j := by
    by_cases hj : j = i
    · subst hj; simp
    · rw [set_ne _ _ (by simpa using hj), set_ne _ _ (by simpa using hj), hs.vars]
  map a := by rw [set_ne _ _ (by simp), set_ne _ _ (by simp), hs.map]
  low b hb := by rw [set_ne _ _ (by simp)]; exact hs.low b hb

lemma set_inr (hs : RefShift N Γ Γ') (a : ℕ) (h : Option Hyp) :
    RefShift N (Γ.set (.inr a) h) (Γ'.set (.inr (N + a)) h) where
  vars j := by rw [set_ne _ _ (by simp), set_ne _ _ (by simp), hs.vars]
  map b := by
    by_cases hb : b = a
    · subst hb; simp
    · rw [set_ne _ _ (by simpa using hb), set_ne _ _ (by simpa using hb), hs.map]
  low b hb := by rw [set_ne _ _ (by simp; omega)]; exact hs.low b hb

lemma split (hs : RefShift N Γ Γ') {Γ₁ Γ₂ : Ctx n} (hadd : Γ₁.Add Γ₂ Γ) :
    ∃ Γ₁' Γ₂', RefShift N Γ₁ Γ₁' ∧ RefShift N Γ₂ Γ₂' ∧ Γ₁'.Add Γ₂' Γ' := by
  let f : Ctx n → Ctx n := fun Δ => Sum.elim (fun i => Δ (.inl i))
    (fun b => if N ≤ b then Δ (.inr (b - N)) else Γ' (.inr b))
  have hf : ∀ Δ : Ctx n, RefShift N Δ (f Δ) := fun Δ =>
    { vars := fun i => rfl
      map := fun a => by simp [f]
      low := fun b hb => by simp [f, not_le.2 hb]; exact hs.low b hb }
  refine ⟨f Γ₁, f Γ₂, hf _, hf _, ?_⟩
  rintro (i | b)
  · simp only [f, Sum.elim_inl]; rw [hs.vars]; exact hadd _
  · simp only [f, Sum.elim_inr]
    split_ifs with hb
    · rw [hs.apply_inr_of_le hb]; exact hadd _
    · exact HypAdd.idem (hs.low b (not_le.1 hb))

end RefShift

end Ctx

/-- Renaming array references preserves typing. -/
theorem HasTypeD.shiftRefs {n : ℕ} {Γ : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A)
    {N : ℕ} {Γ' : Ctx n} (hs : Ctx.RefShift N Γ Γ') : HasTypeD Γ' (t.shiftRefs N) A := by
  induction ht with
  | var hi hrest =>
    exact .var (by rw [hs.vars]; exact hi) ((hs.set_inl _ none).allNonLin hrest)
  | abs _ ih => exact .abs (ih (hs.cons _))
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    obtain ⟨Γ₁', Γ₂', h₁, h₂, hadd'⟩ := hs.split hadd
    split_rule (ih₁ h₁) (ih₂ (by (repeat apply Ctx.RefShift.cons); exact h₂)) hadd'
  | unitI hΓ | natI hΓ | floatI hΓ | prim hΓ => constructor; exact hs.allNonLin hΓ
  | bangI hΓ _ ih => exact .bangI (hs.allNonLin hΓ) (ih hs)
  | borrow _ ih => exact .borrow (ih hs)
  | nec _ hΓ ih => exact .nec (ih hs.refsOnly) (hs.varsNonLin hΓ)
  | ref ha hrest =>
    exact .ref (by rw [hs.map]; exact ha) ((hs.set_inr _ none).allNonLin hrest)

/-! ## Weakening into larger non-linear contexts -/

/-- `Γ ⊆ Γ'`: every assumption of `Γ` is also an assumption of `Γ'`. -/
def Ctx.Sub {n : ℕ} (Γ Γ' : Ctx n) : Prop := ∀ x h, Γ x = some h → Γ' x = some h

lemma Ctx.Sub.refl {n : ℕ} (Γ : Ctx n) : Γ.Sub Γ := fun _ _ h => h

lemma Ctx.Sub.trans {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} (h₁ : Γ₁.Sub Γ₂) (h₂ : Γ₂.Sub Γ₃) :
    Γ₁.Sub Γ₃ := fun x h hx => h₂ x h (h₁ x h hx)

lemma Ctx.Sub.of_add_left {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} (hadd : Γ₁.Add Γ₂ Γ) : Γ₁.Sub Γ := by
  intro x h hx
  have := hadd x; rw [hx] at this
  generalize Γ₂ x = b at this
  generalize Γ x = c at this
  cases this <;> rfl

lemma Ctx.Sub.of_add_right {n : ℕ} {Γ₁ Γ₂ Γ : Ctx n} (hadd : Γ₁.Add Γ₂ Γ) : Γ₂.Sub Γ :=
  Ctx.Sub.of_add_left hadd.comm

/-- A context contained in a non-linear context `Γ` can be completed to `Γ` by adding a
non-linear context. -/
lemma Ctx.Sub.exists_add {n : ℕ} {Γ₁ Γ : Ctx n} (hs : Γ₁.Sub Γ) (hΓ : ∀ x, Γ₁ x = none → NonLin (Γ x)) :
    ∃ Δ : Ctx n, Δ.AllNonLin ∧ Γ₁.Add Δ Γ := by
  classical
  refine ⟨fun x => if Γ₁ x = none then Γ x else none, ?_, ?_⟩
  · intro x; dsimp only; split_ifs with h
    · exact hΓ x h
    · trivial
  · intro x; dsimp only; split_ifs with h
    · rw [h]; exact .noneLeft _
    · obtain ⟨h', e⟩ := Option.ne_none_iff_exists'.1 h
      rw [e, hs x h' e]; exact .noneRight _

/-- Weakening into a larger context whose additional assumptions are non-linear. -/
theorem HasTypeD.mono {n : ℕ} {Γ Γ' : Ctx n} {t : Term n} {A : Ty} (ht : HasTypeD Γ t A)
    (hs : Γ.Sub Γ') (hΓ' : Γ'.AllNonLin) : HasTypeD Γ' t A := by
  obtain ⟨Δ, hΔ, hadd⟩ := hs.exists_add (fun x _ => hΓ' x)
  exact ht.weaken hΔ hadd

/-- Weakening under a binder into a larger context whose additional assumptions are
non-linear. -/
theorem HasTypeD.mono_cons {n : ℕ} {Γ Γ' : Ctx n} {h : Option Hyp} {t : Term (n + 1)} {A : Ty}
    (ht : HasTypeD (Γ.cons h) t A) (hs : Γ.Sub Γ') (hΓ' : Γ'.AllNonLin) :
    HasTypeD (Γ'.cons h) t A := by
  obtain ⟨Δ, hΔ, hadd⟩ := hs.exists_add (fun x _ => hΓ' x)
  exact ht.weaken hΔ.cons_none (hadd.cons_none _)

/-- Weakening under two binders into a larger context whose additional assumptions are
non-linear. -/
theorem HasTypeD.mono_cons₂ {n : ℕ} {Γ Γ' : Ctx n} {h₁ h₂ : Option Hyp} {t : Term (n + 2)}
    {A : Ty} (ht : HasTypeD ((Γ.cons h₁).cons h₂) t A) (hs : Γ.Sub Γ') (hΓ' : Γ'.AllNonLin) :
    HasTypeD ((Γ'.cons h₁).cons h₂) t A := by
  obtain ⟨Δ, hΔ, hadd⟩ := hs.exists_add (fun x _ => hΓ' x)
  exact ht.weaken hΔ.cons_none.cons_none ((hadd.cons_none _).cons_none _)

end LCU
