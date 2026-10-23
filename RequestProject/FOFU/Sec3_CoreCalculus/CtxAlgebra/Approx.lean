module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra.Scale

/-!
# The algebra of contexts: approximating grades

The pointwise order `CtxLe Γ Γ'` (`Γ'` is `Γ` with some grades approximated upwards) and
its compatibility with addition and scaling.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R] {k n ρ : ℕ}

/-! ## Approximating grades -/

/-- `AssmLe a b`: `b` is `a`, possibly with its grade approximated upwards. -/
inductive AssmLe : Option (Assm R k) → Option (Assm R k) → Prop where
  | refl (a : Option (Assm R k)) : AssmLe a a
  | grd (A : Ty R k) {r s : R} : r ≤ s → AssmLe (some (.grd A r)) (some (.grd A s))

/-- `CtxLe Γ Γ'`: `Γ'` is `Γ` with some grades approximated upwards. -/
structure CtxLe (Γ Γ' : TCtx R k n ρ) : Prop where
  refs : Γ'.refs = Γ.refs
  vars : Ctx.Forall₂ AssmLe Γ.vars Γ'.vars

namespace AssmLe

lemma add_exists {a a' b c' : Option (Assm R k)} (h₁ : AssmLe a a') (h₂ : AssmAdd a' b c') :
    ∃ c, AssmAdd a b c ∧ AssmLe c c' := by
  cases h₁ with
  | refl a => exact ⟨_, h₂, .refl _⟩
  | grd T hrs =>
    cases h₂ with
    | noneRight _ => exact ⟨_, .noneRight _, .grd T hrs⟩
    | grd _ _ q => exact ⟨_, .grd T _ q, .grd T (add_le_add_left hrs _)⟩

lemma of_scale {r s : R} {a b c : Option (Assm R k)} (h₁ : AssmScale r a b)
    (h₂ : AssmScale s a c) (h : r ≤ s) : AssmLe b c := by
  cases h₁ with
  | none => cases h₂; exact .refl _
  | grd A q => cases h₂; exact .grd A (mul_le_mul_left h _)

end AssmLe

namespace CtxLe

open Ctx

lemma refl (Γ : TCtx R k n ρ) : CtxLe Γ Γ := ⟨rfl, forall₂_iff.2 fun _ => .refl _⟩

/-- If `A ≤ A'` and `A' + B` is defined, so is `A + B`, and it is below `A' + B`. -/
lemma add_exists {A A' B C' : TCtx R k n ρ} (hA : CtxLe A A') (hC : CtxAdd A' B C') :
    ∃ C, CtxAdd A B C ∧ CtxLe C C' := by
  obtain ⟨v, hv⟩ := Ctx.exists_of_forall fun i => (hA.vars.get i).add_exists (hC.vars.get i)
  refine ⟨⟨C'.refs, v⟩, ⟨?_, forall₃_iff.2 fun i => (hv i).1⟩, rfl, forall₂_iff.2 fun i => (hv i).2⟩
  have := hC.refs
  rwa [hA.refs] at this

/-- If `B ≤ B'` and `A + B'` is defined, so is `A + B`, and it is below `A + B'`. -/
lemma add_exists' {A B B' C' : TCtx R k n ρ} (hB : CtxLe B B') (hC : CtxAdd A B' C') :
    ∃ C, CtxAdd A B C ∧ CtxLe C C' := by
  obtain ⟨C, h1, h2⟩ := add_exists hB hC.comm
  exact ⟨C, h1.comm, h2⟩

/-- `r ≤ s` implies `r · Γ ≤ s · Γ`. -/
lemma of_scale {r s : R} {Γ Γr Γs : TCtx R k n ρ} (hr : CtxScale r Γ Γr) (hs : CtxScale s Γ Γs)
    (h : r ≤ s) : CtxLe Γr Γs :=
  ⟨by rw [hr.refs, hs.refs], forall₂_iff.2 fun i => AssmLe.of_scale (hr.vars.get i) (hs.vars.get i) h⟩

/-- Approximating one graded assumption. -/
lemma setVar {Γ : TCtx R k n ρ} {i : Var n} {A : Ty R k} {r s : R}
    (hi : Γ.vars.get i = some (.grd A r)) (h : r ≤ s) :
    CtxLe Γ (Γ.setVar i (some (.grd A s))) := by
  refine ⟨rfl, forall₂_iff.2 fun j => ?_⟩
  simp only [TCtx.setVar_vars, Ctx.get_set]
  split_ifs with hj
  · subst hj; rw [hi]; exact .grd A h
  · exact .refl _

end CtxLe

end FOFU
