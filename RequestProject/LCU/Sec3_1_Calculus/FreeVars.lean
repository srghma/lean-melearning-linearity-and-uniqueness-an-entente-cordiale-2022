module
public import RequestProject.LCU.Sec3_1_Calculus.Substitution

/-!
# Free variables and linear occurrence

`FreeIn i t` says that the de Bruijn variable `i` occurs free in `t`.

## Main results

* `freeIn_rename`: how free occurrence interacts with renaming.
* `HasTypeD.freeIn_of_lin`: a variable that is *linear* in the context must occur
  free in a well-typed term (linear assumptions cannot be weakened away).
* `HasTypeD.unrename` (strengthening): a variable that is absent from the context can
  be removed from a term that is a renaming.

These facts are used for the typability of the `η⊸` and `assoc` axioms of the
equational theory, and for the ill-typedness results of Section 2
(`not_hasType_lam_pair_dup`).
-/

@[expose] public section

namespace LCU

open Term

/-! ## Free variables and linear occurrence -/

/-- `FreeIn i t`: the variable `i` occurs free in `t`. -/
def FreeIn : {n : ℕ} → Fin n → Term n → Prop
  | _, i, .var j => i = j
  | _, i, .lam t => FreeIn i.succ t
  | _, i, .app t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .pair t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .letPair t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ.succ t₂
  | _, _, .unit => False
  | _, i, .letUnit t₁ t₂ => FreeIn i t₁ ∨ FreeIn i t₂
  | _, i, .bang t => FreeIn i t
  | _, i, .letBang t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ t₂
  | _, i, .borrow t => FreeIn i t
  | _, i, .copy t₁ t₂ => FreeIn i t₁ ∨ FreeIn i.succ t₂
  | _, i, .star t => FreeIn i t
  | _, _, .nat _ => False
  | _, _, .float _ => False
  | _, _, .prim _ => False
  | _, _, .ref _ => False

-- `Ren.exists_of_up` is shared with the FOFU formalisation (`RequestProject/Common/DeBruijn.lean`).
open DeBruijn (Ren.exists_of_up)

lemma freeIn_rename {n m : ℕ} (ρ : Fin n → Fin m) (t : Term n) :
    ∀ j, FreeIn j (t.rename ρ) → ∃ i, ρ i = j := by
  induction t generalizing m with
  | var i => intro j h; exact ⟨i, (h : j = ρ i).symm⟩
  | lam _ ih => intro j h; exact Ren.exists_of_up (ih _ _ h)
  | bang _ ih | borrow _ ih | star _ ih => intro j h; exact ih _ _ h
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | letPair _ _ ih₁ ih₂ | letUnit _ _ ih₁ ih₂
  | letBang _ _ ih₁ ih₂ | copy _ _ ih₁ ih₂ =>
    intro j h
    rcases h with h | h
    · exact ih₁ _ _ h
    · first
        | exact ih₂ _ _ h
        | exact Ren.exists_of_up (ih₂ _ _ h)
        | exact Ren.exists_of_up (Ren.exists_of_up (ih₂ _ _ h))
  | _ => intro j h; exact h.elim

/-- Linear variables occur free in well-typed terms. -/
theorem HasTypeD.freeIn_of_lin {n : ℕ} {Γ : Ctx n} {t : Term n} {B : Ty}
    (ht : HasTypeD Γ t B) : ∀ {i : Fin n} {A : Ty}, Γ (.inl i) = some (.lin A) → FreeIn i t := by
  induction ht with
  | var hi hrest =>
    intro i A h
    simpa using Ctx.AllNonLin.set_not_lin hrest h
  | abs _ ih => intro i A h; exact ih (i := i.succ) h
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro i A h
    have := hadd (.inl i); rw [h] at this
    rcases this.eq_lin with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro i A h; exact (hΓ.not_lin h).elim
  | borrow _ ih => intro i A h; exact ih h
  | nec _ hΓ _ => intro i A h; have := hΓ i; rw [h] at this; exact this.elim
  | ref _ hrest =>
    intro i A h
    have := Ctx.AllNonLin.set_not_lin hrest h
    simp at this

/-- Strengthening: removing an absent variable from a renamed term. -/
theorem HasTypeD.unrename {n m : ℕ} {ρ : Fin n → Fin m} {i : Fin m} {σ : Fin m → Term n}
    (hs : SubstSetup ρ i σ) {Δ : Ctx m} {t : Term n} {B : Ty}
    (ht : HasTypeD Δ (t.rename ρ) B) (hi : Δ (.inl i) = none) :
    HasTypeD (Δ.remove ρ) t B := by
  have := ht.subst_gen hs (Γ' := Ctx.empty) (by rw [hi]; exact Ctx.AllNonLin.empty)
    (Ctx.Add.empty_left _)
  rwa [subst_rename, show σ ∘ ρ = Term.var from funext hs.var, subst_var] at this

end LCU
