module
public import RequestProject.LCU.Sec3_1_Calculus.Substitution

/-!
# Free variables and linear occurrence

`FreeIn i t` says that the de Bruijn variable `i` occurs free in `t`.  It is the generic
occurrence judgment `Binding.Tm.Occurs` of the binding layer.

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

open Term Binding

/-! ## Free variables and linear occurrence -/

/-- `FreeIn i t`: the variable `i` occurs free in `t`. -/
abbrev FreeIn {n ρ : ℕ} (i : Var n) (t : Term n ρ) : Prop := Tm.Occurs i t

lemma freeIn_rename {n m ρ : ℕ} (r : Var n → Var m) (t : Term n ρ) :
    ∀ j, FreeIn j (t.rename r) → ∃ i, r i = j := fun _ h =>
  let ⟨i, hi, _⟩ := Tm.Occurs.of_ren h; ⟨i, hi⟩

/-- Linear variables occur free in well-typed terms. -/
theorem HasTypeD.freeIn_of_lin {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {B : Ty}
    (ht : HasTypeD Γ t B) :
    ∀ {i : Var n} {A : Ty}, Γ.vars.get i = some (.lin A) → FreeIn i t := by
  induction ht with
  | var hi _ =>
    intro i A h
    obtain rfl := hi.eq_of_not (by rw [h]; exact not_nonLin_lin A)
    exact .var
  | abs _ ih => intro i A h; exact .op (.head (ih (i := .succ i) h))
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | unitE _ _ hadd ih₁ ih₂ =>
    intro i A h
    have := hadd.vars.get i; rw [h] at this
    rcases this.eq_lin with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact .op (.head (ih₁ h1))
    · exact .op (.tail (.head (ih₂ h2)))
  | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro i A h
    have := hadd.vars.get i; rw [h] at this
    rcases this.eq_lin with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact .op (.head (ih₁ h1))
    · exact .op (.tail (.head (ih₂ (i := .succ i) h2)))
  | tensorE _ _ hadd ih₁ ih₂ =>
    intro i A h
    have := hadd.vars.get i; rw [h] at this
    rcases this.eq_lin with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact .op (.head (ih₁ h1))
    · exact .op (.tail (.head (ih₂ (i := .succ (.succ i)) h2)))
  | unitI hΓ | bangI hΓ _ _ | natI hΓ | floatI hΓ | prim hΓ =>
    intro i A h; exact (not_lin_of_all hΓ.vars h).elim
  | borrow _ ih => intro i A h; exact .op (.head (ih h))
  | nec _ hΓ _ => intro i A h; exact (not_lin_of_all hΓ h).elim
  | ref _ hv => intro i A h; exact (not_lin_of_all hv h).elim

/-- Strengthening: removing an absent variable from a renamed term. -/
theorem HasTypeD.unrename {n m ρ : ℕ} {r : Var n → Var m} {i : Var m} {σ : Var m → Term n ρ}
    (hs : SubstSetup r i σ) {Δ : TCtx m ρ} {t : Term n ρ} {B : Ty}
    (ht : HasTypeD Δ (t.rename r) B) (hi : Δ.vars.get i = none) :
    HasTypeD (Δ.remove r) t B := by
  have := ht.subst_gen hs (Γ' := TCtx.empty) (by rw [hi]; exact TCtx.AllNonLin.empty)
    (TCtx.Add.empty_left _)
  rwa [subst_rename, show σ ∘ r = Term.var from funext hs.var, subst_var'] at this

end LCU
