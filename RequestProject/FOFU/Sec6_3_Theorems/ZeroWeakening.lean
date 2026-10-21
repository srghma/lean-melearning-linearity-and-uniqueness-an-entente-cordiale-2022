module
public import RequestProject.FOFU.Sec6_3_Theorems.Renaming

/-!
# Weakening by zero-graded assumptions

`HasTypeD.weakenZero`: if `Γ ⊢ t : A` and `Z` is a context of zero-graded (or absent)
assumptions, with arbitrary references, then `Z + Γ ⊢ t : A`.  This is the form of
weakening available in a graded calculus (an assumption `x : [B]_0` may be added).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R] {k n : ℕ}

omit [Grades.PreorderedSemiring R] in
lemma RefAdd.eq_of_right {a c : Option (RefTy R k)} {T : RefTy R k}
    (h : RefAdd a (some T) c) : c = some T := by
  cases h <;> rfl

theorem HasTypeD.weakenZero {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} (h : HasTypeD Γ t A) :
    ∀ {Z Γ' : Ctx R k n}, Z.IsZero → CtxAdd Z Γ Γ' → HasTypeD Γ' t A := by
  induction h with
  | var hi hz =>
    intro Z Γ' hZ hadd
    exact .var ((hadd.vars _).zero_lin (hZ _) hi)
      (fun j hj => (hZ j).add (hadd.vars j) (hz j hj))
  | varG hi hz =>
    intro Z Γ' hZ hadd
    exact .varG ((hadd.vars _).zero_grd (hZ _) hi)
      (fun j hj => (hZ j).add (hadd.vars j) (hz j hj))
  | abs _ ih =>
    intro Z Γ' hZ hadd
    exact .abs (ih (hZ.cons (a := none) trivial) (hadd.cons (.noneLeft _)))
  | app hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .app h2 (ih₁ hZ h1) ‹_›
  | tensorI hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .tensorI h2 (ih₁ hZ h1) ‹_›
  | unitE hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .unitE h2 (ih₁ hZ h1) ‹_›
  | withBorrow hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .withBorrow h2 (ih₁ hZ h1) ‹_›
  | join hfg hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .join hfg h2 (ih₁ hZ h1) ‹_›
  | elim hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .elim h2 (ih₁ hZ h1) ‹_›
  | tensorE hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .tensorE h2 (ih₁ hZ h1) ‹_›
  | unpack hadd₀ _ _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .unpack h2 (ih₁ hZ h1) ‹_›
  | clone ι hadd₀ _ hr hc hA _ ih₁ _ =>
    intro Z Γ' hZ hadd
    obtain ⟨X, h1, h2⟩ := hadd₀.assoc' hadd
    exact .clone ι h2 (ih₁ hZ h1) hr hc hA ‹_›
  | pr hs _ hna ih =>
    intro Z Γ' hZ hadd
    obtain ⟨C, h1, h2⟩ := (CtxScale.of_isZero hZ _).add_exists hs hadd
    exact .pr h2 (ih hZ h1) hna
  | approx hi hrs _ ih =>
    intro Z Γ' hZ hadd
    obtain ⟨C, h1, h2⟩ := (CtxLe.update hi hrs).add_exists' hadd
    exact (ih hZ h1).approxCtx h2
  | pack ι _ ih => intro Z Γ' hZ hadd; exact .pack ι (ih hZ hadd)
  | share r _ ih => intro Z Γ' hZ hadd; exact .share r (ih hZ hadd)
  | split _ ih => intro Z Γ' hZ hadd; exact .split (ih hZ hadd)
  | push _ ih => intro Z Γ' hZ hadd; exact .push (ih hZ hadd)
  | pull _ ih => intro Z Γ' hZ hadd; exact .pull (ih hZ hadd)
  | unborrow _ ih => intro Z Γ' hZ hadd; exact .unborrow (ih hZ hadd)
  | unitI hz => intro Z Γ' hZ hadd; exact .unitI (hZ.add hadd hz)
  | nat m hz => intro Z Γ' hZ hadd; exact .nat m (hZ.add hadd hz)
  | float x hz => intro Z Γ' hZ hadd; exact .float x (hZ.add hadd hz)
  | prim hz hp => intro Z Γ' hZ hadd; exact .prim (hZ.add hadd hz) hp
  | @ref k n Γ a T hz ha =>
    intro Z Γ' hZ hadd
    have := hadd.refs a
    rw [ha] at this
    exact .ref (hZ.add hadd hz) this.eq_of_right
  | nec p hz _ ih =>
    intro Z Γ' hZ hadd
    exact .nec p (hZ.add hadd hz) (ih (Ctx.IsZero.refsOnly Z) hadd.refsOnly)

end FOFU
