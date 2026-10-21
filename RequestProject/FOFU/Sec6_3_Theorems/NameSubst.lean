module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD

/-!
# Substituting identifiers in typing derivations

`HasTypeD.substNames`: if `Γ ⊢ t : A` and `σ` substitutes identifiers for the bound
identifiers, then `σ(Γ) ⊢ t : σ(A)`.  Terms carry no types, so `t` is unchanged.

This is needed by the substitution lemmas (Lemmas 6.2 and 6.3) in the case of `unpack`,
whose body is typed in a context extended with a fresh identifier: the substituted term
must be moved into that context (`HasTypeD.shiftNames`).
-/

@[expose] public section

namespace FOFU

open Ty

variable {R : Type} [Grades.PreorderedSemiring R]

section
omit [Grades.PreorderedSemiring R]

variable {k k' k'' n : ℕ}

/-! ## Identifier substitution on contexts and predicates -/

lemma Assm.subst_subst (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') (a : Assm R k) :
    (a.subst σ).subst τ = a.subst (fun i => (σ i).subst τ) := by
  cases a <;> simp [Assm.subst, Ty.subst_subst]

lemma RefTy.subst_subst (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') (T : RefTy R k) :
    (T.subst σ).subst τ = T.subst (fun i => (σ i).subst τ) := by
  simp [RefTy.subst, Ty.subst_subst, Ident.subst_subst]

namespace Ctx

lemma substNames_substNames (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') (Γ : Ctx R k n) :
    (Γ.substNames σ).substNames τ = Γ.substNames (fun i => (σ i).subst τ) := by
  ext1
  · funext i; simp only [substNames, Option.map_map]
    congr 1; funext a; exact Assm.subst_subst σ τ a
  · funext a; simp only [substNames, Option.map_map]
    congr 1; funext T; exact RefTy.subst_subst σ τ T

lemma shiftNames_substNames_up (σ : Fin k → Ident k') (Γ : Ctx R k n) :
    Γ.shiftNames.substNames (ISubst.up σ) = (Γ.substNames σ).shiftNames := by
  simp only [shiftNames, substNames_substNames]
  rfl

lemma cons_substNames (σ : Fin k → Ident k') (Γ : Ctx R k n) (a : Option (Assm R k)) :
    (Γ.cons a).substNames σ = (Γ.substNames σ).cons (a.map (Assm.subst σ)) := by
  ext1
  · funext i; cases i using Fin.cases <;> rfl
  · rfl

lemma refsOnly_substNames (σ : Fin k → Ident k') (Γ : Ctx R k n) :
    Γ.refsOnly.substNames σ = (Γ.substNames σ).refsOnly := rfl

end Ctx

lemma Copyable.subst {A : Ty R k} (h : Copyable A) (σ : Fin k → Ident k') :
    Copyable (A.subst σ) := by
  induction h with
  | unit => exact .unit
  | float => exact .float
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂

lemma Cloneable.subst {A : Ty R k} (h : Cloneable A) (σ : Fin k → Ident k') :
    Cloneable (A.subst σ) := by
  induction h with
  | array ι => exact .array _
  | refCloneable ι _ ih => exact .refCloneable _ ih
  | refCopyable ι hc => exact .refCopyable _ (hc.subst σ)
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂

end

variable {k k' n : ℕ}

omit [Grades.PreorderedSemiring R] in
lemma PrimTy.subst {p : Prim} {A : Ty R k} (h : PrimTy p A) (σ : Fin k → Ident k') :
    PrimTy p (A.subst σ) := by
  cases h with
  | newArray => exact .newArray
  | readArray p ι => exact .readArray p _
  | writeArray p ι hp => exact .writeArray p _ hp
  | deleteArray ι => exact .deleteArray _
  | newRef A =>
    have := PrimTy.newRef (R := R) (A.subst σ)
    simpa [Ty.subst, Ty.shift_subst_up] using this
  | readRef p ι r A => exact .readRef p _ r _
  | readRefSplit ι q r A => exact .readRefSplit _ q r _
  | swapRef p ι A hp => exact .swapRef p _ _ hp
  | freezeRef ι A => exact .freezeRef _ _

lemma AssmAdd.substNames {a b c : Option (Assm R k)} (h : AssmAdd a b c)
    (σ : Fin k → Ident k') :
    AssmAdd (a.map (Assm.subst σ)) (b.map (Assm.subst σ)) (c.map (Assm.subst σ)) := by
  cases h with
  | noneLeft a => exact .noneLeft _
  | noneRight a => exact .noneRight _
  | grd A r s => exact .grd _ r s

omit [Grades.PreorderedSemiring R] in
lemma RefAdd.substNames {a b c : Option (RefTy R k)} (h : RefAdd a b c)
    (σ : Fin k → Ident k') :
    RefAdd (a.map (RefTy.subst σ)) (b.map (RefTy.subst σ)) (c.map (RefTy.subst σ)) := by
  cases h with
  | noneLeft a => exact .noneLeft _
  | noneRight a => exact .noneRight _
  | both T => exact .both _

lemma AssmScale.substNames {r : R} {a b : Option (Assm R k)} (h : AssmScale r a b)
    (σ : Fin k → Ident k') : AssmScale r (a.map (Assm.subst σ)) (b.map (Assm.subst σ)) := by
  cases h with
  | none => exact .none
  | grd A s => exact .grd _ s

lemma CtxAdd.substNames {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) (σ : Fin k → Ident k') :
    CtxAdd (Γ₁.substNames σ) (Γ₂.substNames σ) (Γ.substNames σ) :=
  ⟨fun i => (h.vars i).substNames σ, fun a => (h.refs a).substNames σ⟩

lemma CtxScale.substNames {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ')
    (σ : Fin k → Ident k') : CtxScale r (Γ.substNames σ) (Γ'.substNames σ) :=
  ⟨fun i => (h.vars i).substNames σ, by simp [Ctx.substNames, h.refs]⟩

lemma Ctx.IsZero.substNames {Γ : Ctx R k n} (h : Γ.IsZero) (σ : Fin k → Ident k') :
    (Γ.substNames σ).IsZero := by
  intro i
  have := h i
  simp only [Ctx.substNames]
  rcases e : Γ.vars i with _ | ⟨A | ⟨A, s⟩⟩ <;> rw [e] at this
  · trivial
  · exact this.elim
  · exact this

lemma zeroRest_substNames {Γ : Ctx R k n} {i : Fin n}
    (h : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) (σ : Fin k → Ident k') :
    ∀ j, j ≠ i → ZeroAssm ((Γ.substNames σ).vars j) := by
  intro j hj
  have := h j hj
  simp only [Ctx.substNames]
  rcases e : Γ.vars j with _ | ⟨A | ⟨A, s⟩⟩ <;> rw [e] at this
  · trivial
  · exact this.elim
  · exact this

/-! ## The lemma -/

theorem HasTypeD.substNames {Γ : Ctx R k n} {t : Term R n} {A : Ty R k}
    (h : HasTypeD Γ t A) : ∀ {k' : ℕ} (σ : Fin k → Ident k'),
      HasTypeD (Γ.substNames σ) t (A.subst σ) := by
  induction h with
  | var hi hz =>
    intro k' σ
    exact .var (by simp [Ctx.substNames, hi, Assm.subst]) (zeroRest_substNames hz σ)
  | varG hi hz =>
    intro k' σ
    exact .varG (by simp [Ctx.substNames, hi, Assm.subst]) (zeroRest_substNames hz σ)
  | abs _ ih =>
    intro k' σ
    have := ih σ
    rw [Ctx.cons_substNames] at this
    exact .abs this
  | app hadd _ _ ih₁ ih₂ => intro k' σ; exact .app (hadd.substNames σ) (ih₁ σ) (ih₂ σ)
  | pr hs _ hna ih => intro k' σ; exact .pr (hs.substNames σ) (ih σ) hna
  | elim hadd _ _ ih₁ ih₂ =>
    intro k' σ
    have := ih₂ σ
    rw [Ctx.cons_substNames] at this
    exact .elim (hadd.substNames σ) (ih₁ σ) this
  | @approx k n Γ t B i C r s hi hrs _ ih =>
    intro k' σ
    have := HasTypeD.approx (i := i) (A := C.subst σ) (r := r)
      (by simp [Ctx.substNames, hi, Assm.subst]) hrs (ih σ)
    rw [Ctx.substNames_update]
    exact this
  | tensorI hadd _ _ ih₁ ih₂ => intro k' σ; exact .tensorI (hadd.substNames σ) (ih₁ σ) (ih₂ σ)
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro k' σ
    have := ih₂ σ
    rw [Ctx.cons_substNames, Ctx.cons_substNames] at this
    exact .tensorE (hadd.substNames σ) (ih₁ σ) this
  | unitI hz => intro k' σ; exact .unitI (hz.substNames σ)
  | unitE hadd _ _ ih₁ ih₂ => intro k' σ; exact .unitE (hadd.substNames σ) (ih₁ σ) (ih₂ σ)
  | pack ι _ ih =>
    intro k' σ
    have := ih σ
    rw [Ty.inst_subst] at this
    exact .pack _ this
  | @unpack k n Γ₁ Γ₂ Γ t₁ t₂ A B hadd _ _ ih₁ ih₂ =>
    intro k' σ
    have := ih₂ (ISubst.up σ)
    rw [Ctx.cons_substNames, Ctx.shiftNames_substNames_up, Ty.shift_subst_up] at this
    exact .unpack (hadd.substNames σ) (ih₁ σ) this
  | share r _ ih => intro k' σ; exact .share r (ih σ)
  | @clone k n Γ₁ Γ₂ Γ t₁ t₂ C C' B r ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro k' σ
    have := ih₂ σ
    rw [Ctx.cons_substNames] at this
    refine .clone (ι.subst σ) (A' := C'.subst (ISubst.up σ)) (hadd.substNames σ) (ih₁ σ) hr
      (hc.subst σ) ?_ this
    rw [← Ty.inst_subst, hA]
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro k' σ; exact .withBorrow (hadd.substNames σ) (ih₁ σ) (ih₂ σ)
  | split _ ih => intro k' σ; exact .split (ih σ)
  | join hfg hadd _ _ ih₁ ih₂ => intro k' σ; exact .join hfg (hadd.substNames σ) (ih₁ σ) (ih₂ σ)
  | push _ ih => intro k' σ; exact .push (ih σ)
  | pull _ ih => intro k' σ; exact .pull (ih σ)
  | nat m hz => intro k' σ; exact .nat m (hz.substNames σ)
  | float x hz => intro k' σ; exact .float x (hz.substNames σ)
  | prim hz hp => intro k' σ; exact .prim (hz.substNames σ) (hp.subst σ)
  | nec p hz _ ih =>
    intro k' σ
    have := ih σ
    rw [Ctx.refsOnly_substNames] at this
    exact .nec p (hz.substNames σ) this
  | unborrow _ ih => intro k' σ; exact .unborrow (ih σ)
  | @ref k n Γ a T hz ha =>
    intro k' σ
    exact .ref (T := T.subst σ) (hz.substNames σ) (by simp [Ctx.substNames, ha])

/-- Moving a derivation into a context extended with a fresh identifier. -/
theorem HasTypeD.shiftNames {Γ : Ctx R k n} {t : Term R n} {A : Ty R k}
    (h : HasTypeD Γ t A) : HasTypeD Γ.shiftNames t A.shift :=
  h.substNames _

end FOFU
