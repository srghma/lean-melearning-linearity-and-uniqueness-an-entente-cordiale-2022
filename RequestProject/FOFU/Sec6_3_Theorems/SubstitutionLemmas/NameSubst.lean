module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingD

/-!
# Renaming identifiers in typing derivations

`HasTypeD.renNames`: if `Γ ⊢ t : A` and `r` renames the identifiers in scope, then
`r(Γ) ⊢ t : r(A)`.  Terms carry no types, so `t` is unchanged.  Since identifiers can only
be replaced by identifiers, renaming covers identifier substitution.

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

variable {k k' k'' n ρ : ℕ}

/-! ## Identifier renaming on contexts -/

namespace TCtx

lemma renNames_renNames (r : Var k → Var k') (r' : Var k' → Var k'') (Γ : TCtx R k n ρ) :
    (Γ.renNames r).renNames r' = Γ.renNames (r' ∘ r) := by
  refine TCtx.ext ?_ ?_
  · simp only [renNames_refs, Ctx.map_map]
    congr 1; funext a; cases a <;> simp [RefTy.ren_ren]
  · simp only [renNames_vars, Ctx.map_map]
    congr 1; funext a; cases a <;> simp [Assm.ren_ren]

lemma shiftNames_renNames_up (r : Var k → Var k') (Γ : TCtx R k n ρ) :
    Γ.shiftNames.renNames (Ren.up r) = (Γ.renNames r).shiftNames := by
  simp only [shiftNames, renNames_renNames]
  rfl

@[simp] lemma cons_renNames (r : Var k → Var k') (Γ : TCtx R k n ρ) (a : Option (Assm R k)) :
    (Γ.cons a).renNames r = (Γ.renNames r).cons (a.map (Assm.ren r)) := rfl

@[simp] lemma refsOnly_renNames (r : Var k → Var k') (Γ : TCtx R k n ρ) :
    Γ.refsOnly.renNames r = (Γ.renNames r).refsOnly :=
  TCtx.ext rfl (by simp)

end TCtx

lemma PrimTy.ren {p : Prim} {A : Ty R k} (h : PrimTy p A) (r : Var k → Var k') :
    PrimTy p (A.ren r) := by
  cases h with
  | newArray => exact .newArray
  | readArray p ι => exact .readArray p _
  | writeArray p ι hp => exact .writeArray p _ hp
  | deleteArray ι => exact .deleteArray _
  | newRef A =>
    have := PrimTy.newRef (R := R) (A.ren r)
    simpa [Ty.ren, Ty.shift_ren_up] using this
  | readRef p ι q A => exact .readRef p _ q _
  | readRefSplit ι q q' A => exact .readRefSplit _ q q' _
  | swapRef p ι A hp => exact .swapRef p _ _ hp
  | freezeRef ι A => exact .freezeRef _ _

lemma RefAdd.renNames {a b c : Option (RefTy R k)} (h : RefAdd a b c) (r : Var k → Var k') :
    RefAdd (a.map (RefTy.ren r)) (b.map (RefTy.ren r)) (c.map (RefTy.ren r)) := by
  cases h with
  | noneLeft a => exact .noneLeft _
  | noneRight a => exact .noneRight _
  | both T => exact .both _

end

variable {k k' n ρ : ℕ}

lemma AssmAdd.renNames {a b c : Option (Assm R k)} (h : AssmAdd a b c) (r : Var k → Var k') :
    AssmAdd (a.map (Assm.ren r)) (b.map (Assm.ren r)) (c.map (Assm.ren r)) := by
  cases h with
  | noneLeft a => exact .noneLeft _
  | noneRight a => exact .noneRight _
  | grd A q s => exact .grd _ q s

lemma AssmScale.renNames {q : R} {a b : Option (Assm R k)} (h : AssmScale q a b)
    (r : Var k → Var k') : AssmScale q (a.map (Assm.ren r)) (b.map (Assm.ren r)) := by
  cases h with
  | none => exact .none
  | grd A s => exact .grd _ s

lemma ZeroAssm.renNames {a : Option (Assm R k)} (h : ZeroAssm a) (r : Var k → Var k') :
    ZeroAssm (a.map (Assm.ren r)) := by
  cases h with
  | none => exact .none
  | grd A => exact .grd _

lemma CtxAdd.renNames {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) (r : Var k → Var k') :
    CtxAdd (Γ₁.renNames r) (Γ₂.renNames r) (Γ.renNames r) :=
  ⟨h.refs.map _ _ _ fun _ _ _ habc => habc.renNames r,
    h.vars.map _ _ _ fun _ _ _ habc => habc.renNames r⟩

lemma CtxScale.renNames {q : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale q Γ Γ')
    (r : Var k → Var k') : CtxScale q (Γ.renNames r) (Γ'.renNames r) :=
  ⟨by simp [h.refs], h.vars.map _ _ fun _ _ hab => hab.renNames r⟩

lemma TCtx.IsZero.renNames {Γ : TCtx R k n ρ} (h : Γ.IsZero) (r : Var k → Var k') :
    (Γ.renNames r).IsZero := h.map _ fun _ ha => ha.renNames r

lemma _root_.Ctx.Pick.renNames {Γ : Ctx (Option (Assm R k)) n} {i : Var n} {a : Assm R k}
    (h : Γ.Pick ZeroAssm i (some a)) (r : Var k → Var k') :
    (Γ.map (Option.map (Assm.ren r))).Pick ZeroAssm i (some (a.ren r)) :=
  h.map (Option.map (Assm.ren r)) fun _ ha => ha.renNames r

/-! ## The lemma -/

theorem HasTypeD.renNames {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k}
    (h : HasTypeD Γ t A) : ∀ {k' : ℕ} (r : Var k → Var k'),
      HasTypeD (Γ.renNames r) t (A.ren r) := by
  induction h with
  | var hi => intro k' r; exact .var (hi.renNames r)
  | varG hi => intro k' r; exact .varG (hi.renNames r)
  | abs _ ih => intro k' r; exact .abs (ih r)
  | app hadd _ _ ih₁ ih₂ => intro k' r; exact .app (hadd.renNames r) (ih₁ r) (ih₂ r)
  | pr hs _ hna ih => intro k' r; exact .pr (hs.renNames r) (ih r) hna
  | elim hadd _ _ ih₁ ih₂ => intro k' r; exact .elim (hadd.renNames r) (ih₁ r) (ih₂ r)
  | @approx k n ρ Γ t B i C q s hi hrs _ ih =>
    intro k' r
    have := HasTypeD.approx (i := i) (A := C.ren r) (r := q)
      (hi.map (Option.map (Assm.ren r))) hrs (ih r)
    rw [TCtx.renNames_setVar]
    exact this
  | tensorI hadd _ _ ih₁ ih₂ => intro k' r; exact .tensorI (hadd.renNames r) (ih₁ r) (ih₂ r)
  | tensorE hadd _ _ ih₁ ih₂ => intro k' r; exact .tensorE (hadd.renNames r) (ih₁ r) (ih₂ r)
  | unitI hz => intro k' r; exact .unitI (hz.renNames r)
  | unitE hadd _ _ ih₁ ih₂ => intro k' r; exact .unitE (hadd.renNames r) (ih₁ r) (ih₂ r)
  | pack ι _ ih =>
    intro k' r
    have := ih r
    rw [Ty.inst_ren] at this
    exact .pack _ this
  | @unpack k n ρ Γ₁ Γ₂ Γ t₁ t₂ A B hadd _ _ ih₁ ih₂ =>
    intro k' r
    have := ih₂ (Ren.up r)
    rw [TCtx.cons_renNames, TCtx.shiftNames_renNames_up, Ty.shift_ren_up] at this
    exact .unpack (hadd.renNames r) (ih₁ r) this
  | share q _ ih => intro k' r; exact .share q (ih r)
  | @clone k n ρ Γ₁ Γ₂ Γ t₁ t₂ C C' B q ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro k' r
    refine .clone (r ι) (A' := C'.ren (Ren.up r)) (hadd.renNames r) (ih₁ r) hr
      (by rw [Ty.cloneable_ren]; exact hc) ?_ (ih₂ r)
    rw [← Ty.inst_ren, hA]
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro k' r; exact .withBorrow (hadd.renNames r) (ih₁ r) (ih₂ r)
  | split _ ih => intro k' r; exact .split (ih r)
  | join hfg hadd _ _ ih₁ ih₂ => intro k' r; exact .join hfg (hadd.renNames r) (ih₁ r) (ih₂ r)
  | push _ ih => intro k' r; exact .push (ih r)
  | pull _ ih => intro k' r; exact .pull (ih r)
  | nat m hz => intro k' r; exact .nat m (hz.renNames r)
  | float x hz => intro k' r; exact .float x (hz.renNames r)
  | prim hz hp => intro k' r; exact .prim (hz.renNames r) (hp.ren r)
  | nec p hz _ ih =>
    intro k' r
    have := ih r
    rw [TCtx.refsOnly_renNames] at this
    exact .nec p (hz.renNames r) this
  | unborrow _ ih => intro k' r; exact .unborrow (ih r)
  | @ref k n ρ Γ a T hz ha =>
    intro k' r
    exact .ref (T := T.ren r) (hz.renNames r) (ha.map (Option.map (RefTy.ren r)))

/-- Moving a derivation into a context extended with a fresh identifier. -/
theorem HasTypeD.shiftNames {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k}
    (h : HasTypeD Γ t A) : HasTypeD Γ.shiftNames t A.shift :=
  h.renNames _

end FOFU
