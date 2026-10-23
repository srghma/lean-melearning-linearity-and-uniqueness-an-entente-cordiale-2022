module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra.Add

/-!
# The algebra of contexts: scaling

Scalar multiplication of assumptions and contexts (`AssmScale`, `CtxScale`): it is
defined exactly on graded contexts (`TCtx.Graded`), composes, and distributes over
addition.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R] {k n ρ : ℕ}

/-! ## Scaling -/

/-- An optional assumption that is not linear (absent or graded). -/
inductive NotLin : Option (Assm R k) → Prop where
  | none : NotLin none
  | grd (A : Ty R k) (r : R) : NotLin (some (.grd A r))

/-- A context with no linear assumptions (the paper's `[Γ]`). -/
def TCtx.Graded (Γ : TCtx R k n ρ) : Prop := Γ.vars.All NotLin

namespace AssmScale

variable {r s q : R} {a b c d : Option (Assm R k)}

lemma one_eq (h : AssmScale 1 a b) : b = a := by
  cases h with
  | none => rfl
  | grd A s => rw [one_mul]

lemma comp (h₁ : AssmScale q a b) (h₂ : AssmScale r b c) : AssmScale (r * q) a c := by
  cases h₁ with
  | none => cases h₂; exact .none
  | grd A s => cases h₂; rw [← mul_assoc]; exact .grd A s

lemma add_scale (h₁ : AssmScale r a b) (h₂ : AssmScale s a c) (h₃ : AssmScale (r + s) a d) :
    AssmAdd b c d := by
  cases h₁ with
  | none => cases h₂; cases h₃; exact .noneLeft _
  | grd A q => cases h₂; cases h₃; rw [add_mul]; exact .grd A _ _

lemma add_exists {a' b' c' : Option (Assm R k)} (h₁ : AssmScale r a a') (h₂ : AssmScale r b b')
    (h₃ : AssmAdd a' b' c') : ∃ c, AssmAdd a b c ∧ AssmScale r c c' := by
  cases h₁ with
  | none =>
    cases h₂ with
    | none => cases h₃; exact ⟨_, .noneLeft _, .none⟩
    | grd T q => cases h₃; exact ⟨_, .noneLeft _, .grd T q⟩
  | grd T p =>
    cases h₂ with
    | none => cases h₃; exact ⟨_, .noneRight _, .grd T p⟩
    | grd T' q =>
      cases h₃ with
      | grd _ _ _ => exact ⟨_, .grd T p q, by rw [← mul_add]; exact .grd T _⟩

lemma zero (h : ZeroAssm a) (r : R) : AssmScale r a a := by
  cases h with
  | none => exact .none
  | grd A =>
    have h := AssmScale.grd (r := r) A 0
    rwa [mul_zero] at h

lemma isZero (h : AssmScale r a b) (ha : ZeroAssm a) : ZeroAssm b := by
  cases h with
  | none => exact .none
  | grd A s => cases ha; simp

lemma isZero_zero (h : AssmScale 0 a b) : ZeroAssm b := by
  cases h with
  | none => exact .none
  | grd A s => simp

lemma not_lin_left {A : Ty R k} (h : AssmScale r (some (.lin A)) b) : False := by cases h

lemma not_lin_right {A : Ty R k} (h : AssmScale r a (some (.lin A))) : False := by cases h

lemma notLin_left (h : AssmScale r a b) : NotLin a := by
  cases h <;> constructor

lemma notLin_right (h : AssmScale r a b) : NotLin b := by
  cases h <;> constructor

lemma exists_of_notLin (h : NotLin a) (r : R) : ∃ b, AssmScale r a b := by
  cases h with
  | none => exact ⟨_, .none⟩
  | grd A s => exact ⟨_, .grd A s⟩

lemma unique (h₁ : AssmScale r a b) (h₂ : AssmScale r a c) : b = c := by
  cases h₁ <;> cases h₂ <;> rfl

end AssmScale

namespace CtxScale

open Ctx

lemma exists_of_graded {Γ : TCtx R k n ρ} (h : Γ.Graded) (r : R) : ∃ Γ', CtxScale r Γ Γ' := by
  obtain ⟨v, hv⟩ := Ctx.exists_of_forall fun i => AssmScale.exists_of_notLin (h.get i) r
  exact ⟨⟨Γ.refs, v⟩, rfl, forall₂_iff.2 hv⟩

lemma graded {r : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale r Γ Γ') : Γ.Graded :=
  all_iff.2 fun i => (h.vars.get i).notLin_left

lemma graded' {r : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale r Γ Γ') : Γ'.Graded :=
  all_iff.2 fun i => (h.vars.get i).notLin_right

lemma one_eq {Γ Γ' : TCtx R k n ρ} (h : CtxScale 1 Γ Γ') : Γ' = Γ :=
  TCtx.ext h.refs (Ctx.ext fun i => (h.vars.get i).one_eq)

lemma unique {r : R} {Γ Γ₁ Γ₂ : TCtx R k n ρ} (h₁ : CtxScale r Γ Γ₁) (h₂ : CtxScale r Γ Γ₂) :
    Γ₁ = Γ₂ :=
  TCtx.ext (h₁.refs.trans h₂.refs.symm) (Ctx.ext fun i => (h₁.vars.get i).unique (h₂.vars.get i))

lemma comp {q r : R} {Γ Γq Γrq : TCtx R k n ρ} (h₁ : CtxScale q Γ Γq) (h₂ : CtxScale r Γq Γrq) :
    CtxScale (r * q) Γ Γrq :=
  ⟨h₂.refs.trans h₁.refs, forall₂_iff.2 fun i => (h₁.vars.get i).comp (h₂.vars.get i)⟩

/-- `r · Γ + s · Γ = (r + s) · Γ`. -/
lemma add_scale {r s : R} {Γ Γr Γs Γrs : TCtx R k n ρ} (hr : CtxScale r Γ Γr)
    (hs : CtxScale s Γ Γs) (hrs : CtxScale (r + s) Γ Γrs) : CtxAdd Γr Γs Γrs := by
  refine ⟨?_, forall₃_iff.2 fun i => (hr.vars.get i).add_scale (hs.vars.get i) (hrs.vars.get i)⟩
  rw [hr.refs, hs.refs, hrs.refs]
  exact forall₃_iff.2 fun _ => RefAdd.idem _

/-- Distributivity, `r · A + r · B = r · (A + B)`, in the form needed for inversion. -/
lemma add_exists {r : R} {A A' B B' C' : TCtx R k n ρ} (hA : CtxScale r A A')
    (hB : CtxScale r B B') (hC : CtxAdd A' B' C') : ∃ C, CtxAdd A B C ∧ CtxScale r C C' := by
  obtain ⟨v, hv⟩ := Ctx.exists_of_forall fun i =>
    (hA.vars.get i).add_exists (hB.vars.get i) (hC.vars.get i)
  refine ⟨⟨C'.refs, v⟩, ⟨?_, forall₃_iff.2 fun i => (hv i).1⟩, rfl, forall₂_iff.2 fun i => (hv i).2⟩
  have := hC.refs
  rwa [hA.refs, hB.refs] at this

/-- A zero context is unchanged by scaling. -/
lemma of_isZero {Z : TCtx R k n ρ} (hZ : Z.IsZero) (r : R) : CtxScale r Z Z :=
  ⟨rfl, forall₂_iff.2 fun i => AssmScale.zero (hZ.get i) r⟩

lemma isZero {r : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale r Γ Γ') (hΓ : Γ.IsZero) : Γ'.IsZero :=
  all_iff.2 fun i => (h.vars.get i).isZero (hΓ.get i)

lemma isZero_zero {Γ Γ' : TCtx R k n ρ} (h : CtxScale 0 Γ Γ') : Γ'.IsZero :=
  all_iff.2 fun i => (h.vars.get i).isZero_zero

lemma refsOnly {r : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale r Γ Γ') :
    CtxScale r Γ.refsOnly Γ'.refsOnly :=
  ⟨h.refs, forall₂_iff.2 fun i => by simpa using AssmScale.none⟩

lemma cons {r : R} {Γ Γ' : TCtx R k n ρ} (h : CtxScale r Γ Γ') {a b : Option (Assm R k)}
    (hab : AssmScale r a b) : CtxScale r (Γ.cons a) (Γ'.cons b) :=
  ⟨h.refs, .snoc h.vars hab⟩

end CtxScale

end FOFU
