module
public import RequestProject.FOFU.Sec3_CoreCalculus.Context
public import Mathlib.Order.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# The algebra of contexts

Properties of the partial operations on contexts of `Context.lean`, used by the
substitution lemmas (Lemmas 6.2 and 6.3):

* context addition is commutative and associative (as relations): `CtxAdd.comm`,
  `CtxAdd.assoc`, and the interchange law `CtxAdd.interchange`;
* scalar multiplication distributes over addition: `CtxScale.add_scale`,
  `CtxScale.add_exists`, and composes: `CtxScale.comp`, `CtxScale.one_eq`;
* the pointwise order on grades `CtxLe Γ Γ'` (`Γ'` is `Γ` with some grades approximated
  upwards), which is compatible with addition and scaling.

Since grades form an arbitrary (not necessarily commutative) pre-ordered semiring, the
grade of a sum is `r + s` and scaling multiplies on the left, `r · (x : [A]_s) =
x : [A]_(r * s)`.

(The analogous development for *Linearity and Uniqueness* is
`RequestProject/LCU/Sec3_1_Calculus/CtxAlgebra.lean`; the statements here are
generalised to grades and so are proved separately.)
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R] {k n ρ : ℕ}

/-! ## Addition of assumptions -/

namespace AssmAdd

lemma comm {a b c : Option (Assm R k)} (h : AssmAdd a b c) : AssmAdd b a c := by
  cases h with
  | noneLeft => cases ‹Option (Assm R k)› <;> first | exact .noneLeft _ | exact .noneRight _
  | noneRight a => exact .noneLeft _
  | grd A r s => rw [add_comm]; exact .grd A s r

lemma assoc {a b ab c abc : Option (Assm R k)} (h₁ : AssmAdd a b ab) (h₂ : AssmAdd ab c abc) :
    ∃ bc, AssmAdd b c bc ∧ AssmAdd a bc abc := by
  cases h₁ with
  | noneLeft b => exact ⟨abc, h₂, .noneLeft _⟩
  | noneRight a => exact ⟨c, .noneLeft _, h₂⟩
  | grd A r s =>
    cases h₂ with
    | noneRight _ => exact ⟨_, .noneRight _, .grd A r s⟩
    | grd _ _ t => exact ⟨_, .grd A s t, by rw [add_assoc]; exact .grd A r (s + t)⟩

lemma none_left_eq {b c : Option (Assm R k)} (h : AssmAdd none b c) : c = b := by
  cases h; rfl

lemma none_right_eq {a c : Option (Assm R k)} (h : AssmAdd a none c) : c = a := by
  cases h <;> rfl

lemma eq_none {a b : Option (Assm R k)} (h : AssmAdd a b none) : a = none ∧ b = none := by
  cases h; exact ⟨rfl, rfl⟩

end AssmAdd

namespace RefAdd

omit [Grades.PreorderedSemiring R] in
lemma comm {a b c : Option (RefTy R k)} (h : RefAdd a b c) : RefAdd b a c := by
  cases h with
  | noneLeft => cases ‹Option (RefTy R k)› <;> first | exact .noneLeft _ | exact .noneRight _
  | noneRight a => exact .noneLeft _
  | both T => exact .both T

omit [Grades.PreorderedSemiring R] in
lemma assoc {a b ab c abc : Option (RefTy R k)} (h₁ : RefAdd a b ab) (h₂ : RefAdd ab c abc) :
    ∃ bc, RefAdd b c bc ∧ RefAdd a bc abc := by
  cases h₁ with
  | noneLeft b => exact ⟨abc, h₂, .noneLeft _⟩
  | noneRight a => exact ⟨c, .noneLeft _, h₂⟩
  | both T =>
    cases h₂ with
    | noneRight _ => exact ⟨_, .noneRight _, .both T⟩
    | both _ => exact ⟨_, .both T, .both T⟩

omit [Grades.PreorderedSemiring R] in
/-- Reference assumptions are idempotent. -/
lemma idem (a : Option (RefTy R k)) : RefAdd a a a := by
  cases a <;> first | exact .noneLeft _ | exact .both _

end RefAdd

/-! ## Addition of contexts -/

namespace CtxAdd

open Ctx

lemma comm {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) : CtxAdd Γ₂ Γ₁ Γ :=
  ⟨h.refs.swap RefAdd.comm, h.vars.swap AssmAdd.comm⟩

lemma assoc {A B AB C ABC : TCtx R k n ρ} (h₁ : CtxAdd A B AB) (h₂ : CtxAdd AB C ABC) :
    ∃ BC, CtxAdd B C BC ∧ CtxAdd A BC ABC := by
  obtain ⟨r, hr₁, hr₂⟩ := h₁.refs.assoc h₂.refs RefAdd.assoc
  obtain ⟨v, hv₁, hv₂⟩ := h₁.vars.assoc h₂.vars AssmAdd.assoc
  exact ⟨⟨r, v⟩, ⟨hr₁, hv₁⟩, ⟨hr₂, hv₂⟩⟩

/-- Associativity, in the other direction. -/
lemma assoc' {A B BC C ABC : TCtx R k n ρ} (h₁ : CtxAdd B C BC) (h₂ : CtxAdd A BC ABC) :
    ∃ AB, CtxAdd A B AB ∧ CtxAdd AB C ABC := by
  obtain ⟨X, h3, h4⟩ := assoc h₁.comm h₂.comm
  exact ⟨X, h3.comm, h4.comm⟩

/-- The interchange law `(A₁ + A₂) + (B₁ + B₂) = (A₁ + B₁) + (A₂ + B₂)`. -/
lemma interchange {A₁ A₂ A B₁ B₂ B C : TCtx R k n ρ} (hA : CtxAdd A₁ A₂ A) (hB : CtxAdd B₁ B₂ B)
    (hC : CtxAdd A B C) :
    ∃ C₁ C₂, CtxAdd A₁ B₁ C₁ ∧ CtxAdd A₂ B₂ C₂ ∧ CtxAdd C₁ C₂ C := by
  obtain ⟨X, hX1, hX2⟩ := assoc hA hC
  obtain ⟨Y, hY1, hY2⟩ := assoc hB hX1.comm
  obtain ⟨C₁, hC1, hC2⟩ := assoc' hY2 hX2
  exact ⟨C₁, Y, hC1, hY1.comm, hC2⟩

/-- `Γ` is the sum of its runtime part `γ` and itself. -/
lemma refsOnly_left (Γ : TCtx R k n ρ) : CtxAdd Γ.refsOnly Γ Γ :=
  ⟨forall₃_iff.2 fun _ => RefAdd.idem _, Forall₃.replicate_left (fun _ => .noneLeft _) _⟩

lemma refsOnly_right (Γ : TCtx R k n ρ) : CtxAdd Γ Γ.refsOnly Γ := (refsOnly_left Γ).comm

lemma refsOnly {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) :
    CtxAdd Γ₁.refsOnly Γ₂.refsOnly Γ.refsOnly :=
  ⟨h.refs, Forall₃.replicate_left (fun _ => .noneLeft _) _⟩

/-- Extending both summands and the sum by new variables. -/
lemma cons {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) {a b c : Option (Assm R k)}
    (habc : AssmAdd a b c) : CtxAdd (Γ₁.cons a) (Γ₂.cons b) (Γ.cons c) :=
  ⟨h.refs, .snoc h.vars habc⟩

/-- Updating one variable in the summands and the sum. -/
lemma setVar {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) (i : Var n) {a b c : Option (Assm R k)}
    (habc : AssmAdd a b c) : CtxAdd (Γ₁.setVar i a) (Γ₂.setVar i b) (Γ.setVar i c) :=
  ⟨h.refs, h.vars.set i habc⟩

end CtxAdd

/-! ## Zero contexts -/

lemma ZeroAssm.add {a b c : Option (Assm R k)} (h : AssmAdd a b c) (ha : ZeroAssm a)
    (hb : ZeroAssm b) : ZeroAssm c := by
  cases h with
  | noneLeft _ => exact hb
  | noneRight _ => exact ha
  | grd A r s => cases ha; cases hb; simp

lemma TCtx.IsZero.add {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) (h₁ : Γ₁.IsZero)
    (h₂ : Γ₂.IsZero) : Γ.IsZero := h.vars.all (fun habc ha hb => ZeroAssm.add habc ha hb) h₁ h₂

lemma TCtx.IsZero.empty : (TCtx.empty : TCtx R k n ρ).IsZero := Ctx.all_replicate .none n

lemma TCtx.IsZero.refsOnly (Γ : TCtx R k n ρ) : Γ.refsOnly.IsZero := Ctx.all_replicate .none n

lemma TCtx.IsZero.cons {Γ : TCtx R k n ρ} (h : Γ.IsZero) {a : Option (Assm R k)}
    (ha : ZeroAssm a) : (Γ.cons a).IsZero := .snoc h ha

lemma TCtx.IsZero.of_cons {Γ : TCtx R k n ρ} {a : Option (Assm R k)} (h : (Γ.cons a).IsZero) :
    Γ.IsZero ∧ ZeroAssm a := Ctx.all_snoc.1 h

/-- Adding a zero assumption to a linear one leaves it unchanged. -/
lemma AssmAdd.zero_lin {z b c : Option (Assm R k)} {A : Ty R k} (h : AssmAdd z b c)
    (hz : ZeroAssm z) (hb : b = some (.lin A)) : c = some (.lin A) := by
  subst hb; cases h with
  | noneLeft _ => rfl

/-- Adding a zero assumption to a graded one leaves its grade unchanged. -/
lemma AssmAdd.zero_grd {z b c : Option (Assm R k)} {A : Ty R k} {r : R} (h : AssmAdd z b c)
    (hz : ZeroAssm z) (hb : b = some (.grd A r)) : c = some (.grd A r) := by
  subst hb; cases h with
  | noneLeft _ => rfl
  | grd _ s _ => cases hz; rw [zero_add]

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
