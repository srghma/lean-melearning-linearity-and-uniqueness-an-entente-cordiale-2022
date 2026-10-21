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

variable {R : Type} [Grades.PreorderedSemiring R] {k n : ℕ}

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

lemma comm {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) : CtxAdd Γ₂ Γ₁ Γ :=
  ⟨fun i => (h.vars i).comm, fun a => (h.refs a).comm⟩

lemma assoc {A B AB C ABC : Ctx R k n} (h₁ : CtxAdd A B AB) (h₂ : CtxAdd AB C ABC) :
    ∃ BC, CtxAdd B C BC ∧ CtxAdd A BC ABC := by
  choose f hf using fun i => (h₁.vars i).assoc (h₂.vars i)
  choose g hg using fun a => (h₁.refs a).assoc (h₂.refs a)
  exact ⟨⟨f, g⟩, ⟨fun i => (hf i).1, fun a => (hg a).1⟩, ⟨fun i => (hf i).2, fun a => (hg a).2⟩⟩

/-- Associativity, in the other direction. -/
lemma assoc' {A B BC C ABC : Ctx R k n} (h₁ : CtxAdd B C BC) (h₂ : CtxAdd A BC ABC) :
    ∃ AB, CtxAdd A B AB ∧ CtxAdd AB C ABC := by
  obtain ⟨X, h3, h4⟩ := assoc h₁.comm h₂.comm
  exact ⟨X, h3.comm, h4.comm⟩

/-- The interchange law `(A₁ + A₂) + (B₁ + B₂) = (A₁ + B₁) + (A₂ + B₂)`. -/
lemma interchange {A₁ A₂ A B₁ B₂ B C : Ctx R k n} (hA : CtxAdd A₁ A₂ A) (hB : CtxAdd B₁ B₂ B)
    (hC : CtxAdd A B C) :
    ∃ C₁ C₂, CtxAdd A₁ B₁ C₁ ∧ CtxAdd A₂ B₂ C₂ ∧ CtxAdd C₁ C₂ C := by
  obtain ⟨X, hX1, hX2⟩ := assoc hA hC
  obtain ⟨Y, hY1, hY2⟩ := assoc hB hX1.comm
  obtain ⟨C₁, hC1, hC2⟩ := assoc' hY2 hX2
  exact ⟨C₁, Y, hC1, hY1.comm, hC2⟩

lemma none_left (Γ : Ctx R k n) : CtxAdd (Ctx.none n) Γ Γ :=
  ⟨fun _ => .noneLeft _, fun _ => .noneLeft _⟩

lemma none_right (Γ : Ctx R k n) : CtxAdd Γ (Ctx.none n) Γ := (none_left Γ).comm

lemma refsOnly {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) :
    CtxAdd Γ₁.refsOnly Γ₂.refsOnly Γ.refsOnly :=
  ⟨fun _ => .noneLeft _, h.refs⟩

end CtxAdd

/-! ## Zero contexts -/

lemma ZeroAssm.add {a b c : Option (Assm R k)} (h : AssmAdd a b c) (ha : ZeroAssm a)
    (hb : ZeroAssm b) : ZeroAssm c := by
  cases h with
  | noneLeft _ => exact hb
  | noneRight _ => exact ha
  | grd A r s => simp only [ZeroAssm] at *; rw [ha, hb, add_zero]

lemma Ctx.IsZero.add {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) (h₁ : Γ₁.IsZero)
    (h₂ : Γ₂.IsZero) : Γ.IsZero := fun i => (h₁ i).add (h.vars i) (h₂ i)

lemma Ctx.IsZero.none : (Ctx.none n : Ctx R k n).IsZero := fun _ => trivial

lemma Ctx.IsZero.refsOnly (Γ : Ctx R k n) : Γ.refsOnly.IsZero := fun _ => trivial

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
  | grd _ s _ => simp only [ZeroAssm] at hz; rw [hz, zero_add]

/-! ## Scaling -/

/-- A context with no linear assumptions (the paper's `[Γ]`). -/
def Ctx.Graded (Γ : Ctx R k n) : Prop := ∀ i A, Γ.vars i ≠ some (.lin A)

omit [Grades.PreorderedSemiring R] in
lemma Ctx.Graded.none : (Ctx.none n : Ctx R k n).Graded := fun _ _ h => by cases h

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
  rcases a with _ | ⟨A | ⟨A, s⟩⟩
  · exact .none
  · exact h.elim
  · simp only [ZeroAssm] at h; subst h
    have h := AssmScale.grd (r := r) A 0
    rwa [mul_zero] at h

lemma isZero (h : AssmScale r a b) (ha : ZeroAssm a) : ZeroAssm b := by
  cases h with
  | none => trivial
  | grd A s => simp only [ZeroAssm] at *; rw [ha, mul_zero]

lemma isZero_zero (h : AssmScale 0 a b) : ZeroAssm b := by
  cases h with
  | none => trivial
  | grd A s => simp only [ZeroAssm]; rw [zero_mul]

lemma not_lin_left {A : Ty R k} (h : AssmScale r (some (.lin A)) b) : False := by cases h

lemma not_lin_right {A : Ty R k} (h : AssmScale r a (some (.lin A))) : False := by cases h

end AssmScale

namespace CtxScale

lemma exists_of_graded {Γ : Ctx R k n} (h : Γ.Graded) (r : R) : ∃ Γ', CtxScale r Γ Γ' := by
  have : ∀ i, ∃ b, AssmScale r (Γ.vars i) b := by
    intro i
    rcases e : Γ.vars i with _ | ⟨A | ⟨A, s⟩⟩
    · exact ⟨_, .none⟩
    · exact absurd e (h i A)
    · exact ⟨_, .grd A s⟩
  choose f hf using this
  exact ⟨⟨f, Γ.refs⟩, ⟨hf, rfl⟩⟩

lemma graded {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ') : Γ.Graded := by
  intro i A e; have := h.vars i; rw [e] at this; exact this.not_lin_left

lemma graded' {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ') : Γ'.Graded := by
  intro i A e; have := h.vars i; rw [e] at this; exact this.not_lin_right

lemma one_eq {Γ Γ' : Ctx R k n} (h : CtxScale 1 Γ Γ') : Γ' = Γ := by
  ext1
  · funext i; exact (h.vars i).one_eq
  · exact h.refs

lemma comp {q r : R} {Γ Γq Γrq : Ctx R k n} (h₁ : CtxScale q Γ Γq) (h₂ : CtxScale r Γq Γrq) :
    CtxScale (r * q) Γ Γrq :=
  ⟨fun i => (h₁.vars i).comp (h₂.vars i), h₂.refs.trans h₁.refs⟩

/-- `r · Γ + s · Γ = (r + s) · Γ`. -/
lemma add_scale {r s : R} {Γ Γr Γs Γrs : Ctx R k n} (hr : CtxScale r Γ Γr)
    (hs : CtxScale s Γ Γs) (hrs : CtxScale (r + s) Γ Γrs) : CtxAdd Γr Γs Γrs := by
  refine ⟨fun i => (hr.vars i).add_scale (hs.vars i) (hrs.vars i), fun a => ?_⟩
  rw [hr.refs, hs.refs, hrs.refs]; exact RefAdd.idem _

/-- Distributivity, `r · A + r · B = r · (A + B)`, in the form needed for inversion. -/
lemma add_exists {r : R} {A A' B B' C' : Ctx R k n} (hA : CtxScale r A A') (hB : CtxScale r B B')
    (hC : CtxAdd A' B' C') : ∃ C, CtxAdd A B C ∧ CtxScale r C C' := by
  choose f hf using fun i => (hA.vars i).add_exists (hB.vars i) (hC.vars i)
  refine ⟨⟨f, C'.refs⟩, ⟨fun i => (hf i).1, fun a => ?_⟩, ⟨fun i => (hf i).2, rfl⟩⟩
  have := hC.refs a
  rwa [hA.refs, hB.refs] at this

/-- A zero context is unchanged by scaling. -/
lemma of_isZero {Z : Ctx R k n} (hZ : Z.IsZero) (r : R) : CtxScale r Z Z :=
  ⟨fun i => AssmScale.zero (hZ i) r, rfl⟩

lemma isZero {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ') (hΓ : Γ.IsZero) : Γ'.IsZero :=
  fun i => (h.vars i).isZero (hΓ i)

lemma isZero_zero {Γ Γ' : Ctx R k n} (h : CtxScale 0 Γ Γ') : Γ'.IsZero :=
  fun i => (h.vars i).isZero_zero

lemma refsOnly {r : R} {Γ Γ' : Ctx R k n} (h : CtxScale r Γ Γ') :
    CtxScale r Γ.refsOnly Γ'.refsOnly := ⟨fun _ => .none, h.refs⟩

end CtxScale

/-! ## Approximating grades -/

/-- `AssmLe a b`: `b` is `a`, possibly with its grade approximated upwards. -/
inductive AssmLe : Option (Assm R k) → Option (Assm R k) → Prop where
  | refl (a : Option (Assm R k)) : AssmLe a a
  | grd (A : Ty R k) {r s : R} : r ≤ s → AssmLe (some (.grd A r)) (some (.grd A s))

/-- `CtxLe Γ Γ'`: `Γ'` is `Γ` with some grades approximated upwards. -/
structure CtxLe (Γ Γ' : Ctx R k n) : Prop where
  vars : ∀ i, AssmLe (Γ.vars i) (Γ'.vars i)
  refs : Γ'.refs = Γ.refs

namespace AssmLe

lemma add_exists {a a' b c' : Option (Assm R k)} (h₁ : AssmLe a a') (h₂ : AssmAdd a' b c') :
    ∃ c, AssmAdd a b c ∧ AssmLe c c' := by
  cases h₁ with
  | refl a => exact ⟨_, h₂, .refl _⟩
  | grd T hrs =>
    cases h₂ with
    | noneRight _ => exact ⟨_, .noneRight _, .grd T hrs⟩
    | grd _ _ q => exact ⟨_, .grd T _ q, .grd T (Grades.PreorderedSemiring.add_mono hrs le_rfl)⟩

lemma of_scale {r s : R} {a b c : Option (Assm R k)} (h₁ : AssmScale r a b)
    (h₂ : AssmScale s a c) (h : r ≤ s) : AssmLe b c := by
  cases h₁ with
  | none => cases h₂; exact .refl _
  | grd A q => cases h₂; exact .grd A (Grades.PreorderedSemiring.mul_mono h le_rfl)

end AssmLe

namespace CtxLe

lemma refl (Γ : Ctx R k n) : CtxLe Γ Γ := ⟨fun _ => .refl _, rfl⟩

/-- If `A ≤ A'` and `A' + B` is defined, so is `A + B`, and it is below `A' + B`. -/
lemma add_exists {A A' B C' : Ctx R k n} (hA : CtxLe A A') (hC : CtxAdd A' B C') :
    ∃ C, CtxAdd A B C ∧ CtxLe C C' := by
  choose f hf using fun i => (hA.vars i).add_exists (hC.vars i)
  refine ⟨⟨f, C'.refs⟩, ⟨fun i => (hf i).1, fun a => ?_⟩, ⟨fun i => (hf i).2, rfl⟩⟩
  have := hC.refs a
  rwa [hA.refs] at this

/-- If `B ≤ B'` and `A + B'` is defined, so is `A + B`, and it is below `A + B'`. -/
lemma add_exists' {A B B' C' : Ctx R k n} (hB : CtxLe B B') (hC : CtxAdd A B' C') :
    ∃ C, CtxAdd A B C ∧ CtxLe C C' := by
  obtain ⟨C, h1, h2⟩ := add_exists hB hC.comm
  exact ⟨C, h1.comm, h2⟩

/-- `r ≤ s` implies `r · Γ ≤ s · Γ`. -/
lemma of_scale {r s : R} {Γ Γr Γs : Ctx R k n} (hr : CtxScale r Γ Γr) (hs : CtxScale s Γ Γs)
    (h : r ≤ s) : CtxLe Γr Γs :=
  ⟨fun i => AssmLe.of_scale (hr.vars i) (hs.vars i) h, by rw [hr.refs, hs.refs]⟩

/-- Approximating one graded assumption. -/
lemma update {Γ : Ctx R k n} {i : Fin n} {A : Ty R k} {r s : R}
    (hi : Γ.vars i = some (.grd A r)) (h : r ≤ s) :
    CtxLe Γ (Γ.update i (some (.grd A s))) := by
  refine ⟨fun j => ?_, rfl⟩
  by_cases hj : j = i
  · subst hj; simp only [Ctx.update, Function.update_self, hi]; exact .grd A h
  · simp only [Ctx.update, Function.update_of_ne hj]; exact .refl _

end CtxLe

end FOFU
