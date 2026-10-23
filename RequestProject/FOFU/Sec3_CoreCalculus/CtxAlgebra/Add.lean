module
public import RequestProject.FOFU.Sec3_CoreCalculus.Context
public import Mathlib.Order.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# The algebra of contexts: addition and zero contexts

Commutativity, associativity and interchange of the addition of assumptions, reference
types and contexts (`AssmAdd`, `RefAdd`, `CtxAdd`), and zero contexts.
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

end FOFU
