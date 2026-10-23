module
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Permissions (Section 5)

*Functional Ownership through Fractional Uniqueness*, §5: the borrowing modality
`&_p A` is graded by a *permission*

  `p, q ::= * | f`   where `f ∈ ℚ` and `0 < f ≤ 1`.

`*` is unique ownership (so `*A ≡ &_* A`), `1` is a mutable borrow and fractions below
`1` are immutable borrows.  Halving (used by `split`) and addition (used by `join`) are
only defined on fractions.

* `FOFU.Frac`: rationals `f` with `0 < f ≤ 1`;
* `FOFU.Frac.half`, `FOFU.Frac.add` (the latter needs `f + g ≤ 1`, otherwise the sum
  is not a permission);
* `FOFU.Perm`: permissions, with `Perm.one` (mutable borrow) and `Perm.star`
  (ownership).

This file is placed in the §5 directory because that is where the paper introduces
permissions; it is imported by the syntax of types in `Sec3_CoreCalculus/Syntax.lean`,
which (being a single inductive type) contains the type formers of all sections.
-/

@[expose] public section

namespace FOFU

/-- Fractional permissions: rationals `f` with `0 < f ≤ 1`. -/
abbrev Frac : Type := {f : ℚ // 0 < f ∧ f ≤ 1}

namespace Frac

/-- The full permission `1`. -/
def one : Frac := ⟨1, by norm_num, le_refl _⟩

/-- Halving a fraction, `p / 2` (rule `split`). -/
def half (f : Frac) : Frac :=
  ⟨f.1 / 2, by linarith [f.2.1], by linarith [f.2.1, f.2.2]⟩

/-- Adding two fractions whose sum is at most `1`, `p + q` (rule `join`). -/
def add (f g : Frac) (h : f.1 + g.1 ≤ 1) : Frac :=
  ⟨f.1 + g.1, by linarith [f.2.1, g.2.1], h⟩

@[simp] lemma one_val : one.1 = 1 := rfl
@[simp] lemma half_val (f : Frac) : (half f).1 = f.1 / 2 := rfl
@[simp] lemma add_val (f g : Frac) (h : f.1 + g.1 ≤ 1) : (add f g h).1 = f.1 + g.1 := rfl

/-- Two halves add up to the original fraction. -/
lemma half_add_half (f : Frac) : (half f).1 + (half f).1 ≤ 1 := by
  simp only [half_val]; linarith [f.2.2]

lemma add_half_half (f : Frac) : add (half f) (half f) (half_add_half f) = f := by
  apply Subtype.ext; simp only [add_val, half_val]; ring

/-! ### Partial commutative monoid laws of `Frac.add`

`Frac.add` is a partial operation (defined when the sum is at most `1`); these are the
laws of a partial commutative monoid without unit, stated with explicit definedness
proofs. -/

lemma add_comm (f g : Frac) (h : f.1 + g.1 ≤ 1) :
    add f g h = add g f (by rwa [_root_.add_comm]) :=
  Subtype.ext (_root_.add_comm _ _)

lemma add_assoc (f g k : Frac) (h₁ : f.1 + g.1 ≤ 1) (h₂ : (add f g h₁).1 + k.1 ≤ 1) :
    add (add f g h₁) k h₂ =
      add f (add g k (by simp only [add_val] at h₂; linarith [f.2.1]))
        (by simp only [add_val] at h₂ ⊢; linarith) :=
  Subtype.ext (_root_.add_assoc _ _ _)

/-- Cancellation: `f + g = f + g'` implies `g = g'`. -/
lemma add_left_cancel {f g g' : Frac} {h : f.1 + g.1 ≤ 1} {h' : f.1 + g'.1 ≤ 1}
    (e : add f g h = add f g' h') : g = g' :=
  Subtype.ext (by simpa using congrArg Subtype.val e)

/-- The full permission cannot be extended: `1 + g` is never defined. -/
lemma not_one_add (g : Frac) : ¬ one.1 + g.1 ≤ 1 := by
  simp only [one_val]; linarith [g.2.1]

/-- A sum is strictly larger than each summand. -/
lemma lt_add_left (f g : Frac) (h : f.1 + g.1 ≤ 1) : f.1 < (add f g h).1 := by
  simp only [add_val]; linarith [g.2.1]

/-- Halving strictly decreases a fraction. -/
lemma half_lt (f : Frac) : (half f).1 < f.1 := by
  simp only [half_val]; linarith [f.2.1]

end Frac

/-- Permissions `p ::= * | f`: unique ownership `*` or a fraction `0 < f ≤ 1`. -/
inductive Perm where
  /-- unique ownership `*` -/
  | star : Perm
  /-- a fractional permission `f` (mutable borrow if `f = 1`, immutable otherwise) -/
  | frac : Frac → Perm
  deriving DecidableEq

namespace Perm

/-- The mutable-borrow permission `1`. -/
abbrev one : Perm := frac Frac.one

end Perm

end FOFU
