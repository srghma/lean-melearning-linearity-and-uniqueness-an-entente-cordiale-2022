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
