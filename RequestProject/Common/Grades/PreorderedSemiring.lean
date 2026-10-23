module
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Pre-ordered semirings of grades

Graded modal type systems such as Granule's index the modality `□_r A` by elements `r`
of a *pre-ordered semiring* `(R, *, 1, +, 0, ⊑)` in which `+` and `*` are monotone with
respect to `⊑`.

* In *Functional Ownership through Fractional Uniqueness* (§3) this is the parameter of
  the whole calculus: the FOFU development (`RequestProject/FOFU/`) is parameterised by
  `{R : Type} [Grades.PreorderedSemiring R]`.
* In *Linearity and Uniqueness: An Entente Cordiale* (§4.1) the semiring `{0, 1, ω}`
  used by Granule for linear logic's `!` is an instance; the instance is declared next
  to that semiring in `RequestProject/LCU/Sec4_Implementation/Granule.lean`.

This file contains the class, its bridge to Mathlib's order mixins (`AddLeftMono`,
`AddRightMono`, `MulLeftMono`, `MulRightMono`, in both directions: instances derived from
the class, and the constructor `PreorderedSemiring.ofMono`), and the instance for the
natural numbers with their usual order (`≤`), which the second paper uses in its examples
("the natural number semiring").

Mathlib's `IsOrderedRing` is not used because it requires a *partial* order, while the
papers only assume a pre-order.
-/

@[expose] public section

namespace Grades

/-- A pre-ordered semiring: a semiring with a pre-order `≤` (written `⊑` in the papers)
for which addition and multiplication are monotone. -/
class PreorderedSemiring (R : Type) extends Semiring R, Preorder R where
  /-- Addition is monotone in both arguments. -/
  add_mono : ∀ {a b c d : R}, a ≤ b → c ≤ d → a + c ≤ b + d
  /-- Multiplication is monotone in both arguments. -/
  mul_mono : ∀ {a b c d : R}, a ≤ b → c ≤ d → a * c ≤ b * d

namespace PreorderedSemiring

variable {R : Type} [PreorderedSemiring R]

/-! The monotonicity fields are exposed as Mathlib's order mixins, so that Mathlib's
lemmas (`add_le_add`, `mul_le_mul'`, `add_le_add_right`, …) and order tactics apply to
grades directly. -/

instance : AddLeftMono R := ⟨fun _ _ _ h => add_mono le_rfl h⟩
instance : AddRightMono R := ⟨fun _ _ _ h => add_mono h le_rfl⟩
instance : MulLeftMono R := ⟨fun _ _ _ h => mul_mono le_rfl h⟩
instance : MulRightMono R := ⟨fun _ _ _ h => mul_mono h le_rfl⟩

/-- Conversely, a semiring with a pre-order and Mathlib's monotonicity mixins is a
pre-ordered semiring. -/
abbrev ofMono (S : Type) [Semiring S] [Preorder S] [AddLeftMono S] [AddRightMono S]
    [MulLeftMono S] [MulRightMono S] : PreorderedSemiring S where
  add_mono := add_le_add
  mul_mono := mul_le_mul'

end PreorderedSemiring

/-- The natural numbers with the usual order: a semiring counting the exact number of
uses, where approximation `r ≤ s` gives upper bounds on usage. -/
instance : PreorderedSemiring ℕ := .ofMono ℕ

end Grades
