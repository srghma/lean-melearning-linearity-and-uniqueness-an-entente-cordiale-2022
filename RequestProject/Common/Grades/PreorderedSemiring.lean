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

This file only contains the class and the instance for the natural numbers with their
usual order (`≤`), which the second paper uses in its examples ("the natural number
semiring").
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

/-- The natural numbers with the usual order: a semiring counting the exact number of
uses, where approximation `r ≤ s` gives upper bounds on usage. -/
instance : PreorderedSemiring ℕ where
  add_mono := Nat.add_le_add
  mul_mono := Nat.mul_le_mul

end Grades
