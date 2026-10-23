module
public import RequestProject.Common.Syntax
public import Lean.Data.Json.Basic

/-!
# LCU syntax: float literals, types and primitives

The types `Ty` and the array primitives `Prim` of the LCU calculus.  See
`RequestProject/LCU/Sec3_1_Calculus/Syntax.lean` for an overview.
-/

@[expose] public section

namespace LCU

open Binding

/-- Float literals: decimal numbers `mantissa × 10^(-exponent)` with lawful equality. -/
abbrev FloatLit : Type := Lean.JsonNumber

/-- Types `A, B ::= A ⊸ B | A ⊗ B | 1 | !A | *A`, extended (Section 3.3) with
`Array A`, `ℕ` and `𝔽` (floating point numbers). -/
inductive Ty where
  /-- linear functions `A ⊸ B` -/
  | lolli : Ty → Ty → Ty
  /-- multiplicative products `A ⊗ B` -/
  | tensor : Ty → Ty → Ty
  /-- the multiplicative unit `1` -/
  | unit : Ty
  /-- the non-linearity modality `!A` -/
  | bang : Ty → Ty
  /-- the uniqueness modality `*A` -/
  | star : Ty → Ty
  /-- arrays `Array A` -/
  | array : Ty → Ty
  /-- natural numbers `ℕ` (sizes and indices) -/
  | nat : Ty
  /-- floating point values `𝔽` -/
  | float : Ty
  deriving DecidableEq, Repr

@[inherit_doc] infixr:25 " ⊸ " => Ty.lolli
@[inherit_doc] infixr:35 " ⊗ " => Ty.tensor

/-- The array primitives of Section 3.3. -/
inductive Prim where
  | newArray
  | readArray
  | writeArray
  | deleteArray
  deriving DecidableEq, Repr

end LCU
