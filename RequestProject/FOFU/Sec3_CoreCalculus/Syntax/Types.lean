module
public import RequestProject.FOFU.Sec5_Fractional.Permission
public import RequestProject.Common.Syntax
public import Lean.Data.Json.Basic

/-!
# Syntax: float literals, types and primitives

The types `Ty R k` (with `k` identifiers in scope) and the resource primitives `Prim` of
*Functional Ownership through Fractional Uniqueness*.  See
`RequestProject/FOFU/Sec3_CoreCalculus/Syntax.lean` for the conventions.
-/

@[expose] public section

namespace FOFU

open Binding

/-- Float literals: decimal numbers `mantissa × 10^(-exponent)` with lawful equality. -/
abbrev FloatLit : Type := Lean.JsonNumber

/-! ## Types -/

/-- The two kinds of resources of §5: `Res ::= Array | Ref`. -/
inductive ResKind where
  | array
  | ref
  deriving DecidableEq

/-- Types, with `k` identifiers in scope:

  `A, B ::= A ⊸ B | A ⊗ B | unit | □_r A | ∃ id. A`  (§3)
  `       | *A`                                        (§4, defined as `&_* A`)
  `       | &_p A | Res_id A | ℕ | 𝔽`                  (§5). -/
inductive Ty (R : Type) : ℕ → Type where
  /-- linear functions `A ⊸ B` (§3) -/
  | lolli {k : ℕ} : Ty R k → Ty R k → Ty R k
  /-- multiplicative products `A ⊗ B` (§3) -/
  | tensor {k : ℕ} : Ty R k → Ty R k → Ty R k
  /-- the multiplicative unit `unit` (§3) -/
  | unit {k : ℕ} : Ty R k
  /-- the graded modality `□_r A` (§3) -/
  | box {k : ℕ} : R → Ty R k → Ty R k
  /-- existential types `∃ id. A` over identifiers (§3); the bound identifier is
  `Var.zero` of `A` -/
  | ex {k : ℕ} : Ty R (k + 1) → Ty R k
  /-- the borrowing modality `&_p A` (§5); `*A` is `&_* A` -/
  | borrow {k : ℕ} : Perm → Ty R k → Ty R k
  /-- resources `Res_id A` (§5): `Array_id A` and `Ref_id A` -/
  | res {k : ℕ} : ResKind → Var k → Ty R k → Ty R k
  /-- natural numbers `ℕ` (§5) -/
  | nat {k : ℕ} : Ty R k
  /-- floating point numbers `𝔽` (§5) -/
  | float {k : ℕ} : Ty R k
  deriving DecidableEq

namespace Ty

variable {R : Type} {k : ℕ}

/-- The uniqueness modality `*A` (§4).  §5 identifies it with `&_* A`. -/
abbrev star (A : Ty R k) : Ty R k := borrow Perm.star A

/-- Mutable arrays of floats `Array_id 𝔽` (§5). -/
abbrev array (ι : Var k) : Ty R k := res ResKind.array ι float

/-- References `Ref_id A` (§5). -/
abbrev ref (ι : Var k) (A : Ty R k) : Ty R k := res ResKind.ref ι A

end Ty

/-! ## Primitives -/

/-- The primitives of the resource interfaces of §5 (mutable arrays of floats and
polymorphic references). -/
inductive Prim where
  | newArray
  | readArray
  | writeArray
  | deleteArray
  | newRef
  | readRef
  /-- amended, grade-splitting `readRef` (not in the paper; needed for `exampleGraded`) -/
  | readRefSplit
  | swapRef
  | freezeRef
  deriving DecidableEq

/-- The number of arguments a primitive takes before it reduces. -/
def Prim.arity : Prim → ℕ
  | .newArray => 1
  | .readArray => 2
  | .writeArray => 3
  | .deleteArray => 1
  | .newRef => 1
  | .readRef => 1
  | .readRefSplit => 1
  | .swapRef => 2
  | .freezeRef => 1

end FOFU
