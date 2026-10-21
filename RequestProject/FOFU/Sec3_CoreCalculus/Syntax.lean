module
public import RequestProject.FOFU.Sec5_Fractional.Permission

/-!
# Syntax of types and terms (Section 3, extended by Sections 4–6)

*Functional Ownership through Fractional Uniqueness* (Marshall, Orchard).

The paper extends the syntax of §3 step by step (§4 adds `share`/`clone` and `*A`, §5
adds borrowing, split/join, push/pull and resources, §6.1 adds runtime terms).  A Lean
inductive type cannot be extended afterwards, so the types `Ty` and terms `Term` below
contain all constructors at once; each constructor's docstring names the section it
comes from.

## Conventions

* **Grades.**  Everything is parameterised by the type `R` of grades of the graded
  modality `□_r A`; the typing rules require `[Grades.PreorderedSemiring R]` (see
  `RequestProject/Common/Grades/PreorderedSemiring.lean`, shared with the LCU paper).
* **Term variables** use intrinsically scoped de Bruijn indices: `Term R n` has `n`
  free variables, `Term.var : Fin n → Term R n`, so `Term R 0` is the type of closed
  terms.  Binders bind index `0`.  In `letPair t₁ t₂` (`let (x, y) = t₁ in t₂`) the
  variable `y` is index `0` and `x` is index `1`.
* **Identifiers** (type variables of kind `Name`) are also de Bruijn: `Ty R k` is the
  type of types with `k` bound identifiers, and `∃ id. A` is `Ty.ex A` with
  `A : Ty R (k + 1)`.  At runtime, resources are named by *runtime identifiers*
  (`Ident.rt a` with `a : ℕ`) that appear in the heap (`id ↦ v_r`).
* **Existentials are Curry-style.**  The identifier of `pack ⟨id, t⟩` and the
  identifier bound by `unpack ⟨id, x⟩ = t₁ in t₂` only appear in types: the terms are
  `pack t` and `unpack t₁ t₂`.  This matches the operational semantics, where
  `unpack ⟨id, x⟩ = pack ⟨id', v⟩ in t` reduces to `t [y/x]` without substituting
  `id'` for `id`.
* **Grade annotations.**  Promotion is always annotated with its grade, `[t]_r`
  (`Term.box r t`); §6.1 uses exactly this Church-style annotation for runtime terms.
  For the same reason `share` carries the grade of the box it produces
  (`Term.share r t`), since its reduction `share (*v) ⤳ [v]` has to produce a
  grade-annotated box.
* **Runtime references** `ref` are named by natural numbers (`Term.ref a`).
-/

@[expose] public section

namespace FOFU

/-! ## Identifiers and types -/

/-- Identifiers `id` (type variables of kind `Name`) in a scope of `k` bound
identifiers: either a bound identifier (de Bruijn index) or a runtime identifier
naming a resource in the heap. -/
inductive Ident (k : ℕ) where
  /-- a bound identifier (introduced by `∃ id. A` or by `unpack`) -/
  | bound : Fin k → Ident k
  /-- a runtime identifier `id`, as allocated in the heap (`id ↦ v_r`) -/
  | rt : ℕ → Ident k
  deriving DecidableEq

/-- The two kinds of resources of §5: `Res ::= Array | Ref`. -/
inductive ResKind where
  | array
  | ref
  deriving DecidableEq

/-- Types, with `k` bound identifiers in scope:

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
  /-- existential types `∃ id. A` over identifiers (§3) -/
  | ex {k : ℕ} : Ty R (k + 1) → Ty R k
  /-- the borrowing modality `&_p A` (§5); `*A` is `&_* A` -/
  | borrow {k : ℕ} : Perm → Ty R k → Ty R k
  /-- resources `Res_id A` (§5): `Array_id A` and `Ref_id A` -/
  | res {k : ℕ} : ResKind → Ident k → Ty R k → Ty R k
  /-- natural numbers `ℕ` (§5) -/
  | nat {k : ℕ} : Ty R k
  /-- floating point numbers `𝔽` (§5) -/
  | float {k : ℕ} : Ty R k

namespace Ty

variable {R : Type} {k : ℕ}

/-- The uniqueness modality `*A` (§4).  §5 identifies it with `&_* A`. -/
abbrev star (A : Ty R k) : Ty R k := borrow Perm.star A

/-- Mutable arrays of floats `Array_id 𝔽` (§5). -/
abbrev array (ι : Ident k) : Ty R k := res ResKind.array ι float

/-- References `Ref_id A` (§5). -/
abbrev ref (ι : Ident k) (A : Ty R k) : Ty R k := res ResKind.ref ι A

end Ty

/-! ## Primitives and terms -/

/-- The primitives of the resource interfaces of §5 (mutable arrays of floats and
polymorphic references). -/
inductive Prim where
  | newArray
  | readArray
  | writeArray
  | deleteArray
  | newRef
  | readRef
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
  | .swapRef => 2
  | .freezeRef => 1

/-- Terms with `n` free (de Bruijn) variables. -/
inductive Term (R : Type) : ℕ → Type where
  /-- variables `x` (§3) -/
  | var {n : ℕ} : Fin n → Term R n
  /-- abstraction `λx. t` (§3) -/
  | lam {n : ℕ} : Term R (n + 1) → Term R n
  /-- application `t₁ t₂` (§3) -/
  | app {n : ℕ} : Term R n → Term R n → Term R n
  /-- pairs `(t₁, t₂)` (§3) -/
  | pair {n : ℕ} : Term R n → Term R n → Term R n
  /-- `let (x, y) = t₁ in t₂` (§3); in `t₂`, `y` is index `0` and `x` is index `1` -/
  | letPair {n : ℕ} : Term R n → Term R (n + 2) → Term R n
  /-- the unit value `()` (§3) -/
  | unit {n : ℕ} : Term R n
  /-- `let () = t₁ in t₂` (§3) -/
  | letUnit {n : ℕ} : Term R n → Term R n → Term R n
  /-- promotion `[t]_r` (§3, grade annotation as in §6.1) -/
  | box {n : ℕ} : R → Term R n → Term R n
  /-- `let [x] = t₁ in t₂` (§3) -/
  | letBox {n : ℕ} : Term R n → Term R (n + 1) → Term R n
  /-- `pack ⟨id, t⟩` (§3); the identifier is not part of the term -/
  | pack {n : ℕ} : Term R n → Term R n
  /-- `unpack ⟨id, x⟩ = t₁ in t₂` (§3); only `x` is a term variable -/
  | unpack {n : ℕ} : Term R n → Term R (n + 1) → Term R n
  /-- `share t` (§4), annotated with the grade `r` of the resulting box `□_r A` -/
  | share {n : ℕ} : R → Term R n → Term R n
  /-- `clone t₁ as x in t₂` (§4) -/
  | clone {n : ℕ} : Term R n → Term R (n + 1) → Term R n
  /-- `withBorrow t₁ t₂` (§5): `t₁` is the function, `t₂` the owned value -/
  | withBorrow {n : ℕ} : Term R n → Term R n → Term R n
  /-- `split t` (§5) -/
  | split {n : ℕ} : Term R n → Term R n
  /-- `join t₁ t₂` (§5) -/
  | join {n : ℕ} : Term R n → Term R n → Term R n
  /-- `push t` (§5.2) -/
  | push {n : ℕ} : Term R n → Term R n
  /-- `pull t` (§5.2) -/
  | pull {n : ℕ} : Term R n → Term R n
  /-- natural number literals (§5) -/
  | nat {n : ℕ} : ℕ → Term R n
  /-- floating point literals (§5) -/
  | float {n : ℕ} : Float → Term R n
  /-- the resource primitives (§5) -/
  | prim {n : ℕ} : Prim → Term R n
  /-- the runtime term `* t` for unique and borrowed values (§6.1) -/
  | star {n : ℕ} : Term R n → Term R n
  /-- the runtime term `unborrow t` (§6.1) -/
  | unborrow {n : ℕ} : Term R n → Term R n
  /-- runtime references `ref` (§6.1) -/
  | ref {n : ℕ} : ℕ → Term R n

end FOFU
