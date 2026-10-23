module
public import RequestProject.FOFU.Sec5_Fractional.Permission
public import RequestProject.Common.Syntax
public import Lean.Data.Json.Basic

/-!
# Syntax of types and terms (Section 3, extended by Sections 4–6)

*Functional Ownership through Fractional Uniqueness* (Marshall, Orchard).

The paper extends the syntax of §3 step by step (§4 adds `share`/`clone` and `*A`, §5
adds borrowing, split/join, push/pull and resources, §6.1 adds runtime terms).  A Lean
inductive type cannot be extended afterwards, so the types `Ty` and terms `Term` below
contain all constructors at once; each constructor's docstring names the section it
comes from.  The source grammar (without the runtime forms of §6.1) is given separately
as `SrcTerm`, embedded into `Term` by the generic operator map.

## Conventions

* **Grades.**  Everything is parameterised by the type `R` of grades of the graded
  modality `□_r A`; the typing rules require `[Grades.PreorderedSemiring R]`.
* **Term variables** are intrinsically scoped de Bruijn indices `Var n`: `Term R n ρ` has
  `n` free variables (`Term.var : Var n → Term R n ρ`), so `Term R 0 ρ` is the type of
  closed terms.  Binders bind `Var.zero`.  In `letPair t₁ t₂` (`let (x, y) = t₁ in t₂`)
  the variable `y` is `Var.zero` and `x` is `Var.succ Var.zero`.
* **Terms are built with the generic binding layer** (`RequestProject/Common/Syntax.lean`):
  `Term R n ρ` is `Binding.Tm` over the signature `sig R ρ`, so renaming, substitution and
  their laws are inherited.  The constructors `Term.lam`, … are pattern synonyms, and
  `Term.rec'` / `Term.cases'` are the default `induction` / `cases` eliminators.
* **Runtime references are scoped** like variables: `ρ` is the number of runtime
  references in scope and `Term.ref : Var ρ → Term R n ρ`.  Source programs are terms
  with `ρ = 0`.
* **Identifiers** (type variables of kind `Name`) are de Bruijn indices `Var k`: `Ty R k`
  is the type of types with `k` identifiers in scope, and `∃ id. A` is `Ty.ex A` with
  `A : Ty R (k + 1)`.  At runtime, resources are named by *runtime identifiers*; these are
  simply the identifiers in scope (the heap of §6.1 has `ι` resources, and runtime types
  are `Ty R ι`).  There is no separate constructor for runtime identifiers.
* **Existentials are Curry-style.**  The identifier of `pack ⟨id, t⟩` and the
  identifier bound by `unpack ⟨id, x⟩ = t₁ in t₂` only appear in types: the terms are
  `pack t` and `unpack t₁ t₂`.  Terms never mention identifiers.
* **Grade annotations.**  Promotion is always annotated with its grade, `[t]_r`
  (`Term.box r t`), as in §6.1, and `share` carries the grade of the box it produces
  (`Term.share r t`).
* **Float literals** are `Lean.JsonNumber`s (`FloatLit`: a mantissa and a decimal
  exponent, with lawful decidable equality), not Lean's built-in `Float`.
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

/-! ## Terms -/

/-- The operators of the FOFU term language (grades `R`, `ρ` runtime references). -/
inductive Op (R : Type) (ρ : ℕ) where
  | lam
  | app
  | pair
  | letPair
  | unit
  | letUnit
  | box (r : R)
  | letBox
  | pack
  | unpack
  | share (r : R)
  | clone
  | withBorrow
  | split
  | join
  | push
  | pull
  | nat (m : ℕ)
  | float (x : FloatLit)
  | prim (p : Prim)
  | star
  | unborrow
  | ref (a : Var ρ)

/-- Binding arities of the operators. -/
def Op.arity {R : Type} {ρ : ℕ} : Op R ρ → List ℕ
  | .lam => [1]
  | .app => [0, 0]
  | .pair => [0, 0]
  | .letPair => [0, 2]
  | .unit => []
  | .letUnit => [0, 0]
  | .box _ => [0]
  | .letBox => [0, 1]
  | .pack => [0]
  | .unpack => [0, 1]
  | .share _ => [0]
  | .clone => [0, 1]
  | .withBorrow => [0, 0]
  | .split => [0]
  | .join => [0, 0]
  | .push => [0]
  | .pull => [0]
  | .nat _ => []
  | .float _ => []
  | .prim _ => []
  | .star => [0]
  | .unborrow => [0]
  | .ref _ => []

/-- The signature of the FOFU term language. -/
abbrev sig (R : Type) (ρ : ℕ) : Sig := ⟨Op R ρ, Op.arity⟩

/-- Terms of FOFU with `n` free variables and `ρ` runtime references (grades `R`). -/
def Term (R : Type) (n ρ : ℕ) : Type := Tm (sig R ρ) n

namespace Term

variable {R : Type} {n ρ : ℕ}

/-- variables `x` (§3) -/
@[match_pattern] abbrev var (i : Var n) : Term R n ρ := Tm.var i
/-- abstraction `λx. t` (§3); the bound variable is `Var.zero` of `t` -/
@[match_pattern] abbrev lam (t : Term R (n + 1) ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .lam (.cons t .nil)
/-- application `t₁ t₂` (§3) -/
@[match_pattern] abbrev app (t₁ : Term R n ρ) (t₂ : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .app (.cons t₁ (.cons t₂ .nil))
/-- pairs `(t₁, t₂)` (§3) -/
@[match_pattern] abbrev pair (t₁ : Term R n ρ) (t₂ : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .pair (.cons t₁ (.cons t₂ .nil))
/-- `let (x, y) = t₁ in t₂` (§3); in `t₂`, `y` is `Var.zero` and `x` is `Var.succ Var.zero` -/
@[match_pattern] abbrev letPair (t₁ : Term R n ρ) (t₂ : Term R (n + 2) ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .letPair (.cons t₁ (.cons t₂ .nil))
/-- the unit value `()` (§3) -/
@[match_pattern] abbrev unit  : Term R n ρ :=
  Tm.op (S := sig R ρ) .unit (.nil)
/-- `let () = t₁ in t₂` (§3) -/
@[match_pattern] abbrev letUnit (t₁ : Term R n ρ) (t₂ : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .letUnit (.cons t₁ (.cons t₂ .nil))
/-- promotion `[t]_r` (§3, grade annotation as in §6.1) -/
@[match_pattern] abbrev box (r : R) (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.box r) (.cons t .nil)
/-- `let [x] = t₁ in t₂` (§3) -/
@[match_pattern] abbrev letBox (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .letBox (.cons t₁ (.cons t₂ .nil))
/-- `pack ⟨id, t⟩` (§3); the identifier is not part of the term -/
@[match_pattern] abbrev pack (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .pack (.cons t .nil)
/-- `unpack ⟨id, x⟩ = t₁ in t₂` (§3); only `x` is a term variable -/
@[match_pattern] abbrev unpack (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .unpack (.cons t₁ (.cons t₂ .nil))
/-- `share t` (§4), annotated with the grade `r` of the resulting box `□_r A` -/
@[match_pattern] abbrev share (r : R) (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.share r) (.cons t .nil)
/-- `clone t₁ as x in t₂` (§4) -/
@[match_pattern] abbrev clone (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .clone (.cons t₁ (.cons t₂ .nil))
/-- `withBorrow t₁ t₂` (§5): `t₁` is the function, `t₂` the owned value -/
@[match_pattern] abbrev withBorrow (t₁ : Term R n ρ) (t₂ : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .withBorrow (.cons t₁ (.cons t₂ .nil))
/-- `split t` (§5) -/
@[match_pattern] abbrev split (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .split (.cons t .nil)
/-- `join t₁ t₂` (§5) -/
@[match_pattern] abbrev join (t₁ : Term R n ρ) (t₂ : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .join (.cons t₁ (.cons t₂ .nil))
/-- `push t` (§5.2) -/
@[match_pattern] abbrev push (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .push (.cons t .nil)
/-- `pull t` (§5.2) -/
@[match_pattern] abbrev pull (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .pull (.cons t .nil)
/-- natural number literals (§5) -/
@[match_pattern] abbrev nat (m : ℕ) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.nat m) (.nil)
/-- floating point literals (§5) -/
@[match_pattern] abbrev float (x : FloatLit) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.float x) (.nil)
/-- the resource primitives (§5) -/
@[match_pattern] abbrev prim (p : Prim) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.prim p) (.nil)
/-- the runtime term `* t` for unique and borrowed values (§6.1) -/
@[match_pattern] abbrev star (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .star (.cons t .nil)
/-- the runtime term `unborrow t` (§6.1) -/
@[match_pattern] abbrev unborrow (t : Term R n ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) .unborrow (.cons t .nil)
/-- runtime references `ref` (§6.1) -/
@[match_pattern] abbrev ref (a : Var ρ) : Term R n ρ :=
  Tm.op (S := sig R ρ) (.ref a) (.nil)

/-- Structural recursion / induction on terms, one case per constructor of the paper's
grammar.  Registered as the default eliminator for `induction`. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : (n : ℕ) → Term R n ρ → Sort _}
    (var : ∀ {n} (i : Var n), motive n (var i))
    (lam : ∀ {n} (t : Term R (n + 1) ρ), motive _ t → motive n (lam t))
    (app : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive _ t₁ → motive _ t₂ → motive n (app t₁
      t₂))
    (pair : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive _ t₁ → motive _ t₂ → motive n (pair
      t₁ t₂))
    (letPair : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R (n + 2) ρ), motive _ t₁ → motive _ t₂ → motive
      n (letPair t₁ t₂))
    (unit : ∀ {n}, motive n (unit))
    (letUnit : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive _ t₁ → motive _ t₂ → motive n
      (letUnit t₁ t₂))
    (box : ∀ {n} (r : R) (t : Term R n ρ), motive _ t → motive n (box r t))
    (letBox : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive _ t₁ → motive _ t₂ → motive
      n (letBox t₁ t₂))
    (pack : ∀ {n} (t : Term R n ρ), motive _ t → motive n (pack t))
    (unpack : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive _ t₁ → motive _ t₂ → motive
      n (unpack t₁ t₂))
    (share : ∀ {n} (r : R) (t : Term R n ρ), motive _ t → motive n (share r t))
    (clone : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive _ t₁ → motive _ t₂ → motive n
      (clone t₁ t₂))
    (withBorrow : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive _ t₁ → motive _ t₂ → motive n
      (withBorrow t₁ t₂))
    (split : ∀ {n} (t : Term R n ρ), motive _ t → motive n (split t))
    (join : ∀ {n} (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive _ t₁ → motive _ t₂ → motive n (join
      t₁ t₂))
    (push : ∀ {n} (t : Term R n ρ), motive _ t → motive n (push t))
    (pull : ∀ {n} (t : Term R n ρ), motive _ t → motive n (pull t))
    (nat : ∀ {n} (m : ℕ), motive n (nat m))
    (float : ∀ {n} (x : FloatLit), motive n (float x))
    (prim : ∀ {n} (p : Prim), motive n (prim p))
    (star : ∀ {n} (t : Term R n ρ), motive _ t → motive n (star t))
    (unborrow : ∀ {n} (t : Term R n ρ), motive _ t → motive n (unborrow t))
    (ref : ∀ {n} (a : Var ρ), motive n (ref a))
    : ∀ {n} (t : Term R n ρ), motive n t
  | _, .var i => var i
  | _, .lam t => lam t (rec' var lam app pair letPair unit letUnit box letBox pack unpack share
      clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .app t₁ t₂ => app t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack unpack
      share clone withBorrow split join push pull nat float prim star unborrow ref t₁) (rec' var
      lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow split join
      push pull nat float prim star unborrow ref t₂)
  | _, .pair t₁ t₂ => pair t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .letPair t₁ t₂ => letPair t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .unit => unit
  | _, .letUnit t₁ t₂ => letUnit t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .box r t => box r t (rec' var lam app pair letPair unit letUnit box letBox pack unpack
      share clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .letBox t₁ t₂ => letBox t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .pack t => pack t (rec' var lam app pair letPair unit letUnit box letBox pack unpack share
      clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .unpack t₁ t₂ => unpack t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .share r t => share r t (rec' var lam app pair letPair unit letUnit box letBox pack unpack
      share clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .clone t₁ t₂ => clone t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .withBorrow t₁ t₂ => withBorrow t₁ t₂ (rec' var lam app pair letPair unit letUnit box
      letBox pack unpack share clone withBorrow split join push pull nat float prim star unborrow
      ref t₁) (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone
      withBorrow split join push pull nat float prim star unborrow ref t₂)
  | _, .split t => split t (rec' var lam app pair letPair unit letUnit box letBox pack unpack
      share clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .join t₁ t₂ => join t₁ t₂ (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t₁)
      (rec' var lam app pair letPair unit letUnit box letBox pack unpack share clone withBorrow
      split join push pull nat float prim star unborrow ref t₂)
  | _, .push t => push t (rec' var lam app pair letPair unit letUnit box letBox pack unpack share
      clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .pull t => pull t (rec' var lam app pair letPair unit letUnit box letBox pack unpack share
      clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .nat m => nat m
  | _, .float x => float x
  | _, .prim p => prim p
  | _, .star t => star t (rec' var lam app pair letPair unit letUnit box letBox pack unpack share
      clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .unborrow t => unborrow t (rec' var lam app pair letPair unit letUnit box letBox pack
      unpack share clone withBorrow split join push pull nat float prim star unborrow ref t)
  | _, .ref a => ref a

/-- Case analysis on terms, one case per constructor of the paper's grammar.  Registered as
the default eliminator for `cases`. -/
@[elab_as_elim, cases_eliminator]
def cases' {motive : Term R n ρ → Sort _}
    (var : ∀ i : Var n, motive (var i))
    (lam : ∀ (t : Term R (n + 1) ρ), motive (lam t))
    (app : ∀ (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive (app t₁ t₂))
    (pair : ∀ (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive (pair t₁ t₂))
    (letPair : ∀ (t₁ : Term R n ρ) (t₂ : Term R (n + 2) ρ), motive (letPair t₁ t₂))
    (unit : motive unit)
    (letUnit : ∀ (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive (letUnit t₁ t₂))
    (box : ∀ (r : R) (t : Term R n ρ), motive (box r t))
    (letBox : ∀ (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive (letBox t₁ t₂))
    (pack : ∀ (t : Term R n ρ), motive (pack t))
    (unpack : ∀ (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive (unpack t₁ t₂))
    (share : ∀ (r : R) (t : Term R n ρ), motive (share r t))
    (clone : ∀ (t₁ : Term R n ρ) (t₂ : Term R (n + 1) ρ), motive (clone t₁ t₂))
    (withBorrow : ∀ (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive (withBorrow t₁ t₂))
    (split : ∀ (t : Term R n ρ), motive (split t))
    (join : ∀ (t₁ : Term R n ρ) (t₂ : Term R n ρ), motive (join t₁ t₂))
    (push : ∀ (t : Term R n ρ), motive (push t))
    (pull : ∀ (t : Term R n ρ), motive (pull t))
    (nat : ∀ (m : ℕ), motive (nat m))
    (float : ∀ (x : FloatLit), motive (float x))
    (prim : ∀ (p : Prim), motive (prim p))
    (star : ∀ (t : Term R n ρ), motive (star t))
    (unborrow : ∀ (t : Term R n ρ), motive (unborrow t))
    (ref : ∀ (a : Var ρ), motive (ref a))
    : ∀ t : Term R n ρ, motive t
  | .var i => var i
  | .lam t => lam t
  | .app t₁ t₂ => app t₁ t₂
  | .pair t₁ t₂ => pair t₁ t₂
  | .letPair t₁ t₂ => letPair t₁ t₂
  | .unit  => unit
  | .letUnit t₁ t₂ => letUnit t₁ t₂
  | .box r t => box r t
  | .letBox t₁ t₂ => letBox t₁ t₂
  | .pack t => pack t
  | .unpack t₁ t₂ => unpack t₁ t₂
  | .share r t => share r t
  | .clone t₁ t₂ => clone t₁ t₂
  | .withBorrow t₁ t₂ => withBorrow t₁ t₂
  | .split t => split t
  | .join t₁ t₂ => join t₁ t₂
  | .push t => push t
  | .pull t => pull t
  | .nat m => nat m
  | .float x => float x
  | .prim p => prim p
  | .star t => star t
  | .unborrow t => unborrow t
  | .ref a => ref a

/-! ### Injectivity of the constructors -/

@[simp] lemma var_inj {i j : Var n} : (var i : Term R n ρ) = var j ↔ i = j := Tm.var_inj
@[simp] lemma lam_inj {t t' : Term R (n + 1) ρ} :
    (lam t : Term R n ρ) = lam t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma app_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R n ρ} :
    (app t₁ t₂ : Term R n ρ) = app t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma pair_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R n ρ} :
    (pair t₁ t₂ : Term R n ρ) = pair t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma letPair_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 2) ρ} :
    (letPair t₁ t₂ : Term R n ρ) = letPair t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma letUnit_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R n ρ} :
    (letUnit t₁ t₂ : Term R n ρ) = letUnit t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma box_inj {r r' : R} {t t' : Term R n ρ} :
    (box r t : Term R n ρ) = box r' t' ↔ r = r' ∧ t = t' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma letBox_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
    (letBox t₁ t₂ : Term R n ρ) = letBox t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma pack_inj {t t' : Term R n ρ} :
    (pack t : Term R n ρ) = pack t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma unpack_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
    (unpack t₁ t₂ : Term R n ρ) = unpack t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma share_inj {r r' : R} {t t' : Term R n ρ} :
    (share r t : Term R n ρ) = share r' t' ↔ r = r' ∧ t = t' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma clone_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
    (clone t₁ t₂ : Term R n ρ) = clone t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma withBorrow_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R n ρ} :
    (withBorrow t₁ t₂ : Term R n ρ) = withBorrow t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma split_inj {t t' : Term R n ρ} :
    (split t : Term R n ρ) = split t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma join_inj {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R n ρ} :
    (join t₁ t₂ : Term R n ρ) = join t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma push_inj {t t' : Term R n ρ} :
    (push t : Term R n ρ) = push t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma pull_inj {t t' : Term R n ρ} :
    (pull t : Term R n ρ) = pull t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma nat_inj {m m' : ℕ} :
    (nat m : Term R n ρ) = nat m' ↔ m = m' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma float_inj {x x' : FloatLit} :
    (float x : Term R n ρ) = float x' ↔ x = x' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma prim_inj {p p' : Prim} :
    (prim p : Term R n ρ) = prim p' ↔ p = p' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma star_inj {t t' : Term R n ρ} :
    (star t : Term R n ρ) = star t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma unborrow_inj {t t' : Term R n ρ} :
    (unborrow t : Term R n ρ) = unborrow t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma ref_inj {a a' : Var ρ} :
    (ref a : Term R n ρ) = ref a' ↔ a = a' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩

end Term

/-! ## Source terms

The source grammar of §3–§5 does not contain the runtime terms `* t`, `unborrow t` and
`ref` of §6.1.  It is given by construction as the generic syntax over a sub-signature,
embedded into `Term` by the generic operator map. -/

/-- The operators of source terms (all operators except the runtime forms of §6.1). -/
inductive SrcOp (R : Type) where
  | lam
  | app
  | pair
  | letPair
  | unit
  | letUnit
  | box (r : R)
  | letBox
  | pack
  | unpack
  | share (r : R)
  | clone
  | withBorrow
  | split
  | join
  | push
  | pull
  | nat (m : ℕ)
  | float (x : FloatLit)
  | prim (p : Prim)

/-- The embedding of source operators into the operators of runtime terms. -/
def SrcOp.toOp {R : Type} {ρ : ℕ} : SrcOp R → Op R ρ
  | .lam => .lam
  | .app => .app
  | .pair => .pair
  | .letPair => .letPair
  | .unit => .unit
  | .letUnit => .letUnit
  | .box r => .box r
  | .letBox => .letBox
  | .pack => .pack
  | .unpack => .unpack
  | .share r => .share r
  | .clone => .clone
  | .withBorrow => .withBorrow
  | .split => .split
  | .join => .join
  | .push => .push
  | .pull => .pull
  | .nat m => .nat m
  | .float x => .float x
  | .prim p => .prim p

lemma SrcOp.toOp_injective {R : Type} {ρ : ℕ} : Function.Injective (SrcOp.toOp (R := R) (ρ := ρ)) := by
  intro o o' h; cases o <;> cases o' <;> simp_all [SrcOp.toOp]

/-- The signature of source terms (a sub-signature of `sig R ρ`). -/
abbrev srcSig (R : Type) : Sig := ⟨SrcOp R, fun o => Op.arity (ρ := 0) o.toOp⟩

/-- Source terms with `n` free variables (no runtime terms, no references). -/
def SrcTerm (R : Type) (n : ℕ) : Type := Tm (srcSig R) n

/-- The embedding of the source signature into the full signature. -/
def srcHom (R : Type) (ρ : ℕ) : SigHom (srcSig R) (sig R ρ) where
  map := SrcOp.toOp
  arity_map o := by cases o <;> rfl

/-- The embedding of source terms into runtime terms (the generic operator map). -/
def SrcTerm.toTerm {R : Type} {n ρ : ℕ} (t : SrcTerm R n) : Term R n ρ := Tm.mapOp (srcHom R ρ) t

lemma SrcTerm.toTerm_injective {R : Type} {n ρ : ℕ} :
    Function.Injective (SrcTerm.toTerm (R := R) (n := n) (ρ := ρ)) :=
  Tm.mapOp_injective (srcHom R ρ) SrcOp.toOp_injective

end FOFU
