module
public import RequestProject.Common.Syntax
public import Lean.Data.Json.Basic

/-!
# The Linear-Cartesian-Unique (LCU) calculus: syntax

Formalisation of Section 3 of *Linearity and Uniqueness: An Entente Cordiale*
(Marshall, Vollmer, Orchard).

## Representation

Terms are intrinsically scoped de Bruijn terms, built with the generic binding layer of
`RequestProject/Common/Syntax.lean`: the term language is described by a signature (its
operators and their binding arities), and `Term n ρ` is the generic `Binding.Tm` over that
signature.  Renaming, substitution and their laws come from the generic layer.

* `Term n ρ` has `n` free variables, `Term.var : Var n → Term n ρ`, so `Term 0 ρ` is the
  type of closed terms.  Binders bind `Var.zero`.
* Runtime array references `a` (Section 3.4) are scoped too: `ρ` is the number of runtime
  references in scope and `Term.ref : Var ρ → Term n ρ`.  Source programs have no
  references: they are terms of `Term n 0`.
* Float literals are `Lean.JsonNumber`s (a mantissa and a decimal exponent, with lawful
  decidable equality), not Lean's built-in `Float`.

The constructors `Term.lam`, `Term.app`, … are pattern synonyms (`@[match_pattern]`) for
the corresponding operator applications, and `Term.rec'` / `Term.cases'` are registered
as the default `induction` / `cases` eliminators, so that terms can be used as if `Term`
were an ordinary inductive type.

## Contents

* `Ty`, `Prim`, `Op`, `Term n ρ`: types, primitives, operators and terms;
* `CoreTy`, `CoreTerm n`: the core grammars of Section 3.1, as separate types embedded
  into `Ty` / `Term n ρ`.  `CoreTerm n` is the generic syntax over a sub-signature, and
  its embedding is the generic operator map `Binding.Tm.mapOp`.
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

/-- The operators of the LCU term language, over `ρ` runtime array references. -/
inductive Op (ρ : ℕ) where
  | lam | app | pair | letPair | unit | letUnit | bang | letBang | borrow | copy | star
  | nat (k : ℕ)
  | float (x : FloatLit)
  | prim (p : Prim)
  | ref (a : Var ρ)
  deriving DecidableEq

/-- Binding arities of the operators: `λx. t` binds one variable in its argument,
`let (x, y) = t₁ in t₂` binds two in its second argument, and so on. -/
def Op.arity {ρ : ℕ} : Op ρ → List ℕ
  | .lam => [1]
  | .app => [0, 0]
  | .pair => [0, 0]
  | .letPair => [0, 2]
  | .unit => []
  | .letUnit => [0, 0]
  | .bang => [0]
  | .letBang => [0, 1]
  | .borrow => [0]
  | .copy => [0, 1]
  | .star => [0]
  | .nat _ => []
  | .float _ => []
  | .prim _ => []
  | .ref _ => []

/-- The signature of the LCU term language. -/
abbrev sig (ρ : ℕ) : Sig := ⟨Op ρ, Op.arity⟩

/-- Terms of the LCU calculus with `n` free variables and `ρ` runtime array references. -/
def Term (n ρ : ℕ) : Type := Tm (sig ρ) n

namespace Term

variable {n ρ : ℕ}

/-- variables `x` -/
@[match_pattern] abbrev var (i : Var n) : Term n ρ := Tm.var i
/-- `λx. t` (the bound variable is `Var.zero` of `t`) -/
@[match_pattern] abbrev lam (t : Term (n + 1) ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .lam (.cons t .nil)
/-- application `t₁ t₂` -/
@[match_pattern] abbrev app (t₁ t₂ : Term n ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .app (.cons t₁ (.cons t₂ .nil))
/-- pairs `(t₁, t₂)` -/
@[match_pattern] abbrev pair (t₁ t₂ : Term n ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .pair (.cons t₁ (.cons t₂ .nil))
/-- `let (x, y) = t₁ in t₂`; in `t₂`, `y` is `Var.zero` and `x` is `Var.succ Var.zero` -/
@[match_pattern] abbrev letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .letPair (.cons t₁ (.cons t₂ .nil))
/-- `unit` -/
@[match_pattern] abbrev unit : Term n ρ := Tm.op (S := sig ρ) .unit .nil
/-- `let unit = t₁ in t₂` -/
@[match_pattern] abbrev letUnit (t₁ t₂ : Term n ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .letUnit (.cons t₁ (.cons t₂ .nil))
/-- `!t` -/
@[match_pattern] abbrev bang (t : Term n ρ) : Term n ρ := Tm.op (S := sig ρ) .bang (.cons t .nil)
/-- `let! x = t₁ in t₂` -/
@[match_pattern] abbrev letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .letBang (.cons t₁ (.cons t₂ .nil))
/-- `&t` -/
@[match_pattern] abbrev borrow (t : Term n ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .borrow (.cons t .nil)
/-- `copy t₁ as x in t₂` -/
@[match_pattern] abbrev copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) : Term n ρ :=
  Tm.op (S := sig ρ) .copy (.cons t₁ (.cons t₂ .nil))
/-- `*t` -/
@[match_pattern] abbrev star (t : Term n ρ) : Term n ρ := Tm.op (S := sig ρ) .star (.cons t .nil)
/-- natural number literals -/
@[match_pattern] abbrev nat (k : ℕ) : Term n ρ := Tm.op (S := sig ρ) (.nat k) .nil
/-- float literals -/
@[match_pattern] abbrev float (x : FloatLit) : Term n ρ := Tm.op (S := sig ρ) (.float x) .nil
/-- the array primitives -/
@[match_pattern] abbrev prim (p : Prim) : Term n ρ := Tm.op (S := sig ρ) (.prim p) .nil
/-- runtime array references `a` -/
@[match_pattern] abbrev ref (a : Var ρ) : Term n ρ := Tm.op (S := sig ρ) (.ref a) .nil

/-- Structural recursion / induction on terms, one case per constructor of the paper's
grammar.  Registered as the default eliminator for `induction`. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : (n : ℕ) → Term n ρ → Sort _}
    (var : ∀ {n} (i : Var n), motive n (var i))
    (lam : ∀ {n} (t : Term (n + 1) ρ), motive _ t → motive n (lam t))
    (app : ∀ {n} (t₁ t₂ : Term n ρ), motive _ t₁ → motive _ t₂ → motive n (app t₁ t₂))
    (pair : ∀ {n} (t₁ t₂ : Term n ρ), motive _ t₁ → motive _ t₂ → motive n (pair t₁ t₂))
    (letPair : ∀ {n} (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ), motive _ t₁ → motive _ t₂ →
      motive n (letPair t₁ t₂))
    (unit : ∀ {n}, motive n unit)
    (letUnit : ∀ {n} (t₁ t₂ : Term n ρ), motive _ t₁ → motive _ t₂ → motive n (letUnit t₁ t₂))
    (bang : ∀ {n} (t : Term n ρ), motive _ t → motive n (bang t))
    (letBang : ∀ {n} (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ), motive _ t₁ → motive _ t₂ →
      motive n (letBang t₁ t₂))
    (borrow : ∀ {n} (t : Term n ρ), motive _ t → motive n (borrow t))
    (copy : ∀ {n} (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ), motive _ t₁ → motive _ t₂ →
      motive n (copy t₁ t₂))
    (star : ∀ {n} (t : Term n ρ), motive _ t → motive n (star t))
    (nat : ∀ {n} (k : ℕ), motive n (nat k))
    (float : ∀ {n} (x : FloatLit), motive n (float x))
    (prim : ∀ {n} (p : Prim), motive n (prim p))
    (ref : ∀ {n} (a : Var ρ), motive n (ref a)) :
    ∀ {n} (t : Term n ρ), motive n t
  | _, .var i => var i
  | _, .lam t => lam t (rec' var lam app pair letPair unit letUnit bang letBang borrow copy
      star nat float prim ref t)
  | _, .app t₁ t₂ => app t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .pair t₁ t₂ => pair t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .letPair t₁ t₂ => letPair t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .unit => unit
  | _, .letUnit t₁ t₂ => letUnit t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .bang t => bang t (rec' var lam app pair letPair unit letUnit bang letBang borrow copy
      star nat float prim ref t)
  | _, .letBang t₁ t₂ => letBang t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .borrow t => borrow t (rec' var lam app pair letPair unit letUnit bang letBang borrow
      copy star nat float prim ref t)
  | _, .copy t₁ t₂ => copy t₁ t₂
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₁)
      (rec' var lam app pair letPair unit letUnit bang letBang borrow copy star nat float prim
        ref t₂)
  | _, .star t => star t (rec' var lam app pair letPair unit letUnit bang letBang borrow copy
      star nat float prim ref t)
  | _, .nat k => nat k
  | _, .float x => float x
  | _, .prim p => prim p
  | _, .ref a => ref a

/-- Case analysis on terms, one case per constructor of the paper's grammar.  Registered as
the default eliminator for `cases`. -/
@[elab_as_elim, cases_eliminator]
def cases' {motive : Term n ρ → Sort _}
    (var : ∀ i : Var n, motive (var i))
    (lam : ∀ t : Term (n + 1) ρ, motive (lam t))
    (app : ∀ t₁ t₂ : Term n ρ, motive (app t₁ t₂))
    (pair : ∀ t₁ t₂ : Term n ρ, motive (pair t₁ t₂))
    (letPair : ∀ (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ), motive (letPair t₁ t₂))
    (unit : motive unit)
    (letUnit : ∀ t₁ t₂ : Term n ρ, motive (letUnit t₁ t₂))
    (bang : ∀ t : Term n ρ, motive (bang t))
    (letBang : ∀ (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ), motive (letBang t₁ t₂))
    (borrow : ∀ t : Term n ρ, motive (borrow t))
    (copy : ∀ (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ), motive (copy t₁ t₂))
    (star : ∀ t : Term n ρ, motive (star t))
    (nat : ∀ k : ℕ, motive (nat k))
    (float : ∀ x : FloatLit, motive (float x))
    (prim : ∀ p : Prim, motive (prim p))
    (ref : ∀ a : Var ρ, motive (ref a)) :
    ∀ t : Term n ρ, motive t
  | .var i => var i
  | .lam t => lam t
  | .app t₁ t₂ => app t₁ t₂
  | .pair t₁ t₂ => pair t₁ t₂
  | .letPair t₁ t₂ => letPair t₁ t₂
  | .unit => unit
  | .letUnit t₁ t₂ => letUnit t₁ t₂
  | .bang t => bang t
  | .letBang t₁ t₂ => letBang t₁ t₂
  | .borrow t => borrow t
  | .copy t₁ t₂ => copy t₁ t₂
  | .star t => star t
  | .nat k => nat k
  | .float x => float x
  | .prim p => prim p
  | .ref a => ref a

/-! ### Injectivity of the constructors

(Distinct constructors can be told apart by `cases` on the equation, or by `simp` after
unfolding the constructors.) -/

section Injectivity

variable {n ρ : ℕ}

@[simp] lemma var_inj {i j : Var n} : (var i : Term n ρ) = var j ↔ i = j := Tm.var_inj
@[simp] lemma lam_inj {t t' : Term (n + 1) ρ} : lam t = lam t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma app_inj {t₁ t₂ t₁' t₂' : Term n ρ} :
    app t₁ t₂ = app t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma pair_inj {t₁ t₂ t₁' t₂' : Term n ρ} :
    pair t₁ t₂ = pair t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma letPair_inj {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 2) ρ} :
    letPair t₁ t₂ = letPair t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma letUnit_inj {t₁ t₂ t₁' t₂' : Term n ρ} :
    letUnit t₁ t₂ = letUnit t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma bang_inj {t t' : Term n ρ} : bang t = bang t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma letBang_inj {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 1) ρ} :
    letBang t₁ t₂ = letBang t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma borrow_inj {t t' : Term n ρ} : borrow t = borrow t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma copy_inj {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 1) ρ} :
    copy t₁ t₂ = copy t₁' t₂' ↔ t₁ = t₁' ∧ t₂ = t₂' :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
@[simp] lemma star_inj {t t' : Term n ρ} : star t = star t' ↔ t = t' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma nat_inj {k k' : ℕ} : (nat k : Term n ρ) = nat k' ↔ k = k' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma float_inj {x x' : FloatLit} : (float x : Term n ρ) = float x' ↔ x = x' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma prim_inj {p p' : Prim} : (prim p : Term n ρ) = prim p' ↔ p = p' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩
@[simp] lemma ref_inj {a a' : Var ρ} : (ref a : Term n ρ) = ref a' ↔ a = a' :=
  ⟨fun h => by cases h; rfl, by rintro rfl; rfl⟩

end Injectivity

end Term

/-! ## The core grammars of Section 3.1

`Ty` and `Term` contain the extensions of Sections 3.3 and 3.4 (arrays, literals,
primitives and runtime references).  The grammars of the core calculus are given
separately, by construction, together with their embeddings. -/

/-- The core types of Section 3.1: `A, B ::= A ⊸ B | A ⊗ B | 1 | !A | *A`. -/
inductive CoreTy where
  | lolli : CoreTy → CoreTy → CoreTy
  | tensor : CoreTy → CoreTy → CoreTy
  | unit : CoreTy
  | bang : CoreTy → CoreTy
  | star : CoreTy → CoreTy
  deriving DecidableEq, Repr

/-- The embedding of core types into the extended types. -/
@[simp] def CoreTy.toTy : CoreTy → Ty
  | .lolli A B => .lolli A.toTy B.toTy
  | .tensor A B => .tensor A.toTy B.toTy
  | .unit => .unit
  | .bang A => .bang A.toTy
  | .star A => .star A.toTy

lemma CoreTy.toTy_injective : Function.Injective CoreTy.toTy := by
  intro A B h
  induction A generalizing B with
  | lolli A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [CoreTy.toTy, Ty.lolli.injEq, reduceCtorEq] at h
    rw [ih₁ h.1, ih₂ h.2]
  | tensor A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [CoreTy.toTy, Ty.tensor.injEq, reduceCtorEq] at h
    rw [ih₁ h.1, ih₂ h.2]
  | unit => cases B <;> simp_all
  | bang A ih => cases B <;> simp only [CoreTy.toTy, Ty.bang.injEq, reduceCtorEq] at h; rw [ih h]
  | star A ih => cases B <;> simp only [CoreTy.toTy, Ty.star.injEq, reduceCtorEq] at h; rw [ih h]

/-- The operators of the core terms of Section 3.1:
`t ::= x | λx. t | t₁ t₂ | (t₁, t₂) | let (x, y) = t₁ in t₂ | unit | let unit = t₁ in t₂
     | !t | let! x = t₁ in t₂ | &t | copy t₁ as x in t₂ | *t`. -/
inductive CoreOp where
  | lam | app | pair | letPair | unit | letUnit | bang | letBang | borrow | copy | star
  deriving DecidableEq

/-- The embedding of the core operators into the operators of the extended language. -/
def CoreOp.toOp {ρ : ℕ} : CoreOp → Op ρ
  | .lam => .lam
  | .app => .app
  | .pair => .pair
  | .letPair => .letPair
  | .unit => .unit
  | .letUnit => .letUnit
  | .bang => .bang
  | .letBang => .letBang
  | .borrow => .borrow
  | .copy => .copy
  | .star => .star

lemma CoreOp.toOp_injective {ρ : ℕ} : Function.Injective (CoreOp.toOp (ρ := ρ)) := by
  intro o o' h; cases o <;> cases o' <;> first | rfl | cases h

/-- The signature of the core terms (a sub-signature of `sig ρ`). -/
abbrev coreSig : Sig := ⟨CoreOp, fun o => Op.arity (ρ := 0) o.toOp⟩

/-- The core terms of Section 3.1 with `n` free variables (no runtime references). -/
def CoreTerm (n : ℕ) : Type := Tm coreSig n

/-- The embedding of the core signature into the full signature. -/
def coreHom (ρ : ℕ) : SigHom coreSig (sig ρ) where
  map := CoreOp.toOp
  arity_map o := by cases o <;> rfl

/-- The embedding of core terms into the extended terms (the generic operator map). -/
def CoreTerm.toTerm {n ρ : ℕ} (t : CoreTerm n) : Term n ρ := Tm.mapOp (coreHom ρ) t

lemma CoreTerm.toTerm_injective {n ρ : ℕ} :
    Function.Injective (CoreTerm.toTerm (n := n) (ρ := ρ)) :=
  Tm.mapOp_injective (coreHom ρ) CoreOp.toOp_injective

end LCU
