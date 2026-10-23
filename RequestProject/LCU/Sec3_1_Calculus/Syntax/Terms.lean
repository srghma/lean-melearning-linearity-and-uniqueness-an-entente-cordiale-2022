module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Types

/-!
# LCU syntax: terms

The operators `Op ρ`, the signature `sig ρ`, the terms `Term n ρ` (generic syntax over
`sig ρ`) and the pattern synonyms `Term.lam`, `Term.app`, … for its constructors.
-/

@[expose] public section

namespace LCU

open Binding

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

end Term

end LCU
