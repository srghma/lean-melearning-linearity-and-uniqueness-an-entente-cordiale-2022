module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Types

/-!
# Syntax: terms

The operators `Op R ρ`, the signature `sig R ρ`, the terms `Term R n ρ` (generic syntax
over `sig R ρ`) and the pattern synonyms `Term.lam`, `Term.app`, … for its constructors.
-/

@[expose] public section

namespace FOFU

open Binding

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

end Term

end FOFU
