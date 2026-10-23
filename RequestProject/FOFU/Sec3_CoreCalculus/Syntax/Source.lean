module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Terms

/-!
# Syntax: source terms

The source grammar `SrcTerm R n` (all constructors except the runtime forms of §6.1),
embedded into `Term` by the generic operator map (`SrcTerm.toTerm`, injective).
-/

@[expose] public section

namespace FOFU

open Binding

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
