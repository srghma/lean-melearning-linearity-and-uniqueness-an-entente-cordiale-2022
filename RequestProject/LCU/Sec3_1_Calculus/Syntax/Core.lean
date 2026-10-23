module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Terms

/-!
# LCU syntax: the core grammars of Section 3.1

`CoreTy` and `CoreTerm n`, the grammars of the core calculus without the extensions of
Sections 3.3 and 3.4, with their embeddings into `Ty` and `Term n ρ`.
-/

@[expose] public section

namespace LCU

open Binding

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
