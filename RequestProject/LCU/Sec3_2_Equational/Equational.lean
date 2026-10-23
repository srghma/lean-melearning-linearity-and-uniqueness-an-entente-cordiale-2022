module
public import RequestProject.LCU.Sec3_1_Calculus.Substitution
public import RequestProject.LCU.Sec3_1_Calculus.Values

/-!
# Equational theory (Section 3.2)

The equational theory `t₁ ≡ t₂` of the LCU calculus: the standard `βη`-equalities of
the multiplicative linear λ-calculus fragment, `β!`/`η!`, and the relative monad
laws `unitR`, `unitL`, `assoc` for the uniqueness fragment, closed under
equivalence and congruence.

This file only contains the definitions:

* `EqAxiom l r`: the axioms, in de Bruijn form;
* `Equiv t₁ t₂` (notation `t₁ ≡ₗ t₂`): their closure under reflexivity, symmetry,
  transitivity and congruence for every term former.

That the axioms preserve typing is proved in `EqAxiomTyping.lean`.
-/

@[expose] public section

namespace LCU

open Term

/-- The axioms of the equational theory, `l ≡ r`. In de Bruijn notation:

* `(β⊸)` `(λx. t) t' ≡ [t'/x]t` and `(η⊸)` `λx. t x ≡ t` (`x` not free in `t`);
* `(β⊗)` `let (x, y) = (t₁, t₂) in t ≡ [t₁/x, t₂/y]t` and
  `(η⊗)` `let (x, y) = t in (x, y) ≡ t`;
* `(β1)` `let unit = unit in t ≡ t` and `(η1)` `let unit = t in unit ≡ t`;
* `(β!)` `let! x = !t in t' ≡ [t/x]t'` and `(η!)` `let! x = t in !x ≡ t`;
* `(unitR)` `copy t as x in &x ≡ t`;
* `(unitL)` `copy &v as x in t' ≡ [v/x]t'` for values `v`;
* `(assoc)` `copy t₁ as x in (copy t₂ as y in t₃) ≡ copy (copy t₁ as x in t₂) as y in t₃`
  where `x` is not free in `t₃` (in de Bruijn form, the left-hand `t₃` is a weakening
  of the right-hand one). -/
inductive EqAxiom : {n ρ : ℕ} → Term n ρ → Term n ρ → Prop where
  | betaLolli {n ρ : ℕ} (t : Term (n + 1) ρ) (t' : Term n ρ) : EqAxiom (app (lam t) t') (t.subst1 t')
  | etaLolli {n ρ : ℕ} (t : Term n ρ) :
      EqAxiom (lam (app (t.rename Var.succ) (var .zero))) t
  | betaTensor {n ρ : ℕ} (t₁ t₂ : Term n ρ) (t : Term (n + 2) ρ) :
      EqAxiom (letPair (pair t₁ t₂) t) (t.subst2 t₁ t₂)
  | etaTensor {n ρ : ℕ} (t : Term n ρ) :
      EqAxiom (letPair t (pair (var (Var.succ .zero)) (var .zero))) t
  | betaUnit {n ρ : ℕ} (t : Term n ρ) : EqAxiom (letUnit unit t) t
  | etaUnit {n ρ : ℕ} (t : Term n ρ) : EqAxiom (letUnit t unit) t
  | betaBang {n ρ : ℕ} (t : Term n ρ) (t' : Term (n + 1) ρ) : EqAxiom (letBang (bang t) t') (t'.subst1 t)
  | etaBang {n ρ : ℕ} (t : Term n ρ) : EqAxiom (letBang t (bang (var .zero))) t
  | unitR {n ρ : ℕ} (t : Term n ρ) : EqAxiom (copy t (borrow (var .zero))) t
  | unitL {n ρ : ℕ} (v : Term n ρ) (t' : Term (n + 1) ρ) :
      IsValue v → EqAxiom (copy (borrow v) t') (t'.subst1 v)
  | assoc {n ρ : ℕ} (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) (t₃ : Term (n + 1) ρ) :
      EqAxiom (copy t₁ (copy t₂ (t₃.rename (Ren.up Var.succ)))) (copy (copy t₁ t₂) t₃)

/-- The equational theory `≡`: the congruence closure of `EqAxiom`. -/
inductive Equiv : {n ρ : ℕ} → Term n ρ → Term n ρ → Prop where
  | ax {n ρ : ℕ} {t t' : Term n ρ} : EqAxiom t t' → Equiv t t'
  | refl {n ρ : ℕ} (t : Term n ρ) : Equiv t t
  | symm {n ρ : ℕ} {t t' : Term n ρ} : Equiv t t' → Equiv t' t
  | trans {n ρ : ℕ} {t t' t'' : Term n ρ} : Equiv t t' → Equiv t' t'' → Equiv t t''
  | lam {n ρ : ℕ} {t t' : Term (n + 1) ρ} : Equiv t t' → Equiv (lam t) (lam t')
  | app {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (app t₁ t₂) (app t₁' t₂')
  | pair {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (pair t₁ t₂) (pair t₁' t₂')
  | letPair {n ρ : ℕ} {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 2) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letPair t₁ t₂) (letPair t₁' t₂')
  | letUnit {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letUnit t₁ t₂) (letUnit t₁' t₂')
  | bang {n ρ : ℕ} {t t' : Term n ρ} : Equiv t t' → Equiv (bang t) (bang t')
  | letBang {n ρ : ℕ} {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 1) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letBang t₁ t₂) (letBang t₁' t₂')
  | borrow {n ρ : ℕ} {t t' : Term n ρ} : Equiv t t' → Equiv (borrow t) (borrow t')
  | copy {n ρ : ℕ} {t₁ t₁' : Term n ρ} {t₂ t₂' : Term (n + 1) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (copy t₁ t₂) (copy t₁' t₂')
  | star {n ρ : ℕ} {t t' : Term n ρ} : Equiv t t' → Equiv (star t) (star t')

@[inherit_doc] infix:50 " ≡ₗ " => Equiv

end LCU
