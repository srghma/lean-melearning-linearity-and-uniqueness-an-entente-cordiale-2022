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
inductive EqAxiom : {n : ℕ} → Term n → Term n → Prop where
  | betaLolli {n : ℕ} (t : Term (n + 1)) (t' : Term n) : EqAxiom (app (lam t) t') (subst1 t' t)
  | etaLolli {n : ℕ} (t : Term n) :
      EqAxiom (lam (app (t.rename Fin.succ) (var 0))) t
  | betaTensor {n : ℕ} (t₁ t₂ : Term n) (t : Term (n + 2)) :
      EqAxiom (letPair (pair t₁ t₂) t) (subst2 t₁ t₂ t)
  | etaTensor {n : ℕ} (t : Term n) :
      EqAxiom (letPair t (pair (var (Fin.succ 0)) (var 0))) t
  | betaUnit {n : ℕ} (t : Term n) : EqAxiom (letUnit unit t) t
  | etaUnit {n : ℕ} (t : Term n) : EqAxiom (letUnit t unit) t
  | betaBang {n : ℕ} (t : Term n) (t' : Term (n + 1)) : EqAxiom (letBang (bang t) t') (subst1 t t')
  | etaBang {n : ℕ} (t : Term n) : EqAxiom (letBang t (bang (var 0))) t
  | unitR {n : ℕ} (t : Term n) : EqAxiom (copy t (borrow (var 0))) t
  | unitL {n : ℕ} (v : Term n) (t' : Term (n + 1)) :
      IsValue v → EqAxiom (copy (borrow v) t') (subst1 v t')
  | assoc {n : ℕ} (t₁ : Term n) (t₂ : Term (n + 1)) (t₃ : Term (n + 1)) :
      EqAxiom (copy t₁ (copy t₂ (t₃.rename (Ren.up Fin.succ)))) (copy (copy t₁ t₂) t₃)

/-- The equational theory `≡`: the congruence closure of `EqAxiom`. -/
inductive Equiv : {n : ℕ} → Term n → Term n → Prop where
  | ax {n : ℕ} {t t' : Term n} : EqAxiom t t' → Equiv t t'
  | refl {n : ℕ} (t : Term n) : Equiv t t
  | symm {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv t' t
  | trans {n : ℕ} {t t' t'' : Term n} : Equiv t t' → Equiv t' t'' → Equiv t t''
  | lam {n : ℕ} {t t' : Term (n + 1)} : Equiv t t' → Equiv (lam t) (lam t')
  | app {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (app t₁ t₂) (app t₁' t₂')
  | pair {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (pair t₁ t₂) (pair t₁' t₂')
  | letPair {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 2)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letPair t₁ t₂) (letPair t₁' t₂')
  | letUnit {n : ℕ} {t₁ t₁' t₂ t₂' : Term n} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letUnit t₁ t₂) (letUnit t₁' t₂')
  | bang {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (bang t) (bang t')
  | letBang {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 1)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letBang t₁ t₂) (letBang t₁' t₂')
  | borrow {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (borrow t) (borrow t')
  | copy {n : ℕ} {t₁ t₁' : Term n} {t₂ t₂' : Term (n + 1)} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (copy t₁ t₂) (copy t₁' t₂')
  | star {n : ℕ} {t t' : Term n} : Equiv t t' → Equiv (star t) (star t')

@[inherit_doc] infix:50 " ≡ₗ " => Equiv

end LCU
