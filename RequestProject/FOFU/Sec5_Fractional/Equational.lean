module
public import RequestProject.FOFU.Sec6_1_Preliminaries.Values

/-!
# Equational theory (§4 and §5.1)

The axioms of the equational theory of the paper:

* (§4) `(β*)`   `clone (share v) as x in t ≡ t [pack ⟨id̅, v⟩ / x]` for values `v`;
* (§4) `(*assoc)` `clone t₁ as x in (clone t₂ as y in t₃)
                   ≡ clone (clone t₁ as x in t₂) as y in t₃` for `x ∉ FV(t₃)`;
* (§5.1) `withBorrow (λx. x) t ≡ t`;
* (§5.1) `withBorrow (λx. f (g x)) t ≡ withBorrow f (withBorrow g t)`;
* (§5.1) `let (x, y) = split t in join x y ≡ t`;
* (§5.1) `split (join t₁ t₂) ≡ (t₁, t₂)`.

`Equiv t₁ t₂` (notation `t₁ ≡ t₂`) is their closure under reflexivity, symmetry,
transitivity and congruence for every term former.  (The paper presents the axioms
across two sections; they are collected in this single inductive type.)

In de Bruijn form, "`x ∉ FV(t₃)`" is expressed by weakening `t₃` past `x`, and the
`f`, `g` of the composition law are weakened under the `λ`.
-/

@[expose] public section

namespace FOFU

open Term

variable {R : Type}

/-- The axioms of the equational theory. -/
inductive EqAxiom : {n ρ : ℕ} → Term R n ρ → Term R n ρ → Prop where
  /-- `(β*)` (§4) -/
  | betaStar {n ρ : ℕ} {v : Term R n ρ} (r : R) (t : Term R (n + 1) ρ) :
      IsValue v → EqAxiom (clone (share r v) t) (t.subst1 (pack v))
  /-- `(*assoc)` (§4) -/
  | starAssoc {n ρ : ℕ} (t₁ : Term R n ρ) (t₂ t₃ : Term R (n + 1) ρ) :
      EqAxiom (clone t₁ (clone t₂ (t₃.rename (Ren.up Var.succ)))) (clone (clone t₁ t₂) t₃)
  /-- `withBorrow (λx. x) t ≡ t` (§5.1) -/
  | withBorrowId {n ρ : ℕ} (t : Term R n ρ) : EqAxiom (withBorrow (lam (var 0)) t) t
  /-- `withBorrow (λx. f (g x)) t ≡ withBorrow f (withBorrow g t)` (§5.1) -/
  | withBorrowComp {n ρ : ℕ} (f g t : Term R n ρ) :
      EqAxiom (withBorrow (lam (app (f.rename Var.succ) (app (g.rename Var.succ) (var 0)))) t)
        (withBorrow f (withBorrow g t))
  /-- `let (x, y) = split t in join x y ≡ t` (§5.1) -/
  | splitJoin {n ρ : ℕ} (t : Term R n ρ) : EqAxiom (letPair (split t) (join (var 1) (var 0))) t
  /-- `split (join t₁ t₂) ≡ (t₁, t₂)` (§5.1) -/
  | joinSplit {n ρ : ℕ} (t₁ t₂ : Term R n ρ) : EqAxiom (split (join t₁ t₂)) (pair t₁ t₂)

/-- The equational theory `≡`: the congruence closure of `EqAxiom`. -/
inductive Equiv : {n ρ : ℕ} → Term R n ρ → Term R n ρ → Prop where
  | ax {n ρ : ℕ} {t t' : Term R n ρ} : EqAxiom t t' → Equiv t t'
  | refl {n ρ : ℕ} (t : Term R n ρ) : Equiv t t
  | symm {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv t' t
  | trans {n ρ : ℕ} {t t' t'' : Term R n ρ} : Equiv t t' → Equiv t' t'' → Equiv t t''
  | lam {n ρ : ℕ} {t t' : Term R (n + 1) ρ} : Equiv t t' → Equiv (lam t) (lam t')
  | app {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term R n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (app t₁ t₂) (app t₁' t₂')
  | pair {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term R n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (pair t₁ t₂) (pair t₁' t₂')
  | letPair {n ρ : ℕ} {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 2) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letPair t₁ t₂) (letPair t₁' t₂')
  | letUnit {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term R n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letUnit t₁ t₂) (letUnit t₁' t₂')
  | box {n ρ : ℕ} (r : R) {t t' : Term R n ρ} : Equiv t t' → Equiv (box r t) (box r t')
  | letBox {n ρ : ℕ} {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (letBox t₁ t₂) (letBox t₁' t₂')
  | pack {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (pack t) (pack t')
  | unpack {n ρ : ℕ} {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (unpack t₁ t₂) (unpack t₁' t₂')
  | share {n ρ : ℕ} (r : R) {t t' : Term R n ρ} : Equiv t t' → Equiv (share r t) (share r t')
  | clone {n ρ : ℕ} {t₁ t₁' : Term R n ρ} {t₂ t₂' : Term R (n + 1) ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (clone t₁ t₂) (clone t₁' t₂')
  | withBorrow {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term R n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (withBorrow t₁ t₂) (withBorrow t₁' t₂')
  | split {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (split t) (split t')
  | join {n ρ : ℕ} {t₁ t₁' t₂ t₂' : Term R n ρ} :
      Equiv t₁ t₁' → Equiv t₂ t₂' → Equiv (join t₁ t₂) (join t₁' t₂')
  | push {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (push t) (push t')
  | pull {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (pull t) (pull t')
  | star {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (star t) (star t')
  | unborrow {n ρ : ℕ} {t t' : Term R n ρ} : Equiv t t' → Equiv (unborrow t) (unborrow t')

@[inherit_doc] infix:50 " ≡ " => Equiv

end FOFU
