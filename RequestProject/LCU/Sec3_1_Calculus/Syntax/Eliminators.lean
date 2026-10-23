module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax.Terms

/-!
# LCU syntax: eliminators and injectivity for terms

`Term.rec'` and `Term.cases'`, the default `induction` / `cases` eliminators with one case
per constructor of the paper's grammar, and injectivity of the constructors.
-/

@[expose] public section

namespace LCU

open Binding

namespace Term

variable {n ρ : ℕ}

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

end LCU
