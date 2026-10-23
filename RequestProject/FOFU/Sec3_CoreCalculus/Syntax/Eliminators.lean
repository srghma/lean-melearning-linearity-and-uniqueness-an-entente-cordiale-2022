module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax.Terms

/-!
# Syntax: eliminators and injectivity for terms

`Term.rec'` and `Term.cases'`, the default `induction` / `cases` eliminators with one case
per constructor of the paper's grammar, and injectivity of the constructors.
-/

@[expose] public section

namespace FOFU

open Binding

namespace Term

variable {R : Type} {n ρ : ℕ}

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

end FOFU
