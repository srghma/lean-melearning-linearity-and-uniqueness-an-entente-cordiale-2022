module
public import RequestProject.LCU.Sec3_1_Calculus.Context

/-!
# Typing rules of the LCU calculus (Figure 1, Section 3.3 and runtime rules)

`HasType Γ t A` formalises the judgment `Γ ⊢ t : A`.

The rules are exactly those of Figure 1, plus the axiomatic rules for the array
primitives of Section 3.3 (with built-in weakening) and typing of numeric literals.
We additionally include the runtime rule for array references `a` (Section 3.4):
the paper only says these are "akin to a variable rule" (the precise rules are in an
appendix that is not part of the provided text), so we choose:

* `[Γ], a : Array A ⊢ a : Array A` (and likewise `[Γ], a : [Array A] ⊢ a : Array A`).

Moreover, in the rule `nec` the premise `∅ ⊢ t : A` is read as "no *variable*
assumptions"; the array references of the conclusion are passed on to the premise.
For source programs (no array references) all of these rules coincide with the paper's.

## Encoding of the contexts of the rules

* The paper's `[Γ], x : A` (variable `x` linear, everything else non-linear) is the
  structural judgment `Γ.vars.Pick NonLin i (some (.lin A))` (from
  `RequestProject/Common/Ctx.lean`: the variable `i` carries `x : A` and every other
  variable is non-linear), together with `Γ.refs.All NonLin`.  There is no side condition
  quantifying over the other variables.
* A premise with an extended context `Γ, x : A` uses `Γ.cons (some (.lin A))`, and the
  body of the binder refers to `x` as `Var.zero`.
* A conclusion `Γ₁ + Γ₂ ⊢ …` is a context `Γ` with a proof of `Γ₁.Add Γ₂ Γ`.
-/

@[expose] public section

namespace LCU

/-! ## Types of the primitives -/

/-- Types of the array primitives (Section 3.3):
```
newArray    : ℕ ⊸ *(Array 𝔽)
readArray   : *(Array 𝔽) ⊸ ℕ ⊸ 𝔽 ⊗ *(Array 𝔽)
writeArray  : *(Array 𝔽) ⊸ ℕ ⊸ 𝔽 ⊸ *(Array 𝔽)
deleteArray : *(Array 𝔽) ⊸ 1
``` -/
def Prim.ty : Prim → Ty
  | .newArray => .nat ⊸ .star (.array .float)
  | .readArray => .star (.array .float) ⊸ .nat ⊸ (.float ⊗ .star (.array .float))
  | .writeArray => .star (.array .float) ⊸ .nat ⊸ .float ⊸ .star (.array .float)
  | .deleteArray => .star (.array .float) ⊸ .unit

/-! ## The typing judgment -/

open Term in
/-- The typing judgment `Γ ⊢ t : A` of the LCU calculus. -/
inductive HasType : {n ρ : ℕ} → TCtx n ρ → Term n ρ → Ty → Prop where
  /-- `[Γ], x : A ⊢ x : A` -/
  | var {n ρ : ℕ} {Γ : TCtx n ρ} {i : Var n} {A : Ty} :
      Γ.vars.Pick NonLin i (some (.lin A)) → Γ.refs.All NonLin → HasType Γ (var i) A
  /-- `Γ, x : A ⊢ t : B` gives `Γ ⊢ λx. t : A ⊸ B` -/
  | abs {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term (n + 1) ρ} {A B : Ty} :
      HasType (Γ.cons (some (.lin A))) t B → HasType Γ (lam t) (A ⊸ B)
  /-- `Γ₁ ⊢ t₁ : A ⊸ B` and `Γ₂ ⊢ t₂ : A` give `Γ₁ + Γ₂ ⊢ t₁ t₂ : B` -/
  | app {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {A B : Ty} :
      HasType Γ₁ t₁ (A ⊸ B) → HasType Γ₂ t₂ A → Γ₁.Add Γ₂ Γ → HasType Γ (app t₁ t₂) B
  /-- `⊗I` -/
  | tensorI {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {A B : Ty} :
      HasType Γ₁ t₁ A → HasType Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasType Γ (pair t₁ t₂) (A ⊗ B)
  /-- `⊗E`: `Γ₁ ⊢ t₁ : A ⊗ B` and `Γ₂, x : A, y : B ⊢ t₂ : C` give
  `Γ₁ + Γ₂ ⊢ let (x, y) = t₁ in t₂ : C` -/
  | tensorE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 2) ρ} {A B C : Ty} :
      HasType Γ₁ t₁ (A ⊗ B) → HasType ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      Γ₁.Add Γ₂ Γ → HasType Γ (letPair t₁ t₂) C
  /-- `1I`: `[Γ] ⊢ unit : 1` -/
  | unitI {n ρ : ℕ} {Γ : TCtx n ρ} : Γ.AllNonLin → HasType Γ unit .unit
  /-- `1E` -/
  | unitE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ t₂ : Term n ρ} {B : Ty} :
      HasType Γ₁ t₁ .unit → HasType Γ₂ t₂ B → Γ₁.Add Γ₂ Γ → HasType Γ (letUnit t₁ t₂) B
  /-- dereliction: `Γ, x : A ⊢ t : B` gives `Γ, x : [A] ⊢ t : B` -/
  | der {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {i : Var n} {A B : Ty} :
      HasType Γ t B → Γ.vars.Lookup i (some (.lin A)) →
      HasType (Γ.setVar i (some (.nonlin A))) t B
  /-- `!I`: `[Γ] ⊢ t : A` gives `[Γ] ⊢ !t : !A` -/
  | bangI {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      Γ.AllNonLin → HasType Γ t A → HasType Γ (bang t) (.bang A)
  /-- `!E`: `Γ₁ ⊢ t₁ : !A` and `Γ₂, x : [A] ⊢ t₂ : B` give
  `Γ₁ + Γ₂ ⊢ let! x = t₁ in t₂ : B` -/
  | bangE {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 1) ρ} {A B : Ty} :
      HasType Γ₁ t₁ (.bang A) → HasType (Γ₂.cons (some (.nonlin A))) t₂ B →
      Γ₁.Add Γ₂ Γ → HasType Γ (letBang t₁ t₂) B
  /-- borrow: `Γ ⊢ t : *A` gives `Γ ⊢ &t : !A` -/
  | borrow {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      HasType Γ t (.star A) → HasType Γ (borrow t) (.bang A)
  /-- copy: `Γ₁ ⊢ t₁ : !A` and `Γ₂, x : *A ⊢ t₂ : !B` give
  `Γ₁ + Γ₂ ⊢ copy t₁ as x in t₂ : !B` -/
  | copy {n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 1) ρ} {A B : Ty} :
      HasType Γ₁ t₁ (.bang A) → HasType (Γ₂.cons (some (.lin (.star A)))) t₂ (.bang B) →
      Γ₁.Add Γ₂ Γ → HasType Γ (copy t₁ t₂) (.bang B)
  /-- necessitation: `∅ ⊢ t : A` gives `[Γ] ⊢ *t : *A` -/
  | nec {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty} :
      HasType Γ.refsOnly t A → Γ.VarsNonLin → HasType Γ (star t) (.star A)
  /-- natural number literals: `[Γ] ⊢ k : ℕ` -/
  | natI {n ρ : ℕ} {Γ : TCtx n ρ} {k : ℕ} : Γ.AllNonLin → HasType Γ (nat k) .nat
  /-- float literals: `[Γ] ⊢ x : 𝔽` -/
  | floatI {n ρ : ℕ} {Γ : TCtx n ρ} {x : FloatLit} : Γ.AllNonLin → HasType Γ (float x) .float
  /-- array primitives: `[Γ] ⊢ p : Prim.ty p` -/
  | prim {n ρ : ℕ} {Γ : TCtx n ρ} {p : Prim} : Γ.AllNonLin → HasType Γ (prim p) p.ty
  /-- runtime array references: `[Γ], a : Array A ⊢ a : Array A` (the hypothesis of `a`
  may be linear or non-linear) -/
  | ref {n ρ : ℕ} {Γ : TCtx n ρ} {a : Var ρ} {h : Hyp ArrTy} :
      Γ.refs.Pick NonLin a (some h) → Γ.vars.All NonLin → HasType Γ (ref a) h.ty.toTy

@[inherit_doc] notation:40 Γ " ⊢ " t " ∶ " A => HasType Γ t A

end LCU
