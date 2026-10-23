module
public import RequestProject.LCU.Sec3_1_Calculus.RenameSubst

/-!
# Values

Value terms of the heap model (Theorem 6):
`v ::= (t₁, t₂) | unit | *t | !t | λx. t | i | a | p`
where `i` are numeric literals, `a` array references and `p` partially-applied
primitives (e.g. `newArray`, `readArray`, `readArray (*a)`).

The value sub-grammar is given *by construction*: `Value n ρ` is an inductive type
whose inhabitants are exactly the values (with `n` free variables), and the
partially applied primitives form the mutually defined type `PrimFun n ρ`, whose
constructors only allow applying a primitive to strictly fewer arguments than its
arity, each argument being itself a value.  Both embed into `Term n ρ`
(`Value.toTerm`, `PrimFun.toTerm`), and the predicates `IsValue t` / `IsPrimFun t`
just say that `t` lies in the image of the corresponding embedding.
-/

@[expose] public section

namespace LCU

open Term

/-! ## The value grammar -/

mutual

/-- The value sub-grammar `v ::= (t₁, t₂) | unit | *t | !t | λx. t | i | a | p`. -/
inductive Value (n ρ : ℕ) : Type where
  /-- `(t₁, t₂)` -/
  | pair (t₁ t₂ : Term n ρ)
  /-- `unit` -/
  | unit
  /-- `*t` -/
  | star (t : Term n ρ)
  /-- `!t` -/
  | bang (t : Term n ρ)
  /-- `λx. t` -/
  | lam (t : Term (n + 1) ρ)
  /-- natural number literals -/
  | nat (k : ℕ)
  /-- float literals -/
  | float (x : FloatLit)
  /-- runtime array references `a` -/
  | ref (a : Var ρ)
  /-- partially applied primitives `p` -/
  | prim (p : PrimFun n ρ)

/-- Partially applied primitives: a primitive applied to fewer arguments than its arity,
all of which are values.  (`newArray` and `deleteArray` have arity `1`, `readArray`
arity `2` and `writeArray` arity `3`.) -/
inductive PrimFun (n ρ : ℕ) : Type where
  /-- a primitive applied to no argument -/
  | const (p : Prim)
  /-- `readArray v` -/
  | readArray₁ (v : Value n ρ)
  /-- `writeArray v` -/
  | writeArray₁ (v : Value n ρ)
  /-- `writeArray v₁ v₂` -/
  | writeArray₂ (v₁ v₂ : Value n ρ)

end

mutual

/-- The embedding of values into terms. -/
def Value.toTerm {n ρ : ℕ} : Value n ρ → Term n ρ
  | .pair t₁ t₂ => .pair t₁ t₂
  | .unit => .unit
  | .star t => .star t
  | .bang t => .bang t
  | .lam t => .lam t
  | .nat k => .nat k
  | .float x => .float x
  | .ref a => .ref a
  | .prim p => p.toTerm

/-- The embedding of partially applied primitives into terms. -/
def PrimFun.toTerm {n ρ : ℕ} : PrimFun n ρ → Term n ρ
  | .const p => .prim p
  | .readArray₁ v => .app (.prim .readArray) v.toTerm
  | .writeArray₁ v => .app (.prim .writeArray) v.toTerm
  | .writeArray₂ v₁ v₂ => .app (.app (.prim .writeArray) v₁.toTerm) v₂.toTerm

end

instance {n ρ : ℕ} : CoeOut (Value n ρ) (Term n ρ) := ⟨Value.toTerm⟩
instance {n ρ : ℕ} : CoeOut (PrimFun n ρ) (Term n ρ) := ⟨PrimFun.toTerm⟩

attribute [simp] Value.toTerm PrimFun.toTerm

/-- `t` is a value, i.e. it is (the embedding of) an element of the grammar `Value n ρ`. -/
def IsValue {n ρ : ℕ} (t : Term n ρ) : Prop := ∃ v : Value n ρ, v.toTerm = t

/-- `t` is a partially applied primitive, i.e. it is (the embedding of) an element of the
grammar `PrimFun n ρ`. -/
def IsPrimFun {n ρ : ℕ} (t : Term n ρ) : Prop := ∃ f : PrimFun n ρ, f.toTerm = t

/-! ## Introduction lemmas for `IsValue`

One lemma per production of the value grammar, so that `IsValue t` can be proved
without constructing the `Value` explicitly. -/

namespace IsValue

variable {n ρ : ℕ}

lemma toTerm (v : Value n ρ) : IsValue v.toTerm := ⟨v, rfl⟩
lemma pair (t₁ t₂ : Term n ρ) : IsValue (Term.pair t₁ t₂) := ⟨.pair t₁ t₂, rfl⟩
lemma unit : IsValue (Term.unit : Term n ρ) := ⟨.unit, rfl⟩
lemma star (t : Term n ρ) : IsValue (Term.star t) := ⟨.star t, rfl⟩
lemma bang (t : Term n ρ) : IsValue (Term.bang t) := ⟨.bang t, rfl⟩
lemma lam (t : Term (n + 1) ρ) : IsValue (Term.lam t) := ⟨.lam t, rfl⟩
lemma nat (k : ℕ) : IsValue (Term.nat k : Term n ρ) := ⟨.nat k, rfl⟩
lemma float (x : FloatLit) : IsValue (Term.float x : Term n ρ) := ⟨.float x, rfl⟩
lemma ref (a : Var ρ) : IsValue (Term.ref a : Term n ρ) := ⟨.ref a, rfl⟩
lemma prim (p : Prim) : IsValue (Term.prim p : Term n ρ) := ⟨.prim (.const p), rfl⟩
/-- `readArray v` (one of two arguments supplied) is a value. -/
lemma readArray₁ {v : Term n ρ} : IsValue v → IsValue (app (.prim .readArray) v)
  | ⟨w, hw⟩ => ⟨.prim (.readArray₁ w), by simp [hw]⟩
/-- `writeArray v` (one of three arguments supplied) is a value. -/
lemma writeArray₁ {v : Term n ρ} : IsValue v → IsValue (app (.prim .writeArray) v)
  | ⟨w, hw⟩ => ⟨.prim (.writeArray₁ w), by simp [hw]⟩
lemma writeArray₂ {v₁ v₂ : Term n ρ} :
    IsValue v₁ → IsValue v₂ → IsValue (app (app (.prim .writeArray) v₁) v₂)
  | ⟨w₁, h₁⟩, ⟨w₂, h₂⟩ => ⟨.prim (.writeArray₂ w₁ w₂), by simp [h₁, h₂]⟩


end IsValue

section
variable {n ρ : ℕ}

/-! ### Terms outside the value grammar -/

/-- Internal tactic: prove `¬ IsValue t` for a term `t` whose head is not a value former. -/
macro "not_value" : tactic =>
  `(tactic| (rintro ⟨v, hv⟩; cases v <;> (try cases hv) <;> (rename_i f; cases f <;> cases hv)))

lemma not_isValue_var (i : Var n) : ¬ IsValue (Term.var i : Term n ρ) := by
  not_value

lemma not_isValue_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) : ¬ IsValue (Term.letPair t₁ t₂) := by
  not_value

lemma not_isValue_letUnit (t₁ t₂ : Term n ρ) : ¬ IsValue (Term.letUnit t₁ t₂) := by
  not_value

lemma not_isValue_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) : ¬ IsValue (Term.letBang t₁ t₂) := by
  not_value

lemma not_isValue_borrow (t : Term n ρ) : ¬ IsValue (Term.borrow t) := by
  not_value

lemma not_isValue_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) : ¬ IsValue (Term.copy t₁ t₂) := by
  not_value

/-- A β-redex is not a value. -/
lemma not_isValue_app_lam (t : Term (n + 1) ρ) (u : Term n ρ) : ¬ IsValue (Term.app (.lam t) u) := by
  not_value

end

/-! ## Partially applied primitives -/

namespace IsPrimFun

variable {n ρ : ℕ}

lemma prim (p : Prim) : IsPrimFun (Term.prim p : Term n ρ) := ⟨.const p, rfl⟩
lemma readArray₁ {v : Term n ρ} : IsValue v → IsPrimFun (app (.prim .readArray) v)
  | ⟨w, hw⟩ => ⟨.readArray₁ w, by simp [hw]⟩
lemma writeArray₁ {v : Term n ρ} : IsValue v → IsPrimFun (app (.prim .writeArray) v)
  | ⟨w, hw⟩ => ⟨.writeArray₁ w, by simp [hw]⟩
lemma writeArray₂ {v₁ v₂ : Term n ρ} :
    IsValue v₁ → IsValue v₂ → IsPrimFun (app (app (.prim .writeArray) v₁) v₂)
  | ⟨w₁, h₁⟩, ⟨w₂, h₂⟩ => ⟨.writeArray₂ w₁ w₂, by simp [h₁, h₂]⟩

/-- Partially applied primitives are values. -/
lemma isValue {t : Term n ρ} : IsPrimFun t → IsValue t
  | ⟨f, hf⟩ => ⟨.prim f, hf⟩

end IsPrimFun

end LCU

namespace LCU

open Term

/-! ## An induction principle for values

`IsValue.induction` lets one prove a property of all values `t` by giving one case
per production of the value grammar, without mentioning `Value`/`PrimFun`. -/

section Induction

variable {n ρ : ℕ}

/-- The cases of the induction principle for values (a bundle of hypotheses). -/
private structure ValueCases (motive : (t : Term n ρ) → IsValue t → Prop) : Prop where
  pair : ∀ t₁ t₂ : Term n ρ, motive (.pair t₁ t₂) (.pair t₁ t₂)
  unit : motive .unit .unit
  star : ∀ t : Term n ρ, motive (.star t) (.star t)
  bang : ∀ t : Term n ρ, motive (.bang t) (.bang t)
  lam : ∀ t : Term (n + 1) ρ, motive (.lam t) (.lam t)
  nat : ∀ k : ℕ, motive (.nat k) (.nat k)
  float : ∀ x : FloatLit, motive (.float x) (.float x)
  ref : ∀ a : Var ρ, motive (.ref a) (.ref a)
  prim : ∀ p : Prim, motive (.prim p) (.prim p)
  readArray₁ : ∀ (v : Term n ρ) (h : IsValue v), motive v h →
    motive (.app (.prim .readArray) v) (.readArray₁ h)
  writeArray₁ : ∀ (v : Term n ρ) (h : IsValue v), motive v h →
    motive (.app (.prim .writeArray) v) (.writeArray₁ h)
  writeArray₂ : ∀ (v₁ v₂ : Term n ρ) (h₁ : IsValue v₁) (h₂ : IsValue v₂), motive v₁ h₁ →
    motive v₂ h₂ → motive (.app (.app (.prim .writeArray) v₁) v₂) (.writeArray₂ h₁ h₂)

mutual

private theorem Value.induction_aux {motive : (t : Term n ρ) → IsValue t → Prop}
    (c : ValueCases motive) : ∀ v : Value n ρ, motive v.toTerm ⟨v, rfl⟩
  | .pair t₁ t₂ => c.pair t₁ t₂
  | .unit => c.unit
  | .star t => c.star t
  | .bang t => c.bang t
  | .lam t => c.lam t
  | .nat k => c.nat k
  | .float x => c.float x
  | .ref a => c.ref a
  | .prim f => PrimFun.induction_aux c f

private theorem PrimFun.induction_aux {motive : (t : Term n ρ) → IsValue t → Prop}
    (c : ValueCases motive) : ∀ f : PrimFun n ρ, motive f.toTerm ⟨.prim f, rfl⟩
  | .const p => c.prim p
  | .readArray₁ v => c.readArray₁ _ ⟨v, rfl⟩ (Value.induction_aux c v)
  | .writeArray₁ v => c.writeArray₁ _ ⟨v, rfl⟩ (Value.induction_aux c v)
  | .writeArray₂ v₁ v₂ =>
    c.writeArray₂ _ _ ⟨v₁, rfl⟩ ⟨v₂, rfl⟩ (Value.induction_aux c v₁) (Value.induction_aux c v₂)

end

/-- Induction principle for values, following the value grammar. -/
@[elab_as_elim]
theorem IsValue.induction {motive : (t : Term n ρ) → IsValue t → Prop}
    (pair : ∀ t₁ t₂ : Term n ρ, motive (.pair t₁ t₂) (.pair t₁ t₂))
    (unit : motive .unit .unit)
    (star : ∀ t : Term n ρ, motive (.star t) (.star t))
    (bang : ∀ t : Term n ρ, motive (.bang t) (.bang t))
    (lam : ∀ t : Term (n + 1) ρ, motive (.lam t) (.lam t))
    (nat : ∀ k : ℕ, motive (.nat k) (.nat k))
    (float : ∀ x : FloatLit, motive (.float x) (.float x))
    (ref : ∀ a : Var ρ, motive (.ref a) (.ref a))
    (prim : ∀ p : Prim, motive (.prim p) (.prim p))
    (readArray₁ : ∀ (v : Term n ρ) (h : IsValue v), motive v h →
      motive (.app (.prim .readArray) v) (.readArray₁ h))
    (writeArray₁ : ∀ (v : Term n ρ) (h : IsValue v), motive v h →
      motive (.app (.prim .writeArray) v) (.writeArray₁ h))
    (writeArray₂ : ∀ (v₁ v₂ : Term n ρ) (h₁ : IsValue v₁) (h₂ : IsValue v₂), motive v₁ h₁ →
      motive v₂ h₂ → motive (.app (.app (.prim .writeArray) v₁) v₂) (.writeArray₂ h₁ h₂))
    {t : Term n ρ} (h : IsValue t) : motive t h := by
  obtain ⟨v, rfl⟩ := h
  exact Value.induction_aux ⟨pair, unit, star, bang, lam, nat, float, ref, prim, readArray₁,
    writeArray₁, writeArray₂⟩ v

end Induction

end LCU
