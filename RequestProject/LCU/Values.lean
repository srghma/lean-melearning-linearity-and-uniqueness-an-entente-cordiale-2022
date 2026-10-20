module
public import RequestProject.LCU.Syntax

/-!
# Values

Value terms of the heap model (Theorem 6):
`v ::= (t₁, t₂) | unit | *t | !t | λx. t | i | a | p`
where `i` are numeric literals, `a` array references and `p` partially-applied
primitives (e.g. `newArray`, `readArray`, `readArray (*a)`).
-/

@[expose] public section

namespace LCU

open Term

/-- The value sub-grammar. Partially applied primitives are primitives applied to
fewer arguments than their arity, where the supplied arguments are values. -/
inductive IsValue : {n : ℕ} → Term n → Prop where
  | pair {n : ℕ} (t₁ t₂ : Term n) : IsValue (pair t₁ t₂)
  | unit {n : ℕ} : IsValue (unit : Term n)
  | star {n : ℕ} (t : Term n) : IsValue (star t)
  | bang {n : ℕ} (t : Term n) : IsValue (bang t)
  | lam {n : ℕ} (t : Term (n + 1)) : IsValue (lam t)
  | nat {n : ℕ} (k : ℕ) : IsValue (nat k : Term n)
  | float {n : ℕ} (x : Float) : IsValue (float x : Term n)
  | ref {n : ℕ} (a : ℕ) : IsValue (ref a : Term n)
  | prim {n : ℕ} (p : Prim) : IsValue (prim p : Term n)
  | readArray₁ {n : ℕ} {v : Term n} : IsValue v → IsValue (app (prim .readArray) v)
  | writeArray₁ {n : ℕ} {v : Term n} : IsValue v → IsValue (app (prim .writeArray) v)
  | writeArray₂ {n : ℕ} {v₁ v₂ : Term n} :
      IsValue v₁ → IsValue v₂ → IsValue (app (app (prim .writeArray) v₁) v₂)

end LCU
