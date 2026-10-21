module
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst

/-!
# Values (Section 6.1)

The values of the call-by-value semantics,

  `v ::= (v₁, v₂) | () | [v] | λx. t | n | p | pack ⟨id, v⟩`        (§6.1, "Values")
  `    | * v | unborrow v | ref`                                       (§6.1, runtime),

where `p` ranges over primitives, possibly partially applied to values.  We also count
float literals as values (the paper's examples use them as values, e.g. `4.2`).

* `PrimSpine t p j`: `t` is the primitive `p` applied to `j` values;
* `IsValue t`: `t` is a value; a primitive spine is a value when it is *partially*
  applied (`j < p.arity`), so that e.g. `readArray v` is a value but
  `readArray v₁ v₂` is not.

Note that the grammar makes `unborrow v` a value even though the rule `⤳un&`
reduces `unborrow (*v)`; we follow the grammar.
-/

@[expose] public section

namespace FOFU

variable {R : Type}

mutual

/-- `t` is a value. -/
inductive IsValue : {n : ℕ} → Term R n → Prop where
  | pair {n : ℕ} {v₁ v₂ : Term R n} : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)
  | unit {n : ℕ} : IsValue (.unit : Term R n)
  | box {n : ℕ} {v : Term R n} (r : R) : IsValue v → IsValue (.box r v)
  | lam {n : ℕ} (t : Term R (n + 1)) : IsValue (.lam t)
  | nat {n : ℕ} (m : ℕ) : IsValue (.nat m : Term R n)
  | float {n : ℕ} (x : Float) : IsValue (.float x : Term R n)
  | prim {n : ℕ} {t : Term R n} {p : Prim} {j : ℕ} : PrimSpine t p j → j < p.arity → IsValue t
  | pack {n : ℕ} {v : Term R n} : IsValue v → IsValue (.pack v)
  | star {n : ℕ} {v : Term R n} : IsValue v → IsValue (.star v)
  | unborrow {n : ℕ} {v : Term R n} : IsValue v → IsValue (.unborrow v)
  | ref {n : ℕ} (a : ℕ) : IsValue (.ref a : Term R n)

/-- `PrimSpine t p j`: `t` is the primitive `p` applied to `j` values. -/
inductive PrimSpine : {n : ℕ} → Term R n → Prim → ℕ → Prop where
  | prim {n : ℕ} (p : Prim) : PrimSpine (.prim p : Term R n) p 0
  | app {n : ℕ} {t v : Term R n} {p : Prim} {j : ℕ} :
      PrimSpine t p j → IsValue v → PrimSpine (.app t v) p (j + 1)

end

end FOFU
