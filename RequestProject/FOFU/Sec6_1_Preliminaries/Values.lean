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
inductive IsValue : {n ρ : ℕ} → Term R n ρ → Prop where
  | pair {n ρ : ℕ} {v₁ v₂ : Term R n ρ} : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)
  | unit {n ρ : ℕ} : IsValue (.unit : Term R n ρ)
  | box {n ρ : ℕ} {v : Term R n ρ} (r : R) : IsValue v → IsValue (.box r v)
  | lam {n ρ : ℕ} (t : Term R (n + 1) ρ) : IsValue (.lam t)
  | nat {n ρ : ℕ} (m : ℕ) : IsValue (.nat m : Term R n ρ)
  | float {n ρ : ℕ} (x : FloatLit) : IsValue (.float x : Term R n ρ)
  | prim {n ρ : ℕ} {t : Term R n ρ} {p : Prim} {j : ℕ} : PrimSpine t p j → j < p.arity → IsValue t
  | pack {n ρ : ℕ} {v : Term R n ρ} : IsValue v → IsValue (.pack v)
  | star {n ρ : ℕ} {v : Term R n ρ} : IsValue v → IsValue (.star v)
  | unborrow {n ρ : ℕ} {v : Term R n ρ} : IsValue v → IsValue (.unborrow v)
  | ref {n ρ : ℕ} (a : Var ρ) : IsValue (.ref a : Term R n ρ)

/-- `PrimSpine t p j`: `t` is the primitive `p` applied to `j` values. -/
inductive PrimSpine : {n ρ : ℕ} → Term R n ρ → Prim → ℕ → Prop where
  | prim {n ρ : ℕ} (p : Prim) : PrimSpine (.prim p : Term R n ρ) p 0
  | app {n ρ : ℕ} {t v : Term R n ρ} {p : Prim} {j : ℕ} :
      PrimSpine t p j → IsValue v → PrimSpine (.app t v) p (j + 1)

end

end FOFU
