module
public import RequestProject.LCU.Sec3_4_HeapModel.Heap

/-!
# The operational heap model (Section 3.4): heap-context compatibility

`Compat H Γ` (`H ⋈ Γ`): heap-context compatibility (Definition 3).
-/

@[expose] public section

namespace LCU

open Term

/-! ## Heap-context compatibility (Definition 3) -/

/-- Heap-context compatibility `H ⋈ Γ`. -/
inductive Compat : {n ρ : ℕ} → Heap n ρ → TCtx n ρ → Prop where
  /-- `∅ ⋈ ∅` -/
  | empty {n ρ : ℕ} : Compat (Heap.empty : Heap n ρ) TCtx.empty
  /-- `H ⋈ Γ` gives `H, a ↦_r arr ⋈ Γ, a : Array A` -/
  | ref {n ρ : ℕ} {H : Heap n ρ} {Γ : TCtx n ρ} {a : Var ρ} {e : ArrEntry} {A : Ty} :
      Compat H Γ → H.ArrFree a →
      Compat (H.setArr a (some e)) (Γ.setRef a (some (.lin (.array A))))
  /-- `H ⋈ Γ₁ + Γ₂`, `x ∉ dom(H)` give `H, x ↦_r (Γ₂ ⊢ t : A) ⋈ Γ₁, x : A`
  (the judgment `Γ₂ ⊢ t : A` is part of the heap entry `e`) -/
  | lin {n ρ : ℕ} {H : Heap n ρ} {Γ₁ Γ₁₂ : TCtx n ρ} {x : Var n} {e : VarEntry n ρ} :
      Compat H Γ₁₂ → Γ₁.Add e.ctx Γ₁₂ → H.VarFree x →
      Compat (H.setVar x (some e)) (Γ₁.setVar x (some (.lin e.ty)))
  /-- `H ⋈ Γ₁ + [Γ₂]`, `x ∉ dom(H)` give `H, x ↦_ω ([Γ₂] ⊢ t : A) ⋈ Γ₁, x : [A]` -/
  | omega {n ρ : ℕ} {H : Heap n ρ} {Γ₁ Γ₂ Γ₁₂ : TCtx n ρ} {x : Var n} {t : Term n ρ} {A : Ty}
      (ht : HasType Γ₂ t A) :
      Compat H Γ₁₂ → Γ₁.Add Γ₂ Γ₁₂ → Γ₂.AllNonLin → H.VarFree x →
      Compat (H.setVar x (some ⟨.omega, Γ₂, t, A, ht⟩)) (Γ₁.setVar x (some (.nonlin A)))

end LCU
