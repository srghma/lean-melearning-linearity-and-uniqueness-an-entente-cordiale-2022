module
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Shared de Bruijn infrastructure

Both formalisations in this project (the LCU calculus of *Linearity and Uniqueness: An
Entente Cordiale*, under `RequestProject/LCU/`, and the ownership calculus of
*Functional Ownership through Fractional Uniqueness*, under `RequestProject/FOFU/`) use
intrinsically scoped de Bruijn syntax: a term with `n` free variables has type `Term n`
and variables are `Fin n`.  Binders bind index `0`.

This file contains the part of the renaming machinery that does not depend on a
particular term language: lifting a renaming `ρ : Fin n → Fin m` under a binder.

* `DeBruijn.Ren.up ρ` keeps index `0` fixed and sends `i + 1` to `ρ i + 1`.

The LCU development re-exports these names in `LCU.Term` (see
`RequestProject/LCU/Sec3_1_Calculus/RenameSubst.lean`), and the FOFU development uses
them for its own terms and for the type-level name variables of its types.
-/

@[expose] public section

namespace DeBruijn

/-- Lifting a renaming under a binder: index `0` is fixed and the others are shifted. -/
def Ren.up {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] lemma Ren.up_zero {n m : ℕ} (ρ : Fin n → Fin m) : Ren.up ρ 0 = 0 := rfl

@[simp] lemma Ren.up_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    Ren.up ρ i.succ = (ρ i).succ := rfl

lemma Ren.up_id {n : ℕ} : Ren.up (id : Fin n → Fin n) = id := by
  funext i; cases i using Fin.cases <;> rfl

lemma Ren.up_comp {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    Ren.up (ρ' ∘ ρ) = Ren.up ρ' ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

/-- Lifting preserves injectivity. -/
lemma Ren.up_injective {n m : ℕ} {ρ : Fin n → Fin m} (h : Function.Injective ρ) :
    Function.Injective (Ren.up ρ) := by
  intro i j e
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · exact absurd e (Fin.succ_ne_zero _).symm
  · exact absurd e (Fin.succ_ne_zero _)
  · simp only [Ren.up_succ, Fin.succ_inj] at e; rw [h e]

/-- A successor index in the image of a lifted renaming comes from the original
renaming. -/
lemma Ren.exists_of_up {n m : ℕ} {ρ : Fin n → Fin m} {j : Fin m} :
    (∃ i, Ren.up ρ i = j.succ) → ∃ i, ρ i = j
  | ⟨i, hi⟩ => by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.succ_ne_zero j).symm
    | succ i => exact ⟨i, by simpa using hi⟩

end DeBruijn
