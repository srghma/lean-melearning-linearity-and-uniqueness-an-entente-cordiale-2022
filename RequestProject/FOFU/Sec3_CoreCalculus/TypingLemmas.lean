module
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

/-!
# Small derived typing rules and tactics for typing examples

* `HasType.var'`: the derived rule `(var')` of §3, i.e. `var` followed by dereliction:
  `0 · Γ, x : [A]_1 ⊢ x : A`.
* `CtxAdd.empty`, `CtxAdd.cons`, `Ctx.IsZero.empty`, `Ctx.IsZero.cons`, `zeroRest_cons_zero`,
  `zeroRest_cons_succ`: structural lemmas for building context side conditions of
  concrete derivations, with contexts built by `Ctx.cons` from `Ctx.empty`.
* `Ctx.ofList`: a context given by the list of its assumptions (variable `#0` first).
* tactics `ctx_add` (proves `CtxAdd Γ₁ Γ₂ Γ`) and `zero_rest` (proves the side condition
  `∀ j, j ≠ i → ZeroAssm (Γ.vars j)` of `var`, or `Γ.IsZero`) for concrete contexts built
  with `Ctx.ofList`, by checking every variable.
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The derived rule `(var')`: `0 · Γ, x : [A]_1 ⊢ x : A` (`var` followed by `der`). -/
theorem HasType.var' {k n : ℕ} {Γ : Ctx R k n} {i : Fin n} {A : Ty R k}
    (hi : Γ.vars i = some (.grd A 1)) (hz : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
    HasType Γ (.var i) A := by
  have hv : HasType (Γ.update i (some (.lin A))) (.var i) A :=
    HasType.var (by simp [Ctx.update]) (fun j hj => by
      simp only [Ctx.update, Function.update_of_ne hj]; exact hz j hj)
  have h := HasType.der (i := i) (A := A) (by simp [Ctx.update]) hv
  have e : (Γ.update i (some (.lin A))).update i (some (.grd A 1)) = Γ := by
    ext j
    · by_cases hj : j = i
      · subst hj; simp [Ctx.update, hi]
      · simp [Ctx.update, Function.update_of_ne hj]
    · rfl
  rwa [e] at h

/-- `∅ + ∅ = ∅`. -/
theorem CtxAdd.empty {k : ℕ} : CtxAdd (Ctx.empty : Ctx R k 0) Ctx.empty Ctx.empty :=
  ⟨fun i => i.elim0, fun _ => RefAdd.noneLeft _⟩

/-- `(Γ₁, x : a) + (Γ₂, x : b) = (Γ, x : c)` when `a + b = c` and `Γ₁ + Γ₂ = Γ`. -/
theorem CtxAdd.cons {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {a b c : Option (Assm R k)}
    (habc : AssmAdd a b c) (h : CtxAdd Γ₁ Γ₂ Γ) :
    CtxAdd (Γ₁.cons a) (Γ₂.cons b) (Γ.cons c) :=
  ⟨fun i => Fin.cases habc (fun j => h.vars j) i, h.refs⟩

theorem Ctx.IsZero.empty {k : ℕ} : (Ctx.empty : Ctx R k 0).IsZero := fun i => i.elim0

theorem Ctx.IsZero.cons {k n : ℕ} {Γ : Ctx R k n} {a : Option (Assm R k)}
    (ha : ZeroAssm a) (h : Γ.IsZero) : (Γ.cons a).IsZero :=
  fun i => Fin.cases ha (fun j => h j) i

/-- Side condition of `var` for the variable `0` of `Γ, x : a`. -/
theorem zeroRest_cons_zero {k n : ℕ} {Γ : Ctx R k n} {a : Option (Assm R k)}
    (h : Γ.IsZero) : ∀ j, j ≠ 0 → ZeroAssm ((Γ.cons a).vars j) := by
  intro j hj
  cases j using Fin.cases with
  | zero => exact absurd rfl hj
  | succ j => exact h j

/-- Side condition of `var` for the variable `i + 1` of `Γ, x : a`. -/
theorem zeroRest_cons_succ {k n : ℕ} {Γ : Ctx R k n} {a : Option (Assm R k)} {i : Fin n}
    (ha : ZeroAssm a) (h : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
    ∀ j, j ≠ i.succ → ZeroAssm ((Γ.cons a).vars j) := by
  intro j hj
  cases j using Fin.cases with
  | zero => exact ha
  | succ j => exact h j (fun e => hj (e ▸ rfl))

/-- The context whose variable `#i` has the `i`-th assumption of the list (no references). -/
abbrev Ctx.ofList {k : ℕ} : (l : List (Option (Assm R k))) → Ctx R k l.length
  | [] => Ctx.empty
  | a :: l => (Ctx.ofList l).cons a

/-- A context built from a list of absent / zero-graded assumptions is zero. -/
theorem Ctx.IsZero.ofList_nil {k : ℕ} : (Ctx.ofList [] : Ctx R k 0).IsZero := Ctx.IsZero.empty

end FOFU

/-- Proves `CtxAdd Γ₁ Γ₂ Γ` for concrete contexts by checking every variable. -/
macro "ctx_add" : tactic => `(tactic| (
  refine ⟨fun i => ?_, fun _ => FOFU.RefAdd.noneLeft _⟩
  fin_cases i <;>
    first
      | exact FOFU.AssmAdd.noneLeft _
      | exact FOFU.AssmAdd.noneRight _
      | exact FOFU.AssmAdd.grd _ _ _))

/-- Proves `∀ j, j ≠ i → ZeroAssm (Γ.vars j)` (or `Γ.IsZero`) for concrete contexts. -/
macro "zero_rest" : tactic => `(tactic| (
  intro j
  fin_cases j <;> first | (intro hj; exact absurd rfl hj) | (intros; trivial) | (intros; rfl)))
