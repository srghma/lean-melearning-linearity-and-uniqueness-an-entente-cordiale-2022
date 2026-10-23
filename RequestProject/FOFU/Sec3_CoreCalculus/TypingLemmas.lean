module
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing

/-!
# Small derived typing rules and tactics for typing examples

* `HasType.var'`: the derived rule `(var')` of §3, i.e. `var` followed by dereliction:
  `0 · Γ, x : [A]_1 ⊢ x : A`.
* `TCtx.ofList`: a source context (no references) given by the list of its assumptions
  (variable `Var.zero` first).
* tactics for the side conditions of concrete derivations, which are all structural
  judgments on length-indexed contexts and are proved by applying their constructors:
  `ctx_add` (proves `CtxAdd Γ₁ Γ₂ Γ`), `zero_ctx` (proves `Γ.IsZero`) and `pick_var`
  (proves the premise `Γ.vars.Pick ZeroAssm i a` of the rule `var`).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The derived rule `(var')`: `0 · Γ, x : [A]_1 ⊢ x : A` (`var` followed by `der`). -/
theorem HasType.var' {k n ρ : ℕ} {Γ : TCtx R k n ρ} {i : Var n} {A : Ty R k}
    (hi : Γ.vars.Pick ZeroAssm i (some (.grd A 1))) : HasType Γ (.var i) A := by
  have hv : HasType (Γ.setVar i (some (.lin A))) (.var i) A := HasType.var (hi.set _)
  have h := HasType.der (i := i) (A := A) (Ctx.Lookup.of_eq (by simp)) hv
  have e : (Γ.setVar i (some (.lin A))).setVar i (some (.grd A 1)) = Γ := by
    refine TCtx.ext rfl ?_
    simp only [TCtx.setVar_vars, Ctx.set_set]
    rw [← hi.get, Ctx.set_get]
  rwa [e] at h

/-- The source context whose variable `Var.zero` has the first assumption of the list,
`Var.succ Var.zero` the second, and so on (no references). -/
abbrev TCtx.ofList {k : ℕ} : (l : List (Option (Assm R k))) → TCtx R k l.length 0
  | [] => TCtx.empty
  | a :: l => (TCtx.ofList l).cons a

end FOFU

/-- Proves `CtxAdd Γ₁ Γ₂ Γ` for concrete contexts by applying the constructors of the
pointwise relations. -/
macro "ctx_add" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩ <;>
    repeat' (first
      | exact Ctx.Forall₃.nil
      | refine Ctx.Forall₃.snoc ?_ ?_
      | exact FOFU.AssmAdd.noneLeft _
      | exact FOFU.AssmAdd.noneRight _
      | exact FOFU.AssmAdd.grd _ _ _
      | exact FOFU.RefAdd.noneLeft _
      | exact FOFU.RefAdd.noneRight _
      | exact FOFU.RefAdd.both _)))

/-- Proves `Γ.IsZero` for concrete contexts. -/
macro "zero_ctx" : tactic => `(tactic| (
  repeat' (first
    | exact Ctx.All.nil
    | refine Ctx.All.snoc ?_ ?_
    | exact FOFU.ZeroAssm.none
    | exact FOFU.ZeroAssm.grd _)))

/-- Proves the premise `Γ.vars.Pick ZeroAssm i a` of the rule `var` for concrete contexts. -/
macro "pick_var" : tactic => `(tactic| (
  repeat' (first
    | refine Ctx.Pick.here ?_
    | refine Ctx.Pick.there ?_ ?_
    | exact Ctx.All.nil
    | refine Ctx.All.snoc ?_ ?_
    | exact FOFU.ZeroAssm.none
    | exact FOFU.ZeroAssm.grd _)))
