module
public import RequestProject.LCU.CbnSemantics
public import RequestProject.LCU.CounterProgress

/-!
# The heap-model counterexamples under the repaired call-by-name semantics

The terms used to refute Theorem 6 (Progress) and Theorem 4 (Conservation) for the
heap model behave well under the substitution-based reduction `CbnStep`: they reduce
to values of their type.
-/

@[expose] public section

namespace LCU

open Term

/-- `&(*((λz. z) unit)) ⟶ !((λz. z) unit)`: the progress counterexample takes a step. -/
theorem progressCounterexample_cbnStep :
    CbnStep ProgressCounterexample.prog (bang (app (lam (var 0)) unit)) :=
  .betaBorrow _

/-- `copy !((λz. z) unit) as x in &x ⟶* !((λz. z) unit)`: the conservation counterexample
reduces to a value of type `!1`. -/
theorem conservationCounterexample_cbnSteps :
    CbnSteps ConservationCounterexample.prog (bang (app (lam (var 0)) unit)) ∧
      HasType Ctx.empty (bang (app (lam (var 0)) unit) : Term 0) (.bang .unit) ∧
      IsValue (bang (app (lam (var 0)) unit) : Term 0) := by
  have hs : CbnSteps ConservationCounterexample.prog (bang (app (lam (var 0)) unit)) :=
    Relation.ReflTransGen.head (.betaCopy _ _)
      (Relation.ReflTransGen.single (.betaBorrow _))
  refine ⟨hs, ?_, .bang _⟩
  exact hs.preserves (Ctx.noVars_zero _) (fun _ => trivial)
    ConservationCounterexample.prog_typed

end LCU
