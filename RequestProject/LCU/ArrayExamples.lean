module
public import RequestProject.LCU.ArraySemantics

/-!
# An example run of the store-based array semantics

The program `readArray (writeArray (newArray 3) 0 x) 0` is well-typed in the empty
context, at type `𝔽 ⊗ *(Array 𝔽)`, and evaluates from the empty store to the value
`(x, *a)`: the read sees the destructive write.
-/

@[expose] public section

namespace LCU

open Term

/-- `readArray (writeArray (newArray 3) 0 x) 0`. -/
def writeReadProg (x : Float) : Term 0 :=
  app (app (prim .readArray)
    (app (app (app (prim .writeArray) (app (prim .newArray) (nat 3))) (nat 0)) (float x)))
    (nat 0)

theorem writeReadProg_hasType (x : Float) :
    HasType (Ctx.empty : Ctx 0) (writeReadProg x) (.float ⊗ .star (.array .float)) := by
  rw [hasType_iff_hasTypeD]
  have h : (Ctx.empty : Ctx 0).AllNonLin := Ctx.AllNonLin.empty
  exact .app_of h (.app_of h (.prim h)
    (.app_of h (.app_of h (.app_of h (.prim h) (.app_of h (.prim h) (.natI h))) (.natI h))
      (.floatI h))) (.natI h)

/-- The program evaluates to `(x, *a)` (with `a = 0` the freshly allocated array). -/
theorem writeReadProg_eval (x : Float) :
    ∃ σ, ASteps Store.empty (writeReadProg x) σ (pair (float x) (star (ref 0))) := by
  have e : Function.update (fun _ : ℕ => (0 : Float)) 0 x 0 = x := by simp
  -- allocation
  have s₁ := AStep.app (nat 0) (AStep.primArg (PrimReady.prim .readArray)
    (AStep.app (float x) (AStep.app (nat 0) (AStep.primArg (PrimReady.prim .writeArray)
      (AStep.newArray (n := 0) Store.empty 3 0 rfl)))))
  -- destructive update
  have s₂ := AStep.app (nat 0) (AStep.primArg (PrimReady.prim .readArray)
    (AStep.writeArray (n := 0) (Store.empty.set 0 (some fun _ => 0)) 0 0 x
      (fun _ => 0) (by simp)))
  -- read
  have s₃ := AStep.readArray (n := 0) ((Store.empty.set 0 (some fun _ => 0)).set 0
    (some (Function.update (fun _ => 0) 0 x))) 0 0 (Function.update (fun _ => 0) 0 x) (by simp)
  rw [e] at s₃
  exact ⟨_, (((ASteps.refl _ _).tail s₁).tail s₂).tail s₃⟩

end LCU
