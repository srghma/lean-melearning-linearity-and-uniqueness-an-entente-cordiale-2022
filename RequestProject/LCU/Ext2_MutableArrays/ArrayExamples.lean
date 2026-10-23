module
public import RequestProject.LCU.Ext2_MutableArrays.ArrayProgress

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
def writeReadProg (x : FloatLit) : Term 0 0 :=
  app (app (prim .readArray)
    (app (app (app (prim .writeArray) (app (prim .newArray) (nat 3))) (nat 0)) (float x)))
    (nat 0)

/-- The example program is well typed in the empty context. -/
theorem writeReadProg_hasType (x : FloatLit) :
    HasType (TCtx.empty : TCtx 0 0) (writeReadProg x) (.float ⊗ .star (.array .float)) := by
  rw [hasType_iff_hasTypeD]
  have h : (TCtx.empty : TCtx 0 0).AllNonLin := TCtx.AllNonLin.empty
  exact .app_of h (.app_of h (.prim h)
    (.app_of h (.app_of h (.app_of h (.prim h) (.app_of h (.prim h) (.natI h))) (.natI h))
      (.floatI h))) (.natI h)

/-- The program evaluates to `(x, *a)`, where `a` is the newly allocated array (the only
reference in scope). -/
theorem writeReadProg_eval (x : FloatLit) :
    ∃ σ : Store 1, ASteps Store.empty (writeReadProg x) σ (pair (float x) (star (ref .zero))) := by
  have e : Function.update (fun _ : ℕ => (0 : FloatLit)) 0 x 0 = x := by simp
  -- allocation
  have s₁ := AStep.app (nat 0) (AStep.primArg (PrimReady.prim .readArray)
    (AStep.app (float x) (AStep.app (nat 0) (AStep.primArg (PrimReady.prim .writeArray)
      (AStep.newArray (n := 0) Store.empty 3)))))
  -- destructive update
  have s₂ := AStep.app (nat 0) (AStep.primArg (PrimReady.prim .readArray)
    (AStep.writeArray (n := 0) (Store.empty ,, some fun _ => 0) .zero 0 x
      (fun _ => 0) (by simp)))
  -- read
  have s₃ := AStep.readArray (n := 0) ((Store.empty ,, some fun _ => 0).set .zero
    (some (Function.update (fun _ => 0) 0 x))) .zero 0 (Function.update (fun _ => 0) 0 x)
    (by simp)
  rw [e] at s₃
  exact ⟨_, ((ASteps.refl.tail s₁).tail s₂).tail s₃⟩

end LCU
