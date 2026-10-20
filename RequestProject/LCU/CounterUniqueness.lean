module
public import RequestProject.LCU.Metatheory

/-!
# Theorem 5 (Uniqueness) does not hold as stated

Counterexample: the closed source program
```
let! z = (copy !(newArray 1) as x in &x) in z   :   *(Array 𝔽)
```
is well typed (`x : **(Array 𝔽)`, so `&x : !(*(Array 𝔽))`).  Evaluating it from the
empty heap, `newArray 1` allocates `a = 0`, `copy_β` copies it into a fresh array
`b = 1` and binds `x ↦₁ **b`, the borrow `&**b ⇝ !*b` marks `b` as shared
(`b ↦_ω`), and finally `let!` binds `z ↦_ω *b` and returns `*b`.  So the program
reduces to the unique value `*b` although `b ∉ dom(∅)` and `b ↦_ω` in the final heap.
The underlying issue is that borrowing a doubly-unique value `**b` produces a
duplicable `!(*b)`.
-/

@[expose] public section

namespace LCU

open Term

namespace UniquenessCounterexample

/-- `copy !(newArray 1) as x in &x` -/
def C : Term 0 := copy (bang (app (prim .newArray) (nat 1))) (borrow (var 0))

/-- `let! z = (copy !(newArray 1) as x in &x) in z` -/
def prog : Term 0 := letBang C (var 0)

lemma prog_typed : HasType Ctx.empty prog (.star (.array .float)) := by
  rw [hasType_iff_hasTypeD]
  have hnew : HasTypeD (Ctx.empty : Ctx 0) (app (prim .newArray) (nat 1)) (.star (.array .float)) :=
    .app (A := .nat) (.prim Ctx.AllNonLin.empty) (.natI Ctx.AllNonLin.empty) (Ctx.Add.empty_left _)
  have hC : HasTypeD (Ctx.empty : Ctx 0) C (.bang (.star (.array .float))) :=
    .copy (.bangI Ctx.AllNonLin.empty hnew)
      (.borrow (HasTypeD.var_zero_single (.lin (.star (.star (.array .float))))))
      (Ctx.Add.empty_left _)
  exact .bangE hC (HasTypeD.var_zero_single (.nonlin (.star (.array .float))))
    (Ctx.Add.empty_right _)

/-- The renaming of references used by `copy_β`. -/
def θ : ℕ → ℕ := fun a => a + 1

def H₀ : Heap 0 := Heap.empty
def H₁ : Heap 0 := H₀.setArr 0 (some ⟨.one, newArr 1⟩)
def H₁c : Heap 0 := H₁.setArr 1 (some ⟨.one, newArr 1⟩)
def Γv : Ctx 0 := Ctx.empty.set (.inr 0) (some (.lin .float))
def eₓ : VarEntry 0 := ⟨.one, Γv, star (renameRefs θ (star (ref 0))), .star (.star (.array .float))⟩
def H₂ : Heap 1 := H₁c.push eₓ
def H₃ : Heap 1 := H₂.setVar 0 none
noncomputable def H₄ : Heap 1 := H₃.markOmega (star (ref 1))
def Γb : Ctx 1 := Ctx.empty.set (.inr 1) (some (.nonlin .float))
def e_z : VarEntry 1 := ⟨.omega, Γb, star (ref 1), .star (.array .float)⟩
noncomputable def H₅ : Heap 2 := H₄.push e_z

lemma allNonLin_empty_set_nonlin {n : ℕ} (x : Fin n ⊕ ℕ) (A : Ty) :
    ((Ctx.empty : Ctx n).set x (some (.nonlin A))).AllNonLin := by
  intro y
  by_cases hy : y = x
  · subst hy; simp
  · rw [Ctx.set_ne _ _ hy]; trivial

lemma allNonLin_empty_set_set {n : ℕ} (x : Fin n ⊕ ℕ) (h : Option Hyp) :
    (((Ctx.empty : Ctx n).set x h).set x none).AllNonLin := by
  rw [Ctx.set_set]
  intro y
  by_cases hy : y = x
  · subst hy; simp
  · rw [Ctx.set_ne _ _ hy]; trivial

lemma refIn_star_ref {n : ℕ} (a b : ℕ) : RefIn a (star (ref b) : Term n) ↔ a = b := Iff.rfl

lemma typed_star_ref {n : ℕ} (Γ : Ctx n) (b : ℕ) (h : Hyp) (hb : Γ (.inr b) = some h)
    (hrest : (Γ.set (.inr b) none).AllNonLin) :
    HasType Γ (star (ref b)) (.star (.array h.ty)) := by
  refine HasType.nec (HasType.ref (h := h) (by simpa using hb) ?_) ?_
  · rintro (i | a)
    · trivial
    · by_cases ha : a = b
      · subst ha; simp
      · rw [Ctx.set_ne _ _ (by simpa using ha)]
        have := hrest (.inr a); rwa [Ctx.set_ne _ _ (by simpa using ha)] at this
  · intro i; have := hrest (.inl i); rwa [Ctx.set_ne _ _ (by simp)] at this

lemma step₁ : Step H₀ prog H₁ (letBang (copy (bang (star (ref 0))) (borrow (var 0))) (var 0))
    BCtx.empty UCtx.empty := by
  have := Step.letBang (t₂ := var 0) (le_refl 0)
    (Step.copyBang (t₂ := borrow (var 0)) (le_refl 0)
      (Step.newArray (H := H₀) (a := 0) (k := 1) rfl))
  exact this

lemma copyHeap : CopyHeap H₁ (star (ref 0)) θ H₁c where
  vars := rfl
  fresh := by intro a ha; rw [refIn_star_ref] at ha; subst ha; rfl
  inj := by intro a b ha hb _; rw [refIn_star_ref] at ha hb; rw [ha, hb]
  copied := by intro a ha; rw [refIn_star_ref] at ha; subst ha; rfl
  rest := by
    intro b hb
    have : b ≠ 1 := fun e => hb 0 rfl (by rw [e]; rfl)
    simp [H₁c, Heap.setArr, Function.update_of_ne this]

lemma step₂ : Step H₁ (letBang (copy (bang (star (ref 0))) (borrow (var 0))) (var 0))
    H₂ (letBang (borrow (var 0)) (var 0))
    (BCtx.single (Fin.last 0) (.lin (.star (.star (.array .float))))) UCtx.empty := by
  have := Step.letBang (t₂ := var 0) (Nat.zero_le 1)
    (Step.betaCopy (H := H₁) (t := borrow (var 0)) (Γ := Γv) (A := .star (.array .float))
      (IsValue.star _) (typed_star_ref Γv 0 (.lin .float) rfl (allNonLin_empty_set_set _ _))
      (by intro a ha; rw [refIn_star_ref] at ha; subst ha; simp [H₁, Heap.setArr])
      copyHeap)
  exact this

lemma H₂_vars_zero : H₂.vars 0 = some (eₓ.lift (Nat.le_succ 0)) := by
  simp [H₂, Heap.push, Heap.setVar]

lemma step₃ : Step H₂ (letBang (borrow (var 0)) (var 0))
    H₃ (letBang (borrow (star (star (ref 1)))) (var 0)) BCtx.empty (UCtx.single 0 .one) := by
  have := Step.letBang (t₂ := var 0) (le_refl 1)
    (Step.borrow (Step.var₁ (H := H₂) (x := 0) H₂_vars_zero rfl))
  exact this

lemma H₃_arrs_one : H₃.arrs 1 = some ⟨.one, newArr 1⟩ := rfl

lemma step₄ : Step H₃ (letBang (borrow (star (star (ref 1)))) (var 0))
    H₄ (letBang (bang (star (ref 1))) (var 0)) BCtx.empty UCtx.empty := by
  have := Step.letBang (t₂ := var 0) (le_refl 1)
    (Step.betaBorrow (H := H₃) (v := star (ref 1)) (IsValue.star _)
      (by intro a ha; rw [refIn_star_ref] at ha; subst ha; rw [H₃_arrs_one]; simp))
  exact this

lemma step₅ : Step H₄ (letBang (bang (star (ref 1))) (var 0)) H₅ (var 1)
    (BCtx.single (Fin.last 1) (.nonlin (.star (.array .float)))) UCtx.empty := by
  have := Step.betaBang (H := H₄) (t₂ := var 0) (Γ := Γb) (t₁ := star (ref 1))
    (A := .star (.array .float))
    (allNonLin_empty_set_nonlin _ _)
    (typed_star_ref Γb 1 (.nonlin .float) rfl (allNonLin_empty_set_set _ _))
  exact this

lemma H₅_vars_one : H₅.vars 1 = some (e_z.lift (Nat.le_succ 1)) := by
  simp [H₅, Heap.push, Heap.setVar]

lemma step₆ : Step H₅ (var 1) H₅ (star (ref 1)) BCtx.empty (UCtx.single 1 .one) := by
  have := Step.varω (H := H₅) (x := 1) H₅_vars_one rfl
  exact this

lemma H₅_arrs_one : H₅.arrs 1 = some ⟨.omega, newArr 1⟩ := by
  simp [H₅, H₄, Heap.push, Heap.setVar, Heap.lift, Heap.markOmega, refIn_star_ref, H₃_arrs_one]

end UniquenessCounterexample

open UniquenessCounterexample in
/-- **Theorem 5 (Uniqueness) is false as stated.** -/
theorem not_uniqueness : ¬ Uniqueness := by
  intro hU
  have hsteps := Steps.ext step₁ (Steps.ext step₂ (Steps.ext step₃ (Steps.ext step₄
    (Steps.ext step₅ (Steps.ext step₆ Steps.refl)))))
  have := (hU Ctx.empty prog _ prog_typed Ctx.empty Ctx.empty H₀ (Ctx.Add.empty_left _)
    Compat.empty _ _ _ _ hsteps 1 rfl).2 rfl
  obtain ⟨e', he', hr⟩ := this
  rw [H₅_arrs_one] at he'
  cases he'
  cases hr

end LCU
