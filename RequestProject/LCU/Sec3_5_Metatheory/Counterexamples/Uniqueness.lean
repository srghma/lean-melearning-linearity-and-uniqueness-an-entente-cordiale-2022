module
public import RequestProject.LCU.Sec3_5_Metatheory.Metatheory

/-!
# Theorem 5 (Uniqueness) does not hold as stated

Counterexample: the closed source program
```
let! z = (copy !(newArray 1) as x in &x) in z   :   *(Array 𝔽)
```
is well typed (`x : **(Array 𝔽)`, so `&x : !(*(Array 𝔽))`).  Evaluating it from the
empty heap, `newArray 1` allocates an array `a`, `copy_β` copies it into a new array
`b` and binds `x ↦₁ **b`, the borrow `&**b ⇝ !*b` marks `b` as shared
(`b ↦_ω`), and finally `let!` binds `z ↦_ω *b` and returns `*b`.  (References are de
Bruijn indices: after the copy, `b` is the reference `0` and `a` is the reference `1`.)  So the program
reduces to the unique value `*b` although `b ∉ dom(∅)` and `b ↦_ω` in the final heap.
The underlying issue is that borrowing a doubly-unique value `**b` produces a
duplicable `!(*b)`.
-/

@[expose] public section

namespace LCU

open Term

namespace UniquenessCounterexample

/-! ## The program and its type -/

/-- `copy !(newArray 1) as x in &x` -/
def C : Term 0 0 := copy (bang (app (prim .newArray) (nat 1))) (borrow (var 0))

/-- `let! z = (copy !(newArray 1) as x in &x) in z` -/
def prog : Term 0 0 := letBang C (var 0)

/-- The program is well typed: `x : **(Array 𝔽)`, so `&x : !(*(Array 𝔽))`. -/
lemma prog_typed : HasType TCtx.empty prog (.star (.array .float)) := by
  rw [hasType_iff_hasTypeD]
  have hnew : HasTypeD (TCtx.empty : TCtx 0 0) (app (prim .newArray) (nat 1))
      (.star (.array .float)) :=
    .app (A := .nat) (.prim TCtx.AllNonLin.empty) (.natI TCtx.AllNonLin.empty)
      (TCtx.Add.empty_left _)
  have hC : HasTypeD (TCtx.empty : TCtx 0 0) C (.bang (.star (.array .float))) :=
    .copy (.bangI TCtx.AllNonLin.empty hnew)
      (.borrow (HasTypeD.var_zero_single (.lin (.star (.star (.array .float))))))
      (TCtx.Add.empty_left _)
  exact .bangE hC (HasTypeD.var_zero_single (.nonlin (.star (.array .float))))
    (TCtx.Add.empty_right _)

/-! ## Auxiliary typing facts -/

/-- `*a : *(Array A)` for the most recent reference `a = 0`, if all other assumptions are
non-linear. -/
lemma typed_star_ref {n ρ : ℕ} {R : Ctx (Option (Hyp ArrTy)) ρ} {V : Ctx (Option (Hyp Ty)) n}
    (h : Hyp ArrTy) (hR : R.All NonLin) (hV : V.All NonLin) :
    HasType (⟨R ,, some h, V⟩ : TCtx n (ρ + 1)) (star (ref .zero)) (.star h.ty.toTy) :=
  .nec (.ref (.here hR) (TCtx.allNonLin_replicate _)) hV

/-! ## The heaps along the reduction

`H₀` is empty; `H₁` contains the array allocated by `newArray 1`; `H₁c` also contains its
copy (the new reference `0`); `H₂` binds `x ↦₁ **0`; `H₃` has removed `x` again; `H₄`
marks the array `0` as shared (`ω`); `H₅` binds `z ↦_ω *0`. -/

/-- The renaming of references used by `copy_β`: the array is copied to the new
reference `0`. -/
def θ : Var 1 → Var 2 := fun _ => .zero

/-- The initial (empty) heap. -/
def H₀ : Heap 0 0 := Heap.empty
/-- After `newArray 1`: the new array `0` is allocated with usage `1`. -/
def H₁ : Heap 0 1 := H₀.pushArr ⟨.one, newArr 1⟩
/-- After copying: the copy `0` of the array (now `1`) is allocated too. -/
def H₁c : Heap 0 2 := H₁.pushArr ⟨.one, newArr 1⟩

/-- The context of the judgment recorded for the copy: it refers to the copy `0`. -/
def Γv : TCtx 0 2 := ⟨.nil ,, none ,, some (.lin (.array .float)), .nil⟩

lemma typed_copy :
    HasType Γv (star (renameRefs θ (star (ref .zero)))) (.star (.star (.array .float))) :=
  .nec (typed_star_ref (.lin (.array .float)) (.snoc .nil .none) .nil) .nil

/-- The heap entry `x ↦₁ (Γv ⊢ **0 : **(Array 𝔽))` created by `copy_β`. -/
def eₓ : VarEntry 0 2 :=
  ⟨.one, Γv, star (renameRefs θ (star (ref .zero))), .star (.star (.array .float)), typed_copy⟩
/-- After `copy_β`: `x` (variable `0`) is bound to `**0`. -/
def H₂ : Heap 1 2 := H₁c.push eₓ
/-- After looking up the linear `x`, its binding is removed. -/
def H₃ : Heap 1 2 := H₂.setVar .zero none
/-- After the borrow `&**0 ⇝ !*0`, the array `0` is marked as shared (`ω`). -/
noncomputable def H₄ : Heap 1 2 := H₃.markOmega (star (ref .zero))
/-- The context of the judgment recorded for `z`, with the reference `0` non-linear. -/
def Γb : TCtx 1 2 := ⟨.nil ,, none ,, some (.nonlin (.array .float)), .nil ,, none⟩
/-- The heap entry `z ↦_ω (Γb ⊢ *0 : *(Array 𝔽))` created by `!β`. -/
def e_z : VarEntry 1 2 :=
  ⟨.omega, Γb, star (ref .zero), .star (.array .float),
    typed_star_ref (.nonlin (.array .float)) (.snoc .nil .none) (.snoc .nil .none)⟩
/-- After `!β`: `z` (variable `0`) is bound to `*0`. -/
noncomputable def H₅ : Heap 2 2 := H₄.push e_z

/-! ## The six reduction steps -/

/-- Step 1: `newArray 1` (under `!`, rule `copy_!`) allocates a new array. -/
lemma step₁ : Step H₀ prog 0 1 H₁
    (letBang (copy (bang (star (ref .zero))) (borrow (var 0))) (var 0))
    BCtx.empty UCtx.empty :=
  Step.letBang (t₂ := var 0) (Step.copyBang (t₂ := borrow (var 0))
    (Step.newArray (H := H₀) (k := 1)))

/-- `H₁c` is a valid result of copying the arrays referenced by `*0` along `θ`. -/
lemma copyHeap : CopyHeap H₁ (star (ref .zero)) 1 θ H₁c where
  vars := rfl
  old _ := rfl
  fresh _ _ _ := nofun
  inj a b _ _ _ := by
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ b => exact b.elim0
    | succ a => exact a.elim0
  copied a ha := by rw [refIn_star_ref] at ha; subst ha; rfl
  onto c hc := by
    cases c with
    | zero => exact ⟨.zero, refIn_star_ref.2 rfl, rfl⟩
    | succ c => exact absurd rfl (hc c)

/-- Step 2 (`copy_β`): copy the array to the new reference `0` and bind `x ↦₁ **0`. -/
lemma step₂ : Step H₁ (letBang (copy (bang (star (ref .zero))) (borrow (var 0))) (var 0)) 1 1
    H₂ (letBang (borrow (var 0)) (var 0))
    (BCtx.new1 (.lin (.star (.star (.array .float))))) UCtx.empty := by
  have := Step.letBang (t₂ := var 0)
    (Step.betaCopy (H := H₁) (t := borrow (var 0)) (Γ := Γv) (A := .star (.array .float))
      (IsValue.star _) typed_copy
      (by intro a ha; rw [refIn_star_ref] at ha; subst ha; simp [H₁, Heap.pushArr]) copyHeap)
  exact this

/-- Step 3 (`var₁`): the linear variable `x` is replaced by `**0` and removed. -/
lemma step₃ : Step H₂ (letBang (borrow (var 0)) (var 0)) 0 0
    H₃ (letBang (borrow (star (star (ref .zero)))) (var 0)) BCtx.empty
    (UCtx.single .zero .one) :=
  Step.letBang (t₂ := var 0)
    (Step.borrow (Step.var₁ (H := H₂) (x := .zero) (e := eₓ.lift 1 0) (Heap.varAt_iff.2 ⟨rfl, rfl⟩)))

/-- Step 4 (`&β`): `&**0 ⇝ !*0`, marking the array `0` as shared. -/
lemma step₄ : Step H₃ (letBang (borrow (star (star (ref .zero)))) (var 0)) 0 0
    H₄ (letBang (bang (star (ref .zero))) (var 0)) BCtx.empty UCtx.empty :=
  Step.letBang (t₂ := var 0)
    (Step.betaBorrow (H := H₃) (v := star (ref .zero)) (IsValue.star _)
      (by intro a ha; rw [refIn_star_ref] at ha; subst ha; simp [H₃, H₂, H₁c, Heap.push,
        Heap.pushArr]))

/-- Step 5 (`!β`): `let! z = !*0 in z` binds `z ↦_ω *0`. -/
lemma step₅ : Step H₄ (letBang (bang (star (ref .zero))) (var 0)) 1 0 H₅ (var 0)
    (BCtx.new1 (.nonlin (.star (.array .float)))) UCtx.empty :=
  Step.betaBang (H := H₄) (t₂ := var 0) (Γ := Γb) (t₁ := star (ref .zero))
    (A := .star (.array .float)) ⟨.snoc (.snoc .nil .none) (.nonlin _), .snoc .nil .none⟩
    e_z.typed

/-- Step 6 (`var_ω`): `z` is replaced by `*0`, a unique value whose array is shared. -/
lemma step₆ : Step H₅ (var 0) 0 0 H₅ (star (ref .zero)) BCtx.empty (UCtx.single .zero .one) :=
  Step.varω (H := H₅) (x := .zero) (e := e_z.lift 1 0) (Heap.varAt_iff.2 ⟨rfl, rfl⟩)

/-- In the final heap the array `0` has usage `ω`. -/
lemma H₅_arrs_zero : H₅.arrs.get .zero = some ⟨.omega, newArr 1⟩ := by
  simp [H₅, H₄, Heap.push, Heap.markOmega, refIn_star_ref, H₃, H₂, H₁c, Heap.pushArr]

end UniquenessCounterexample

/-! ## The disproof -/

open UniquenessCounterexample in
/-- **Theorem 5 (Uniqueness) is false as stated.** -/
theorem not_uniqueness : ¬ Uniqueness := by
  intro hU
  have hsteps := Steps.tail (Steps.tail (Steps.tail (Steps.tail (Steps.tail (Steps.tail
    (Steps.refl (H := H₀) (t := prog)) step₁) step₂) step₃) step₄) step₅) step₆
  obtain ⟨e', he', hr⟩ := (hU TCtx.empty prog _ prog_typed TCtx.empty TCtx.empty H₀
    (TCtx.Add.empty_left _) Compat.empty _ _ _ _ _ hsteps .zero (refIn_ref.2 rfl)).2
    (fun b => b.elim0)
  rw [H₅_arrs_zero] at he'
  cases he'
  cases hr

end LCU
