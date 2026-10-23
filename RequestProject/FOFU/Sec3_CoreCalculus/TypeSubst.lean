module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax

/-!
# Renaming of identifiers in types

Types `Ty R k` contain de Bruijn identifiers `Var k`.  Since identifiers can only be
replaced by identifiers, substitution of identifiers is *renaming*: `Ty.ren r A` applies
`r : Var k → Var k'` to all free identifiers of `A` (lifted under `∃` by `Ren.up`).  This
covers

* `Ty.shift A : Ty R (k + 1)`: weakening by one identifier (used when the context is
  extended with an identifier, as in `unpack`, and when the heap allocates a resource);
* `Ty.inst A ι : Ty R k` for `A : Ty R (k + 1)`: the instantiation `A [ι / id]` of the
  bound identifier of `∃ id. A` (used in `pack`).

The main law is `Ty.ren_ren` (renamings compose).
-/

@[expose] public section

namespace FOFU

namespace Ty

variable {R : Type} {k k' k'' : ℕ}

/-- Renaming of the free identifiers of a type. -/
def ren : {k k' : ℕ} → (Var k → Var k') → Ty R k → Ty R k'
  | _, _, r, lolli A B => lolli (ren r A) (ren r B)
  | _, _, r, tensor A B => tensor (ren r A) (ren r B)
  | _, _, _, unit => unit
  | _, _, r, box s A => box s (ren r A)
  | _, _, r, ex A => ex (ren (Ren.up r) A)
  | _, _, r, borrow p A => borrow p (ren r A)
  | _, _, r, res κ ι A => res κ (r ι) (ren r A)
  | _, _, _, nat => nat
  | _, _, _, float => float

/-- Weakening a type by one identifier (the new identifier is `Var.zero`). -/
def shift (A : Ty R k) : Ty R (k + 1) := A.ren Var.succ

/-- Instantiating the bound identifier `Var.zero`: `A [ι / id]`. -/
def inst (A : Ty R (k + 1)) (ι : Var k) : Ty R k := A.ren (Var.cons ι id)

@[simp] lemma ren_lolli (r : Var k → Var k') (A B : Ty R k) :
    (lolli A B).ren r = lolli (A.ren r) (B.ren r) := rfl
@[simp] lemma ren_tensor (r : Var k → Var k') (A B : Ty R k) :
    (tensor A B).ren r = tensor (A.ren r) (B.ren r) := rfl
@[simp] lemma ren_unit (r : Var k → Var k') : (unit : Ty R k).ren r = unit := rfl
@[simp] lemma ren_box (r : Var k → Var k') (s : R) (A : Ty R k) :
    (box s A).ren r = box s (A.ren r) := rfl
@[simp] lemma ren_ex (r : Var k → Var k') (A : Ty R (k + 1)) :
    (ex A).ren r = ex (A.ren (Ren.up r)) := rfl
@[simp] lemma ren_borrow (r : Var k → Var k') (p : Perm) (A : Ty R k) :
    (borrow p A).ren r = borrow p (A.ren r) := rfl
@[simp] lemma ren_res (r : Var k → Var k') (κ : ResKind) (ι : Var k) (A : Ty R k) :
    (res κ ι A).ren r = res κ (r ι) (A.ren r) := rfl
@[simp] lemma ren_nat (r : Var k → Var k') : (nat : Ty R k).ren r = nat := rfl
@[simp] lemma ren_float (r : Var k → Var k') : (float : Ty R k).ren r = float := rfl

lemma ren_ren (r : Var k → Var k') (r' : Var k' → Var k'') (A : Ty R k) :
    (A.ren r).ren r' = A.ren (r' ∘ r) := by
  induction A generalizing k' k'' with
  | lolli A B ihA ihB => simp only [ren, ihA, ihB]
  | tensor A B ihA ihB => simp only [ren, ihA, ihB]
  | unit => rfl
  | box s A ih => simp only [ren, ih]
  | ex A ih => simp only [ren, ih, Ren.up_comp]
  | borrow p A ih => simp only [ren, ih]
  | res κ ι A ih => simp only [ren, ih, Function.comp]
  | nat => rfl
  | float => rfl

@[simp] lemma ren_id (A : Ty R k) : A.ren id = A := by
  induction A with
  | lolli A B ihA ihB => simp only [ren, ihA, ihB]
  | tensor A B ihA ihB => simp only [ren, ihA, ihB]
  | unit => rfl
  | box s A ih => simp only [ren, ih]
  | ex A ih => simp only [ren, Ren.up_id, ih]
  | borrow p A ih => simp only [ren, ih]
  | res κ ι A ih => simp only [ren, ih, id]
  | nat => rfl
  | float => rfl

/-- Two renamings that agree give the same result. -/
lemma ren_congr {r r' : Var k → Var k'} (h : ∀ i, r i = r' i) (A : Ty R k) :
    A.ren r = A.ren r' := by
  rw [show r = r' from funext h]

/-- Renaming along an injective map is injective. -/
lemma ren_injective {r : Var k → Var k'} (hr : Function.Injective r) :
    Function.Injective (ren (R := R) r) := by
  intro A B h
  induction A generalizing k' with
  | lolli A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [ren, lolli.injEq, reduceCtorEq] at h; rw [ih₁ hr h.1, ih₂ hr h.2]
  | tensor A₁ A₂ ih₁ ih₂ =>
    cases B <;> simp only [ren, tensor.injEq, reduceCtorEq] at h; rw [ih₁ hr h.1, ih₂ hr h.2]
  | unit => cases B <;> simp_all [ren]
  | box s A ih =>
    cases B <;> simp only [ren, box.injEq, reduceCtorEq] at h; rw [h.1, ih hr h.2]
  | ex A ih =>
    cases B <;> simp only [ren, ex.injEq, reduceCtorEq] at h; rw [ih (Ren.up_injective hr) h]
  | borrow p A ih =>
    cases B <;> simp only [ren, borrow.injEq, reduceCtorEq] at h; rw [h.1, ih hr h.2]
  | res κ ι A ih =>
    cases B <;> simp only [ren, res.injEq, reduceCtorEq] at h
    rw [h.1, hr h.2.1, ih hr h.2.2]
  | nat => cases B <;> simp_all [ren]
  | float => cases B <;> simp_all [ren]

/-- Shifting commutes with lifted renamings. -/
lemma shift_ren_up (r : Var k → Var k') (A : Ty R k) :
    A.shift.ren (Ren.up r) = (A.ren r).shift := by
  simp only [shift, ren_ren]; rfl

/-- Instantiation commutes with renaming. -/
lemma inst_ren (r : Var k → Var k') (A : Ty R (k + 1)) (ι : Var k) :
    (A.inst ι).ren r = (A.ren (Ren.up r)).inst (r ι) := by
  simp only [inst, ren_ren]
  apply ren_congr
  intro i; cases i <;> rfl

/-- Instantiating a shifted type gives the type back. -/
@[simp] lemma shift_inst (A : Ty R k) (ι : Var k) : A.shift.inst ι = A := by
  simp only [shift, inst, ren_ren]
  exact ren_id A

@[simp] lemma shift_unit : (unit : Ty R k).shift = unit := rfl
@[simp] lemma shift_nat : (nat : Ty R k).shift = nat := rfl
@[simp] lemma shift_float : (float : Ty R k).shift = float := rfl
@[simp] lemma shift_lolli (A B : Ty R k) : (lolli A B).shift = lolli A.shift B.shift := rfl
@[simp] lemma shift_tensor (A B : Ty R k) : (tensor A B).shift = tensor A.shift B.shift := rfl
@[simp] lemma shift_box (r : R) (A : Ty R k) : (box r A).shift = box r A.shift := rfl
@[simp] lemma shift_borrow (p : Perm) (A : Ty R k) : (borrow p A).shift = borrow p A.shift := rfl
@[simp] lemma shift_res (κ : ResKind) (ι : Var k) (A : Ty R k) :
    (res κ ι A).shift = res κ ι.succ A.shift := rfl

end Ty

end FOFU
