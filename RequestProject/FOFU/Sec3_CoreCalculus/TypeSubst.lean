module
public import RequestProject.FOFU.Sec3_CoreCalculus.Syntax

/-!
# Substitution of identifiers in types

Types `Ty R k` contain de Bruijn identifiers (`Ident.bound`).  This file defines
simultaneous substitution of identifiers for bound identifiers, which covers

* `Ty.shift A : Ty R (k + 1)`: weakening by one identifier (used when the context is
  extended with an identifier, as in `unpack`);
* `Ty.inst A ι : Ty R k` for `A : Ty R (k + 1)`: the instantiation `A [ι / id]` of the
  bound identifier of `∃ id. A` (used in `pack`);
* name renamings (substitutions by bound identifiers).

The main law is `Ty.subst_subst` (substitutions compose), from which the commutation
lemmas used in the metatheory are derived.
-/

@[expose] public section

namespace FOFU

namespace Ident

variable {k k' k'' : ℕ}

/-- Substitution of identifiers for bound identifiers. -/
def subst (σ : Fin k → Ident k') : Ident k → Ident k'
  | bound i => σ i
  | rt a => rt a

/-- Weakening an identifier by one more bound identifier. -/
def shift (ι : Ident k) : Ident (k + 1) := ι.subst (fun i => bound i.succ)

@[simp] lemma subst_bound' (σ : Fin k → Ident k') (i : Fin k) : (bound i).subst σ = σ i := rfl
@[simp] lemma subst_rt (σ : Fin k → Ident k') (a : ℕ) : (rt a : Ident k).subst σ = rt a := rfl
@[simp] lemma shift_bound (i : Fin k) : (bound i).shift = bound i.succ := rfl
@[simp] lemma shift_rt (a : ℕ) : (rt a : Ident k).shift = rt a := rfl

lemma subst_subst (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') (ι : Ident k) :
    (ι.subst σ).subst τ = ι.subst (fun i => (σ i).subst τ) := by
  cases ι <;> rfl

@[simp] lemma subst_id (ι : Ident k) : ι.subst bound = ι := by cases ι <;> rfl

end Ident

/-- Lifting an identifier substitution under an identifier binder. -/
def ISubst.up {k k' : ℕ} (σ : Fin k → Ident k') : Fin (k + 1) → Ident (k' + 1) :=
  Fin.cases (Ident.bound 0) (fun i => (σ i).shift)

@[simp] lemma ISubst.up_zero {k k' : ℕ} (σ : Fin k → Ident k') :
    ISubst.up σ 0 = Ident.bound 0 := rfl
@[simp] lemma ISubst.up_succ {k k' : ℕ} (σ : Fin k → Ident k') (i : Fin k) :
    ISubst.up σ i.succ = (σ i).shift := rfl

lemma Ident.shift_subst_up {k k' : ℕ} (σ : Fin k → Ident k') (ι : Ident k) :
    ι.shift.subst (ISubst.up σ) = (ι.subst σ).shift := by
  cases ι <;> rfl

lemma ISubst.up_comp {k k' k'' : ℕ} (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') :
    (fun i => (ISubst.up σ i).subst (ISubst.up τ)) = ISubst.up (fun i => (σ i).subst τ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [ISubst.up_succ]
    cases σ i with
    | bound j => rfl
    | rt a => rfl

lemma ISubst.up_bound {k : ℕ} : ISubst.up (Ident.bound : Fin k → Ident k) = Ident.bound := by
  funext i; cases i using Fin.cases <;> rfl

namespace Ty

variable {R : Type} {k k' k'' : ℕ}

/-- Simultaneous substitution of identifiers for the bound identifiers of a type. -/
def subst : {k k' : ℕ} → (Fin k → Ident k') → Ty R k → Ty R k'
  | _, _, σ, lolli A B => lolli (subst σ A) (subst σ B)
  | _, _, σ, tensor A B => tensor (subst σ A) (subst σ B)
  | _, _, _, unit => unit
  | _, _, σ, box r A => box r (subst σ A)
  | _, _, σ, ex A => ex (subst (ISubst.up σ) A)
  | _, _, σ, borrow p A => borrow p (subst σ A)
  | _, _, σ, res κ ι A => res κ (ι.subst σ) (subst σ A)
  | _, _, _, nat => nat
  | _, _, _, float => float

/-- Weakening a type by one bound identifier (the new identifier is index `0`). -/
def shift (A : Ty R k) : Ty R (k + 1) := A.subst (fun i => Ident.bound i.succ)

/-- Instantiating the bound identifier `0`: `A [ι / id]`. -/
def inst (A : Ty R (k + 1)) (ι : Ident k) : Ty R k := A.subst (Fin.cases ι Ident.bound)

lemma subst_subst (σ : Fin k → Ident k') (τ : Fin k' → Ident k'') (A : Ty R k) :
    (A.subst σ).subst τ = A.subst (fun i => (σ i).subst τ) := by
  induction A generalizing k' k'' with
  | lolli A B ihA ihB => simp only [subst, ihA, ihB]
  | tensor A B ihA ihB => simp only [subst, ihA, ihB]
  | unit => rfl
  | box r A ih => simp only [subst, ih]
  | ex A ih => simp only [subst, ih, ISubst.up_comp]
  | borrow p A ih => simp only [subst, ih]
  | res κ ι A ih => simp only [subst, ih, Ident.subst_subst]
  | nat => rfl
  | float => rfl

lemma subst_bound (A : Ty R k) : A.subst Ident.bound = A := by
  induction A with
  | lolli A B ihA ihB => simp only [subst, ihA, ihB]
  | tensor A B ihA ihB => simp only [subst, ihA, ihB]
  | unit => rfl
  | box r A ih => simp only [subst, ih]
  | ex A ih => simp only [subst, ISubst.up_bound, ih]
  | borrow p A ih => simp only [subst, ih]
  | res κ ι A ih => simp only [subst, ih, Ident.subst_id]
  | nat => rfl
  | float => rfl

/-- Two substitutions that agree give the same result. -/
lemma subst_congr {σ τ : Fin k → Ident k'} (h : ∀ i, σ i = τ i) (A : Ty R k) :
    A.subst σ = A.subst τ := by
  rw [show σ = τ from funext h]

/-- Shifting commutes with lifted substitutions. -/
lemma shift_subst_up (σ : Fin k → Ident k') (A : Ty R k) :
    A.shift.subst (ISubst.up σ) = (A.subst σ).shift := by
  simp only [shift, subst_subst]
  apply subst_congr
  intro i
  cases h : σ i <;> simp [h]

/-- Instantiation commutes with substitution. -/
lemma inst_subst (σ : Fin k → Ident k') (A : Ty R (k + 1)) (ι : Ident k) :
    (A.inst ι).subst σ = (A.subst (ISubst.up σ)).inst (ι.subst σ) := by
  simp only [inst, subst_subst]
  apply subst_congr
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Fin.cases_succ, Ident.subst_bound', ISubst.up_succ]
    cases σ i <;> rfl

/-- Instantiating a shifted type gives the type back. -/
@[simp] lemma shift_inst (A : Ty R k) (ι : Ident k) : A.shift.inst ι = A := by
  simp only [shift, inst, subst_subst, Ident.subst_bound', Fin.cases_succ]
  exact subst_bound A

@[simp] lemma shift_unit : (unit : Ty R k).shift = unit := rfl
@[simp] lemma shift_nat : (nat : Ty R k).shift = nat := rfl
@[simp] lemma shift_float : (float : Ty R k).shift = float := rfl
@[simp] lemma shift_lolli (A B : Ty R k) : (lolli A B).shift = lolli A.shift B.shift := rfl
@[simp] lemma shift_tensor (A B : Ty R k) : (tensor A B).shift = tensor A.shift B.shift := rfl
@[simp] lemma shift_box (r : R) (A : Ty R k) : (box r A).shift = box r A.shift := rfl
@[simp] lemma shift_borrow (p : Perm) (A : Ty R k) : (borrow p A).shift = borrow p A.shift := rfl
@[simp] lemma shift_res (κ : ResKind) (ι : Ident k) (A : Ty R k) :
    (res κ ι A).shift = res κ ι.shift A.shift := rfl

end Ty

end FOFU
