module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypeSubst

/-!
# Resources and their interfaces (Section 5)

* `PrimTy p A`: the types of the resource primitives, i.e. the interfaces for mutable
  arrays of floats (`newArray`, `readArray`, `writeArray`, `deleteArray`) and for
  polymorphic references (`newRef`, `readRef`, `swapRef`, `freezeRef`).  The
  primitives are typed in any context of the form `0 · Γ` (rule `prim` of `HasType`).
  Each schematic variable of the paper (`id`, `p`, `r`, `A`) is a parameter of the
  corresponding constructor; `writeArray` and `swapRef` require `p ≡ 1 ∨ p ≡ *`.
* `Ty.copyable A` and `Ty.cloneable A`: the predicates `copyable` and `cloneable` of §5
  (`cloneable` is the side condition of the rule `Clone` of §4).  They are `Bool`-valued
  functions, so side conditions are closed by `rfl` / `decide`.
* `Term.Allocates t`: the predicate `resourceAllocator(t)` restricting promotion
  (rule `pr`, §3 and §5).  The paper only says that it holds of terms that allocate
  resources; we take it to mean that `t` contains `newArray`, `newRef` or a `clone`
  (which allocates copies of resources).  It is defined with the generic "some operator
  occurs" predicate of the binding layer, and is decidable.
-/

@[expose] public section

namespace FOFU

open Binding

variable {R : Type} {k : ℕ}

open Ty

/-- The types of the resource primitives (§5). -/
inductive PrimTy : Prim → Ty R k → Prop where
  /-- `newArray : ℕ ⊸ ∃ id. *(Array_id 𝔽)` -/
  | newArray : PrimTy .newArray (lolli nat (ex (star (array .zero))))
  /-- `readArray : &_p (Array_id 𝔽) ⊸ ℕ ⊸ 𝔽 ⊗ &_p (Array_id 𝔽)` -/
  | readArray (p : Perm) (ι : Var k) :
      PrimTy .readArray
        (lolli (borrow p (array ι)) (lolli nat (tensor float (borrow p (array ι)))))
  /-- `writeArray : &_p (Array_id 𝔽) ⊸ ℕ ⊸ 𝔽 ⊸ &_p (Array_id 𝔽)` for `p ≡ 1 ∨ p ≡ *` -/
  | writeArray (p : Perm) (ι : Var k) (hp : p = Perm.one ∨ p = Perm.star) :
      PrimTy .writeArray
        (lolli (borrow p (array ι)) (lolli nat (lolli float (borrow p (array ι)))))
  /-- `deleteArray : *(Array_id 𝔽) ⊸ unit` -/
  | deleteArray (ι : Var k) : PrimTy .deleteArray (lolli (star (array ι)) unit)
  /-- `newRef : A ⊸ ∃ id. *(Ref_id A)` -/
  | newRef (A : Ty R k) : PrimTy .newRef (lolli A (ex (star (ref .zero A.shift))))
  /-- `readRef : &_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))` -/
  | readRef (p : Perm) (ι : Var k) (r : R) (A : Ty R k) :
      PrimTy .readRef
        (lolli (borrow p (ref ι (box r A))) (tensor A (borrow p (ref ι (box r A)))))
  /-- **Amendment (not in the paper).** The grade-splitting read
  `readRefSplit : *(Ref_id (□_(q+r) A)) ⊸ □_q A ⊗ *(Ref_id (□_r A))`, i.e. Granule's
  `readRef : *(Ref id (a [q+r])) → (a [q], *(Ref id (a [r])))`.  It is the interface that
  the paper's `exampleGraded` uses.  It changes the type of the reference, so it is only
  offered for the unique permission `*` (a borrow `&_p` with `p ≢ *` cannot change type:
  other borrows of the same reference, or the owner waiting in `withBorrow`, still expect
  the old type). -/
  | readRefSplit [Add R] (ι : Var k) (q r : R) (A : Ty R k) :
      PrimTy .readRefSplit
        (lolli (star (ref ι (box (q + r) A))) (tensor (box q A) (star (ref ι (box r A)))))
  /-- `swapRef : &_p (Ref_id A) ⊸ A ⊸ A ⊗ &_p (Ref_id A)` for `p ≡ 1 ∨ p ≡ *` -/
  | swapRef (p : Perm) (ι : Var k) (A : Ty R k) (hp : p = Perm.one ∨ p = Perm.star) :
      PrimTy .swapRef (lolli (borrow p (ref ι A)) (lolli A (tensor A (borrow p (ref ι A)))))
  /-- `freezeRef : *(Ref_id A) ⊸ A` -/
  | freezeRef (ι : Var k) (A : Ty R k) : PrimTy .freezeRef (lolli (star (ref ι A)) A)

/-- `copyable(A)`: `unit`, `𝔽`, and products of copyable types. -/
def Ty.copyable : Ty R k → Bool
  | .unit => true
  | .float => true
  | .tensor A B => A.copyable && B.copyable
  | _ => false

/-- `cloneable(A)`: arrays of floats `Array_id 𝔽`, references `Ref_id A` to cloneable or
copyable types, and products of cloneable types. -/
def Ty.cloneable : Ty R k → Bool
  | .res .array _ .float => true
  | .res .ref _ A => A.cloneable || A.copyable
  | .tensor A B => A.cloneable && B.cloneable
  | _ => false

@[simp] lemma Ty.cloneable_array (ι : Var k) : (array ι : Ty R k).cloneable = true := rfl

/-- `copyable` does not depend on the identifiers. -/
@[simp] lemma Ty.copyable_ren {k' : ℕ} (r : Var k → Var k') (A : Ty R k) :
    (A.ren r).copyable = A.copyable := by
  induction A generalizing k' <;> simp_all [Ty.copyable, Ty.ren]

/-- `cloneable` does not depend on the identifiers. -/
@[simp] lemma Ty.cloneable_ren {k' : ℕ} (r : Var k → Var k') (A : Ty R k) :
    (A.ren r).cloneable = A.cloneable := by
  induction A generalizing k' with
  | res κ ι A ih =>
    cases κ
    · cases A <;> simp_all [Ty.cloneable, Ty.ren]
    · simp only [Ty.ren, Ty.cloneable, ih, Ty.copyable_ren]
  | _ => simp_all [Ty.cloneable, Ty.ren]

/-- The allocating operators: `clone`, `newArray` and `newRef`. -/
def Op.allocates {ρ : ℕ} : Op R ρ → Bool
  | .clone => true
  | .prim .newArray => true
  | .prim .newRef => true
  | _ => false

/-- `resourceAllocator(t)`: `t` contains an allocating construct (`newArray`, `newRef`
or `clone`). -/
def Term.Allocates {n ρ : ℕ} (t : Term R n ρ) : Prop :=
  Tm.HasOp (S := sig R ρ) (fun o => Op.allocates o = true) t

instance Term.decidableAllocates {n ρ : ℕ} (t : Term R n ρ) : Decidable t.Allocates :=
  Tm.decidableHasOp _ t

/-- Renaming does not change whether a term allocates. -/
@[simp] lemma Term.allocates_ren {n m ρ : ℕ} (r : Var n → Var m) (t : Term R n ρ) :
    Term.Allocates (Tm.ren r t : Term R m ρ) ↔ t.Allocates :=
  Tm.hasOp_ren_iff r t

end FOFU
