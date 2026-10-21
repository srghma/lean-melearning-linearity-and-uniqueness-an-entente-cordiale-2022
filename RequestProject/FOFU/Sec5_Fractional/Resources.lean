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
* `Copyable A` and `Cloneable A`: the predicates `copyable` and `cloneable` of §5
  (`cloneable` is the side condition of the rule `Clone` of §4).
* `Term.Allocates t`: the predicate `resourceAllocator(t)` restricting promotion
  (rule `pr`, §3 and §5).  The paper only says that it holds of terms that allocate
  resources; we take it to mean that `t` contains `newArray`, `newRef` or a `clone`
  (which allocates copies of resources).
-/

@[expose] public section

namespace FOFU

variable {R : Type} {k : ℕ}

open Ty

/-- The types of the resource primitives (§5). -/
inductive PrimTy : Prim → Ty R k → Prop where
  /-- `newArray : ℕ ⊸ ∃ id. *(Array_id 𝔽)` -/
  | newArray : PrimTy .newArray (lolli nat (ex (star (array (.bound 0)))))
  /-- `readArray : &_p (Array_id 𝔽) ⊸ ℕ ⊸ 𝔽 ⊗ &_p (Array_id 𝔽)` -/
  | readArray (p : Perm) (ι : Ident k) :
      PrimTy .readArray
        (lolli (borrow p (array ι)) (lolli nat (tensor float (borrow p (array ι)))))
  /-- `writeArray : &_p (Array_id 𝔽) ⊸ ℕ ⊸ 𝔽 ⊸ &_p (Array_id 𝔽)` for `p ≡ 1 ∨ p ≡ *` -/
  | writeArray (p : Perm) (ι : Ident k) (hp : p = Perm.one ∨ p = Perm.star) :
      PrimTy .writeArray
        (lolli (borrow p (array ι)) (lolli nat (lolli float (borrow p (array ι)))))
  /-- `deleteArray : *(Array_id 𝔽) ⊸ unit` -/
  | deleteArray (ι : Ident k) : PrimTy .deleteArray (lolli (star (array ι)) unit)
  /-- `newRef : A ⊸ ∃ id. *(Ref_id A)` -/
  | newRef (A : Ty R k) : PrimTy .newRef (lolli A (ex (star (ref (.bound 0) A.shift))))
  /-- `readRef : &_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))` -/
  | readRef (p : Perm) (ι : Ident k) (r : R) (A : Ty R k) :
      PrimTy .readRef
        (lolli (borrow p (ref ι (box r A))) (tensor A (borrow p (ref ι (box r A)))))
  /-- **Amendment (not in the paper).** The grade-splitting read
  `readRefSplit : *(Ref_id (□_(q+r) A)) ⊸ □_q A ⊗ *(Ref_id (□_r A))`, i.e. Granule's
  `readRef : *(Ref id (a [q+r])) → (a [q], *(Ref id (a [r])))`.  It is the interface that
  the paper's `exampleGraded` uses.  It changes the type of the reference, so it is only
  offered for the unique permission `*` (a borrow `&_p` with `p ≢ *` cannot change type:
  other borrows of the same reference, or the owner waiting in `withBorrow`, still expect
  the old type). -/
  | readRefSplit [Add R] (ι : Ident k) (q r : R) (A : Ty R k) :
      PrimTy .readRefSplit
        (lolli (star (ref ι (box (q + r) A))) (tensor (box q A) (star (ref ι (box r A)))))
  /-- `swapRef : &_p (Ref_id A) ⊸ A ⊸ A ⊗ &_p (Ref_id A)` for `p ≡ 1 ∨ p ≡ *` -/
  | swapRef (p : Perm) (ι : Ident k) (A : Ty R k) (hp : p = Perm.one ∨ p = Perm.star) :
      PrimTy .swapRef (lolli (borrow p (ref ι A)) (lolli A (tensor A (borrow p (ref ι A)))))
  /-- `freezeRef : *(Ref_id A) ⊸ A` -/
  | freezeRef (ι : Ident k) (A : Ty R k) : PrimTy .freezeRef (lolli (star (ref ι A)) A)

/-- `copyable(A)`: `unit`, `𝔽`, and products of copyable types. -/
inductive Copyable : Ty R k → Prop where
  | unit : Copyable unit
  | float : Copyable float
  | tensor {A B : Ty R k} : Copyable A → Copyable B → Copyable (tensor A B)

/-- `cloneable(A)`: arrays of floats, references to cloneable or copyable types, and
products of cloneable types. -/
inductive Cloneable : Ty R k → Prop where
  | array (ι : Ident k) : Cloneable (array ι)
  /-- `cloneable(A) ∨ copyable(A) ⟹ cloneable(Ref_id A)`, first disjunct -/
  | refCloneable (ι : Ident k) {A : Ty R k} : Cloneable A → Cloneable (ref ι A)
  /-- `cloneable(A) ∨ copyable(A) ⟹ cloneable(Ref_id A)`, second disjunct -/
  | refCopyable (ι : Ident k) {A : Ty R k} : Copyable A → Cloneable (ref ι A)
  | tensor {A B : Ty R k} : Cloneable A → Cloneable B → Cloneable (tensor A B)

/-- `resourceAllocator(t)`: `t` contains an allocating construct (`newArray`, `newRef`
or `clone`). -/
def Term.Allocates : {n : ℕ} → Term R n → Prop
  | _, .var _ => False
  | _, .lam t => t.Allocates
  | _, .app t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .pair t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .letPair t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .unit => False
  | _, .letUnit t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .box _ t => t.Allocates
  | _, .letBox t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .pack t => t.Allocates
  | _, .unpack t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .share _ t => t.Allocates
  | _, .clone _ _ => True
  | _, .withBorrow t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .split t => t.Allocates
  | _, .join t₁ t₂ => t₁.Allocates ∨ t₂.Allocates
  | _, .push t => t.Allocates
  | _, .pull t => t.Allocates
  | _, .nat _ => False
  | _, .float _ => False
  | _, .prim p => p = .newArray ∨ p = .newRef
  | _, .star t => t.Allocates
  | _, .unborrow t => t.Allocates
  | _, .ref _ => False

end FOFU
