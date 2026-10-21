module
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst

/-!
# Heaps and configurations (Section 6.1)

Heaps of the paper,

  `H ::= ∅ | H, x ↦_r v | H, ref ↦_p id | H, id ↦ v_r`
  `v_r ::= arr | ref(v)`        `arr ::= init | arr[n] = v`,

map program variables to graded values, references to (fractional permissions and)
identifiers, and identifiers to resources.  A configuration `H ⊢ t` pairs a heap with a
term whose free variables are in the heap.

## Representation

* A heap with `n` program variables is a `Heap R n`.  Its variables are the de Bruijn
  variables of the configuration's term `t : Term R n`, so `fv(t) ⊆ dom(H)` holds by
  construction.  The stored values may mention any heap variable; when the heap grows
  (`Heap.snoc`), all stored terms are weakened.
* References and identifiers are natural numbers; `H.refs a = some (p, id)` is the entry
  `a ↦_p id` and `H.ress id = some v_r` is the entry `id ↦ v_r`.  Heaps are therefore
  taken up to reordering of their entries, as the reduction rules (which match entries
  "anywhere in the heap") require.  Heap permissions are rationals.
* `ArrVal.read arr i` is the most recent value written at index `i` (the paper's rule
  for `readArray` matches `arr[i] = v`).
-/

@[expose] public section

namespace FOFU

variable {R : Type}

/-- Array values `arr ::= init | arr[n] = v`. -/
inductive ArrVal (R : Type) (n : ℕ) where
  | init : ArrVal R n
  | write : ArrVal R n → ℕ → Term R n → ArrVal R n

/-- Resource values `v_r ::= arr | ref(v)`. -/
inductive ResVal (R : Type) (n : ℕ) where
  | arr : ArrVal R n → ResVal R n
  | ref : Term R n → ResVal R n

namespace ArrVal

variable {n m : ℕ}

/-- The value most recently written at index `i`. -/
def read : ArrVal R n → ℕ → Option (Term R n)
  | init, _ => none
  | write a j v, i => if i = j then some v else a.read i

/-- Renaming the variables of the stored values. -/
def rename (ρ : Fin n → Fin m) : ArrVal R n → ArrVal R m
  | init => init
  | write a j v => write (a.rename ρ) j (v.rename ρ)

end ArrVal

/-- Renaming the variables of a resource value. -/
def ResVal.rename {n m : ℕ} (ρ : Fin n → Fin m) : ResVal R n → ResVal R m
  | arr a => arr (a.rename ρ)
  | ref v => ref (v.rename ρ)

/-- Heaps with `n` program variables. -/
structure Heap (R : Type) (n : ℕ) where
  /-- `x ↦_r v`: grade and value of each program variable -/
  vars : Fin n → R × Term R n
  /-- `ref ↦_p id` -/
  refs : ℕ → Option (ℚ × ℕ)
  /-- `id ↦ v_r` -/
  ress : ℕ → Option (ResVal R n)

namespace Heap

variable {n : ℕ}

/-- The empty heap `∅`. -/
def empty : Heap R 0 := ⟨Fin.elim0, fun _ => none, fun _ => none⟩

/-- `H, x ↦_r v` for a fresh (last) variable `x`. -/
def snoc (H : Heap R n) (r : R) (v : Term R n) : Heap R (n + 1) where
  vars := Fin.lastCases (r, v.rename Fin.castSucc)
    (fun i => ((H.vars i).1, (H.vars i).2.rename Fin.castSucc))
  refs := H.refs
  ress := fun id => (H.ress id).map (ResVal.rename Fin.castSucc)

/-- Adding (or overwriting) the entry `ref ↦_p id`. -/
def addRef (H : Heap R n) (a : ℕ) (p : ℚ) (id : ℕ) : Heap R n :=
  { H with refs := Function.update H.refs a (some (p, id)) }

/-- Removing the entry for the reference `a`. -/
def eraseRef (H : Heap R n) (a : ℕ) : Heap R n :=
  { H with refs := Function.update H.refs a none }

/-- Adding (or overwriting) the entry `id ↦ v_r`. -/
def addRes (H : Heap R n) (id : ℕ) (vr : ResVal R n) : Heap R n :=
  { H with ress := Function.update H.ress id (some vr) }

/-- Removing the entry for the identifier `id`. -/
def eraseRes (H : Heap R n) (id : ℕ) : Heap R n :=
  { H with ress := Function.update H.ress id none }

/-- `id` is fresh for `H`: it has no entry and no reference points to it. -/
def IdFresh (H : Heap R n) (id : ℕ) : Prop :=
  H.ress id = none ∧ ∀ a q, H.refs a ≠ some (q, id)

@[simp] lemma snoc_refs (H : Heap R n) (r : R) (v : Term R n) : (H.snoc r v).refs = H.refs := rfl
@[simp] lemma addRes_refs (H : Heap R n) (id : ℕ) (vr : ResVal R n) :
    (H.addRes id vr).refs = H.refs := rfl
@[simp] lemma eraseRes_refs (H : Heap R n) (id : ℕ) : (H.eraseRes id).refs = H.refs := rfl
@[simp] lemma addRef_ress (H : Heap R n) (a : ℕ) (p : ℚ) (id : ℕ) :
    (H.addRef a p id).ress = H.ress := rfl
@[simp] lemma eraseRef_ress (H : Heap R n) (a : ℕ) : (H.eraseRef a).ress = H.ress := rfl

end Heap

end FOFU
