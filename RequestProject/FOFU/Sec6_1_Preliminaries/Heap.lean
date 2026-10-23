module
public import RequestProject.FOFU.Sec3_CoreCalculus.RenameSubst
public import RequestProject.Common.Ctx

/-!
# Heaps and configurations (Section 6.1)

Heaps of the paper,

  `H ::= ∅ | H, x ↦_r v | H, ref ↦_p id | H, id ↦ v_r`
  `v_r ::= arr | ref(v)`        `arr ::= init | arr[n] = v`,

map program variables to graded values, references to fractional permissions and
identifiers, and identifiers to resources.  A configuration `H ⊢ t` pairs a heap with a
term whose free variables and references are in the heap.

## Representation: scoped heaps

A heap `H : Heap R n ρ ι` has exactly one entry for each of the `n` program variables, the
`ρ` runtime references and the `ι` identifiers in scope.  The configuration's term is a
`Term R n ρ`, so `fv(t) ⊆ dom(H)` and `refs(t) ⊆ dom(H)` hold *by construction*, and the
runtime types are `Ty R ι`.

* `H.vars : Ctx (R × Term R n ρ) n`: the entry `x ↦_r v` of each variable; the stored
  values may mention every variable and reference in scope.
* `H.refs : Ctx (Option (Frac × Var ι)) ρ`: the entry `ref ↦_p id` of each reference, or
  `none` if the reference has been deallocated.  Permissions are fractions `0 < p ≤ 1`
  (`Frac`), so a heap cannot store a meaningless permission.
* `H.ress : Ctx (Option (ResVal R n ρ)) ι`: the entry `id ↦ v_r` of each identifier, or
  `none` if the identifier has no resource (`id ∉ dom(H)`).

Heaps grow *at index zero*, like contexts under binders: `H.snoc r v` binds the new
variable `Var.zero`, `H.newRef p id` allocates the new reference `Var.zero`, and
`H.addId o` adds the new identifier `Var.zero`; the stored terms are weakened accordingly.
Allocation therefore *creates* a fresh name, and no freshness premise is needed.

* `ArrVal.Reads arr i v` (`arr[i] = v`) says that `v` is the most recent value written
  at index `i` (the paper's rule for `readArray` matches `arr[i] = v`); `ArrVal.read`
  is the corresponding function.
-/

@[expose] public section

namespace FOFU

variable {R : Type}

/-- Array values `arr ::= init | arr[n] = v`. -/
inductive ArrVal (R : Type) (n ρ : ℕ) where
  | init : ArrVal R n ρ
  | write : ArrVal R n ρ → ℕ → Term R n ρ → ArrVal R n ρ

/-- Resource values `v_r ::= arr | ref(v)`. -/
inductive ResVal (R : Type) (n ρ : ℕ) where
  | arr : ArrVal R n ρ → ResVal R n ρ
  | ref : Term R n ρ → ResVal R n ρ

namespace ArrVal

variable {n ρ m ρ' : ℕ}

/-- The value most recently written at index `i`. -/
def read : ArrVal R n ρ → ℕ → Option (Term R n ρ)
  | init, _ => none
  | write a j v, i => if i = j then some v else a.read i

/-- Applying a map to the stored values. -/
def map (f : Term R n ρ → Term R m ρ') : ArrVal R n ρ → ArrVal R m ρ'
  | init => init
  | write a j v => write (a.map f) j (f v)

/-- `arr[i] = v`: the value most recently written at index `i` of `arr` is `v`. -/
inductive Reads : ArrVal R n ρ → ℕ → Term R n ρ → Prop where
  /-- the last write is at index `i` -/
  | here {a : ArrVal R n ρ} {i : ℕ} {v : Term R n ρ} : Reads (write a i v) i v
  /-- the last write is at another index `j ≠ i` -/
  | there {a : ArrVal R n ρ} {i j : ℕ} {v w : Term R n ρ} :
      i ≠ j → Reads a i v → Reads (write a j w) i v

@[simp] lemma reads_iff {a : ArrVal R n ρ} {i : ℕ} {v : Term R n ρ} :
    a.Reads i v ↔ a.read i = some v := by
  constructor
  · intro h
    induction h with
    | here => simp [read]
    | there hij _ ih => simp [read, hij, ih]
  · intro h
    induction a with
    | init => simp [read] at h
    | write a j w ih =>
      by_cases hij : i = j
      · subst hij; simp [read] at h; subst h; exact .here
      · simp [read, hij] at h; exact .there hij (ih h)

end ArrVal

/-- Applying a map to the stored values of a resource. -/
def ResVal.map {n ρ m ρ' : ℕ} (f : Term R n ρ → Term R m ρ') : ResVal R n ρ → ResVal R m ρ'
  | arr a => arr (a.map f)
  | ref v => ref (f v)

/-- Heaps with `n` program variables, `ρ` references and `ι` identifiers. -/
structure Heap (R : Type) (n ρ ι : ℕ) where
  /-- `x ↦_r v`: grade and value of each program variable -/
  vars : Ctx (R × Term R n ρ) n
  /-- `ref ↦_p id` (or `none` for a deallocated reference) -/
  refs : Ctx (Option (Frac × Var ι)) ρ
  /-- `id ↦ v_r` (or `none` if `id ∉ dom(H)`) -/
  ress : Ctx (Option (ResVal R n ρ)) ι

namespace Heap

variable {n ρ ι : ℕ}

/-- The empty heap `∅`. -/
def empty : Heap R 0 0 0 := ⟨.nil, .nil, .nil⟩

/-- `H, x ↦_r v` for a new variable `x = Var.zero`; the stored terms are weakened. -/
def snoc (H : Heap R n ρ ι) (r : R) (v : Term R n ρ) : Heap R (n + 1) ρ ι where
  vars := H.vars.map (fun e => (e.1, e.2.rename Var.succ)) ,, (r, v.rename Var.succ)
  refs := H.refs
  ress := H.ress.map (Option.map (ResVal.map (Term.rename Var.succ)))

/-- `H, ref ↦_p id` for a new reference `ref = Var.zero`; the stored terms are weakened. -/
def newRef (H : Heap R n ρ ι) (p : Frac) (id : Var ι) : Heap R n (ρ + 1) ι where
  vars := H.vars.map (fun e => (e.1, renameRefs Var.succ e.2))
  refs := H.refs ,, some (p, id)
  ress := H.ress.map (Option.map (ResVal.map (renameRefs Var.succ)))

/-- Adding a new identifier `id = Var.zero`, with the entry `id ↦ v_r` (`o = some v_r`) or
without entry (`o = none`); the identifiers of the references are weakened. -/
def addId (H : Heap R n ρ ι) (o : Option (ResVal R n ρ)) : Heap R n ρ (ι + 1) where
  vars := H.vars
  refs := H.refs.map (Option.map fun e => (e.1, e.2.succ))
  ress := H.ress ,, o

/-- Replacing the entry of the identifier `id`. -/
def setRes (H : Heap R n ρ ι) (id : Var ι) (o : Option (ResVal R n ρ)) : Heap R n ρ ι :=
  { H with ress := H.ress.set id o }

/-- Replacing the entry of the reference `a`. -/
def setRef (H : Heap R n ρ ι) (a : Var ρ) (o : Option (Frac × Var ι)) : Heap R n ρ ι :=
  { H with refs := H.refs.set a o }

/-- Deallocating the reference `a`. -/
abbrev eraseRef (H : Heap R n ρ ι) (a : Var ρ) : Heap R n ρ ι := H.setRef a none

/-- Removing the entry of the identifier `id`. -/
abbrev eraseRes (H : Heap R n ρ ι) (id : Var ι) : Heap R n ρ ι := H.setRes id none

@[simp] lemma snoc_refs (H : Heap R n ρ ι) (r : R) (v : Term R n ρ) :
    (H.snoc r v).refs = H.refs := rfl
@[simp] lemma newRef_refs (H : Heap R n ρ ι) (p : Frac) (id : Var ι) :
    (H.newRef p id).refs = H.refs ,, some (p, id) := rfl
@[simp] lemma snoc_ress (H : Heap R n ρ ι) (r : R) (v : Term R n ρ) :
    (H.snoc r v).ress = H.ress.map (Option.map (ResVal.map (Term.rename Var.succ))) := rfl
@[simp] lemma newRef_ress (H : Heap R n ρ ι) (p : Frac) (id : Var ι) :
    (H.newRef p id).ress = H.ress.map (Option.map (ResVal.map (renameRefs Var.succ))) := rfl
@[simp] lemma addId_refs (H : Heap R n ρ ι) (o : Option (ResVal R n ρ)) :
    (H.addId o).refs = H.refs.map (Option.map fun e => (e.1, e.2.succ)) := rfl
@[simp] lemma addId_ress (H : Heap R n ρ ι) (o : Option (ResVal R n ρ)) :
    (H.addId o).ress = H.ress ,, o := rfl
@[simp] lemma setRes_refs (H : Heap R n ρ ι) (id : Var ι) (o : Option (ResVal R n ρ)) :
    (H.setRes id o).refs = H.refs := rfl
@[simp] lemma setRes_ress (H : Heap R n ρ ι) (id : Var ι) (o : Option (ResVal R n ρ)) :
    (H.setRes id o).ress = H.ress.set id o := rfl
@[simp] lemma setRef_refs (H : Heap R n ρ ι) (a : Var ρ) (o : Option (Frac × Var ι)) :
    (H.setRef a o).refs = H.refs.set a o := rfl
@[simp] lemma setRef_ress (H : Heap R n ρ ι) (a : Var ρ) (o : Option (Frac × Var ι)) :
    (H.setRef a o).ress = H.ress := rfl

end Heap

end FOFU
