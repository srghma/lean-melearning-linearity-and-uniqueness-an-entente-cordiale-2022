module
public import RequestProject.LCU.Ext2_MutableArrays.RefShift

/-!
# A store-based semantics for the array primitives, and type safety

`CbnSemantics.lean` gives a substitution-based call-by-name semantics for the fragment
without array primitives.  Here we extend it with a *store* of mutable floating-point
arrays, following the array rules of the heap model (Section 3.4):

* `newArray k ⟶ *a` allocates a new array `a` (filled with `0`);
* `readArray (*a) k ⟶ (arr[k], *a)` reads the array;
* `writeArray (*a) k x ⟶ *a` destructively updates the array in the store;
* `deleteArray (*a) ⟶ unit`;
* `copy !u as x in t ⟶ [*θ(u)/x]t`, where `θ` renames the array references of `u` to
  new references pointing to copies of the arrays (rule `copy_β`); concretely every
  array is copied, and `θ` maps `a` to its copy;
* the arguments of primitives are evaluated (also under `*`), and otherwise the rules
  are those of `CbnStep`.

This file contains the definitions: stores (`Store`), the reduction `AStep` and its
reflexive-transitive closure `ASteps`, and well-typed configurations (`ConfOK`).

As in the heap model, configurations are scoped: a configuration `σ ⊢ t` has
`t : Term n ρ` and a store `σ : Store ρ` with one (optional) array for each of the `ρ`
references in scope, and a step `AStep σ t e σ' t'` allocates `e` new references (the most
recent ones, at index zero); the other subterms are weakened along `Var.shiftN e`.
The metatheory is split over two further files:

* `ArrayPreservation.lean`: **subject reduction** (`AStep.preserves`);
* `ArrayProgress.lean`: **progress** (`astep_progress`) and hence **syntactic type
  safety** for closed programs (`array_type_safety`): a well-typed closed program,
  started in the empty store, never gets stuck, even with arrays and in-place updates.

**Caveat.** `deleteArray` does not free memory in this semantics: the array stays in the
store.  Safe deallocation needs the uniqueness guarantee (no other reference to the
deleted array survives), and this file does not prove that guarantee. Here array
references are typed non-linearly throughout.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Stores -/

/-- A store for `ρ` array references: each reference is allocated to an array of floats, or
unallocated (`none`).  Out-of-bounds accesses are ignored, as in the paper, so arrays are
total functions. -/
abbrev Store (ρ : ℕ) : Type := Ctx (Option (ℕ → FloatLit)) ρ

namespace Store

variable {ρ : ℕ}

/-- The empty store. -/
def empty : Store 0 := .nil

/-- Extend a store with a copy of every array: the copy of `a` is `Var.lowAdd a`, the
original is `Var.shiftN ρ a`. -/
def copyAll (σ : Store ρ) : Store (ρ + ρ) := σ.append σ

/-- `a ↦ arr ∈ σ`: the reference `a` is allocated with contents `arr`. -/
def At (σ : Store ρ) (a : Var ρ) (arr : ℕ → FloatLit) : Prop := σ.Lookup a (some arr)

@[simp] lemma at_iff {σ : Store ρ} {a : Var ρ} {arr : ℕ → FloatLit} :
    σ.At a arr ↔ σ.get a = some arr := Ctx.lookup_iff

end Store

/-! ## Reduction -/

/-- Partially applied primitives whose already supplied arguments are fully evaluated
(the array argument to a reference `*a`, the index to a literal `k`); the next argument
of such a term is evaluated.  This is a sub-grammar of the partially applied primitives
`PrimFun` of the paper. -/
inductive ReadyPrim (n ρ : ℕ) : Type where
  /-- a primitive applied to no argument -/
  | const (p : Prim)
  /-- `readArray (*a)` -/
  | read₁ (a : Var ρ)
  /-- `writeArray (*a)` -/
  | write₁ (a : Var ρ)
  /-- `writeArray (*a) k` -/
  | write₂ (a : Var ρ) (k : ℕ)

namespace ReadyPrim

variable {n ρ : ℕ}

/-- The embedding into terms. -/
@[simp] def toTerm : ReadyPrim n ρ → Term n ρ
  | const p => .prim p
  | read₁ a => .app (.prim .readArray) (.star (.ref a))
  | write₁ a => .app (.prim .writeArray) (.star (.ref a))
  | write₂ a k => .app (.app (.prim .writeArray) (.star (.ref a))) (.nat k)

/-- The embedding into the partially applied primitives of the paper. -/
def toPrimFun : ReadyPrim n ρ → PrimFun n ρ
  | const p => .const p
  | read₁ a => .readArray₁ (.star (.ref a))
  | write₁ a => .writeArray₁ (.star (.ref a))
  | write₂ a k => .writeArray₂ (.star (.ref a)) (.nat k)

@[simp] lemma toPrimFun_toTerm (p : ReadyPrim n ρ) : p.toPrimFun.toTerm = p.toTerm := by
  cases p <;> rfl

/-- Renaming the array references of a ready primitive. -/
def renameRefs {ρ' : ℕ} (θ : Var ρ → Var ρ') : ReadyPrim n ρ → ReadyPrim n ρ'
  | const p => const p
  | read₁ a => read₁ (θ a)
  | write₁ a => write₁ (θ a)
  | write₂ a k => write₂ (θ a) k

@[simp] lemma renameRefs_toTerm {ρ' : ℕ} (θ : Var ρ → Var ρ') (p : ReadyPrim n ρ) :
    (p.renameRefs θ).toTerm = LCU.renameRefs θ p.toTerm := by
  cases p <;> rfl

end ReadyPrim

/-- `t` is (the embedding of) an element of the grammar `ReadyPrim n ρ`. -/
def PrimReady {n ρ : ℕ} (t : Term n ρ) : Prop := ∃ p : ReadyPrim n ρ, p.toTerm = t

namespace PrimReady

variable {n ρ : ℕ}

lemma prim (p : Prim) : PrimReady (Term.prim p : Term n ρ) := ⟨.const p, rfl⟩
lemma read₁ (a : Var ρ) : PrimReady (app (Term.prim .readArray) (star (ref a)) : Term n ρ) :=
  ⟨.read₁ a, rfl⟩
lemma write₁ (a : Var ρ) : PrimReady (app (Term.prim .writeArray) (star (ref a)) : Term n ρ) :=
  ⟨.write₁ a, rfl⟩
lemma write₂ (a : Var ρ) (k : ℕ) :
    PrimReady (app (app (Term.prim .writeArray) (star (ref a))) (nat k) : Term n ρ) :=
  ⟨.write₂ a k, rfl⟩

/-- Ready primitives are partially applied primitives in the sense of `Values.lean`. -/
lemma isPrimFun {t : Term n ρ} : PrimReady t → IsPrimFun t
  | ⟨p, hp⟩ => ⟨p.toPrimFun, by rw [ReadyPrim.toPrimFun_toTerm, hp]⟩

end PrimReady

/-- Single-step reduction `σ ⊢ t ⟶ σ' ⊢ t'` of the store-based semantics, allocating `e`
new array references. -/
inductive AStep : {n ρ : ℕ} → Store ρ → Term n ρ → (e : ℕ) → Store (ρ + e) →
    Term n (ρ + e) → Prop where
  | betaLolli {n ρ : ℕ} (σ : Store ρ) (t : Term (n + 1) ρ) (u : Term n ρ) :
      AStep σ (app (lam t) u) 0 σ (t.subst1 u)
  | betaTensor {n ρ : ℕ} (σ : Store ρ) (t₁ t₂ : Term n ρ) (t : Term (n + 2) ρ) :
      AStep σ (letPair (pair t₁ t₂) t) 0 σ (t.subst2 t₁ t₂)
  | betaUnit {n ρ : ℕ} (σ : Store ρ) (t : Term n ρ) : AStep σ (letUnit unit t) 0 σ t
  | betaBang {n ρ : ℕ} (σ : Store ρ) (u : Term n ρ) (t : Term (n + 1) ρ) :
      AStep σ (letBang (bang u) t) 0 σ (t.subst1 u)
  | betaBorrow {n ρ : ℕ} (σ : Store ρ) (t : Term n ρ) : AStep σ (borrow (star t)) 0 σ (bang t)
  /-- `copy_β`: every array is copied; the references of `u` are renamed to the copies. -/
  | betaCopy {n ρ : ℕ} (σ : Store ρ) (u : Term n ρ) (t : Term (n + 1) ρ) :
      AStep σ (copy (bang u) t) ρ σ.copyAll
        ((LCU.renameRefs (Var.shiftN ρ) t).subst1 (star (LCU.renameRefs Var.lowAdd u)))
  | app {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)}
      (u : Term n ρ) :
      AStep σ t e σ' t' → AStep σ (app t u) e σ' (app t' (LCU.renameRefs (Var.shiftN e) u))
  | letPair {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)}
      (u : Term (n + 2) ρ) :
      AStep σ t e σ' t' →
      AStep σ (letPair t u) e σ' (letPair t' (LCU.renameRefs (Var.shiftN e) u))
  | letUnit {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)}
      (u : Term n ρ) :
      AStep σ t e σ' t' →
      AStep σ (letUnit t u) e σ' (letUnit t' (LCU.renameRefs (Var.shiftN e) u))
  | letBang {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)}
      (u : Term (n + 1) ρ) :
      AStep σ t e σ' t' →
      AStep σ (letBang t u) e σ' (letBang t' (LCU.renameRefs (Var.shiftN e) u))
  | borrow {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)} :
      AStep σ t e σ' t' → AStep σ (borrow t) e σ' (borrow t')
  | copy {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {t : Term n ρ} {t' : Term n (ρ + e)}
      (u : Term (n + 1) ρ) :
      AStep σ t e σ' t' → AStep σ (copy t u) e σ' (copy t' (LCU.renameRefs (Var.shiftN e) u))
  /-- evaluation of the next argument of a primitive -/
  | primArg {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} {f t : Term n ρ}
      {t' : Term n (ρ + e)} :
      PrimReady f → AStep σ t e σ' t' →
      AStep σ (app f t) e σ' (app (LCU.renameRefs (Var.shiftN e) f) t')
  /-- evaluation under `*` of the (unique) array argument of a primitive -/
  | primStar {n ρ e : ℕ} {σ : Store ρ} {σ' : Store (ρ + e)} (p : Prim) {s : Term n ρ}
      {s' : Term n (ρ + e)} :
      AStep σ s e σ' s' → AStep σ (app (prim p) (star s)) e σ' (app (prim p) (star s'))
  /-- `newArray`: the new array is the new reference `Var.zero` -/
  | newArray {n ρ : ℕ} (σ : Store ρ) (k : ℕ) :
      AStep σ (app (prim .newArray) (nat k) : Term n ρ) 1 (σ ,, some fun _ => 0)
        (star (ref .zero))
  | readArray {n ρ : ℕ} (σ : Store ρ) (a : Var ρ) (k : ℕ) (arr : ℕ → FloatLit) : σ.At a arr →
      AStep σ (app (app (prim .readArray) (star (ref a))) (nat k) : Term n ρ) 0 σ
        (pair (float (arr k)) (star (ref a)))
  | writeArray {n ρ : ℕ} (σ : Store ρ) (a : Var ρ) (k : ℕ) (x : FloatLit) (arr : ℕ → FloatLit) :
      σ.At a arr →
      AStep σ (app (app (app (prim .writeArray) (star (ref a))) (nat k)) (float x) : Term n ρ) 0
        (σ.set a (some (Function.update arr k x))) (star (ref a))
  | deleteArray {n ρ : ℕ} (σ : Store ρ) (a : Var ρ) :
      AStep σ (app (prim .deleteArray) (star (ref a)) : Term n ρ) 0 σ unit

/-- Multi-step reduction `σ ⊢ t ⟶* σ' ⊢ t'`. -/
inductive ASteps {n ρ : ℕ} (σ : Store ρ) (t : Term n ρ) :
    {ρ' : ℕ} → Store ρ' → Term n ρ' → Prop where
  | refl : ASteps σ t σ t
  | tail {ρ' e : ℕ} {σ' : Store ρ'} {t' : Term n ρ'} {σ'' : Store (ρ' + e)}
      {t'' : Term n (ρ' + e)} :
      ASteps σ t σ' t' → AStep σ' t' e σ'' t'' → ASteps σ t σ'' t''

/-! ## Well-typed configurations -/

/-- A typing context `Γ` is compatible with the store `σ`: there are no variable
assumptions, array references are non-linear, and every typed reference is allocated. -/
structure ConfOK {n ρ : ℕ} (σ : Store ρ) (Γ : TCtx n ρ) : Prop where
  noVars : Γ.NoVars
  refsNonLin : Γ.RefsNonLin
  alloc : ∀ a h, Γ.refs.get a = some h → σ.get a ≠ none

/-- A context compatible with a store is non-linear. -/
lemma ConfOK.allNonLin {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} (h : ConfOK σ Γ) : Γ.AllNonLin :=
  h.noVars.allNonLin h.refsNonLin

end LCU
