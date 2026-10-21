module
public import RequestProject.LCU.Ext2_MutableArrays.RefShift

/-!
# A store-based semantics for the array primitives, and type safety

`CbnSemantics.lean` gives a substitution-based call-by-name semantics for the fragment
without array primitives.  Here we extend it with a *store* of mutable floating-point
arrays, following the array rules of the heap model (Section 3.4):

* `newArray k ⟶ *a` allocates a fresh array `a` (filled with `0`);
* `readArray (*a) k ⟶ (arr[k], *a)` reads the array;
* `writeArray (*a) k x ⟶ *a` destructively updates the array in the store;
* `deleteArray (*a) ⟶ unit`;
* `copy !u as x in t ⟶ [*θ(u)/x]t`, where `θ` renames the array references of `u` to
  fresh references pointing to copies of the arrays (rule `copy_β`); concretely `θ`
  maps `a` to `N + a` for a bound `N` above all allocated references;
* the arguments of primitives are evaluated (also under `*`), and otherwise the rules
  are those of `CbnStep`.

This file contains the definitions: stores (`Store`), the reduction `AStep` and its
reflexive-transitive closure `ASteps`, and well-typed configurations (`ConfOK`).
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

/-- A store maps array references to arrays of floats (`none`: unallocated).
Out-of-bounds accesses are ignored, as in the paper, so arrays are total functions.
Stores are finite by construction: only finitely many references are allocated. -/
structure Store where
  /-- the array allocated at a reference, if any -/
  get : ℕ → Option (ℕ → Float)
  /-- only finitely many references are allocated -/
  finite : ∃ N, ∀ b, N ≤ b → get b = none

instance : CoeFun Store (fun _ => ℕ → Option (ℕ → Float)) := ⟨Store.get⟩

namespace Store

/-- All references from `N` on are unallocated. -/
def FreshFrom (σ : Store) (N : ℕ) : Prop := ∀ b, N ≤ b → σ b = none

/-- Update the array allocated at a reference. -/
def set (σ : Store) (a : ℕ) (v : Option (ℕ → Float)) : Store where
  get := Function.update σ.get a v
  finite := by
    obtain ⟨N, hN⟩ := σ.finite
    refine ⟨max N (a + 1), fun b hb => ?_⟩
    rw [Function.update_of_ne (by omega)]
    exact hN b (by omega)

@[simp] lemma set_apply (σ : Store) (a : ℕ) (v : Option (ℕ → Float)) (b : ℕ) :
    σ.set a v b = Function.update σ.get a v b := rfl

/-- Extend a store (whose references from `N` on are unallocated) with a copy of every
array: the copy of `a` lives at `N + a`. -/
def copyShift (σ : Store) (N : ℕ) : Store where
  get b := if N ≤ b then σ (b - N) else σ b
  finite := by
    obtain ⟨M, hM⟩ := σ.finite
    refine ⟨N + M, fun b hb => ?_⟩
    simp only [show N ≤ b by omega, if_true]
    exact hM _ (by omega)

@[simp] lemma copyShift_apply (σ : Store) (N b : ℕ) :
    σ.copyShift N b = if N ≤ b then σ (b - N) else σ b := rfl

/-- The empty store. -/
def empty : Store := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

@[simp] lemma empty_apply (b : ℕ) : Store.empty b = none := rfl

/-- Every store has a fresh bound. -/
lemma exists_freshFrom (σ : Store) : ∃ N, σ.FreshFrom N := σ.finite

end Store

/-! ## Reduction -/

/-- Partially applied primitives whose already supplied arguments are fully evaluated
(the array argument to a reference `*a`, the index to a literal `k`); the next argument
of such a term is evaluated.  This is a sub-grammar of the partially applied primitives
`PrimFun` of the paper. -/
inductive ReadyPrim (n : ℕ) : Type where
  /-- a primitive applied to no argument -/
  | const (p : Prim)
  /-- `readArray (*a)` -/
  | read₁ (a : ℕ)
  /-- `writeArray (*a)` -/
  | write₁ (a : ℕ)
  /-- `writeArray (*a) k` -/
  | write₂ (a k : ℕ)

namespace ReadyPrim

variable {n : ℕ}

/-- The embedding into terms. -/
@[simp] def toTerm : ReadyPrim n → Term n
  | const p => .prim p
  | read₁ a => .app (.prim .readArray) (.star (.ref a))
  | write₁ a => .app (.prim .writeArray) (.star (.ref a))
  | write₂ a k => .app (.app (.prim .writeArray) (.star (.ref a))) (.nat k)

/-- The embedding into the partially applied primitives of the paper. -/
def toPrimFun : ReadyPrim n → PrimFun n
  | const p => .const p
  | read₁ a => .readArray₁ (.star (.ref a))
  | write₁ a => .writeArray₁ (.star (.ref a))
  | write₂ a k => .writeArray₂ (.star (.ref a)) (.nat k)

@[simp] lemma toPrimFun_toTerm (p : ReadyPrim n) : p.toPrimFun.toTerm = p.toTerm := by
  cases p <;> rfl

end ReadyPrim

/-- `t` is (the embedding of) an element of the grammar `ReadyPrim n`. -/
def PrimReady {n : ℕ} (t : Term n) : Prop := ∃ p : ReadyPrim n, p.toTerm = t

namespace PrimReady

variable {n : ℕ}

lemma prim (p : Prim) : PrimReady (Term.prim p : Term n) := ⟨.const p, rfl⟩
lemma read₁ (a : ℕ) : PrimReady (app (Term.prim .readArray) (star (ref a)) : Term n) :=
  ⟨.read₁ a, rfl⟩
lemma write₁ (a : ℕ) : PrimReady (app (Term.prim .writeArray) (star (ref a)) : Term n) :=
  ⟨.write₁ a, rfl⟩
lemma write₂ (a k : ℕ) :
    PrimReady (app (app (Term.prim .writeArray) (star (ref a))) (nat k) : Term n) :=
  ⟨.write₂ a k, rfl⟩

/-- Ready primitives are partially applied primitives in the sense of `Values.lean`. -/
lemma isPrimFun {t : Term n} : PrimReady t → IsPrimFun t
  | ⟨p, hp⟩ => ⟨p.toPrimFun, by rw [ReadyPrim.toPrimFun_toTerm, hp]⟩

end PrimReady

/-- Single-step reduction `σ ⊢ t ⟶ σ' ⊢ t'` of the store-based semantics. -/
inductive AStep : {n : ℕ} → Store → Term n → Store → Term n → Prop where
  | betaLolli {n : ℕ} (σ : Store) (t : Term (n + 1)) (u : Term n) :
      AStep σ (app (lam t) u) σ (subst1 u t)
  | betaTensor {n : ℕ} (σ : Store) (t₁ t₂ : Term n) (t : Term (n + 2)) :
      AStep σ (letPair (pair t₁ t₂) t) σ (subst2 t₁ t₂ t)
  | betaUnit {n : ℕ} (σ : Store) (t : Term n) : AStep σ (letUnit unit t) σ t
  | betaBang {n : ℕ} (σ : Store) (u : Term n) (t : Term (n + 1)) :
      AStep σ (letBang (bang u) t) σ (subst1 u t)
  | betaBorrow {n : ℕ} (σ : Store) (t : Term n) : AStep σ (borrow (star t)) σ (bang t)
  /-- `copy_β`: the arrays of `u` are copied to the fresh references `N + a`. -/
  | betaCopy {n : ℕ} (σ : Store) (N : ℕ) (u : Term n) (t : Term (n + 1)) :
      σ.FreshFrom N → AStep σ (copy (bang u) t) (σ.copyShift N) (subst1 (star (u.shiftRefs N)) t)
  | app {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term n) :
      AStep σ t σ' t' → AStep σ (app t u) σ' (app t' u)
  | letPair {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 2)) :
      AStep σ t σ' t' → AStep σ (letPair t u) σ' (letPair t' u)
  | letUnit {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term n) :
      AStep σ t σ' t' → AStep σ (letUnit t u) σ' (letUnit t' u)
  | letBang {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 1)) :
      AStep σ t σ' t' → AStep σ (letBang t u) σ' (letBang t' u)
  | borrow {n : ℕ} {σ σ' : Store} {t t' : Term n} :
      AStep σ t σ' t' → AStep σ (borrow t) σ' (borrow t')
  | copy {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 1)) :
      AStep σ t σ' t' → AStep σ (copy t u) σ' (copy t' u)
  /-- evaluation of the next argument of a primitive -/
  | primArg {n : ℕ} {σ σ' : Store} {f t t' : Term n} :
      PrimReady f → AStep σ t σ' t' → AStep σ (app f t) σ' (app f t')
  /-- evaluation under `*` of the (unique) array argument of a primitive -/
  | primStar {n : ℕ} {σ σ' : Store} (p : Prim) {s s' : Term n} :
      AStep σ s σ' s' → AStep σ (app (prim p) (star s)) σ' (app (prim p) (star s'))
  | newArray {n : ℕ} (σ : Store) (k a : ℕ) : σ a = none →
      AStep σ (app (prim .newArray) (nat k) : Term n) (σ.set a (some fun _ => 0))
        (star (ref a))
  | readArray {n : ℕ} (σ : Store) (a k : ℕ) (arr : ℕ → Float) : σ a = some arr →
      AStep σ (app (app (prim .readArray) (star (ref a))) (nat k) : Term n) σ
        (pair (float (arr k)) (star (ref a)))
  | writeArray {n : ℕ} (σ : Store) (a k : ℕ) (x : Float) (arr : ℕ → Float) : σ a = some arr →
      AStep σ (app (app (app (prim .writeArray) (star (ref a))) (nat k)) (float x) : Term n)
        (σ.set a (some (Function.update arr k x))) (star (ref a))
  | deleteArray {n : ℕ} (σ : Store) (a : ℕ) :
      AStep σ (app (prim .deleteArray) (star (ref a)) : Term n) σ unit

/-- Multi-step reduction `σ ⊢ t ⟶* σ' ⊢ t'`. -/
inductive ASteps {n : ℕ} : Store → Term n → Store → Term n → Prop where
  | refl (σ : Store) (t : Term n) : ASteps σ t σ t
  | tail {σ σ' σ'' : Store} {t t' t'' : Term n} :
      ASteps σ t σ' t' → AStep σ' t' σ'' t'' → ASteps σ t σ'' t''

/-! ## Well-typed configurations -/

/-- A typing context `Γ` is compatible with the store `σ`: there are no variable
assumptions, array references are non-linear, and every typed reference is allocated. -/
structure ConfOK {n : ℕ} (σ : Store) (Γ : Ctx n) : Prop where
  noVars : Γ.NoVars
  refsNonLin : Γ.RefsNonLin
  alloc : ∀ a h, Γ (.inr a) = some h → σ a ≠ none

/-- A context compatible with a store is non-linear. -/
lemma ConfOK.allNonLin {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) : Γ.AllNonLin :=
  h.noVars.allNonLin h.refsNonLin

/-- Unallocated references do not occur in a compatible context. -/
lemma ConfOK.not_alloc {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) {a : ℕ}
    (ha : σ a = none) : Γ (.inr a) = none := by
  by_contra hne
  obtain ⟨h', e⟩ := Option.ne_none_iff_exists'.1 hne
  exact h.alloc a h' e ha

end LCU
