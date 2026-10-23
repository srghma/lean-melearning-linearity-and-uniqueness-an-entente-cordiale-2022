module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping
public import RequestProject.LCU.Sec3_1_Calculus.RefRenaming

/-!
# The operational heap model (Section 3.4): heaps

Configurations `H ⊢ t` of the heap model.  The reduction relation is in `Step.lean` and
heap-context compatibility in `Compat.lean`.

## Main definitions

* `Usage` (`1` or `ω`), usage contexts `UCtx m` and binding contexts `BCtx m`.
* `Heap n ρ`: variable bindings `x ↦ᵣ (Γ ⊢ t : A)` (`VarEntry`, which stores the typing
  derivation) for the `n` variables and array bindings `a ↦ᵣ arr` (`ArrEntry`) for the `ρ`
  array references in scope.
* `Heap.lift`, `Heap.push`, `Heap.pushArr`: growing configurations.
* `RefIn a t`: the array reference `a` occurs in `t`; `CopyHeap`: the heap produced by
  `copy_β`.

## Scoped heaps

A configuration `H ⊢ t` has `t : Term n ρ` and `H : Heap n ρ`: the heap has one (optional)
entry for each variable and for each array reference in scope.  Hence every reference of a
term is in the domain of the heap *by construction*, and allocation needs no freshness
premise: a new array is the new reference `Var.zero`.

Configurations grow *at index zero*.  A step that opens `d` binders and allocates `e`
arrays goes from scope `(n, ρ)` to `(n + d, ρ + e)`; the old variables and references are
weakened along `Var.shiftN d` and `Var.shiftN e` (`Term.wk`, `Heap.lift`), and the opened
binders are the new variables.  In particular the body `t` of `(λx. t) t'` is the reduct of
the β-rule *as it is*: its bound variable `Var.zero` is the new heap variable `x`.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Usage annotations and usage contexts -/

/-- Usage / reference counters `r ::= 1 | ω`. -/
inductive Usage where
  | one
  | omega
  deriving DecidableEq, Repr

/-- The order `1 ≤ ω` (a partial order: `1 ≤ 1`, `1 ≤ ω`, `ω ≤ ω`, but not `ω ≤ 1`). -/
instance : PartialOrder Usage where
  le r s := r = .one ∨ s = .omega
  le_refl r := by cases r <;> simp
  le_trans r s t := by cases r <;> cases s <;> cases t <;> simp
  le_antisymm r s := by cases r <;> cases s <;> simp

instance : DecidableRel (α := Usage) (· ≤ ·) := fun r s =>
  inferInstanceAs (Decidable (r = .one ∨ s = .omega))

@[simp] lemma Usage.one_le (r : Usage) : Usage.one ≤ r := Or.inl rfl
@[simp] lemma Usage.le_omega (r : Usage) : r ≤ Usage.omega := Or.inr rfl
@[simp] lemma Usage.not_omega_le_one : ¬ Usage.omega ≤ Usage.one := by
  rintro (h | h) <;> cases h

/-- Usage contexts `Δ ::= ∅ | Δ, x : r` over `m` variables (`none` = absent). -/
abbrev UCtx (m : ℕ) : Type := Ctx (Option Usage) m

/-- Binding contexts recording the typing of binders opened during reduction. -/
abbrev BCtx (m : ℕ) : Type := Ctx (Option (Hyp Ty)) m

/-- The empty usage / binding context. -/
def UCtx.empty {m : ℕ} : UCtx m := .replicate m none
def BCtx.empty {m : ℕ} : BCtx m := .replicate m none

/-- The singleton context `x : r`. -/
def UCtx.single {m : ℕ} (x : Var m) (r : Usage) : UCtx m := UCtx.empty.set x (some r)

/-- Addition of optional usages: a variable used in both contexts is used `ω` times. -/
def Usage.addOpt : Option Usage → Option Usage → Option Usage
  | none, r => r
  | r, none => r
  | some _, some _ => some .omega

/-- Addition of usage contexts. -/
def UCtx.add {m : ℕ} (Δ₁ Δ₂ : UCtx m) : UCtx m := Ctx.zipWith Usage.addOpt Δ₁ Δ₂

/-- Disjoint union of (usage or binding) contexts, `Γ₁, Γ₂`. -/
def optUnion {α : Type} {m : ℕ} (Γ₁ Γ₂ : Ctx (Option α) m) : Ctx (Option α) m :=
  Ctx.zipWith Option.or Γ₁ Γ₂

/-- Comparison of optional usages: both absent, or both present with `r ≤ s`. -/
inductive OptUsageLe : Option Usage → Option Usage → Prop where
  /-- the variable is in neither domain -/
  | none : OptUsageLe none none
  /-- the variable is in both domains, with `r ≤ s` -/
  | some {r s : Usage} : r ≤ s → OptUsageLe (some r) (some s)

/-- `Δ ⊑ Δ'`: pointwise lifting of `≤` (both sides must have the same domain). -/
def UCtx.Le {m : ℕ} (Δ Δ' : UCtx m) : Prop := Ctx.Forall₂ OptUsageLe Δ Δ'

/-- The usage marker of a hypothesis: `x : A ↦ 1`, `x : [A] ↦ ω`. -/
def Hyp.usage {T : Type} : Hyp T → Usage
  | .lin _ => .one
  | .nonlin _ => .omega

/-- Usage extraction from a binding context (Definition 4). -/
def BCtx.usage {m : ℕ} (Γ : BCtx m) : UCtx m := Γ.map (Option.map Hyp.usage)

/-- Usage extraction from a typing context (Definition 4; array references are dropped). -/
def TCtx.usage {n ρ : ℕ} (Γ : TCtx n ρ) : UCtx n := Γ.vars.map (Option.map Hyp.usage)

/-! ## Heaps -/

/-- A variable allocation `x ↦_r (Γ ⊢ t : A)`.  The typing judgment is part of the
entry and is required to hold: a heap can only record *derivable* judgments `Γ ⊢ t : A`. -/
structure VarEntry (n ρ : ℕ) where
  /-- the usage / reference counter `r` -/
  r : Usage
  /-- the context `Γ` of the recorded judgment -/
  ctx : TCtx n ρ
  /-- the bound term `t` -/
  term : Term n ρ
  /-- the type `A` of the recorded judgment -/
  ty : Ty
  /-- the recorded judgment `Γ ⊢ t : A` holds -/
  typed : HasType ctx term ty

/-- Array objects `arr`: finite arrays of floats, with `arr[i] = v` for `i < arr.length`. -/
abbrev ArrObj : Type := List FloatLit

/-- `arr[i] = x`: the element at index `i` of the array object `arr` is `x`. -/
inductive ArrObj.Reads : ArrObj → ℕ → FloatLit → Prop where
  | zero {x : FloatLit} {arr : ArrObj} : ArrObj.Reads (x :: arr) 0 x
  | succ {x y : FloatLit} {arr : ArrObj} {i : ℕ} :
      ArrObj.Reads arr i x → ArrObj.Reads (y :: arr) (i + 1) x

@[simp] lemma ArrObj.reads_iff {arr : ArrObj} {i : ℕ} {x : FloatLit} :
    ArrObj.Reads arr i x ↔ arr[i]? = some x := by
  constructor
  · intro h
    induction h with
    | zero => rfl
    | succ _ ih => simpa using ih
  · intro h
    induction arr generalizing i with
    | nil => simp at h
    | cons y arr ih =>
      cases i with
      | zero => simp at h; subst h; exact .zero
      | succ i => exact .succ (ih (by simpa using h))

/-- An array allocation `a ↦_r arr`. -/
structure ArrEntry where
  r : Usage
  arr : ArrObj

/-- Heaps `H ::= ∅ | H, x ↦_r (Γ ⊢ t : A) | H, a ↦_r arr`, over `n` variables and `ρ`
array references (`none` = not allocated). -/
structure Heap (n ρ : ℕ) where
  /-- the variable allocations -/
  vars : Ctx (Option (VarEntry n ρ)) n
  /-- the array allocations -/
  arrs : Ctx (Option ArrEntry) ρ

namespace Heap

variable {n ρ : ℕ}

/-- The empty heap. -/
def empty : Heap n ρ := ⟨.replicate n none, .replicate ρ none⟩

/-- Update the binding of a variable. -/
def setVar (H : Heap n ρ) (x : Var n) (e : Option (VarEntry n ρ)) : Heap n ρ :=
  ⟨H.vars.set x e, H.arrs⟩

/-- Update the allocation of an array reference. -/
def setArr (H : Heap n ρ) (a : Var ρ) (e : Option ArrEntry) : Heap n ρ :=
  ⟨H.vars, H.arrs.set a e⟩

@[simp] lemma setVar_vars (H : Heap n ρ) (x : Var n) (e : Option (VarEntry n ρ)) :
    (H.setVar x e).vars = H.vars.set x e := rfl
@[simp] lemma setVar_arrs (H : Heap n ρ) (x : Var n) (e : Option (VarEntry n ρ)) :
    (H.setVar x e).arrs = H.arrs := rfl
@[simp] lemma setArr_vars (H : Heap n ρ) (a : Var ρ) (e : Option ArrEntry) :
    (H.setArr a e).vars = H.vars := rfl
@[simp] lemma setArr_arrs (H : Heap n ρ) (a : Var ρ) (e : Option ArrEntry) :
    (H.setArr a e).arrs = H.arrs.set a e := rfl
@[simp] lemma empty_vars : (empty : Heap n ρ).vars = .replicate n none := rfl
@[simp] lemma empty_arrs : (empty : Heap n ρ).arrs = .replicate ρ none := rfl

/-! ### Lookup judgments

The membership facts used as premises of the reduction and compatibility rules are
instances of the structural lookup judgment `Ctx.Lookup` (defined by *here / there*
rules). -/

/-- `x ↦_r e ∈ H`: the variable `x` is bound to the entry `e`, whose usage is `r`. -/
inductive VarAt (H : Heap n ρ) (x : Var n) : Usage → VarEntry n ρ → Prop where
  | mk {e : VarEntry n ρ} : H.vars.Lookup x (some e) → VarAt H x e.r e

/-- `x ∉ dom(H)`: the variable `x` is not bound in `H`. -/
def VarFree (H : Heap n ρ) (x : Var n) : Prop := H.vars.Lookup x none

/-- `a ↦ e ∈ H`: the array reference `a` is allocated with entry `e`. -/
def ArrAt (H : Heap n ρ) (a : Var ρ) (e : ArrEntry) : Prop := H.arrs.Lookup a (some e)

/-- `a ∉ dom(H)`: the array reference `a` is not allocated in `H`. -/
def ArrFree (H : Heap n ρ) (a : Var ρ) : Prop := H.arrs.Lookup a none

@[simp] lemma varAt_iff {H : Heap n ρ} {x : Var n} {r : Usage} {e : VarEntry n ρ} :
    H.VarAt x r e ↔ H.vars.get x = some e ∧ e.r = r :=
  ⟨fun | .mk h => ⟨h.eq, rfl⟩, fun ⟨h₁, h₂⟩ => h₂ ▸ .mk (.of_eq h₁)⟩
@[simp] lemma varFree_iff {H : Heap n ρ} {x : Var n} : H.VarFree x ↔ H.vars.get x = none :=
  Ctx.lookup_iff
@[simp] lemma arrAt_iff {H : Heap n ρ} {a : Var ρ} {e : ArrEntry} :
    H.ArrAt a e ↔ H.arrs.get a = some e := Ctx.lookup_iff
@[simp] lemma arrFree_iff {H : Heap n ρ} {a : Var ρ} : H.ArrFree a ↔ H.arrs.get a = none :=
  Ctx.lookup_iff

/-- Usage extraction `H̄` (Definition 4). -/
def usage (H : Heap n ρ) : UCtx n := H.vars.map (Option.map VarEntry.r)

end Heap

/-! ## Growing configurations -/

/-- Weakening a variable allocation by `d` new variables and `e` new array references. -/
def VarEntry.lift {n ρ : ℕ} (d e : ℕ) (en : VarEntry n ρ) : VarEntry (n + d) (ρ + e) :=
  ⟨en.r, en.ctx.lift d e, en.term.wk d e, en.ty, en.typed.wk d e⟩

/-- Weakening a heap by `d` new (unbound) variables and `e` new (unallocated) array
references. -/
def Heap.lift {n ρ : ℕ} (d e : ℕ) (H : Heap n ρ) : Heap (n + d) (ρ + e) :=
  ⟨(H.vars.map (Option.map (VarEntry.lift d e))).pad none d, H.arrs.pad none e⟩

/-- Extending a heap with a binding for a new variable (`Var.zero`). -/
def Heap.push {n ρ : ℕ} (H : Heap n ρ) (en : VarEntry n ρ) : Heap (n + 1) ρ :=
  ⟨(H.lift 1 0).vars.set .zero (some (en.lift 1 0)), H.arrs⟩

/-- Extending a heap with a new array (`Var.zero`). -/
def Heap.pushArr {n ρ : ℕ} (H : Heap n ρ) (en : ArrEntry) : Heap n (ρ + 1) :=
  ⟨(H.lift 0 1).vars, H.arrs ,, some en⟩

/-- Padding a binding context with `d` new entries for the new variables. -/
def BCtx.lift {n : ℕ} (d : ℕ) (Γ : BCtx n) : BCtx (n + d) := Γ.pad none d

/-- Padding a usage context with `d` new (absent) entries. -/
def UCtx.lift {n : ℕ} (d : ℕ) (Δ : UCtx n) : UCtx (n + d) := Δ.pad none d

/-- The binding context of a rule opening one binder `x : h`. -/
def BCtx.new1 {n : ℕ} (h : Hyp Ty) : BCtx (n + 1) := BCtx.empty ,, some h

/-! ## Array references occurring in terms -/

/-- `RefIn a t`: the array reference `a` occurs in `t` (i.e. `a ∈ arrRefs(t)`). -/
def RefIn {n ρ : ℕ} (a : Var ρ) (t : Term n ρ) : Prop := Binding.Tm.HasOp (· = Op.ref a) t

lemma refIn_ref {n ρ : ℕ} {a b : Var ρ} : RefIn a (ref b : Term n ρ) ↔ a = b := by
  simp only [RefIn, Binding.Tm.hasOp_op_iff, Binding.Args.not_hasOp_nil, or_false]
  exact ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

lemma refIn_star {n ρ : ℕ} {a : Var ρ} {t : Term n ρ} : RefIn a (star t) ↔ RefIn a t := by
  simp only [RefIn, Binding.Tm.hasOp_op_iff, Binding.Args.hasOp_cons_iff,
    Binding.Args.not_hasOp_nil, or_false]
  exact ⟨fun h => h.resolve_left nofun, .inr⟩

lemma refIn_star_ref {n ρ : ℕ} {a b : Var ρ} : RefIn a (star (ref b) : Term n ρ) ↔ a = b := by
  rw [refIn_star, refIn_ref]

open Classical in
/-- `[H]_ω` restricted to the arrays referenced by `v`: all their reference counts
become `ω`. -/
noncomputable def Heap.markOmega {n ρ : ℕ} (H : Heap n ρ) (v : Term n ρ) : Heap n ρ :=
  ⟨H.vars, .ofFn fun a =>
    if RefIn a v then (H.arrs.get a).map (fun e => ⟨.omega, e.arr⟩) else H.arrs.get a⟩

/-- `(H'', θ) ≡ copy(H|arrRefs(v))`: `H₂` extends `H` (weakened by `e` new references) with
copies `θ a` (with reference count `1`) of the arrays `a` referenced by `v`; the new
references are exactly these copies. -/
structure CopyHeap {n ρ : ℕ} (H : Heap n ρ) (v : Term n ρ) (e : ℕ) (θ : Var ρ → Var (ρ + e))
    (H₂ : Heap n (ρ + e)) : Prop where
  vars : H₂.vars = (H.lift 0 e).vars
  old : ∀ b, H₂.arrs.get (Var.shiftN e b) = H.arrs.get b
  fresh : ∀ a, RefIn a v → ∀ b, θ a ≠ Var.shiftN e b
  inj : ∀ a b, RefIn a v → RefIn b v → θ a = θ b → a = b
  copied : ∀ a, RefIn a v → H₂.arrs.get (θ a) = (H.arrs.get a).map (fun en => ⟨.one, en.arr⟩)
  onto : ∀ c, (∀ b, Var.shiftN e b ≠ c) → ∃ a, RefIn a v ∧ θ a = c

/-- Initial contents of `newArray k`. -/
def newArr (k : ℕ) : ArrObj := List.replicate k 0

end LCU
