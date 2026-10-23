module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping
public import RequestProject.LCU.Sec3_1_Calculus.RefRenaming

/-!
# The operational heap model (Section 3.4)

Single-step reductions `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`.

## Main definitions

* `Usage` (`1` or `ω`), usage contexts `UCtx m` and binding contexts `BCtx m`.
* `Heap n ρ`: variable bindings `x ↦ᵣ (Γ ⊢ t : A)` (`VarEntry`, which stores the typing
  derivation) for the `n` variables and array bindings `a ↦ᵣ arr` (`ArrEntry`) for the `ρ`
  array references in scope.
* `Step H t d e H' t' Γ Δ`: single-step call-by-name reduction, which opens `d` binders and
  allocates `e` arrays; `Steps` is its reflexive-transitive closure.
* `FullStep` / `FullSteps`: full β-reduction (also reducing under `!`, pairs, ...), used
  in Theorem 7; `Irreducible`.
* `Compat H Γ` (`H ⋈ Γ`): heap-context compatibility (Definition 3).

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

The binding context `Γ` and the usage context `Δ` of a step are given over the final scope
`n + d` (entries of variables that are not newly bound are `none` in `Γ`).

## Reconstruction of elided rules

The text shows only the core rules and states that the remaining ones (for
products, unit, the congruence for `copy`, and the rules for array primitives) follow
"much the same scheme" or are in the appendix, which is not part of the provided
text.  We include the rules shown in the text verbatim, and complete them with:
congruence rules evaluating the eliminated term of every elimination form
(`app`, `let (x, y)`, `let unit`, `let!`, `&`, `copy`), the β-rules for products
and unit, and the evaluation of arguments of (partially applied) primitives.
The copies created by `copy_β` get reference count `1`, and `newArray k` allocates
an array of length `k` filled with `0`.
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

/-! ## Single-step reduction -/

/-- The single-step reduction relation `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`, opening `d` binders and
allocating `e` arrays. -/
inductive Step : {n ρ : ℕ} → Heap n ρ → Term n ρ → (d e : ℕ) → Heap (n + d) (ρ + e) →
    Term (n + d) (ρ + e) → BCtx (n + d) → UCtx (n + d) → Prop where
  /-- `var₁`: `H, x ↦₁ t ⊢ x ⇝ H ⊢ t | ∅ | x : 1` -/
  | var₁ {n ρ : ℕ} {H : Heap n ρ} {x : Var n} {e : VarEntry n ρ} :
      H.VarAt x .one e →
      Step H (var x) 0 0 (H.setVar x none) e.term BCtx.empty (UCtx.single x .one)
  /-- `var_ω`: `H, x ↦_ω t ⊢ x ⇝ H, x ↦_ω t ⊢ t | ∅ | x : 1` -/
  | varω {n ρ : ℕ} {H : Heap n ρ} {x : Var n} {e : VarEntry n ρ} :
      H.VarAt x .omega e →
      Step H (var x) 0 0 H e.term BCtx.empty (UCtx.single x .one)
  /-- `β`: `H ⊢ (λx. t) t' ⇝ H, x ↦₁ (Γ ⊢ t' : A) ⊢ t | x : A | ∅` given `Γ ⊢ t' : A` -/
  | beta {n ρ : ℕ} {H : Heap n ρ} {t : Term (n + 1) ρ} {t' : Term n ρ} {Γ : TCtx n ρ} {A : Ty}
      (ht : HasType Γ t' A) :
      Step H (app (lam t) t') 1 0 (H.push ⟨.one, Γ, t', A, ht⟩) t (BCtx.new1 (.lin A))
        UCtx.empty
  /-- `app`: reduction on the left of an application -/
  | app {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t₁ d e H' t₁' Γ Δ → Step H (app t₁ t₂) d e H' (app t₁' (t₂.wk d e)) Γ Δ
  /-- evaluation of the arguments of partially applied primitives -/
  | appPrim {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₂' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} : IsPrimFun t₁ →
      Step H t₂ d e H' t₂' Γ Δ → Step H (app t₁ t₂) d e H' (app (t₁.wk d e) t₂') Γ Δ
  /-- congruence for `let (x, y) = t₁ in t₂` -/
  | letPair {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 2) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t₁ d e H' t₁' Γ Δ →
      Step H (letPair t₁ t₂) d e H' (letPair t₁' (t₂.wkUnder 2 d e)) Γ Δ
  /-- `⊗β`: `H ⊢ let (x, y) = (t₁, t₂) in t ⇝ H, x ↦₁ t₁, y ↦₁ t₂ ⊢ t | x : A, y : B | ∅` -/
  | betaPair {n ρ : ℕ} {H : Heap n ρ} {t₁ t₂ : Term n ρ} {t : Term (n + 2) ρ}
      {Γ₁ Γ₂ : TCtx n ρ} {A B : Ty} (h₁ : HasType Γ₁ t₁ A) (h₂ : HasType Γ₂ t₂ B) :
      Step H (letPair (pair t₁ t₂) t) 2 0
        ((H.push ⟨.one, Γ₁, t₁, A, h₁⟩).push (VarEntry.lift 1 0 ⟨.one, Γ₂, t₂, B, h₂⟩))
        t (BCtx.new1 (.lin A) ,, some (.lin B)) UCtx.empty
  /-- congruence for `let unit = t₁ in t₂` -/
  | letUnit {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t₁ d e H' t₁' Γ Δ → Step H (letUnit t₁ t₂) d e H' (letUnit t₁' (t₂.wk d e)) Γ Δ
  /-- `1β`: `H ⊢ let unit = unit in t ⇝ H ⊢ t | ∅ | ∅` -/
  | betaUnit {n ρ : ℕ} {H : Heap n ρ} {t : Term n ρ} :
      Step H (letUnit unit t) 0 0 H t BCtx.empty UCtx.empty
  /-- congruence for `let! x = t₁ in t₂` -/
  | letBang {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 1) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t₁ d e H' t₁' Γ Δ →
      Step H (letBang t₁ t₂) d e H' (letBang t₁' (t₂.wkUnder 1 d e)) Γ Δ
  /-- `!β`: `H ⊢ let! x = !t₁ in t₂ ⇝ H, x ↦_ω ([Γ] ⊢ t₁ : A) ⊢ t₂ | x : [A] | ∅` -/
  | betaBang {n ρ : ℕ} {H : Heap n ρ} {t₁ : Term n ρ} {t₂ : Term (n + 1) ρ} {Γ : TCtx n ρ}
      {A : Ty} : Γ.AllNonLin → (ht : HasType Γ t₁ A) →
      Step H (letBang (bang t₁) t₂) 1 0 (H.push ⟨.omega, Γ, t₁, A, ht⟩) t₂
        (BCtx.new1 (.nonlin A)) UCtx.empty
  /-- `&`: congruence for borrowing -/
  | borrow {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t d e H' t' Γ Δ → Step H (borrow t) d e H' (borrow t') Γ Δ
  /-- `&β`: `H, H' ⊢ &*v ⇝ [H]_ω, H' ⊢ !v | ∅ | ∅` where `dom(H) ≡ arrRefs(v)` -/
  | betaBorrow {n ρ : ℕ} {H : Heap n ρ} {v : Term n ρ} :
      IsValue v → (∀ a, RefIn a v → ¬ H.ArrFree a) →
      Step H (borrow (star v)) 0 0 (H.markOmega v) (bang v) BCtx.empty UCtx.empty
  /-- congruence for `copy t₁ as x in t₂` -/
  | copy {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 1) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t₁ d e H' t₁' Γ Δ →
      Step H (copy t₁ t₂) d e H' (copy t₁' (t₂.wkUnder 1 d e)) Γ Δ
  /-- `copy_!`: evaluation under `!` in `copy !t as x in t₂` -/
  | copyBang {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t₂ : Term (n + 1) ρ} {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t d e H' t' Γ Δ →
      Step H (copy (bang t) t₂) d e H' (copy (bang t') (t₂.wkUnder 1 d e)) Γ Δ
  /-- `copy_β`: `H, H' ⊢ copy !v as x in t ⇝ H, H', H'', x ↦₁ (Γ ⊢ *θ(v) : *A) ⊢ t | x : *A | ∅`
  given `dom(H') ≡ arrRefs(v)` and `(H'', θ) ≡ copy(H')`.  The `e` copies are the new
  references.  Since heap entries record derivable judgments only, the rule requires the
  recorded judgment `Γ ⊢ *θ(v) : *A` (whose context `Γ` refers to the copies) to hold. -/
  | betaCopy {n ρ e : ℕ} {H : Heap n ρ} {H₂ : Heap n (ρ + e)} {v : Term n ρ}
      {t : Term (n + 1) ρ} {Γ : TCtx n (ρ + e)} {A : Ty} {θ : Var ρ → Var (ρ + e)} :
      IsValue v → (hc : HasType Γ (star (renameRefs θ v)) (.star A)) →
      (∀ a, RefIn a v → ¬ H.ArrFree a) → CopyHeap H v e θ H₂ →
      Step H (copy (bang v) t) 1 e (H₂.push ⟨.one, Γ, star (renameRefs θ v), .star A, hc⟩)
        (renameRefs (Var.shiftN e) t) (BCtx.new1 (.lin (.star A))) UCtx.empty
  /-- `newArray`: `H ⊢ newArray k ⇝ H, a ↦₁ arr ⊢ *a | ∅ | ∅` for a new reference `a` -/
  | newArray {n ρ : ℕ} {H : Heap n ρ} {k : ℕ} :
      Step H (app (prim .newArray) (nat k)) 0 1 (H.pushArr ⟨.one, newArr k⟩) (star (ref .zero))
        BCtx.empty UCtx.empty
  /-- `readArray`: `H, a ↦_r (arr[i] = v) ⊢ readArray (*a) i ⇝ … ⊢ (v, *a) | ∅ | ∅` -/
  | readArray {n ρ : ℕ} {H : Heap n ρ} {a : Var ρ} {i : ℕ} {e : ArrEntry} {x : FloatLit} :
      H.ArrAt a e → e.arr.Reads i x →
      Step H (app (app (prim .readArray) (star (ref a))) (nat i)) 0 0 H
        (pair (float x) (star (ref a))) BCtx.empty UCtx.empty
  /-- `writeArray`: `H, a ↦_r arr ⊢ writeArray (*a) i v ⇝ H, a ↦_r (arr[i] = v) ⊢ *a | ∅ | ∅` -/
  | writeArray {n ρ : ℕ} {H : Heap n ρ} {a : Var ρ} {i : ℕ} {e : ArrEntry} {x : FloatLit} :
      H.ArrAt a e →
      Step H (app (app (app (prim .writeArray) (star (ref a))) (nat i)) (float x)) 0 0
        (H.setArr a (some ⟨e.r, e.arr.set i x⟩)) (star (ref a)) BCtx.empty UCtx.empty
  /-- `deleteArray`: `H, a ↦_r arr ⊢ deleteArray (*a) ⇝ H ⊢ unit | ∅ | ∅` -/
  | deleteArray {n ρ : ℕ} {H : Heap n ρ} {a : Var ρ} {e : ArrEntry} :
      H.ArrAt a e →
      Step H (app (prim .deleteArray) (star (ref a))) 0 0 (H.setArr a none) unit
        BCtx.empty UCtx.empty

/-- Multi-step reduction `H ⊢ t ⇒ H' ⊢ t' | Γ | Δ` (the reflexive-transitive closure of
`Step`).  The map `κ` records how the array references of the initial configuration are
embedded into the final one (it is a composite of `Var.shiftN`s). -/
inductive Steps {n ρ : ℕ} (H : Heap n ρ) (t : Term n ρ) :
    {m ρ' : ℕ} → Heap m ρ' → Term m ρ' → (Var ρ → Var ρ') → BCtx m → UCtx m → Prop where
  | refl : Steps H t H t id BCtx.empty UCtx.empty
  | tail {m ρ' d e : ℕ} {H' : Heap m ρ'} {t' : Term m ρ'} {κ : Var ρ → Var ρ'} {Γ₁ : BCtx m}
      {Δ₁ : UCtx m} {H'' : Heap (m + d) (ρ' + e)} {t'' : Term (m + d) (ρ' + e)}
      {Γ₂ : BCtx (m + d)} {Δ₂ : UCtx (m + d)} :
      Steps H t H' t' κ Γ₁ Δ₁ → Step H' t' d e H'' t'' Γ₂ Δ₂ →
      Steps H t H'' t'' (Var.shiftN e ∘ κ) (optUnion (Γ₁.lift d) Γ₂) (UCtx.add (Δ₁.lift d) Δ₂)

/-! ## Full β-reduction -/

/-- Full β-reduction: the reduction relation extended with all congruences (in all
positions that are not under a binder). -/
inductive FullStep : {n ρ : ℕ} → Heap n ρ → Term n ρ → (d e : ℕ) → Heap (n + d) (ρ + e) →
    Term (n + d) (ρ + e) → BCtx (n + d) → UCtx (n + d) → Prop where
  | base {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      Step H t d e H' t' Γ Δ → FullStep H t d e H' t' Γ Δ
  | app₁ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ → FullStep H (app t₁ t₂) d e H' (app t₁' (t₂.wk d e)) Γ Δ
  | app₂ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₂' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₂ d e H' t₂' Γ Δ → FullStep H (app t₁ t₂) d e H' (app (t₁.wk d e) t₂') Γ Δ
  | pair₁ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ → FullStep H (pair t₁ t₂) d e H' (pair t₁' (t₂.wk d e)) Γ Δ
  | pair₂ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₂' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₂ d e H' t₂' Γ Δ → FullStep H (pair t₁ t₂) d e H' (pair (t₁.wk d e) t₂') Γ Δ
  | letPair {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 2) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ →
      FullStep H (letPair t₁ t₂) d e H' (letPair t₁' (t₂.wkUnder 2 d e)) Γ Δ
  | letUnit₁ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ →
      FullStep H (letUnit t₁ t₂) d e H' (letUnit t₁' (t₂.wk d e)) Γ Δ
  | letUnit₂ {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ t₂ : Term n ρ}
      {t₂' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₂ d e H' t₂' Γ Δ →
      FullStep H (letUnit t₁ t₂) d e H' (letUnit (t₁.wk d e) t₂') Γ Δ
  | bang {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t d e H' t' Γ Δ → FullStep H (bang t) d e H' (bang t') Γ Δ
  | letBang {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 1) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ →
      FullStep H (letBang t₁ t₂) d e H' (letBang t₁' (t₂.wkUnder 1 d e)) Γ Δ
  | borrow {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t d e H' t' Γ Δ → FullStep H (borrow t) d e H' (borrow t') Γ Δ
  | copy {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t₁ : Term n ρ}
      {t₂ : Term (n + 1) ρ} {t₁' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t₁ d e H' t₁' Γ Δ →
      FullStep H (copy t₁ t₂) d e H' (copy t₁' (t₂.wkUnder 1 d e)) Γ Δ
  | star {n ρ d e : ℕ} {H : Heap n ρ} {H' : Heap (n + d) (ρ + e)} {t : Term n ρ}
      {t' : Term (n + d) (ρ + e)} {Γ : BCtx (n + d)} {Δ : UCtx (n + d)} :
      FullStep H t d e H' t' Γ Δ → FullStep H (star t) d e H' (star t') Γ Δ

/-- Multi-step full β-reduction `H ⊢ t ⇒_β H' ⊢ t' | Γ | Δ`. -/
inductive FullSteps {n ρ : ℕ} (H : Heap n ρ) (t : Term n ρ) :
    {m ρ' : ℕ} → Heap m ρ' → Term m ρ' → (Var ρ → Var ρ') → BCtx m → UCtx m → Prop where
  | refl : FullSteps H t H t id BCtx.empty UCtx.empty
  | tail {m ρ' d e : ℕ} {H' : Heap m ρ'} {t' : Term m ρ'} {κ : Var ρ → Var ρ'} {Γ₁ : BCtx m}
      {Δ₁ : UCtx m} {H'' : Heap (m + d) (ρ' + e)} {t'' : Term (m + d) (ρ' + e)}
      {Γ₂ : BCtx (m + d)} {Δ₂ : UCtx (m + d)} :
      FullSteps H t H' t' κ Γ₁ Δ₁ → FullStep H' t' d e H'' t'' Γ₂ Δ₂ →
      FullSteps H t H'' t'' (Var.shiftN e ∘ κ) (optUnion (Γ₁.lift d) Γ₂)
        (UCtx.add (Δ₁.lift d) Δ₂)

/-- A term is irreducible (in a heap) if no full β-reduction applies to it. -/
def Irreducible {m ρ : ℕ} (H : Heap m ρ) (v : Term m ρ) : Prop :=
  ¬ ∃ (d e : ℕ) (H' : Heap (m + d) (ρ + e)) (v' : Term (m + d) (ρ + e)) (Γ : BCtx (m + d))
    (Δ : UCtx (m + d)), FullStep H v d e H' v' Γ Δ

/-! ## Heap-context compatibility (Definition 3) -/

/-- Heap-context compatibility `H ⋈ Γ`. -/
inductive Compat : {n ρ : ℕ} → Heap n ρ → TCtx n ρ → Prop where
  /-- `∅ ⋈ ∅` -/
  | empty {n ρ : ℕ} : Compat (Heap.empty : Heap n ρ) TCtx.empty
  /-- `H ⋈ Γ` gives `H, a ↦_r arr ⋈ Γ, a : Array A` -/
  | ref {n ρ : ℕ} {H : Heap n ρ} {Γ : TCtx n ρ} {a : Var ρ} {e : ArrEntry} {A : Ty} :
      Compat H Γ → H.ArrFree a →
      Compat (H.setArr a (some e)) (Γ.setRef a (some (.lin (.array A))))
  /-- `H ⋈ Γ₁ + Γ₂`, `x ∉ dom(H)` give `H, x ↦_r (Γ₂ ⊢ t : A) ⋈ Γ₁, x : A`
  (the judgment `Γ₂ ⊢ t : A` is part of the heap entry `e`) -/
  | lin {n ρ : ℕ} {H : Heap n ρ} {Γ₁ Γ₁₂ : TCtx n ρ} {x : Var n} {e : VarEntry n ρ} :
      Compat H Γ₁₂ → Γ₁.Add e.ctx Γ₁₂ → H.VarFree x →
      Compat (H.setVar x (some e)) (Γ₁.setVar x (some (.lin e.ty)))
  /-- `H ⋈ Γ₁ + [Γ₂]`, `x ∉ dom(H)` give `H, x ↦_ω ([Γ₂] ⊢ t : A) ⋈ Γ₁, x : [A]` -/
  | omega {n ρ : ℕ} {H : Heap n ρ} {Γ₁ Γ₂ Γ₁₂ : TCtx n ρ} {x : Var n} {t : Term n ρ} {A : Ty}
      (ht : HasType Γ₂ t A) :
      Compat H Γ₁₂ → Γ₁.Add Γ₂ Γ₁₂ → Γ₂.AllNonLin → H.VarFree x →
      Compat (H.setVar x (some ⟨.omega, Γ₂, t, A, ht⟩)) (Γ₁.setVar x (some (.nonlin A)))

end LCU
