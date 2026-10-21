module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping

/-!
# The operational heap model (Section 3.4)

Single-step reductions `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`.

## Main definitions

* `Usage` (`1` or `ω`), usage contexts `UCtx m` and binding contexts `BCtx m`.
* `Heap n`: variable bindings `x ↦ᵣ (Γ ⊢ t : A)` (`VarEntry`, which stores the typing
  derivation) and array bindings `a ↦ᵣ arr` (`ArrEntry`).
* `Step H t H' t' Γ Δ`: single-step call-by-name reduction; `Steps` is its
  reflexive-transitive closure.
* `FullStep` / `FullSteps`: full β-reduction (also reducing under `!`, pairs, ...), used
  in Theorem 7; `Irreducible`.
* `Compat H Γ` (`H ⋈ Γ`): heap-context compatibility (Definition 3).

## De Bruijn representation of heaps

A heap for `Term n` provides (optional) bindings for each of the `n` variables and
for array references `a : ℕ`.  When a reduction opens a binder, the scope grows: a
step goes from `Heap n`, `Term n` to `Heap m`, `Term m` with `n ≤ m`; the old
variables keep their indices (they are embedded with `Fin.castLE`) and the newly
opened binders get the indices `n, n+1, …`.  Removing a variable from the heap (rule
`var₁`) leaves the scope unchanged and just erases the binding.

The binding context `Γ` and the usage context `Δ` of a reduction are given over the
final scope `m` (entries of variables that are not newly bound are `none` in `Γ`).

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
abbrev UCtx (m : ℕ) : Type := Fin m → Option Usage

/-- Binding contexts recording the typing of binders opened during reduction. -/
abbrev BCtx (m : ℕ) : Type := Fin m → Option Hyp

/-- The empty usage / binding context. -/
def UCtx.empty {m : ℕ} : UCtx m := fun _ => none
def BCtx.empty {m : ℕ} : BCtx m := fun _ => none

/-- The singleton context `x : r`. -/
def UCtx.single {m : ℕ} (x : Fin m) (r : Usage) : UCtx m := fun y => if y = x then some r else none
def BCtx.single {m : ℕ} (x : Fin m) (h : Hyp) : BCtx m := fun y => if y = x then some h else none

/-- Addition of usage contexts: a variable used in both contexts is used `ω` times. -/
def UCtx.add {m : ℕ} (Δ₁ Δ₂ : UCtx m) : UCtx m := fun x =>
  match Δ₁ x, Δ₂ x with
  | none, r => r
  | r, none => r
  | some _, some _ => some .omega

/-- Disjoint union of (usage or binding) contexts, `Γ₁, Γ₂`. -/
def optUnion {α : Type} {m : ℕ} (f g : Fin m → Option α) : Fin m → Option α :=
  fun x => (f x).or (g x)

/-- `Δ ⊑ Δ'`: pointwise lifting of `≤` (both sides must have the same domain). -/
def UCtx.Le {m : ℕ} (Δ Δ' : UCtx m) : Prop := ∀ x,
  match Δ x, Δ' x with
  | none, none => True
  | some r, some s => r ≤ s
  | _, _ => False

/-- Embedding an optional assignment on `n` variables into a larger scope `m`. -/
def liftTo {α : Type} {n : ℕ} (m : ℕ) (f : Fin n → Option α) : Fin m → Option α :=
  fun j => if hj : (j : ℕ) < n then f ⟨j, hj⟩ else none

/-- The usage marker of a hypothesis: `x : A ↦ 1`, `x : [A] ↦ ω`. -/
def Hyp.usage : Hyp → Usage
  | .lin _ => .one
  | .nonlin _ => .omega

/-- Usage extraction from a binding context (Definition 4). -/
def BCtx.usage {m : ℕ} (Γ : BCtx m) : UCtx m := fun x => (Γ x).map Hyp.usage

/-- Usage extraction from a typing context (Definition 4; array references are dropped). -/
def Ctx.usage {m : ℕ} (Γ : Ctx m) : UCtx m := fun x => (Γ (.inl x)).map Hyp.usage

/-- Embedding a context into a larger scope (the new variables are absent). -/
def Ctx.liftTo {n : ℕ} (m : ℕ) (Γ : Ctx n) : Ctx m :=
  Sum.elim (fun j => if hj : (j : ℕ) < n then Γ (.inl ⟨j, hj⟩) else none) (fun a => Γ (.inr a))

/-! ## Heaps -/

/-- A variable allocation `x ↦_r (Γ ⊢ t : A)`.  The typing judgment is part of the
entry and is required to hold: a heap can only record *derivable* judgments `Γ ⊢ t : A`. -/
structure VarEntry (n : ℕ) where
  /-- the usage / reference counter `r` -/
  r : Usage
  /-- the context `Γ` of the recorded judgment -/
  ctx : Ctx n
  /-- the bound term `t` -/
  term : Term n
  /-- the type `A` of the recorded judgment -/
  ty : Ty
  /-- the recorded judgment `Γ ⊢ t : A` holds -/
  typed : HasType ctx term ty

/-- Array objects `arr`: finite arrays of floats, with `arr[i] = v` for `i < arr.length`. -/
abbrev ArrObj : Type := List Float

/-- An array allocation `a ↦_r arr`. -/
structure ArrEntry where
  r : Usage
  arr : ArrObj

/-- Heaps `H ::= ∅ | H, x ↦_r (Γ ⊢ t : A) | H, a ↦_r arr`. -/
structure Heap (n : ℕ) where
  /-- the variable allocations -/
  vars : Fin n → Option (VarEntry n)
  /-- the array allocations -/
  arrs : ℕ → Option ArrEntry
  /-- heaps are finite: only finitely many array references are allocated -/
  arrs_finite : ∃ N, ∀ a, N ≤ a → arrs a = none

namespace Heap

variable {n m : ℕ}

/-- The empty heap. -/
def empty : Heap n := ⟨fun _ => none, fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

/-- Update the binding of a variable. -/
def setVar (H : Heap n) (x : Fin n) (e : Option (VarEntry n)) : Heap n :=
  ⟨Function.update H.vars x e, H.arrs, H.arrs_finite⟩

/-- Update the allocation of an array reference. -/
def setArr (H : Heap n) (a : ℕ) (e : Option ArrEntry) : Heap n :=
  ⟨H.vars, Function.update H.arrs a e, by
    obtain ⟨N, hN⟩ := H.arrs_finite
    refine ⟨max N (a + 1), fun b hb => ?_⟩
    rw [Function.update_of_ne (by omega)]
    exact hN b (by omega)⟩

/-- Usage extraction `H̄` (Definition 4). -/
def usage (H : Heap n) : UCtx n := fun x => (H.vars x).map VarEntry.r

end Heap

/-- Embedding a context into a larger scope is a renaming of contexts. -/
lemma Ctx.renCtx_liftTo {n m : ℕ} (h : n ≤ m) (Γ : Ctx n) :
    Ctx.RenCtx (Fin.castLE h) Γ (Γ.liftTo m) where
  inj := Fin.castLE_injective h
  map i := by simp [Ctx.liftTo, i.isLt]
  off j hj := by
    simp only [Ctx.liftTo, Sum.elim_inl]
    split_ifs with hjn
    · exact absurd (Fin.ext rfl) (hj ⟨j, hjn⟩)
    · trivial
  refs _ := rfl

/-- Embedding a variable allocation into a larger scope. -/
def VarEntry.lift {n m : ℕ} (h : n ≤ m) (e : VarEntry n) : VarEntry m :=
  ⟨e.r, e.ctx.liftTo m, e.term.rename (Fin.castLE h), e.ty,
    e.typed.rename (Ctx.renCtx_liftTo h e.ctx)⟩

/-- Embedding a heap into a larger scope. -/
def Heap.lift {n m : ℕ} (h : n ≤ m) (H : Heap n) : Heap m :=
  ⟨fun j => if hj : (j : ℕ) < n then (H.vars ⟨j, hj⟩).map (VarEntry.lift h) else none, H.arrs,
    H.arrs_finite⟩

/-- Extending a heap with a binding for a fresh variable (index `n`). -/
def Heap.push {n : ℕ} (H : Heap n) (e : VarEntry n) : Heap (n + 1) :=
  (H.lift (Nat.le_succ n)).setVar (Fin.last n) (some (e.lift (Nat.le_succ n)))

/-- Renaming moving the bound variable `0` of a body to the last position. -/
def Ren.toLast {n : ℕ} : Fin (n + 1) → Fin (n + 1) := Fin.cases (Fin.last n) Fin.castSucc

/-- Renaming moving the two bound variables `y = 0`, `x = 1` of the body of a
`let (x, y)` to positions `n + 1` and `n`. -/
def Ren.toLast₂ {n : ℕ} : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases (Fin.last (n + 1)) (Fin.cases (Fin.last n).castSucc (fun j => j.castSucc.castSucc))

/-! ## Array references occurring in terms -/

/-- `RefIn a t`: the array reference `a` occurs in `t` (i.e. `a ∈ arrRefs(t)`). -/
def RefIn (a : ℕ) : {n : ℕ} → Term n → Prop
  | _, .var _ => False
  | _, .lam t => RefIn a t
  | _, .app t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .pair t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .letPair t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .unit => False
  | _, .letUnit t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .bang t => RefIn a t
  | _, .letBang t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .borrow t => RefIn a t
  | _, .copy t₁ t₂ => RefIn a t₁ ∨ RefIn a t₂
  | _, .star t => RefIn a t
  | _, .nat _ => False
  | _, .float _ => False
  | _, .prim _ => False
  | _, .ref b => a = b

open Classical in
/-- `[H]_ω` restricted to the arrays referenced by `v`: all their reference counts
become `ω`. -/
noncomputable def Heap.markOmega {n : ℕ} (H : Heap n) (v : Term n) : Heap n :=
  ⟨H.vars, fun a => if RefIn a v then (H.arrs a).map (fun e => ⟨.omega, e.arr⟩) else H.arrs a, by
    obtain ⟨N, hN⟩ := H.arrs_finite
    exact ⟨N, fun a ha => by dsimp only; split_ifs <;> simp [hN a ha]⟩⟩

/-- `(H'', θ) ≡ copy(H|arrRefs(v))`: `H₂` extends `H` with fresh copies `θ a` (with
reference count `1`) of the arrays `a` referenced by `v`. -/
structure CopyHeap {n : ℕ} (H : Heap n) (v : Term n) (θ : ℕ → ℕ) (H₂ : Heap n) : Prop where
  vars : H₂.vars = H.vars
  fresh : ∀ a, RefIn a v → H.arrs (θ a) = none
  inj : ∀ a b, RefIn a v → RefIn b v → θ a = θ b → a = b
  copied : ∀ a, RefIn a v → H₂.arrs (θ a) = (H.arrs a).map (fun e => ⟨.one, e.arr⟩)
  rest : ∀ b, (∀ a, RefIn a v → θ a ≠ b) → H₂.arrs b = H.arrs b

/-- Initial contents of `newArray k`. -/
def newArr (k : ℕ) : ArrObj := List.replicate k 0

/-! ## Single-step reduction -/

/-- The single-step reduction relation `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`. -/
inductive Step : {n m : ℕ} → Heap n → Term n → Heap m → Term m → BCtx m → UCtx m → Prop where
  /-- `var₁`: `H, x ↦₁ t ⊢ x ⇝ H ⊢ t | ∅ | x : 1` -/
  | var₁ {n : ℕ} {H : Heap n} {x : Fin n} {e : VarEntry n} :
      H.vars x = some e → e.r = .one →
      Step H (var x) (H.setVar x none) e.term BCtx.empty (UCtx.single x .one)
  /-- `var_ω`: `H, x ↦_ω t ⊢ x ⇝ H, x ↦_ω t ⊢ t | ∅ | x : 1` -/
  | varω {n : ℕ} {H : Heap n} {x : Fin n} {e : VarEntry n} :
      H.vars x = some e → e.r = .omega →
      Step H (var x) H e.term BCtx.empty (UCtx.single x .one)
  /-- `β`: `H ⊢ (λx. t) t' ⇝ H, x ↦₁ (Γ ⊢ t' : A) ⊢ t | x : A | ∅` given `Γ ⊢ t' : A` -/
  | beta {n : ℕ} {H : Heap n} {t : Term (n + 1)} {t' : Term n} {Γ : Ctx n} {A : Ty}
      (ht : HasType Γ t' A) :
      Step H (app (lam t) t') (H.push ⟨.one, Γ, t', A, ht⟩) (t.rename Ren.toLast)
        (BCtx.single (Fin.last n) (.lin A)) UCtx.empty
  /-- `app`: reduction on the left of an application -/
  | app {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₁' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      Step H t₁ H' t₁' Γ Δ → Step H (app t₁ t₂) H' (app t₁' (t₂.rename (Fin.castLE h))) Γ Δ
  /-- evaluation of the arguments of partially applied primitives -/
  | appPrim {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₂' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) : IsPrimFun t₁ →
      Step H t₂ H' t₂' Γ Δ → Step H (app t₁ t₂) H' (app (t₁.rename (Fin.castLE h)) t₂') Γ Δ
  /-- congruence for `let (x, y) = t₁ in t₂` -/
  | letPair {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 2)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      Step H t₁ H' t₁' Γ Δ →
      Step H (letPair t₁ t₂) H' (letPair t₁' (t₂.rename (Ren.up (Ren.up (Fin.castLE h))))) Γ Δ
  /-- `⊗β`: `H ⊢ let (x, y) = (t₁, t₂) in t ⇝ H, x ↦₁ t₁, y ↦₁ t₂ ⊢ t | x : A, y : B | ∅` -/
  | betaPair {n : ℕ} {H : Heap n} {t₁ t₂ : Term n} {t : Term (n + 2)} {Γ₁ Γ₂ : Ctx n}
      {A B : Ty} (h₁ : HasType Γ₁ t₁ A) (h₂ : HasType Γ₂ t₂ B) :
      Step H (letPair (pair t₁ t₂) t)
        ((H.push ⟨.one, Γ₁, t₁, A, h₁⟩).push (VarEntry.lift (Nat.le_succ n) ⟨.one, Γ₂, t₂, B, h₂⟩))
        (t.rename Ren.toLast₂)
        (optUnion (BCtx.single (Fin.last n).castSucc (.lin A)) (BCtx.single (Fin.last (n + 1)) (.lin B)))
        UCtx.empty
  /-- congruence for `let unit = t₁ in t₂` -/
  | letUnit {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₁' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      Step H t₁ H' t₁' Γ Δ → Step H (letUnit t₁ t₂) H' (letUnit t₁' (t₂.rename (Fin.castLE h))) Γ Δ
  /-- `1β`: `H ⊢ let unit = unit in t ⇝ H ⊢ t | ∅ | ∅` -/
  | betaUnit {n : ℕ} {H : Heap n} {t : Term n} :
      Step H (letUnit unit t) H t BCtx.empty UCtx.empty
  /-- congruence for `let! x = t₁ in t₂` -/
  | letBang {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 1)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      Step H t₁ H' t₁' Γ Δ →
      Step H (letBang t₁ t₂) H' (letBang t₁' (t₂.rename (Ren.up (Fin.castLE h)))) Γ Δ
  /-- `!β`: `H ⊢ let! x = !t₁ in t₂ ⇝ H, x ↦_ω ([Γ] ⊢ t₁ : A) ⊢ t₂ | x : [A] | ∅` -/
  | betaBang {n : ℕ} {H : Heap n} {t₁ : Term n} {t₂ : Term (n + 1)} {Γ : Ctx n} {A : Ty} :
      Γ.AllNonLin → (ht : HasType Γ t₁ A) →
      Step H (letBang (bang t₁) t₂) (H.push ⟨.omega, Γ, t₁, A, ht⟩) (t₂.rename Ren.toLast)
        (BCtx.single (Fin.last n) (.nonlin A)) UCtx.empty
  /-- `&`: congruence for borrowing -/
  | borrow {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} :
      Step H t H' t' Γ Δ → Step H (borrow t) H' (borrow t') Γ Δ
  /-- `&β`: `H, H' ⊢ &*v ⇝ [H]_ω, H' ⊢ !v | ∅ | ∅` where `dom(H) ≡ arrRefs(v)` -/
  | betaBorrow {n : ℕ} {H : Heap n} {v : Term n} :
      IsValue v → (∀ a, RefIn a v → H.arrs a ≠ none) →
      Step H (borrow (star v)) (H.markOmega v) (bang v) BCtx.empty UCtx.empty
  /-- congruence for `copy t₁ as x in t₂` -/
  | copy {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 1)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      Step H t₁ H' t₁' Γ Δ →
      Step H (copy t₁ t₂) H' (copy t₁' (t₂.rename (Ren.up (Fin.castLE h)))) Γ Δ
  /-- `copy_!`: evaluation under `!` in `copy !t as x in t₂` -/
  | copyBang {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t₂ : Term (n + 1)}
      {t' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      Step H t H' t' Γ Δ →
      Step H (copy (bang t) t₂) H' (copy (bang t') (t₂.rename (Ren.up (Fin.castLE h)))) Γ Δ
  /-- `copy_β`: `H, H' ⊢ copy !v as x in t ⇝ H, H', H'', x ↦₁ (Γ ⊢ *θ(v) : *A) ⊢ t | x : *A | ∅`
  given `dom(H') ≡ arrRefs(v)` and `(H'', θ) ≡ copy(H')`.  Since heap entries record
  derivable judgments only, the rule requires the recorded judgment `Γ ⊢ *θ(v) : *A`
  (whose context `Γ` refers to the fresh copies `θ a`) to hold. -/
  | betaCopy {n : ℕ} {H H₂ : Heap n} {v : Term n} {t : Term (n + 1)} {Γ : Ctx n} {A : Ty}
      {θ : ℕ → ℕ} :
      IsValue v → (hc : HasType Γ (star (renameRefs θ v)) (.star A)) →
      (∀ a, RefIn a v → H.arrs a ≠ none) → CopyHeap H v θ H₂ →
      Step H (copy (bang v) t) (H₂.push ⟨.one, Γ, star (renameRefs θ v), .star A, hc⟩)
        (t.rename Ren.toLast) (BCtx.single (Fin.last n) (.lin (.star A))) UCtx.empty
  /-- `newArray`: `H ⊢ newArray k ⇝ H, a ↦₁ arr ⊢ *a | ∅ | ∅` for `a # H` -/
  | newArray {n : ℕ} {H : Heap n} {a k : ℕ} :
      H.arrs a = none →
      Step H (app (prim .newArray) (nat k)) (H.setArr a (some ⟨.one, newArr k⟩)) (star (ref a))
        BCtx.empty UCtx.empty
  /-- `readArray`: `H, a ↦_r (arr[i] = v) ⊢ readArray (*a) i ⇝ … ⊢ (v, *a) | ∅ | ∅` -/
  | readArray {n : ℕ} {H : Heap n} {a i : ℕ} {e : ArrEntry} {x : Float} :
      H.arrs a = some e → e.arr[i]? = some x →
      Step H (app (app (prim .readArray) (star (ref a))) (nat i)) H (pair (float x) (star (ref a)))
        BCtx.empty UCtx.empty
  /-- `writeArray`: `H, a ↦_r arr ⊢ writeArray (*a) i v ⇝ H, a ↦_r (arr[i] = v) ⊢ *a | ∅ | ∅` -/
  | writeArray {n : ℕ} {H : Heap n} {a i : ℕ} {e : ArrEntry} {x : Float} :
      H.arrs a = some e →
      Step H (app (app (app (prim .writeArray) (star (ref a))) (nat i)) (float x))
        (H.setArr a (some ⟨e.r, e.arr.set i x⟩)) (star (ref a))
        BCtx.empty UCtx.empty
  /-- `deleteArray`: `H, a ↦_r arr ⊢ deleteArray (*a) ⇝ H ⊢ unit | ∅ | ∅` -/
  | deleteArray {n : ℕ} {H : Heap n} {a : ℕ} {e : ArrEntry} :
      H.arrs a = some e →
      Step H (app (prim .deleteArray) (star (ref a))) (H.setArr a none) unit
        BCtx.empty UCtx.empty

/-- Multi-step reduction `H ⊢ t ⇒ H' ⊢ t' | Γ | Δ` (rules `refl` and `ext`). -/
inductive Steps : {n m : ℕ} → Heap n → Term n → Heap m → Term m → BCtx m → UCtx m → Prop where
  | refl {n : ℕ} {H : Heap n} {t : Term n} : Steps H t H t BCtx.empty UCtx.empty
  | ext {n m p : ℕ} {H : Heap n} {H' : Heap m} {H'' : Heap p} {t₁ : Term n} {t₂ : Term m}
      {t₃ : Term p} {Γ₁ : BCtx m} {Δ₁ : UCtx m} {Γ₂ : BCtx p} {Δ₂ : UCtx p} :
      Step H t₁ H' t₂ Γ₁ Δ₁ → Steps H' t₂ H'' t₃ Γ₂ Δ₂ →
      Steps H t₁ H'' t₃ (optUnion (liftTo p Γ₁) Γ₂) (UCtx.add (liftTo p Δ₁) Δ₂)

/-! ## Full β-reduction -/

/-- Full β-reduction: the reduction relation extended with all congruences (in all
positions that are not under a binder). -/
inductive FullStep : {n m : ℕ} → Heap n → Term n → Heap m → Term m → BCtx m → UCtx m → Prop where
  | base {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} : Step H t H' t' Γ Δ → FullStep H t H' t' Γ Δ
  | app₁ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₁' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ → FullStep H (app t₁ t₂) H' (app t₁' (t₂.rename (Fin.castLE h))) Γ Δ
  | app₂ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₂' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₂ H' t₂' Γ Δ → FullStep H (app t₁ t₂) H' (app (t₁.rename (Fin.castLE h)) t₂') Γ Δ
  | pair₁ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₁' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ → FullStep H (pair t₁ t₂) H' (pair t₁' (t₂.rename (Fin.castLE h))) Γ Δ
  | pair₂ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₂' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₂ H' t₂' Γ Δ → FullStep H (pair t₁ t₂) H' (pair (t₁.rename (Fin.castLE h)) t₂') Γ Δ
  | letPair {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 2)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ →
      FullStep H (letPair t₁ t₂) H' (letPair t₁' (t₂.rename (Ren.up (Ren.up (Fin.castLE h))))) Γ Δ
  | letUnit₁ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₁' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ →
      FullStep H (letUnit t₁ t₂) H' (letUnit t₁' (t₂.rename (Fin.castLE h))) Γ Δ
  | letUnit₂ {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ t₂ : Term n} {t₂' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₂ H' t₂' Γ Δ →
      FullStep H (letUnit t₁ t₂) H' (letUnit (t₁.rename (Fin.castLE h)) t₂') Γ Δ
  | bang {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} : FullStep H t H' t' Γ Δ → FullStep H (bang t) H' (bang t') Γ Δ
  | letBang {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 1)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ →
      FullStep H (letBang t₁ t₂) H' (letBang t₁' (t₂.rename (Ren.up (Fin.castLE h)))) Γ Δ
  | borrow {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} : FullStep H t H' t' Γ Δ → FullStep H (borrow t) H' (borrow t') Γ Δ
  | copy {n m : ℕ} {H : Heap n} {H' : Heap m} {t₁ : Term n} {t₂ : Term (n + 1)}
      {t₁' : Term m} {Γ : BCtx m} {Δ : UCtx m} (h : n ≤ m) :
      FullStep H t₁ H' t₁' Γ Δ →
      FullStep H (copy t₁ t₂) H' (copy t₁' (t₂.rename (Ren.up (Fin.castLE h)))) Γ Δ
  | star {n m : ℕ} {H : Heap n} {H' : Heap m} {t : Term n} {t' : Term m} {Γ : BCtx m}
      {Δ : UCtx m} : FullStep H t H' t' Γ Δ → FullStep H (star t) H' (star t') Γ Δ

/-- Multi-step full β-reduction `H ⊢ t ⇒_β H' ⊢ t' | Γ | Δ`. -/
inductive FullSteps : {n m : ℕ} → Heap n → Term n → Heap m → Term m → BCtx m → UCtx m → Prop where
  | refl {n : ℕ} {H : Heap n} {t : Term n} : FullSteps H t H t BCtx.empty UCtx.empty
  | ext {n m p : ℕ} {H : Heap n} {H' : Heap m} {H'' : Heap p} {t₁ : Term n} {t₂ : Term m}
      {t₃ : Term p} {Γ₁ : BCtx m} {Δ₁ : UCtx m} {Γ₂ : BCtx p} {Δ₂ : UCtx p} :
      FullStep H t₁ H' t₂ Γ₁ Δ₁ → FullSteps H' t₂ H'' t₃ Γ₂ Δ₂ →
      FullSteps H t₁ H'' t₃ (optUnion (liftTo p Γ₁) Γ₂) (UCtx.add (liftTo p Δ₁) Δ₂)

/-- A term is irreducible (in a heap) if no full β-reduction applies to it. -/
def Irreducible {m : ℕ} (H : Heap m) (v : Term m) : Prop :=
  ¬ ∃ (p : ℕ) (H' : Heap p) (v' : Term p) (Γ : BCtx p) (Δ : UCtx p), FullStep H v H' v' Γ Δ

/-! ## Heap-context compatibility (Definition 3) -/

/-- Heap-context compatibility `H ⋈ Γ`. -/
inductive Compat : {n : ℕ} → Heap n → Ctx n → Prop where
  /-- `∅ ⋈ ∅` -/
  | empty {n : ℕ} : Compat (Heap.empty : Heap n) Ctx.empty
  /-- `H ⋈ Γ` gives `H, a ↦_r arr ⋈ Γ, a : Array A` -/
  | ref {n : ℕ} {H : Heap n} {Γ : Ctx n} {a : ℕ} {e : ArrEntry} {A : Ty} :
      Compat H Γ → H.arrs a = none →
      Compat (H.setArr a (some e)) (Γ.set (.inr a) (some (.lin A)))
  /-- `H ⋈ Γ₁ + Γ₂`, `x ∉ dom(H)` give `H, x ↦_r (Γ₂ ⊢ t : A) ⋈ Γ₁, x : A`
  (the judgment `Γ₂ ⊢ t : A` is part of the heap entry `e`) -/
  | lin {n : ℕ} {H : Heap n} {Γ₁ Γ₁₂ : Ctx n} {x : Fin n} {e : VarEntry n} :
      Compat H Γ₁₂ → Γ₁.Add e.ctx Γ₁₂ → H.vars x = none →
      Compat (H.setVar x (some e)) (Γ₁.set (.inl x) (some (.lin e.ty)))
  /-- `H ⋈ Γ₁ + [Γ₂]`, `x ∉ dom(H)` give `H, x ↦_ω ([Γ₂] ⊢ t : A) ⋈ Γ₁, x : [A]` -/
  | omega {n : ℕ} {H : Heap n} {Γ₁ Γ₁₂ : Ctx n} {x : Fin n} {e : VarEntry n} :
      Compat H Γ₁₂ → Γ₁.Add e.ctx Γ₁₂ → e.r = .omega → e.ctx.AllNonLin → H.vars x = none →
      Compat (H.setVar x (some e)) (Γ₁.set (.inl x) (some (.nonlin e.ty)))

end LCU
