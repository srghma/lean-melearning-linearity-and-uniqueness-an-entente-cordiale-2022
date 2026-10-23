module
public import RequestProject.LCU.Sec3_4_HeapModel.Heap

/-!
# The operational heap model (Section 3.4): reduction

Single-step reductions `H ⊢ t ⇝ H' ⊢ t' | Γ | Δ`.

## Main definitions

* `Step H t d e H' t' Γ Δ`: single-step call-by-name reduction, which opens `d` binders and
  allocates `e` arrays; `Steps` is its reflexive-transitive closure.
* `FullStep` / `FullSteps`: full β-reduction (also reducing under `!`, pairs, ...), used
  in Theorem 7; `Irreducible`.

The binding context `Γ` and the usage context `Δ` of a step are given over the final scope
`n + d` (entries of variables that are not newly bound are `none` in `Γ`).  Configurations
grow at index zero; see `Heap.lean`.

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

end LCU
