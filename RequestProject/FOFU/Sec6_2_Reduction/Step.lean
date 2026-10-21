module
public import RequestProject.FOFU.Sec6_1_Preliminaries.Values
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap
public import RequestProject.Common.Grades.PreorderedSemiring

/-!
# Single-step and multi-step reduction (Section 6.2)

`Step H t s H' t'` is the judgment `H ⊢ t ⤳_s H' ⊢ t'` (usage context `s`), and
`Steps H t s H' t'` is its reflexive–transitive closure `H ⊢ t ⇒_s H' ⊢ t'`
(rules `refl` and `ext`).

## Binding fresh heap variables

The rules that bind a value to a fresh heap variable `y` and continue with `t [y / x]`
(`⤳β`, `⤳∃β`, `⤳⊗β`, `⤳□β`, `⤳clone β`, `⤳with&`) extend a `Heap R n` to a
`Heap R (n + 1)` whose new variable is the last one (`Fin.last n`); the body is
renamed accordingly by `Term.openLast` (or `Term.openLast2` for pairs).  When a
congruence rule reduces a subterm and the heap grows, the other subterms are weakened
into the larger scope.

## Rules of the paper

`var`, `beta`, `appL`, `appR`, `exBeta`, `tensorBeta`, `boxCong`, `boxBeta`,
`newArray`, `readArray`, `writeArray`, `deleteArray`, `share`, `clone`, `withBorrow`,
`unborrow`, `push`, `pull`, `splitRef`, `joinRef`.

* `share`: the paper writes `H, H' ⊢ share (*v) ⤳_s ([H]_0), H' ⊢ [v]` with
  `dom(H) ≡ refs(v)`, but never defines `[H]_0`; we leave the heap unchanged.  The
  produced box carries the grade annotation of `share`.
* `clone`: `copy(H')` is not defined in the paper.  We copy, for each reference `a` of
  `v` (in some order), its resource to a fresh identifier with a fresh reference of
  permission `1`, and rename the references of `v` accordingly (`CopyHeap`).
* `readArray` reads the most recent write at the index (see `ArrVal.read`).

## Reconstructed rules (not in the paper)

The paper only gives congruence rules for application and promotion, no β-rule for
`let () = () in t`, and no rules for the reference primitives.  We add the evident
call-by-value, left-to-right congruence rules for all other elimination and
introduction forms, the rule `unitBeta`, and rules `newRef`, `readRef`, `swapRef`,
`freezeRef` analogous to the array rules.  Adding rules only makes the counterexamples
of `Sec6_3_Theorems` stronger: they exhibit stuck terms even with these rules.
-/

@[expose] public section

namespace FOFU

variable {R : Type}

namespace Term

/-- Renaming the variable bound by a one-variable binder to the new last heap variable:
`t [y / x]` for `y = Fin.last n`. -/
def openLast {n : ℕ} (t : Term R (n + 1)) : Term R (n + 1) :=
  t.rename (Fin.cases (Fin.last n) Fin.castSucc)

/-- Renaming the two variables bound by `let (x, y) = _ in t` to the two new last heap
variables `x' = n`, `y' = n + 1`. -/
def openLast2 {n : ℕ} (t : Term R (n + 2)) : Term R (n + 2) :=
  t.rename (Fin.cases (Fin.last (n + 1)) (Fin.cases (Fin.last n).castSucc
    (fun i => i.castSucc.castSucc)))

end Term

/-- `CopyHeap H as θ H'`: `H'` extends `H` with fresh copies of the resources of the
references in the list `as`, each copy getting a fresh identifier and a fresh reference
`θ a` of permission `1`. -/
inductive CopyHeap {n : ℕ} : Heap R n → List ℕ → (ℕ → ℕ) → Heap R n → Prop where
  | nil (H : Heap R n) (θ : ℕ → ℕ) : CopyHeap H [] θ H
  | cons {H H' : Heap R n} {a : ℕ} {as : List ℕ} {θ : ℕ → ℕ} {q : ℚ} {id id' : ℕ}
      {vr : ResVal R n} :
      H.refs a = some (q, id) → H.ress id = some vr →
      H.refs (θ a) = none → H.IdFresh id' →
      CopyHeap ((H.addRef (θ a) 1 id').addRes id' vr) as θ H' →
      CopyHeap H (a :: as) θ H'

variable [Grades.PreorderedSemiring R]

open Term in
/-- Single-step reduction `H ⊢ t ⤳_s H' ⊢ t'`. -/
inductive Step : {n m : ℕ} → Heap R n → Term R n → R → Heap R m → Term R m → Prop where
  -- ### Lambda calculus
  /-- `⤳var`: `∃ r'. s + r' ⊑ r  ⟹  H, x ↦_r v ⊢ x ⤳_s H, x ↦_r v ⊢ v` -/
  | var {n : ℕ} {H : Heap R n} {i : Fin n} {s : R} :
      (∃ r', s + r' ≤ (H.vars i).1) → Step H (var i) s H (H.vars i).2
  /-- `⤳β`: `H ⊢ (λx. t) v ⤳_s H, y ↦_s v ⊢ t [y / x]` -/
  | beta {n : ℕ} {H : Heap R n} {t : Term R (n + 1)} {v : Term R n} {s : R} :
      IsValue v → Step H (app (lam t) v) s (H.snoc s v) t.openLast
  /-- `⤳appL` -/
  | appL {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ t₁' t₂ : Term R n} {s : R}
      (h : n ≤ m) {t₁'' : Term R m} :
      Step H t₁ s H' t₁'' → Step H (app t₁ t₂) s H' (app t₁'' (t₂.weaken h))
  /-- `⤳appR` -/
  | appR {n m : ℕ} {H : Heap R n} {H' : Heap R m} {v t₂ : Term R n} {t₂' : Term R m} {s : R}
      (h : n ≤ m) :
      IsValue v → Step H t₂ s H' t₂' → Step H (app v t₂) s H' (app (v.weaken h) t₂')
  -- ### Existential types
  /-- `⤳∃β`: `H ⊢ unpack ⟨id, x⟩ = pack ⟨id', v⟩ in t ⤳_s H, y ↦_s v ⊢ t [y / x]` -/
  | exBeta {n : ℕ} {H : Heap R n} {v : Term R n} {t : Term R (n + 1)} {s : R} :
      IsValue v → Step H (unpack (pack v) t) s (H.snoc s v) t.openLast
  -- ### Tensors
  /-- `⤳⊗β` -/
  | tensorBeta {n : ℕ} {H : Heap R n} {v₁ v₂ : Term R n} {t : Term R (n + 2)} {s : R} :
      IsValue v₁ → IsValue v₂ →
      Step H (letPair (pair v₁ v₂) t) s ((H.snoc s v₁).snoc s (v₂.rename Fin.castSucc))
        t.openLast2
  -- ### Graded modalities
  /-- `⤳□`: `H ⊢ t ⤳_(s * r) H' ⊢ t'  ⟹  H ⊢ [t]_r ⤳_s H' ⊢ [t']_r` -/
  | boxCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m}
      {r s : R} :
      Step H t (s * r) H' t' → Step H (box r t) s H' (box r t')
  /-- `⤳□β`: `H ⊢ let [x] = [v]_r in t ⤳_s H, y ↦_(s * r) v ⊢ t [y / x]` -/
  | boxBeta {n : ℕ} {H : Heap R n} {v : Term R n} {t : Term R (n + 1)} {r s : R} :
      IsValue v → Step H (letBox (box r v) t) s (H.snoc (s * r) v) t.openLast
  -- ### Arrays
  /-- `⤳newArray` -/
  | newArray {n : ℕ} {H : Heap R n} {m : ℕ} {s : R} {a id : ℕ} :
      H.refs a = none → H.IdFresh id →
      Step H (app (prim .newArray) (nat m)) s
        ((H.addRef a 1 id).addRes id (.arr .init)) (pack (star (ref a)))
  /-- `⤳readArray` -/
  | readArray {n : ℕ} {H : Heap R n} {a id i : ℕ} {q : ℚ} {arr : ArrVal R n} {v : Term R n}
      {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.arr arr) → arr.read i = some v →
      Step H (app (app (prim .readArray) (star (ref a))) (nat i)) s H (pair v (star (ref a)))
  /-- `⤳writeArray` -/
  | writeArray {n : ℕ} {H : Heap R n} {a id i : ℕ} {q : ℚ} {arr : ArrVal R n} {v : Term R n}
      {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.arr arr) → IsValue v →
      Step H (app (app (app (prim .writeArray) (star (ref a))) (nat i)) v) s
        (H.addRes id (.arr (arr.write i v))) (star (ref a))
  /-- `⤳deleteArray` -/
  | deleteArray {n : ℕ} {H : Heap R n} {a id : ℕ} {q : ℚ} {arr : ArrVal R n} {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.arr arr) →
      Step H (app (prim .deleteArray) (star (ref a))) s ((H.eraseRef a).eraseRes id) unit
  -- ### References (reconstructed)
  /-- `newRef v` allocates a reference with permission `1` (reconstructed) -/
  | newRef {n : ℕ} {H : Heap R n} {v : Term R n} {s : R} {a id : ℕ} :
      IsValue v → H.refs a = none → H.IdFresh id →
      Step H (app (prim .newRef) v) s
        ((H.addRef a 1 id).addRes id (.ref v)) (pack (star (ref a)))
  /-- `readRef` returns the contents of a boxed stored value (reconstructed) -/
  | readRef {n : ℕ} {H : Heap R n} {a id : ℕ} {q : ℚ} {r : R} {v : Term R n} {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.ref (box r v)) →
      Step H (app (prim .readRef) (star (ref a))) s H (pair v (star (ref a)))
  /-- `swapRef` exchanges the stored value (reconstructed) -/
  | swapRef {n : ℕ} {H : Heap R n} {a id : ℕ} {q : ℚ} {v₀ v : Term R n} {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.ref v₀) → IsValue v →
      Step H (app (app (prim .swapRef) (star (ref a))) v) s
        (H.addRes id (.ref v)) (pair v₀ (star (ref a)))
  /-- `freezeRef` deallocates the reference and returns its contents (reconstructed) -/
  | freezeRef {n : ℕ} {H : Heap R n} {a id : ℕ} {q : ℚ} {v : Term R n} {s : R} :
      H.refs a = some (q, id) → H.ress id = some (.ref v) →
      Step H (app (prim .freezeRef) (star (ref a))) s ((H.eraseRef a).eraseRes id) v
  -- ### Sharing and cloning
  /-- `⤳share β` (the heap is left unchanged, see the module docstring) -/
  | share {n : ℕ} {H : Heap R n} {v : Term R n} {r s : R} :
      IsValue v → Step H (share r (star v)) s H (box r v)
  /-- `⤳clone β` -/
  | clone {n : ℕ} {H H' : Heap R n} {v : Term R n} {t : Term R (n + 1)} {r s : R}
      {as : List ℕ} {θ : ℕ → ℕ} :
      IsValue v → as.Nodup → (∀ a, a ∈ as ↔ a ∈ v.refs) → CopyHeap H as θ H' →
      Step H (clone (box r v) t) s (H'.snoc s (pack (star (v.renameRefs θ)))) t.openLast
  -- ### Borrowing
  /-- `⤳with&`: `H ⊢ withBorrow (λx. t) (*v) ⤳_s H, y ↦_s (*v) ⊢ unborrow (t [y / x])` -/
  | withBorrow {n : ℕ} {H : Heap R n} {t : Term R (n + 1)} {v : Term R n} {s : R} :
      IsValue v → Step H (withBorrow (lam t) (star v)) s (H.snoc s (star v)) (unborrow t.openLast)
  /-- `⤳un&`: `H ⊢ unborrow (*v) ⤳_s H ⊢ *v` -/
  | unborrow {n : ℕ} {H : Heap R n} {v : Term R n} {s : R} :
      IsValue v → Step H (unborrow (star v)) s H (star v)
  -- ### Push and pull
  /-- `H ⊢ push (*(v₁, v₂)) ⤳_s H ⊢ (*v₁, *v₂)` -/
  | push {n : ℕ} {H : Heap R n} {v₁ v₂ : Term R n} {s : R} :
      IsValue v₁ → IsValue v₂ → Step H (push (star (pair v₁ v₂))) s H (pair (star v₁) (star v₂))
  /-- `H ⊢ pull (*v₁, *v₂) ⤳_s H ⊢ *(v₁, v₂)` -/
  | pull {n : ℕ} {H : Heap R n} {v₁ v₂ : Term R n} {s : R} :
      IsValue v₁ → IsValue v₂ → Step H (pull (pair (star v₁) (star v₂))) s H (star (pair v₁ v₂))
  -- ### Split and join
  /-- `⤳splitRef` -/
  | splitRef {n : ℕ} {H : Heap R n} {a a₁ a₂ id : ℕ} {p : ℚ} {vr : ResVal R n} {s : R} :
      H.refs a = some (p, id) → H.ress id = some vr →
      (H.eraseRef a).refs a₁ = none → (H.eraseRef a).refs a₂ = none → a₁ ≠ a₂ →
      Step H (split (star (ref a))) s
        (((H.eraseRef a).addRef a₁ (p / 2) id).addRef a₂ (p / 2) id)
        (pair (star (ref a₁)) (star (ref a₂)))
  /-- `⤳joinRef` -/
  | joinRef {n : ℕ} {H : Heap R n} {a a₁ a₂ id : ℕ} {p q : ℚ} {vr : ResVal R n} {s : R} :
      H.refs a₁ = some (p, id) → H.refs a₂ = some (q, id) → a₁ ≠ a₂ → H.ress id = some vr →
      ((H.eraseRef a₁).eraseRef a₂).refs a = none →
      Step H (join (star (ref a₁)) (star (ref a₂))) s
        (((H.eraseRef a₁).eraseRef a₂).addRef a (p + q) id) (star (ref a))
  -- ### Reconstructed congruence rules (call-by-value, left to right)
  | pairL {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ t₂ : Term R n} {t₁' : Term R m}
      {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' → Step H (pair t₁ t₂) s H' (pair t₁' (t₂.weaken h))
  | pairR {n m : ℕ} {H : Heap R n} {H' : Heap R m} {v t₂ : Term R n} {t₂' : Term R m}
      {s : R} (h : n ≤ m) :
      IsValue v → Step H t₂ s H' t₂' → Step H (pair v t₂) s H' (pair (v.weaken h) t₂')
  | letPairCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ : Term R n} {t₁' : Term R m}
      {t₂ : Term R (n + 2)} {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' →
      Step H (letPair t₁ t₂) s H' (letPair t₁'
        (t₂.rename (DeBruijn.Ren.up (DeBruijn.Ren.up (Fin.castLE h)))))
  | letUnitCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ t₂ : Term R n} {t₁' : Term R m}
      {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' → Step H (letUnit t₁ t₂) s H' (letUnit t₁' (t₂.weaken h))
  | unitBeta {n : ℕ} {H : Heap R n} {t : Term R n} {s : R} :
      Step H (letUnit unit t) s H t
  | letBoxCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ : Term R n} {t₁' : Term R m}
      {t₂ : Term R (n + 1)} {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' →
      Step H (letBox t₁ t₂) s H' (letBox t₁' (t₂.rename (DeBruijn.Ren.up (Fin.castLE h))))
  | packCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m} {s : R} :
      Step H t s H' t' → Step H (pack t) s H' (pack t')
  | unpackCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ : Term R n} {t₁' : Term R m}
      {t₂ : Term R (n + 1)} {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' →
      Step H (unpack t₁ t₂) s H' (unpack t₁' (t₂.rename (DeBruijn.Ren.up (Fin.castLE h))))
  | shareCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m}
      {r s : R} :
      Step H t s H' t' → Step H (share r t) s H' (share r t')
  | cloneCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ : Term R n} {t₁' : Term R m}
      {t₂ : Term R (n + 1)} {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' →
      Step H (clone t₁ t₂) s H' (clone t₁' (t₂.rename (DeBruijn.Ren.up (Fin.castLE h))))
  | withBorrowL {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ t₂ : Term R n} {t₁' : Term R m}
      {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' → Step H (withBorrow t₁ t₂) s H' (withBorrow t₁' (t₂.weaken h))
  | withBorrowR {n m : ℕ} {H : Heap R n} {H' : Heap R m} {v t₂ : Term R n} {t₂' : Term R m}
      {s : R} (h : n ≤ m) :
      IsValue v → Step H t₂ s H' t₂' → Step H (withBorrow v t₂) s H' (withBorrow (v.weaken h) t₂')
  | splitCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m} {s : R} :
      Step H t s H' t' → Step H (split t) s H' (split t')
  | joinL {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t₁ t₂ : Term R n} {t₁' : Term R m}
      {s : R} (h : n ≤ m) :
      Step H t₁ s H' t₁' → Step H (join t₁ t₂) s H' (join t₁' (t₂.weaken h))
  | joinR {n m : ℕ} {H : Heap R n} {H' : Heap R m} {v t₂ : Term R n} {t₂' : Term R m}
      {s : R} (h : n ≤ m) :
      IsValue v → Step H t₂ s H' t₂' → Step H (join v t₂) s H' (join (v.weaken h) t₂')
  | pushCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m} {s : R} :
      Step H t s H' t' → Step H (push t) s H' (push t')
  | pullCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m} {s : R} :
      Step H t s H' t' → Step H (pull t) s H' (pull t')
  | unborrowCong {n m : ℕ} {H : Heap R n} {H' : Heap R m} {t : Term R n} {t' : Term R m}
      {s : R} :
      Step H t s H' t' → Step H (unborrow t) s H' (unborrow t')

/-- Multi-step reduction `H ⊢ t ⇒_s H' ⊢ t'` (rules `refl` and `ext`). -/
inductive Steps : {n m : ℕ} → Heap R n → Term R n → R → Heap R m → Term R m → Prop where
  | refl {n : ℕ} (H : Heap R n) (t : Term R n) (s : R) : Steps H t s H t
  | ext {n m k : ℕ} {H : Heap R n} {H' : Heap R m} {H'' : Heap R k} {t₁ : Term R n}
      {t₂ : Term R m} {t₃ : Term R k} {s : R} :
      Step H t₁ s H' t₂ → Steps H' t₂ s H'' t₃ → Steps H t₁ s H'' t₃

end FOFU
