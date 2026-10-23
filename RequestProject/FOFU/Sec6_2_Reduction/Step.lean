module
public import RequestProject.FOFU.Sec6_1_Preliminaries.Values
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap
public import RequestProject.Common.Grades.PreorderedSemiring

/-!
# Single-step and multi-step reduction (Section 6.2)

`Step H t s d e f H' t'` is the judgment `H ⊢ t ⤳_s H' ⊢ t'` (usage context `s`), and
`Steps H t s H' t' θr θi` is its reflexive–transitive closure `H ⊢ t ⇒_s H' ⊢ t'`
(rules `refl` and `ext`).

## Scoped configurations

A configuration is a heap `H : Heap R n ρ ι` and a term `t : Term R n ρ`.  A step may bind
`d` new heap variables, allocate `e` new references and `f` new identifiers: it goes from
`(n, ρ, ι)` to `(n + d, ρ + e, ι + f)`.  The indices `d`, `e`, `f` are part of the judgment,
so "the heap only grows" holds by construction.  The new names are the most recent ones
(index `Var.zero`), and the old ones are weakened along `Var.shiftN`.

* The rules that bind a value to a fresh heap variable `y` and continue with `t [y / x]`
  (`⤳β`, `⤳∃β`, `⤳⊗β`, `⤳□β`, `⤳clone β`, `⤳with&`) continue with the body `t` *as it is*:
  its bound variable `Var.zero` is the new heap variable.
* When a congruence rule reduces a subterm and the configuration grows, the other
  subterms are weakened into the larger scope (`Term.wk2`, `Term.wkUnder`).
* `Steps` records how the old references and identifiers are embedded into the final
  configuration (`θr`, `θi`), so that the statements of §6.3 can compare permissions
  before and after a reduction sequence.

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
* `splitRef` / `joinRef`: the split references are two new references and the joined
  reference is a new reference; the consumed references are deallocated (their entries
  become `none`).  Since heap permissions are fractions `0 < p ≤ 1`, `joinRef` requires
  `p + q ≤ 1`, like the typing rule of `join`.
* `readArray` reads the most recent write at the index (see `ArrVal.Reads`).

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

variable {n ρ : ℕ}

/-- Weakening a term into a configuration that has grown by `d` variables and `e`
references. -/
def wk2 (d e : ℕ) (t : Term R n ρ) : Term R (n + d) (ρ + e) :=
  renameRefs (Var.shiftN e) (t.rename (Var.shiftN d))

/-- Weakening the body of a binder of `k` variables into a configuration that has grown by
`d` variables and `e` references. -/
def wkUnder (k d e : ℕ) (t : Term R (n + k) ρ) : Term R (n + d + k) (ρ + e) :=
  renameRefs (Var.shiftN e) (t.rename (Ren.upN k (Var.shiftN d)))

end Term

/-- `CopyHeap H as e H' θ`: `H'` extends `H` with fresh copies of the resources of the
`e` references in the list `as`, each copy getting a fresh identifier and a fresh
reference of permission `1`; `θ` maps each reference of `as` to its copy (and the other
references to themselves). -/
inductive CopyHeap {n ρ ι : ℕ} (H : Heap R n ρ ι) :
    List (Var ρ) → (e : ℕ) → Heap R n (ρ + e) (ι + e) → (Var ρ → Var (ρ + e)) → Prop where
  | nil : CopyHeap H [] 0 H id
  | cons {as : List (Var ρ)} {e : ℕ} {H' : Heap R n (ρ + e) (ι + e)} {θ : Var ρ → Var (ρ + e)}
      {a : Var ρ} {q : Frac} {id : Var (ι + e)} {vr : ResVal R n (ρ + e)} :
      CopyHeap H as e H' θ → H'.refs.Lookup (Var.shiftN e a) (some (q, id)) →
      H'.ress.Lookup id (some vr) →
      CopyHeap H (a :: as) (e + 1) ((H'.addId (some vr)).newRef Frac.one .zero)
        (fun b => if b = a then .zero else (θ b).succ)

variable [Grades.PreorderedSemiring R]

open Term in
/-- Single-step reduction `H ⊢ t ⤳_s H' ⊢ t'`, binding `d` new variables, allocating `e`
new references and `f` new identifiers. -/
inductive Step : {n ρ ι : ℕ} → Heap R n ρ ι → Term R n ρ → R → (d e f : ℕ) →
    Heap R (n + d) (ρ + e) (ι + f) → Term R (n + d) (ρ + e) → Prop where
  -- ### Lambda calculus
  /-- `⤳var`: `∃ r'. s + r' ⊑ r  ⟹  H, x ↦_r v ⊢ x ⤳_s H, x ↦_r v ⊢ v` -/
  | var {n ρ ι : ℕ} {H : Heap R n ρ ι} {i : Var n} {r s : R} {v : Term R n ρ} :
      H.vars.Lookup i (r, v) → (∃ r', s + r' ≤ r) → Step H (var i) s 0 0 0 H v
  /-- `⤳β`: `H ⊢ (λx. t) v ⤳_s H, y ↦_s v ⊢ t [y / x]` -/
  | beta {n ρ ι : ℕ} {H : Heap R n ρ ι} {t : Term R (n + 1) ρ} {v : Term R n ρ} {s : R} :
      IsValue v → Step H (app (lam t) v) s 1 0 0 (H.snoc s v) t
  /-- `⤳appL` -/
  | appL {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ t₂ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t₁ s d e f H' t₁' → Step H (app t₁ t₂) s d e f H' (app t₁' (t₂.wk2 d e))
  /-- `⤳appR` -/
  | appR {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {v t₂ : Term R n ρ} {t₂' : Term R (n + d) (ρ + e)} {s : R} :
      IsValue v → Step H t₂ s d e f H' t₂' → Step H (app v t₂) s d e f H' (app (v.wk2 d e) t₂')
  -- ### Existential types
  /-- `⤳∃β`: `H ⊢ unpack ⟨id, x⟩ = pack ⟨id', v⟩ in t ⤳_s H, y ↦_s v ⊢ t [y / x]` -/
  | exBeta {n ρ ι : ℕ} {H : Heap R n ρ ι} {v : Term R n ρ} {t : Term R (n + 1) ρ} {s : R} :
      IsValue v → Step H (unpack (pack v) t) s 1 0 0 (H.snoc s v) t
  -- ### Tensors
  /-- `⤳⊗β`: `H ⊢ let (x, y) = (v₁, v₂) in t ⤳_s H, x' ↦_s v₁, y' ↦_s v₂ ⊢ t [x'/x, y'/y]` -/
  | tensorBeta {n ρ ι : ℕ} {H : Heap R n ρ ι} {v₁ v₂ : Term R n ρ} {t : Term R (n + 2) ρ}
      {s : R} :
      IsValue v₁ → IsValue v₂ →
      Step H (letPair (pair v₁ v₂) t) s 2 0 0 ((H.snoc s v₁).snoc s (v₂.rename Var.succ)) t
  -- ### Graded modalities
  /-- `⤳□`: `H ⊢ t ⤳_(s * r) H' ⊢ t'  ⟹  H ⊢ [t]_r ⤳_s H' ⊢ [t']_r` -/
  | boxCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {r s : R} :
      Step H t (s * r) d e f H' t' → Step H (box r t) s d e f H' (box r t')
  /-- `⤳□β`: `H ⊢ let [x] = [v]_r in t ⤳_s H, y ↦_(s * r) v ⊢ t [y / x]` -/
  | boxBeta {n ρ ι : ℕ} {H : Heap R n ρ ι} {v : Term R n ρ} {t : Term R (n + 1) ρ} {r s : R} :
      IsValue v → Step H (letBox (box r v) t) s 1 0 0 (H.snoc (s * r) v) t
  -- ### Arrays
  /-- `⤳newArray`: a new identifier with an uninitialised array, and a new reference of
  permission `1` to it -/
  | newArray {n ρ ι : ℕ} {H : Heap R n ρ ι} {m : ℕ} {s : R} :
      Step H (app (prim .newArray) (nat m)) s 0 1 1
        ((H.addId (some (.arr .init))).newRef Frac.one .zero) (pack (star (ref .zero)))
  /-- `⤳readArray` -/
  | readArray {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {i : ℕ} {q : Frac}
      {arr : ArrVal R n ρ} {v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.arr arr)) → arr.Reads i v →
      Step H (app (app (prim .readArray) (star (ref a))) (nat i)) s 0 0 0 H
        (pair v (star (ref a)))
  /-- `⤳writeArray` -/
  | writeArray {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {i : ℕ} {q : Frac}
      {arr : ArrVal R n ρ} {v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.arr arr)) → IsValue v →
      Step H (app (app (app (prim .writeArray) (star (ref a))) (nat i)) v) s 0 0 0
        (H.setRes id (some (.arr (arr.write i v)))) (star (ref a))
  /-- `⤳deleteArray` -/
  | deleteArray {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {q : Frac}
      {arr : ArrVal R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.arr arr)) →
      Step H (app (prim .deleteArray) (star (ref a))) s 0 0 0 ((H.eraseRef a).eraseRes id) unit
  -- ### References (reconstructed)
  /-- `newRef v` allocates a reference with permission `1` (reconstructed) -/
  | newRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {v : Term R n ρ} {s : R} :
      IsValue v →
      Step H (app (prim .newRef) v) s 0 1 1
        ((H.addId (some (.ref v))).newRef Frac.one .zero) (pack (star (ref .zero)))
  /-- `readRef` returns the contents of a boxed stored value (reconstructed) -/
  | readRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {q : Frac} {r : R}
      {v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.ref (box r v))) →
      Step H (app (prim .readRef) (star (ref a))) s 0 0 0 H (pair v (star (ref a)))
  /-- **Amendment (not in the paper).** `readRefSplit` splits the grade of a stored box
  `[v]_(q+r)`: it returns `[v]_q` and leaves `[v]_r` in the reference. -/
  | readRefSplit {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {p : Frac} {q r : R}
      {v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (p, id)) → H.ress.Lookup id (some (.ref (box (q + r) v))) →
      Step H (app (prim .readRefSplit) (star (ref a))) s 0 0 0
        (H.setRes id (some (.ref (box r v)))) (pair (box q v) (star (ref a)))
  /-- `swapRef` exchanges the stored value (reconstructed) -/
  | swapRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {q : Frac}
      {v₀ v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.ref v₀)) → IsValue v →
      Step H (app (app (prim .swapRef) (star (ref a))) v) s 0 0 0
        (H.setRes id (some (.ref v))) (pair v₀ (star (ref a)))
  /-- `freezeRef` deallocates the reference and returns its contents (reconstructed) -/
  | freezeRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {q : Frac}
      {v : Term R n ρ} {s : R} :
      H.refs.Lookup a (some (q, id)) → H.ress.Lookup id (some (.ref v)) →
      Step H (app (prim .freezeRef) (star (ref a))) s 0 0 0 ((H.eraseRef a).eraseRes id) v
  -- ### Sharing and cloning
  /-- `⤳share β` (the heap is left unchanged, see the module docstring) -/
  | share {n ρ ι : ℕ} {H : Heap R n ρ ι} {v : Term R n ρ} {r s : R} :
      IsValue v → Step H (share r (star v)) s 0 0 0 H (box r v)
  /-- `⤳clone β`: the resources of the references of `v` are copied (`CopyHeap`), and
  `x` is bound to `pack ⟨id̅, *θ(v)⟩` -/
  | clone {n ρ ι e : ℕ} {H : Heap R n ρ ι} {H' : Heap R n (ρ + e) (ι + e)} {v : Term R n ρ}
      {t : Term R (n + 1) ρ} {r s : R} {as : List (Var ρ)} {θ : Var ρ → Var (ρ + e)} :
      IsValue v → as.Nodup → (∀ a, a ∈ as ↔ v.RefOccurs a) → CopyHeap H as e H' θ →
      Step H (clone (box r v) t) s 1 e e (H'.snoc s (pack (star (renameRefs θ v))))
        (renameRefs (Var.shiftN e) t)
  -- ### Borrowing
  /-- `⤳with&`: `H ⊢ withBorrow (λx. t) (*v) ⤳_s H, y ↦_s (*v) ⊢ unborrow (t [y / x])` -/
  | withBorrow {n ρ ι : ℕ} {H : Heap R n ρ ι} {t : Term R (n + 1) ρ} {v : Term R n ρ} {s : R} :
      IsValue v → Step H (withBorrow (lam t) (star v)) s 1 0 0 (H.snoc s (star v)) (unborrow t)
  /-- `⤳un&`: `H ⊢ unborrow (*v) ⤳_s H ⊢ *v` -/
  | unborrow {n ρ ι : ℕ} {H : Heap R n ρ ι} {v : Term R n ρ} {s : R} :
      IsValue v → Step H (unborrow (star v)) s 0 0 0 H (star v)
  -- ### Push and pull
  /-- `H ⊢ push (*(v₁, v₂)) ⤳_s H ⊢ (*v₁, *v₂)` -/
  | push {n ρ ι : ℕ} {H : Heap R n ρ ι} {v₁ v₂ : Term R n ρ} {s : R} :
      IsValue v₁ → IsValue v₂ →
      Step H (push (star (pair v₁ v₂))) s 0 0 0 H (pair (star v₁) (star v₂))
  /-- `H ⊢ pull (*v₁, *v₂) ⤳_s H ⊢ *(v₁, v₂)` -/
  | pull {n ρ ι : ℕ} {H : Heap R n ρ ι} {v₁ v₂ : Term R n ρ} {s : R} :
      IsValue v₁ → IsValue v₂ →
      Step H (pull (pair (star v₁) (star v₂))) s 0 0 0 H (star (pair v₁ v₂))
  -- ### Split and join
  /-- `⤳splitRef`: `ref ↦_p id` is replaced by two new references `ref₁ ↦_(p/2) id`,
  `ref₂ ↦_(p/2) id` -/
  | splitRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {a : Var ρ} {id : Var ι} {p : Frac}
      {vr : ResVal R n ρ} {s : R} :
      H.refs.Lookup a (some (p, id)) → H.ress.Lookup id (some vr) →
      Step H (split (star (ref a))) s 0 2 0
        (((H.eraseRef a).newRef p.half id).newRef p.half id)
        (pair (star (ref (.succ .zero))) (star (ref .zero)))
  /-- `⤳joinRef`: `ref₁ ↦_p id`, `ref₂ ↦_q id` are replaced by a new reference
  `ref ↦_(p+q) id` -/
  | joinRef {n ρ ι : ℕ} {H : Heap R n ρ ι} {a₁ a₂ : Var ρ} {id : Var ι} {p q : Frac}
      {vr : ResVal R n ρ} {s : R} (h : p.1 + q.1 ≤ 1) :
      H.refs.Lookup a₁ (some (p, id)) → H.refs.Lookup a₂ (some (q, id)) → a₁ ≠ a₂ →
      H.ress.Lookup id (some vr) →
      Step H (join (star (ref a₁)) (star (ref a₂))) s 0 1 0
        (((H.eraseRef a₁).eraseRef a₂).newRef (p.add q h) id) (star (ref .zero))
  -- ### Reconstructed congruence rules (call-by-value, left to right)
  | pairL {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ t₂ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t₁ s d e f H' t₁' → Step H (pair t₁ t₂) s d e f H' (pair t₁' (t₂.wk2 d e))
  | pairR {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {v t₂ : Term R n ρ} {t₂' : Term R (n + d) (ρ + e)} {s : R} :
      IsValue v → Step H t₂ s d e f H' t₂' → Step H (pair v t₂) s d e f H' (pair (v.wk2 d e) t₂')
  | letPairCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {t₂ : Term R (n + 2) ρ} {s : R} :
      Step H t₁ s d e f H' t₁' →
      Step H (letPair t₁ t₂) s d e f H' (letPair t₁' (t₂.wkUnder 2 d e))
  | letUnitCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ t₂ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t₁ s d e f H' t₁' → Step H (letUnit t₁ t₂) s d e f H' (letUnit t₁' (t₂.wk2 d e))
  | unitBeta {n ρ ι : ℕ} {H : Heap R n ρ ι} {t : Term R n ρ} {s : R} :
      Step H (letUnit unit t) s 0 0 0 H t
  | letBoxCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {t₂ : Term R (n + 1) ρ} {s : R} :
      Step H t₁ s d e f H' t₁' →
      Step H (letBox t₁ t₂) s d e f H' (letBox t₁' (t₂.wkUnder 1 d e))
  | packCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t s d e f H' t' → Step H (pack t) s d e f H' (pack t')
  | unpackCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {t₂ : Term R (n + 1) ρ} {s : R} :
      Step H t₁ s d e f H' t₁' →
      Step H (unpack t₁ t₂) s d e f H' (unpack t₁' (t₂.wkUnder 1 d e))
  | shareCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {r s : R} :
      Step H t s d e f H' t' → Step H (share r t) s d e f H' (share r t')
  | cloneCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {t₂ : Term R (n + 1) ρ} {s : R} :
      Step H t₁ s d e f H' t₁' →
      Step H (clone t₁ t₂) s d e f H' (clone t₁' (t₂.wkUnder 1 d e))
  | withBorrowL {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ t₂ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t₁ s d e f H' t₁' →
      Step H (withBorrow t₁ t₂) s d e f H' (withBorrow t₁' (t₂.wk2 d e))
  | withBorrowR {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {v t₂ : Term R n ρ} {t₂' : Term R (n + d) (ρ + e)} {s : R} :
      IsValue v → Step H t₂ s d e f H' t₂' →
      Step H (withBorrow v t₂) s d e f H' (withBorrow (v.wk2 d e) t₂')
  | splitCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t s d e f H' t' → Step H (split t) s d e f H' (split t')
  | joinL {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t₁ t₂ : Term R n ρ} {t₁' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t₁ s d e f H' t₁' → Step H (join t₁ t₂) s d e f H' (join t₁' (t₂.wk2 d e))
  | joinR {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {v t₂ : Term R n ρ} {t₂' : Term R (n + d) (ρ + e)} {s : R} :
      IsValue v → Step H t₂ s d e f H' t₂' → Step H (join v t₂) s d e f H' (join (v.wk2 d e) t₂')
  | pushCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t s d e f H' t' → Step H (push t) s d e f H' (push t')
  | pullCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t s d e f H' t' → Step H (pull t) s d e f H' (pull t')
  | unborrowCong {n ρ ι d e f : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {t : Term R n ρ} {t' : Term R (n + d) (ρ + e)} {s : R} :
      Step H t s d e f H' t' → Step H (unborrow t) s d e f H' (unborrow t')

/-- Multi-step reduction `H ⊢ t ⇒_s H' ⊢ t'` (rules `refl` and `ext`).  The maps
`θr : Var ρ → Var ρ'` and `θi : Var ι → Var ι'` send the references and identifiers of the
initial configuration to their names in the final one. -/
inductive Steps : {n ρ ι n' ρ' ι' : ℕ} → Heap R n ρ ι → Term R n ρ → R →
    Heap R n' ρ' ι' → Term R n' ρ' → (Var ρ → Var ρ') → (Var ι → Var ι') → Prop where
  | refl {n ρ ι : ℕ} (H : Heap R n ρ ι) (t : Term R n ρ) (s : R) : Steps H t s H t id id
  | ext {n ρ ι d e f n' ρ' ι' : ℕ} {H : Heap R n ρ ι} {H' : Heap R (n + d) (ρ + e) (ι + f)}
      {H'' : Heap R n' ρ' ι'} {t₁ : Term R n ρ} {t₂ : Term R (n + d) (ρ + e)}
      {t₃ : Term R n' ρ'} {s : R} {θr : Var (ρ + e) → Var ρ'} {θi : Var (ι + f) → Var ι'} :
      Step H t₁ s d e f H' t₂ → Steps H' t₂ s H'' t₃ θr θi →
      Steps H t₁ s H'' t₃ (θr ∘ Var.shiftN e) (θi ∘ Var.shiftN f)

end FOFU
