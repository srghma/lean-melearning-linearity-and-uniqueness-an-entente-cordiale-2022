module
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap
public import RequestProject.FOFU.Sec6_1_Preliminaries.TypingRefs

/-!
# Heap compatibility (Definition 6.4) and Example 6.5

`Compat gc H Γ` is the relation `H ⋈ Γ` of Definition 6.4, between a heap
`H : Heap R n ρ ι` and a context `Γ : TCtx R ι n ρ` over the same scope (the identifiers of
the heap are the identifiers of the types of the context).

The rules are those of the paper, read in the scoped representation of heaps (the newly
added entry is always the most recent name `Var.zero`, so the freshness of the paper's
names holds by construction):

* `empty`:   `∅ ⋈ ∅`;
* `extRes`:  `H, id ↦ v_r ⋈ Γ + γ,  γ ⊢ v_r : Res_id A
              ⟹  H, ref ↦_p id, id ↦ v_r ⋈ (Γ, ref : Res_id A)`.
  In the scoped representation the entry `id ↦ v_r` is an entry of the premise heap
  (`H.ress.Lookup id (some v_r)`), and the conclusion adds the new reference
  (`H.newRef p id`); `γ` is a runtime context (it has no assumptions on variables);
* `gcArr`:   `H ⋈ ∅  ⟹  H, ref ↦_p id ⋈ ∅`;
* `ext`:     `H ⋈ Γ + s · Γ',  Γ' ⊢ v : A,  ∃ r'. s + r' ≡ r
              ⟹  (H, x ↦_r v) ⋈ (Γ, x : [A]_s)`;
* `extLin`:  `H ⋈ Γ + Γ',  Γ' ⊢ v : A,  ∃ r'. 1 + r' ≡ r
              ⟹  (H, x ↦_r v) ⋈ (Γ, x : A)`.

In addition, the structural rule

* `freshId`: `H ⋈ Γ  ⟹  H, id ⋈ Γ, id`

adds an identifier without resource entry to the heap and to the context.  It is an
artifact of the scoped representation (in the paper, identifiers are drawn from an
infinite supply and need not be introduced), and it does not add resource entries.

## The flag `gc`

With these rules alone (`Compat false`) **no heap containing a resource entry `id ↦ v_r`
is compatible with any context** (`Compat.ress_eq_none`): the only rule whose conclusion
contains such an entry is `extRes`, and its premise still contains the same entry.  The
evident repair is a garbage-collection rule for identifier entries analogous to `gcArr`,

* `gcRes`:   `H ⋈ ∅  ⟹  H, id ↦ v_r ⋈ ∅`,

which is available in the variant `Compat true` (the Boolean index `gc` of `Compat`
selects the variant; `gcRes` concludes `Compat true`).  The theorems of §6.3 are stated
for both variants.

The typing `γ ⊢ v_r : Res_id A` of resource values is not given in the paper; we take
an array to have type `Array_id A` when all the values written to it have type `A`, and
`ref(v)` to have type `Ref_id A` when `v : A` (`ResValTy`).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- Extending a context by a new reference `Var.zero` with the assumption `o`. -/
def TCtx.addRef {k n ρ : ℕ} (Γ : TCtx R k n ρ) (o : Option (RefTy R k)) : TCtx R k n (ρ + 1) :=
  ⟨Γ.refs ,, o, Γ.vars⟩

omit [Grades.PreorderedSemiring R] in
@[simp] lemma TCtx.addRef_refs {k n ρ : ℕ} (Γ : TCtx R k n ρ) (o : Option (RefTy R k)) :
    (Γ.addRef o).refs = Γ.refs ,, o := rfl
omit [Grades.PreorderedSemiring R] in
@[simp] lemma TCtx.addRef_vars {k n ρ : ℕ} (Γ : TCtx R k n ρ) (o : Option (RefTy R k)) :
    (Γ.addRef o).vars = Γ.vars := rfl

/-- Typing of array values: every written value has the element type. -/
inductive ArrValTy {ι n ρ : ℕ} (γ : TCtx R ι n ρ) : ArrVal R n ρ → Ty R ι → Prop where
  | init (A : Ty R ι) : ArrValTy γ .init A
  | write {a : ArrVal R n ρ} {i : ℕ} {v : Term R n ρ} {A : Ty R ι} :
      ArrValTy γ a A → HasType γ v A → ArrValTy γ (.write a i v) A

/-- Typing of resource values `γ ⊢ v_r : Res_id A`. -/
inductive ResValTy {ι n ρ : ℕ} (γ : TCtx R ι n ρ) : ResVal R n ρ → RefTy R ι → Prop where
  | arr {a : ArrVal R n ρ} {id : Var ι} {A : Ty R ι} :
      ArrValTy γ a A → ResValTy γ (.arr a) ⟨.array, id, A⟩
  | ref {v : Term R n ρ} {id : Var ι} {A : Ty R ι} :
      HasType γ v A → ResValTy γ (.ref v) ⟨.ref, id, A⟩

/-- Heap compatibility `H ⋈ Γ` (Definition 6.4).  The index `gc` selects the variant:
the rule `gcRes` only derives judgments `Compat true H Γ`. -/
inductive Compat : Bool → {n ρ ι : ℕ} → Heap R n ρ ι → TCtx R ι n ρ → Prop where
  /-- `∅ ⋈ ∅` -/
  | empty {gc : Bool} : Compat gc Heap.empty TCtx.empty
  /-- `H ⋈ Γ  ⟹  H, id ⋈ Γ, id` (a new identifier without resource entry) -/
  | freshId {gc : Bool} {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ : TCtx R ι n ρ} :
      Compat gc H Γ → Compat gc (H.addId none) Γ.shiftNames
  /-- `H, id ↦ v_r ⋈ Γ + γ,  γ ⊢ v_r : Res_id A
      ⟹  H, ref ↦_p id, id ↦ v_r ⋈ (Γ, ref : Res_id A)` -/
  | extRes {gc : Bool} {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ γ Δ : TCtx R ι n ρ} {p : Frac}
      {id : Var ι} {vr : ResVal R n ρ} {κ : ResKind} {A : Ty R ι} :
      H.ress.Lookup id (some vr) → γ.vars = .replicate n none →
      ResValTy γ vr ⟨κ, id, A⟩ → CtxAdd Γ γ Δ → Compat gc H Δ →
      Compat gc (H.newRef p id) (Γ.addRef (some ⟨κ, id, A⟩))
  /-- `H ⋈ ∅  ⟹  H, ref ↦_p id ⋈ ∅` -/
  | gcArr {gc : Bool} {ρ ι : ℕ} {H : Heap R 0 ρ ι} {p : Frac} {id : Var ι} :
      Compat gc H TCtx.empty → Compat gc (H.newRef p id) TCtx.empty
  /-- `H ⋈ ∅  ⟹  H, id ↦ v_r ⋈ ∅` (only in the variant `Compat true`; not in the paper) -/
  | gcRes {ρ ι : ℕ} {H : Heap R 0 ρ ι} {vr : ResVal R 0 ρ} :
      Compat true H TCtx.empty → Compat true (H.addId (some vr)) TCtx.empty
  /-- `H ⋈ Γ + s · Γ',  Γ' ⊢ v : A,  ∃ r'. s + r' ≡ r  ⟹  (H, x ↦_r v) ⋈ (Γ, x : [A]_s)` -/
  | ext {gc : Bool} {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ Γ' Γs Δ : TCtx R ι n ρ} {v : Term R n ρ}
      {A : Ty R ι} {r s : R} :
      Compat gc H Δ → CtxScale s Γ' Γs → CtxAdd Γ Γs Δ → HasType Γ' v A → (∃ r', s + r' = r) →
      Compat gc (H.snoc r v) (Γ.cons (some (.grd A s)))
  /-- `H ⋈ Γ + Γ',  Γ' ⊢ v : A,  ∃ r'. 1 + r' ≡ r  ⟹  (H, x ↦_r v) ⋈ (Γ, x : A)` -/
  | extLin {gc : Bool} {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ Γ' Δ : TCtx R ι n ρ} {v : Term R n ρ}
      {A : Ty R ι} {r : R} :
      Compat gc H Δ → CtxAdd Γ Γ' Δ → HasType Γ' v A → (∃ r', 1 + r' = r) →
      Compat gc (H.snoc r v) (Γ.cons (some (.lin A)))

namespace Compat

/-- **Defect of Definition 6.4.** With the rules of the paper, a compatible heap has no
resource entries `id ↦ v_r`. -/
theorem ress_eq_none {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ : TCtx R ι n ρ} (h : Compat false H Γ) :
    ∀ j, H.ress.get j = none := by
  generalize hgc : false = gc at h
  induction h with
  | empty => intro j; cases j
  | freshId _ ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => simpa using ih hgc j
  | @extRes _ _ _ _ _ _ _ _ _ id _ _ _ hid _ _ _ _ ih =>
    exfalso
    have := ih hgc id
    simp [hid.eq] at this
  | gcArr _ ih => intro j; simp [ih hgc j]
  | gcRes => cases hgc
  | ext _ _ _ _ _ ih => intro j; simp [ih hgc j]
  | extLin _ _ _ _ ih => intro j; simp [ih hgc j]

/-- Every reference assumed in a compatible context is allocated in the heap. -/
theorem refs_ne_none {gc : Bool} {n ρ ι : ℕ} {H : Heap R n ρ ι} {Γ : TCtx R ι n ρ}
    (h : Compat gc H Γ) {a : Var ρ} (ha : Γ.refs.get a ≠ none) : H.refs.get a ≠ none := by
  induction h with
  | empty => cases a
  | freshId _ ih =>
    simp only [TCtx.shiftNames, TCtx.renNames_refs, Ctx.get_map, ne_eq,
      Option.map_eq_none_iff] at ha
    simpa using ih ha
  | extRes _ _ _ hadd _ ih =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [TCtx.addRef_refs, Ctx.get_snoc_succ] at ha
      simpa using ih ((hadd.refs.get a).ne_none_left ha)
  | gcArr _ _ => simp at ha
  | gcRes _ _ => simp at ha
  | ext _ _ hadd _ _ ih => exact ih ((hadd.refs.get a).ne_none_left ha)
  | extLin _ hadd _ _ ih => exact ih ((hadd.refs.get a).ne_none_left ha)

end Compat

/-! ## Example 6.5 -/

/-- **Example 6.5.** With the natural-number semiring, the context `x : [A]_1, y : [B]_2`
is compatible with the heap `x ↦_7 v₁, y ↦_2 v₂`, assuming `∅ ⊢ v₁ : A` and
`x : [A]_3 ⊢ v₂ : B`.  (This holds for both variants of `Compat`.) -/
theorem example_6_5 (gc : Bool) {A B : Ty ℕ 0} {v₁ : Term ℕ 0 0} {v₂ : Term ℕ 1 0}
    (h₁ : HasType TCtx.empty v₁ A) (h₂ : HasType (TCtx.empty.cons (some (.grd A 3))) v₂ B) :
    Compat gc ((Heap.empty.snoc 7 v₁).snoc 2 v₂)
      ((TCtx.empty.cons (some (.grd A 1))).cons (some (.grd B 2))) := by
  refine Compat.ext (Γ' := TCtx.empty.cons (some (.grd A 3)))
    (Γs := TCtx.empty.cons (some (.grd A 6))) (Δ := TCtx.empty.cons (some (.grd A 7)))
    ?_ ?_ ?_ h₂ ⟨0, rfl⟩
  · refine Compat.ext (Γ' := TCtx.empty) (Γs := TCtx.empty) (Δ := TCtx.empty) Compat.empty
      ⟨rfl, .nil⟩ ⟨.nil, .nil⟩ h₁ ⟨0, rfl⟩
  · exact ⟨rfl, .snoc .nil (AssmScale.grd A 3)⟩
  · exact ⟨.nil, .snoc .nil (AssmAdd.grd A 1 6)⟩

end FOFU
