module
public import RequestProject.FOFU.Sec3_CoreCalculus.Typing
public import RequestProject.FOFU.Sec6_1_Preliminaries.Heap

/-!
# Heap compatibility (Definition 6.4) and Example 6.5

`Compat gc H Γ` is the relation `H ⋈ Γ` of Definition 6.4, between a heap with `n`
variables and a closed-scope context (`k = 0` identifiers) with `n` variables.

The rules are those of the paper:

* `empty`:   `∅ ⋈ ∅`;
* `extRes`:  `H, id ↦ v_r ⋈ Γ + γ,  γ ⊢ v_r : Res_id A
              ⟹  H, ref ↦_p id, id ↦ v_r ⋈ (Γ, ref : Res_id A)`;
* `gcArr`:   `H ⋈ ∅  ⟹  H, ref ↦_p id ⋈ ∅`;
* `ext`:     `H ⋈ Γ + s · Γ',  Γ' ⊢ v : A,  ∃ r'. s + r' ≡ r
              ⟹  (H, x ↦_r v) ⋈ (Γ, x : [A]_s)`;
* `extLin`:  `H ⋈ Γ + Γ',  Γ' ⊢ v : A,  ∃ r'. 1 + r' ≡ r
              ⟹  (H, x ↦_r v) ⋈ (Γ, x : A)`.

## The flag `gc`

With these rules alone (`gc = false`) **no heap containing a resource entry `id ↦ v_r`
is compatible with any context** (`Compat.ress_eq_none`): the only rule whose conclusion
contains such an entry is `extRes`, and its premise still contains the same entry.  The
evident repair is a garbage-collection rule for identifier entries analogous to `gcArr`,

* `gcRes`:   `H ⋈ ∅  ⟹  H, id ↦ v_r ⋈ ∅`,

which is enabled when `gc = true`.  The theorems of §6.3 are stated for both variants.

The typing `γ ⊢ v_r : Res_id A` of resource values is not given in the paper; we take
an array to have type `Array_id A` when all the values written to it have type `A`, and
`ref(v)` to have type `Ref_id A` when `v : A` (`ResValTy`).
-/

@[expose] public section

namespace FOFU

variable {R : Type} [Grades.PreorderedSemiring R]

/-- Typing of array values: every written value has the element type. -/
inductive ArrValTy {n : ℕ} (γ : Ctx R 0 n) : ArrVal R n → Ty R 0 → Prop where
  | init (A : Ty R 0) : ArrValTy γ .init A
  | write {a : ArrVal R n} {i : ℕ} {v : Term R n} {A : Ty R 0} :
      ArrValTy γ a A → HasType γ v A → ArrValTy γ (.write a i v) A

/-- Typing of resource values `γ ⊢ v_r : Res_id A`. -/
inductive ResValTy {n : ℕ} (γ : Ctx R 0 n) : ResVal R n → RefTy R 0 → Prop where
  | arr {a : ArrVal R n} {ι : Ident 0} {A : Ty R 0} :
      ArrValTy γ a A → ResValTy γ (.arr a) ⟨.array, ι, A⟩
  | ref {v : Term R n} {ι : Ident 0} {A : Ty R 0} :
      HasType γ v A → ResValTy γ (.ref v) ⟨.ref, ι, A⟩

/-- Heap compatibility `H ⋈ Γ` (Definition 6.4); `gc = true` adds the rule `gcRes`. -/
inductive Compat (gc : Bool) : {n : ℕ} → Heap R n → Ctx R 0 n → Prop where
  /-- `∅ ⋈ ∅` -/
  | empty : Compat gc Heap.empty Ctx.empty
  /-- `H, id ↦ v_r ⋈ Γ + γ,  γ ⊢ v_r : Res_id A
      ⟹  H, ref ↦_p id, id ↦ v_r ⋈ (Γ, ref : Res_id A)` -/
  | extRes {n : ℕ} {H : Heap R n} {Γ γ Δ : Ctx R 0 n} {a : ℕ} {p : ℚ} {id : ℕ}
      {vr : ResVal R n} {T : RefTy R 0} :
      H.refs a = none → Γ.refs a = none → T.id = .rt id → (∀ i, γ.vars i = none) →
      ResValTy γ vr T → CtxAdd Γ γ Δ → Compat gc (H.addRes id vr) Δ →
      Compat gc ((H.addRef a p id).addRes id vr) (Γ.addRef a T)
  /-- `H ⋈ ∅  ⟹  H, ref ↦_p id ⋈ ∅` -/
  | gcArr {H : Heap R 0} {a : ℕ} {p : ℚ} {id : ℕ} :
      H.refs a = none → Compat gc H Ctx.empty → Compat gc (H.addRef a p id) Ctx.empty
  /-- `H ⋈ ∅  ⟹  H, id ↦ v_r ⋈ ∅` (only when `gc = true`; not in the paper) -/
  | gcRes {H : Heap R 0} {id : ℕ} {vr : ResVal R 0} :
      gc = true → H.ress id = none → Compat gc H Ctx.empty → Compat gc (H.addRes id vr) Ctx.empty
  /-- `H ⋈ Γ + s · Γ',  Γ' ⊢ v : A,  ∃ r'. s + r' ≡ r  ⟹  (H, x ↦_r v) ⋈ (Γ, x : [A]_s)` -/
  | ext {n : ℕ} {H : Heap R n} {Γ Γ' Γs Δ : Ctx R 0 n} {v : Term R n} {A : Ty R 0} {r s : R} :
      Compat gc H Δ → CtxScale s Γ' Γs → CtxAdd Γ Γs Δ → HasType Γ' v A → (∃ r', s + r' = r) →
      Compat gc (H.snoc r v) (Γ.snoc (some (.grd A s)))
  /-- `H ⋈ Γ + Γ',  Γ' ⊢ v : A,  ∃ r'. 1 + r' ≡ r  ⟹  (H, x ↦_r v) ⋈ (Γ, x : A)` -/
  | extLin {n : ℕ} {H : Heap R n} {Γ Γ' Δ : Ctx R 0 n} {v : Term R n} {A : Ty R 0} {r : R} :
      Compat gc H Δ → CtxAdd Γ Γ' Δ → HasType Γ' v A → (∃ r', 1 + r' = r) →
      Compat gc (H.snoc r v) (Γ.snoc (some (.lin A)))

namespace Compat

/-- **Defect of Definition 6.4.** With the rules of the paper, a compatible heap has no
resource entries `id ↦ v_r`. -/
theorem ress_eq_none {n : ℕ} {H : Heap R n} {Γ : Ctx R 0 n} (h : Compat false H Γ) :
    ∀ j, H.ress j = none := by
  induction h with
  | empty => intro j; rfl
  | @extRes n H Γ γ Δ a p id' vr T _ _ _ _ _ _ _ ih =>
    exfalso
    have := ih id'
    simp [Heap.addRes] at this
  | gcArr _ _ ih => exact ih
  | gcRes hgc => exact absurd hgc Bool.false_ne_true
  | ext _ _ _ _ _ ih => intro j; simp [Heap.snoc, ih j]
  | extLin _ _ _ _ ih => intro j; simp [Heap.snoc, ih j]

/-- Every reference assumed in a compatible context is allocated in the heap. -/
theorem refs_ne_none {gc : Bool} {n : ℕ} {H : Heap R n} {Γ : Ctx R 0 n} (h : Compat gc H Γ)
    {a : ℕ} (ha : Γ.refs a ≠ none) : H.refs a ≠ none := by
  induction h with
  | empty => exact absurd rfl ha
  | @extRes n H Γ γ Δ a' p id vr T _ _ _ _ _ hadd _ ih =>
    by_cases e : a = a'
    · subst e; simp [Heap.addRef, Heap.addRes]
    · simp only [Ctx.addRef, Function.update_of_ne e] at ha
      have := ih ((hadd.refs a).ne_none_left ha)
      simpa [Heap.addRef, Heap.addRes, Function.update_of_ne e] using this
  | gcArr _ _ _ => exact absurd rfl ha
  | gcRes _ _ _ => exact absurd rfl ha
  | ext _ _ hadd _ _ ih => exact ih ((hadd.refs a).ne_none_left ha)
  | extLin _ hadd _ _ ih => exact ih ((hadd.refs a).ne_none_left ha)

end Compat

/-! ## Example 6.5 -/

/-- **Example 6.5.** With the natural-number semiring, the context `x : [A]_1, y : [B]_2`
is compatible with the heap `x ↦_7 v₁, y ↦_2 v₂`, assuming `∅ ⊢ v₁ : A` and
`x : [A]_3 ⊢ v₂ : B`.  (This holds for both variants of `Compat`.) -/
theorem example_6_5 (gc : Bool) {A B : Ty ℕ 0} {v₁ : Term ℕ 0} {v₂ : Term ℕ 1}
    (h₁ : HasType Ctx.empty v₁ A) (h₂ : HasType (Ctx.empty.snoc (some (.grd A 3))) v₂ B) :
    Compat gc ((Heap.empty.snoc 7 v₁).snoc 2 v₂)
      ((Ctx.empty.snoc (some (.grd A 1))).snoc (some (.grd B 2))) := by
  refine Compat.ext (Γ' := Ctx.empty.snoc (some (.grd A 3)))
    (Γs := Ctx.empty.snoc (some (.grd A 6))) (Δ := Ctx.empty.snoc (some (.grd A 7)))
    ?_ ?_ ?_ h₂ ⟨0, rfl⟩
  · refine Compat.ext (Γ' := Ctx.empty) (Γs := Ctx.empty) (Δ := Ctx.empty) Compat.empty
      ⟨fun i => i.elim0, rfl⟩ ⟨fun i => i.elim0, fun _ => RefAdd.noneLeft _⟩ h₁ ⟨0, rfl⟩
  · refine ⟨fun i => ?_, rfl⟩
    rw [Fin.fin_one_eq_zero i]
    exact AssmScale.grd A 3
  · refine ⟨fun i => ?_, fun _ => RefAdd.noneLeft _⟩
    rw [Fin.fin_one_eq_zero i]
    exact AssmAdd.grd A 1 6

end FOFU
