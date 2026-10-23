module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas
public import Mathlib.Data.Fintype.Basic

/-!
# A dereliction-free presentation of the typing judgment

`HasTypeD` has the same rules as `HasType` except that the dereliction rule `der` is
replaced by the derived rule `(var')` of §3 (`varG`: `0 · Γ, x : [A]_1 ⊢ x : A`).
The two judgments are equivalent (`hasType_iff_hasTypeD`): dereliction is admissible
for `HasTypeD` (`HasTypeD.der`), because a linear variable is used at exactly one
occurrence of `var`, which dereliction turns into `varG`.

Working with `HasTypeD` makes the substitution lemmas provable by induction: with an
explicit dereliction rule, the context of the substituted term may overlap with a
variable that is derelicted later, which breaks the induction.

The same idea is used for *Linearity and Uniqueness* in
`RequestProject/LCU/Sec3_1_Calculus/TypingD.lean` (reused here as a technique; the rule
sets differ, so the code is not shared).

We also prove that approximation extends to whole contexts (`HasTypeD.approxCtx`): if
`Γ ⊢ t : A` and `Γ'` is `Γ` with some grades approximated upwards, then `Γ' ⊢ t : A`.
-/

@[expose] public section

namespace FOFU

open Ty

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The dereliction-free typing judgment (see the module docstring). -/
inductive HasTypeD : {k n ρ : ℕ} → TCtx R k n ρ → Term R n ρ → Ty R k → Prop where
  /-- `0 · Γ, x : A ⊢ x : A` -/
  | var {k n ρ : ℕ} {Γ : TCtx R k n ρ} {i : Var n} {A : Ty R k} :
      Γ.vars.Pick ZeroAssm i (some (.lin A)) → HasTypeD Γ (.var i) A
  /-- `0 · Γ, x : [A]_1 ⊢ x : A` (the derived rule `var'`) -/
  | varG {k n ρ : ℕ} {Γ : TCtx R k n ρ} {i : Var n} {A : Ty R k} :
      Γ.vars.Pick ZeroAssm i (some (.grd A 1)) → HasTypeD Γ (.var i) A
  /-- `Γ, x : A ⊢ t : B  ⟹  Γ ⊢ λx. t : A ⊸ B` -/
  | abs {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R (n + 1) ρ} {A B : Ty R k} :
      HasTypeD (Γ.cons (some (.lin A))) t B → HasTypeD Γ (.lam t) (lolli A B)
  /-- `Γ₁ ⊢ t₁ : A ⊸ B,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ t₁ t₂ : B` -/
  | app {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (lolli A B) → HasTypeD Γ₂ t₂ A → HasTypeD Γ (.app t₁ t₂) B
  /-- `[Γ] ⊢ t : A,  ¬ resourceAllocator(t)  ⟹  r · Γ ⊢ [t]_r : □_r A` -/
  | pr {k n ρ : ℕ} {Γ₀ Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} {r : R} :
      CtxScale r Γ₀ Γ → HasTypeD Γ₀ t A → ¬ t.Allocates → HasTypeD Γ (.box r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : [A]_r ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ let [x] = t₁ in t₂ : B` -/
  | elim {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A B : Ty R k} {r : R} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (box r A) → HasTypeD (Γ₂.cons (some (.grd A r))) t₂ B →
      HasTypeD Γ (.letBox t₁ t₂) B
  /-- approximation: `Γ, x : [A]_r ⊢ t : B,  r ⊑ s  ⟹  Γ, x : [A]_s ⊢ t : B` -/
  | approx {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} {i : Var n} {A : Ty R k}
      {r s : R} :
      Γ.vars.Lookup i (some (.grd A r)) → r ≤ s → HasTypeD Γ t B →
      HasTypeD (Γ.setVar i (some (.grd A s))) t B
  /-- `Γ₁ ⊢ t₁ : A,  Γ₂ ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ (t₁, t₂) : A ⊗ B` -/
  | tensorI {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ A → HasTypeD Γ₂ t₂ B → HasTypeD Γ (.pair t₁ t₂) (tensor A B)
  /-- `Γ₁ ⊢ t₁ : A ⊗ B,  Γ₂, x : A, y : B ⊢ t₂ : C  ⟹  Γ₁ + Γ₂ ⊢ let (x, y) = t₁ in t₂ : C` -/
  | tensorE {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 2) ρ}
      {A B C : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (tensor A B) →
      HasTypeD ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      HasTypeD Γ (.letPair t₁ t₂) C
  /-- `0 · Γ ⊢ () : unit` -/
  | unitI {k n ρ : ℕ} {Γ : TCtx R k n ρ} : Γ.IsZero → HasTypeD Γ .unit unit
  /-- `Γ₁ ⊢ t₁ : unit,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ let () = t₁ in t₂ : A` -/
  | unitE {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ unit → HasTypeD Γ₂ t₂ A → HasTypeD Γ (.letUnit t₁ t₂) A
  /-- `Γ ⊢ t : A [ι / id]  ⟹  Γ ⊢ pack ⟨ι, t⟩ : ∃ id. A` -/
  | pack {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R (k + 1)} (ι : Var k) :
      HasTypeD Γ t (A.inst ι) → HasTypeD Γ (.pack t) (ex A)
  /-- `Γ₁ ⊢ t₁ : ∃ id. A,  Γ₂, id, x : A ⊢ t₂ : B,  id ∉ fv(B)
      ⟹  Γ₁ + Γ₂ ⊢ unpack ⟨id, x⟩ = t₁ in t₂ : B` -/
  | unpack {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A : Ty R (k + 1)} {B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (ex A) →
      HasTypeD (Γ₂.shiftNames.cons (some (.lin A))) t₂ B.shift →
      HasTypeD Γ (.unpack t₁ t₂) B
  /-- `Γ ⊢ t : *A  ⟹  Γ ⊢ share t : □_r A` (§4) -/
  | share {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} (r : R) :
      HasTypeD Γ t (star A) → HasTypeD Γ (.share r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : ∃ id. *A' ⊢ t₂ : B,  1 ⊑ r,  cloneable(A)
      ⟹  Γ₁ + Γ₂ ⊢ clone t₁ as x in t₂ : B` (§4), where `A'` abstracts an identifier
      of `A` -/
  | clone {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A : Ty R k} {A' : Ty R (k + 1)} {B : Ty R k} {r : R} (ι : Var k) :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (box r A) → 1 ≤ r → A.cloneable = true → A'.inst ι = A →
      HasTypeD (Γ₂.cons (some (.lin (ex (star A'))))) t₂ B →
      HasTypeD Γ (.clone t₁ t₂) B
  /-- `Γ₁ ⊢ t₁ : &₁ A ⊸ &₁ B,  Γ₂ ⊢ t₂ : *A  ⟹  Γ₁ + Γ₂ ⊢ withBorrow t₁ t₂ : *B` (§5) -/
  | withBorrow {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (lolli (borrow Perm.one A) (borrow Perm.one B)) →
      HasTypeD Γ₂ t₂ (star A) → HasTypeD Γ (.withBorrow t₁ t₂) (star B)
  /-- `Γ ⊢ t : &_p A  ⟹  Γ ⊢ split t : &_(p/2) A ⊗ &_(p/2) A` (§5) -/
  | split {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} {f : Frac} :
      HasTypeD Γ t (borrow (.frac f) A) →
      HasTypeD Γ (.split t) (tensor (borrow (.frac f.half) A) (borrow (.frac f.half) A))
  /-- `Γ₁ ⊢ t₁ : &_p A,  Γ₂ ⊢ t₂ : &_q A  ⟹  Γ₁ + Γ₂ ⊢ join t₁ t₂ : &_(p+q) A` (§5) -/
  | join {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A : Ty R k} {f g : Frac}
      (h : f.1 + g.1 ≤ 1) :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (borrow (.frac f) A) → HasTypeD Γ₂ t₂ (borrow (.frac g) A) →
      HasTypeD Γ (.join t₁ t₂) (borrow (.frac (f.add g h)) A)
  /-- `Γ ⊢ t : &_p (A ⊗ B)  ⟹  Γ ⊢ push t : &_p A ⊗ &_p B` (§5.2) -/
  | push {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A B : Ty R k} {p : Perm} :
      HasTypeD Γ t (borrow p (tensor A B)) →
      HasTypeD Γ (.push t) (tensor (borrow p A) (borrow p B))
  /-- `Γ ⊢ t : &_p A ⊗ &_p B  ⟹  Γ ⊢ pull t : &_p (A ⊗ B)` (§5.2) -/
  | pull {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A B : Ty R k} {p : Perm} :
      HasTypeD Γ t (tensor (borrow p A) (borrow p B)) →
      HasTypeD Γ (.pull t) (borrow p (tensor A B))
  /-- natural number literals: `0 · Γ ⊢ n : ℕ` -/
  | nat {k n ρ : ℕ} {Γ : TCtx R k n ρ} (m : ℕ) : Γ.IsZero → HasTypeD Γ (.nat m) nat
  /-- float literals: `0 · Γ ⊢ x : 𝔽` -/
  | float {k n ρ : ℕ} {Γ : TCtx R k n ρ} (x : FloatLit) : Γ.IsZero → HasTypeD Γ (.float x) float
  /-- the resource primitives: `0 · Γ ⊢ p : A` for the types `A` of `PrimTy` -/
  | prim {k n ρ : ℕ} {Γ : TCtx R k n ρ} {p : Prim} {A : Ty R k} :
      Γ.IsZero → PrimTy p A → HasTypeD Γ (.prim p) A
  /-- `γ ⊢ t : A  ⟹  0 · Γ, γ ⊢ *t : &_p A` (§6.1) -/
  | nec {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} (p : Perm) :
      Γ.IsZero → HasTypeD Γ.refsOnly t A → HasTypeD Γ (.star t) (borrow p A)
  /-- `Γ ⊢ t : &₁ A  ⟹  Γ ⊢ unborrow t : *A` (§6.1) -/
  | unborrow {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} :
      HasTypeD Γ t (borrow Perm.one A) → HasTypeD Γ (.unborrow t) (star A)
  /-- `0 · Γ, ref : Res_id A ⊢ ref : Res_id A` (§6.1) -/
  | ref {k n ρ : ℕ} {Γ : TCtx R k n ρ} {a : Var ρ} {T : RefTy R k} :
      Γ.IsZero → Γ.refs.Lookup a (some T) → HasTypeD Γ (.ref a) T.toTy


/-! ## Context lemmas about `setVar` -/

lemma Ctx.map_set {α β : Type} {n : ℕ} (f : α → β) (Γ : Ctx α n) (i : Var n) (a : α) :
    (Γ.set i a).map f = (Γ.map f).set i (f a) :=
  Ctx.ext fun j => by simp only [Ctx.get_map, Ctx.get_set]; split_ifs <;> rfl

namespace TCtx

section
omit [Grades.PreorderedSemiring R]

variable {k k' n ρ : ℕ}

@[simp] lemma cons_setVar_succ (Γ : TCtx R k n ρ) (a b : Option (Assm R k)) (i : Var n) :
    (Γ.cons a).setVar (.succ i) b = (Γ.setVar i b).cons a := rfl

lemma renNames_setVar (r : Var k → Var k') (Γ : TCtx R k n ρ) (i : Var n)
    (a : Option (Assm R k)) :
    (Γ.setVar i a).renNames r = (Γ.renNames r).setVar i (a.map (Assm.ren r)) :=
  TCtx.ext rfl (Ctx.map_set _ _ _ _)

lemma setVar_comm (Γ : TCtx R k n ρ) {i j : Var n} (h : i ≠ j) (a b : Option (Assm R k)) :
    (Γ.setVar i a).setVar j b = (Γ.setVar j b).setVar i a :=
  TCtx.ext rfl (Ctx.set_comm _ h a b)

@[simp] lemma setVar_get (Γ : TCtx R k n ρ) (i : Var n) : Γ.setVar i (Γ.vars.get i) = Γ :=
  TCtx.ext rfl (Ctx.set_get _ _)

@[simp] lemma setVar_setVar (Γ : TCtx R k n ρ) (i : Var n) (a b : Option (Assm R k)) :
    (Γ.setVar i a).setVar i b = Γ.setVar i b :=
  TCtx.ext rfl (Ctx.set_set _ _ _ _)

end

end TCtx

lemma AssmAdd.noneRight' {k : ℕ} (a : Option (Assm R k)) : AssmAdd a none a := by
  cases a
  · exact .noneLeft _
  · exact .noneRight _

/-- A linear assumption of a sum comes from exactly one of the summands. -/
lemma AssmAdd.lin_cases {k : ℕ} {a b : Option (Assm R k)} {A : Ty R k}
    (h : AssmAdd a b (some (.lin A))) :
    (a = some (.lin A) ∧ b = none) ∨ (a = none ∧ b = some (.lin A)) := by
  cases h with
  | noneLeft _ => exact Or.inr ⟨rfl, rfl⟩
  | noneRight _ => exact Or.inl ⟨rfl, rfl⟩

lemma AssmLe.cases' {k : ℕ} {a b : Option (Assm R k)} (h : AssmLe a b) :
    b = a ∨ ∃ A r s, a = some (.grd A r) ∧ b = some (.grd A s) ∧ r ≤ s := by
  cases h with
  | refl => exact Or.inl rfl
  | grd A h => exact Or.inr ⟨A, _, _, rfl, rfl, h⟩

/-- Splitting a linear assumption of a sum, and updating it on the side it comes from. -/
lemma CtxAdd.lin_split {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} (h : CtxAdd Γ₁ Γ₂ Γ) {i : Var n}
    {A : Ty R k} (hi : Γ.vars.get i = some (.lin A)) (g : Option (Assm R k)) :
    (Γ₁.vars.get i = some (.lin A) ∧ CtxAdd (Γ₁.setVar i g) Γ₂ (Γ.setVar i g)) ∨
    (Γ₂.vars.get i = some (.lin A) ∧ CtxAdd Γ₁ (Γ₂.setVar i g) (Γ.setVar i g)) := by
  have := h.vars.get i
  rw [hi] at this
  rcases this.lin_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    have := h.setVar i (a := g) (AssmAdd.noneRight' g)
    rwa [← h2, TCtx.setVar_get] at this
  · refine Or.inr ⟨h2, ?_⟩
    have := h.setVar i (b := g) (AssmAdd.noneLeft g)
    rwa [← h1, TCtx.setVar_get] at this

/-! ## Approximation of whole contexts -/

namespace HasTypeD

theorem approxCtx {k n ρ : ℕ} {Γ Γ' : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasTypeD Γ t B) (hle : CtxLe Γ Γ') : HasTypeD Γ' t B := by
  classical
  suffices H : ∀ S : Finset (Var n), ∀ Γ' : TCtx R k n ρ, CtxLe Γ Γ' →
      (∀ j, j ∉ S → Γ'.vars.get j = Γ.vars.get j) → HasTypeD Γ' t B from
    H Finset.univ Γ' hle (fun j hj => absurd (Finset.mem_univ j) hj)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Γ' hle hS
    have e : Γ' = Γ := TCtx.ext hle.refs (Ctx.ext fun j => hS j (Finset.notMem_empty j))
    rw [e]; exact h
  | insert j S hj ih =>
    intro Γ' hle hS
    have h₁ : HasTypeD (Γ'.setVar j (Γ.vars.get j)) t B := by
      refine ih _ ⟨hle.refs, Ctx.forall₂_iff.2 fun i => ?_⟩ (fun i hi => ?_)
      · simp only [TCtx.setVar_vars, Ctx.get_set]
        split_ifs with hij
        · subst hij; exact .refl _
        · exact hle.vars.get i
      · simp only [TCtx.setVar_vars, Ctx.get_set]
        split_ifs with hij
        · subst hij; rfl
        · exact hS i (by simp [hij, hi])
    rcases (hle.vars.get j).cases' with e | ⟨A, r, s, e₁, e₂, hrs⟩
    · rw [← e, TCtx.setVar_get] at h₁; exact h₁
    · rw [e₁] at h₁
      have := HasTypeD.approx (i := j) (A := A) (r := r) (Ctx.Lookup.of_eq (by simp)) hrs h₁
      rw [TCtx.setVar_setVar, ← e₂, TCtx.setVar_get] at this
      exact this

/-! ## Dereliction is admissible -/

theorem der {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} (h : HasTypeD Γ t B) :
    ∀ {i : Var n} {A : Ty R k}, Γ.vars.get i = some (.lin A) →
      HasTypeD (Γ.setVar i (some (.grd A 1))) t B := by
  induction h with
  | @var k n ρ Γ j C hj =>
    intro i A hi
    have hji : i = j := hj.eq_of_not (by rw [hi]; exact not_zeroAssm_lin A)
    subst hji
    rw [hj.get] at hi; cases hi
    exact .varG (hj.set _)
  | @varG k n ρ Γ j C hj =>
    intro i A hi
    have hji : i = j := hj.eq_of_not (by rw [hi]; exact not_zeroAssm_lin A)
    subst hji
    rw [hj.get] at hi; cases hi
  | abs _ ih =>
    intro i A hi
    exact .abs (ih (i := .succ i) hi)
  | app hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .app h (ih₁ h1) ‹_›
    · exact .app h ‹_› (ih₂ h2)
  | tensorI hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .tensorI h (ih₁ h1) ‹_›
    · exact .tensorI h ‹_› (ih₂ h2)
  | unitE hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .unitE h (ih₁ h1) ‹_›
    · exact .unitE h ‹_› (ih₂ h2)
  | withBorrow hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .withBorrow h (ih₁ h1) ‹_›
    · exact .withBorrow h ‹_› (ih₂ h2)
  | join hfg hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .join hfg h (ih₁ h1) ‹_›
    · exact .join hfg h ‹_› (ih₂ h2)
  | elim hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .elim h (ih₁ h1) ‹_›
    · exact .elim h ‹_› (ih₂ (i := .succ i) h2)
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .tensorE h (ih₁ h1) ‹_›
    · exact .tensorE h ‹_› (ih₂ (i := .succ (.succ i)) h2)
  | unpack hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .unpack h (ih₁ h1) ‹_›
    · have := ih₂ (i := .succ i) (A := A.shift) (by
        simp [TCtx.shiftNames, h2, Ty.shift])
      refine .unpack h ‹_› ?_
      rw [TCtx.shiftNames, TCtx.renNames_setVar]
      exact this
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .clone ι h (ih₁ h1) hr hc hA ‹_›
    · exact .clone ι h ‹_› hr hc hA (ih₂ (i := .succ i) h2)
  | pr hs _ _ _ =>
    intro i A hi
    have := hs.vars.get i; rw [hi] at this; exact this.not_lin_right.elim
  | @approx k n ρ Γ t B j C r s hj hrs _ ih =>
    intro i A hi
    by_cases hji : j = i
    · subst hji; simp at hi
    · rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ (Ne.symm hji)] at hi
      have := HasTypeD.approx (i := j)
        (Ctx.Lookup.of_eq (by rw [TCtx.setVar_vars, Ctx.get_set_ne _ _ hji]; exact hj.eq)) hrs
        (ih hi)
      rwa [TCtx.setVar_comm _ (Ne.symm hji)] at this
  | pack ι _ ih => intro i A hi; exact .pack ι (ih hi)
  | share r _ ih => intro i A hi; exact .share r (ih hi)
  | split _ ih => intro i A hi; exact .split (ih hi)
  | push _ ih => intro i A hi; exact .push (ih hi)
  | pull _ ih => intro i A hi; exact .pull (ih hi)
  | unborrow _ ih => intro i A hi; exact .unborrow (ih hi)
  | unitI hz | nat _ hz | float _ hz | prim hz _ | nec _ hz _ _ | ref hz _ =>
    intro i A hi
    have := hz.get i; rw [hi] at this; exact this.elim

end HasTypeD

/-! ## Equivalence with `HasType` -/

theorem HasType.toD {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasType Γ t B) : HasTypeD Γ t B := by
  induction h with
  | der hi _ ih => exact ih.der hi.eq
  | var hi => exact .var hi
  | abs _ ih => exact .abs ih
  | app hadd _ _ ih₁ ih₂ => exact .app hadd ih₁ ih₂
  | pr hs _ hna ih => exact .pr hs ih hna
  | elim hadd _ _ ih₁ ih₂ => exact .elim hadd ih₁ ih₂
  | approx hi hrs _ ih => exact .approx hi hrs ih
  | tensorI hadd _ _ ih₁ ih₂ => exact .tensorI hadd ih₁ ih₂
  | tensorE hadd _ _ ih₁ ih₂ => exact .tensorE hadd ih₁ ih₂
  | unitI hz => exact .unitI hz
  | unitE hadd _ _ ih₁ ih₂ => exact .unitE hadd ih₁ ih₂
  | pack ι _ ih => exact .pack ι ih
  | unpack hadd _ _ ih₁ ih₂ => exact .unpack hadd ih₁ ih₂
  | share r _ ih => exact .share r ih
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ => exact .clone ι hadd ih₁ hr hc hA ih₂
  | withBorrow hadd _ _ ih₁ ih₂ => exact .withBorrow hadd ih₁ ih₂
  | split _ ih => exact .split ih
  | join hfg hadd _ _ ih₁ ih₂ => exact .join hfg hadd ih₁ ih₂
  | push _ ih => exact .push ih
  | pull _ ih => exact .pull ih
  | nat m hz => exact .nat m hz
  | float x hz => exact .float x hz
  | prim hz hp => exact .prim hz hp
  | nec p hz _ ih => exact .nec p hz ih
  | unborrow _ ih => exact .unborrow ih
  | ref hz ha => exact .ref hz ha

theorem HasTypeD.toHasType {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasTypeD Γ t B) : HasType Γ t B := by
  induction h with
  | varG hi => exact .var' hi
  | var hi => exact .var hi
  | abs _ ih => exact .abs ih
  | app hadd _ _ ih₁ ih₂ => exact .app hadd ih₁ ih₂
  | pr hs _ hna ih => exact .pr hs ih hna
  | elim hadd _ _ ih₁ ih₂ => exact .elim hadd ih₁ ih₂
  | approx hi hrs _ ih => exact .approx hi hrs ih
  | tensorI hadd _ _ ih₁ ih₂ => exact .tensorI hadd ih₁ ih₂
  | tensorE hadd _ _ ih₁ ih₂ => exact .tensorE hadd ih₁ ih₂
  | unitI hz => exact .unitI hz
  | unitE hadd _ _ ih₁ ih₂ => exact .unitE hadd ih₁ ih₂
  | pack ι _ ih => exact .pack ι ih
  | unpack hadd _ _ ih₁ ih₂ => exact .unpack hadd ih₁ ih₂
  | share r _ ih => exact .share r ih
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ => exact .clone ι hadd ih₁ hr hc hA ih₂
  | withBorrow hadd _ _ ih₁ ih₂ => exact .withBorrow hadd ih₁ ih₂
  | split _ ih => exact .split ih
  | join hfg hadd _ _ ih₁ ih₂ => exact .join hfg hadd ih₁ ih₂
  | push _ ih => exact .push ih
  | pull _ ih => exact .pull ih
  | nat m hz => exact .nat m hz
  | float x hz => exact .float x hz
  | prim hz hp => exact .prim hz hp
  | nec p hz _ ih => exact .nec p hz ih
  | unborrow _ ih => exact .unborrow ih
  | ref hz ha => exact .ref hz ha

/-- The dereliction-free judgment is equivalent to the paper's. -/
theorem hasType_iff_hasTypeD {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} :
    HasType Γ t B ↔ HasTypeD Γ t B := ⟨HasType.toD, HasTypeD.toHasType⟩

/-- Approximation of whole contexts, for the paper's judgment. -/
theorem HasType.approxCtx {k n ρ : ℕ} {Γ Γ' : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k}
    (h : HasType Γ t B) (hle : CtxLe Γ Γ') : HasType Γ' t B :=
  (h.toD.approxCtx hle).toHasType

end FOFU
