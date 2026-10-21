module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas
public import Mathlib.Data.Finset.Insert

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
inductive HasTypeD : {k n : ℕ} → Ctx R k n → Term R n → Ty R k → Prop where
  /-- `0 · Γ, x : A ⊢ x : A` -/
  | var {k n : ℕ} {Γ : Ctx R k n} {i : Fin n} {A : Ty R k}
      (hi : Γ.vars i = some (.lin A)) (hz : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
      HasTypeD Γ (.var i) A
  /-- `0 · Γ, x : [A]_1 ⊢ x : A` (the derived rule `var'`) -/
  | varG {k n : ℕ} {Γ : Ctx R k n} {i : Fin n} {A : Ty R k}
      (hi : Γ.vars i = some (.grd A 1)) (hz : ∀ j, j ≠ i → ZeroAssm (Γ.vars j)) :
      HasTypeD Γ (.var i) A
  /-- `Γ, x : A ⊢ t : B  ⟹  Γ ⊢ λx. t : A ⊸ B` -/
  | abs {k n : ℕ} {Γ : Ctx R k n} {t : Term R (n + 1)} {A B : Ty R k} :
      HasTypeD (Γ.cons (some (.lin A))) t B → HasTypeD Γ (.lam t) (lolli A B)
  /-- `Γ₁ ⊢ t₁ : A ⊸ B,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ t₁ t₂ : B` -/
  | app {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (lolli A B) → HasTypeD Γ₂ t₂ A → HasTypeD Γ (.app t₁ t₂) B
  /-- `[Γ] ⊢ t : A,  ¬ resourceAllocator(t)  ⟹  r · Γ ⊢ [t]_r : □_r A` -/
  | pr {k n : ℕ} {Γ₀ Γ : Ctx R k n} {t : Term R n} {A : Ty R k} {r : R} :
      CtxScale r Γ₀ Γ → HasTypeD Γ₀ t A → ¬ t.Allocates → HasTypeD Γ (.box r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : [A]_r ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ let [x] = t₁ in t₂ : B` -/
  | elim {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 1)}
      {A B : Ty R k} {r : R} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (box r A) → HasTypeD (Γ₂.cons (some (.grd A r))) t₂ B →
      HasTypeD Γ (.letBox t₁ t₂) B
  /-- approximation: `Γ, x : [A]_r ⊢ t : B,  r ⊑ s  ⟹  Γ, x : [A]_s ⊢ t : B` -/
  | approx {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {B : Ty R k} {i : Fin n} {A : Ty R k}
      {r s : R} :
      Γ.vars i = some (.grd A r) → r ≤ s → HasTypeD Γ t B →
      HasTypeD (Γ.update i (some (.grd A s))) t B
  /-- `Γ₁ ⊢ t₁ : A,  Γ₂ ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ (t₁, t₂) : A ⊗ B` -/
  | tensorI {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ A → HasTypeD Γ₂ t₂ B → HasTypeD Γ (.pair t₁ t₂) (tensor A B)
  /-- `Γ₁ ⊢ t₁ : A ⊗ B,  Γ₂, x : A, y : B ⊢ t₂ : C  ⟹  Γ₁ + Γ₂ ⊢ let (x, y) = t₁ in t₂ : C` -/
  | tensorE {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 2)}
      {A B C : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (tensor A B) →
      HasTypeD ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      HasTypeD Γ (.letPair t₁ t₂) C
  /-- `0 · Γ ⊢ () : unit` -/
  | unitI {k n : ℕ} {Γ : Ctx R k n} : Γ.IsZero → HasTypeD Γ .unit unit
  /-- `Γ₁ ⊢ t₁ : unit,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ let () = t₁ in t₂ : A` -/
  | unitE {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ unit → HasTypeD Γ₂ t₂ A → HasTypeD Γ (.letUnit t₁ t₂) A
  /-- `Γ ⊢ t : A [ι / id]  ⟹  Γ ⊢ pack ⟨ι, t⟩ : ∃ id. A` -/
  | pack {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R (k + 1)} (ι : Ident k) :
      HasTypeD Γ t (A.inst ι) → HasTypeD Γ (.pack t) (ex A)
  /-- `Γ₁ ⊢ t₁ : ∃ id. A,  Γ₂, id, x : A ⊢ t₂ : B,  id ∉ fv(B)
      ⟹  Γ₁ + Γ₂ ⊢ unpack ⟨id, x⟩ = t₁ in t₂ : B` -/
  | unpack {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 1)}
      {A : Ty R (k + 1)} {B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (ex A) →
      HasTypeD (Γ₂.shiftNames.cons (some (.lin A))) t₂ B.shift →
      HasTypeD Γ (.unpack t₁ t₂) B
  /-- `Γ ⊢ t : *A  ⟹  Γ ⊢ share t : □_r A` (§4) -/
  | share {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} (r : R) :
      HasTypeD Γ t (star A) → HasTypeD Γ (.share r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : ∃ id. *A' ⊢ t₂ : B,  1 ⊑ r,  cloneable(A)
      ⟹  Γ₁ + Γ₂ ⊢ clone t₁ as x in t₂ : B` (§4), where `A'` abstracts an identifier
      of `A` -/
  | clone {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ : Term R n} {t₂ : Term R (n + 1)}
      {A : Ty R k} {A' : Ty R (k + 1)} {B : Ty R k} {r : R} (ι : Ident k) :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (box r A) → 1 ≤ r → Cloneable A → A'.inst ι = A →
      HasTypeD (Γ₂.cons (some (.lin (ex (star A'))))) t₂ B →
      HasTypeD Γ (.clone t₁ t₂) B
  /-- `Γ₁ ⊢ t₁ : &₁ A ⊸ &₁ B,  Γ₂ ⊢ t₂ : *A  ⟹  Γ₁ + Γ₂ ⊢ withBorrow t₁ t₂ : *B` (§5) -/
  | withBorrow {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (lolli (borrow Perm.one A) (borrow Perm.one B)) →
      HasTypeD Γ₂ t₂ (star A) → HasTypeD Γ (.withBorrow t₁ t₂) (star B)
  /-- `Γ ⊢ t : &_p A  ⟹  Γ ⊢ split t : &_(p/2) A ⊗ &_(p/2) A` (§5) -/
  | split {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} {f : Frac} :
      HasTypeD Γ t (borrow (.frac f) A) →
      HasTypeD Γ (.split t) (tensor (borrow (.frac f.half) A) (borrow (.frac f.half) A))
  /-- `Γ₁ ⊢ t₁ : &_p A,  Γ₂ ⊢ t₂ : &_q A  ⟹  Γ₁ + Γ₂ ⊢ join t₁ t₂ : &_(p+q) A` (§5) -/
  | join {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A : Ty R k} {f g : Frac}
      (h : f.1 + g.1 ≤ 1) :
      CtxAdd Γ₁ Γ₂ Γ → HasTypeD Γ₁ t₁ (borrow (.frac f) A) → HasTypeD Γ₂ t₂ (borrow (.frac g) A) →
      HasTypeD Γ (.join t₁ t₂) (borrow (.frac (f.add g h)) A)
  /-- `Γ ⊢ t : &_p (A ⊗ B)  ⟹  Γ ⊢ push t : &_p A ⊗ &_p B` (§5.2) -/
  | push {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A B : Ty R k} {p : Perm} :
      HasTypeD Γ t (borrow p (tensor A B)) →
      HasTypeD Γ (.push t) (tensor (borrow p A) (borrow p B))
  /-- `Γ ⊢ t : &_p A ⊗ &_p B  ⟹  Γ ⊢ pull t : &_p (A ⊗ B)` (§5.2) -/
  | pull {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A B : Ty R k} {p : Perm} :
      HasTypeD Γ t (tensor (borrow p A) (borrow p B)) →
      HasTypeD Γ (.pull t) (borrow p (tensor A B))
  /-- natural number literals: `0 · Γ ⊢ n : ℕ` -/
  | nat {k n : ℕ} {Γ : Ctx R k n} (m : ℕ) : Γ.IsZero → HasTypeD Γ (.nat m) nat
  /-- float literals: `0 · Γ ⊢ x : 𝔽` -/
  | float {k n : ℕ} {Γ : Ctx R k n} (x : Float) : Γ.IsZero → HasTypeD Γ (.float x) float
  /-- the resource primitives: `0 · Γ ⊢ p : A` for the types `A` of `PrimTy` -/
  | prim {k n : ℕ} {Γ : Ctx R k n} {p : Prim} {A : Ty R k} :
      Γ.IsZero → PrimTy p A → HasTypeD Γ (.prim p) A
  /-- `γ ⊢ t : A  ⟹  0 · Γ, γ ⊢ *t : &_p A` (§6.1) -/
  | nec {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} (p : Perm) :
      Γ.IsZero → HasTypeD Γ.refsOnly t A → HasTypeD Γ (.star t) (borrow p A)
  /-- `Γ ⊢ t : &₁ A  ⟹  Γ ⊢ unborrow t : *A` (§6.1) -/
  | unborrow {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {A : Ty R k} :
      HasTypeD Γ t (borrow Perm.one A) → HasTypeD Γ (.unborrow t) (star A)
  /-- `0 · Γ, ref : Res_id A ⊢ ref : Res_id A` (§6.1) -/
  | ref {k n : ℕ} {Γ : Ctx R k n} {a : ℕ} {T : RefTy R k} :
      Γ.IsZero → Γ.refs a = some T → HasTypeD Γ (.ref a) T.toTy


/-! ## Context lemmas about `update` -/

namespace Ctx

section
omit [Grades.PreorderedSemiring R]

variable {k k' n : ℕ}

lemma cons_update_succ (Γ : Ctx R k n) (a b : Option (Assm R k)) (i : Fin n) :
    (Γ.cons a).update i.succ b = (Γ.update i b).cons a := by
  ext1
  · funext j
    cases j using Fin.cases with
    | zero => simp [Ctx.update, Ctx.cons, (Fin.succ_ne_zero i).symm]
    | succ j =>
      by_cases h : j = i
      · subst h; simp [Ctx.update, Ctx.cons]
      · simp [Ctx.update, Ctx.cons]
  · rfl

lemma substNames_update (σ : Fin k → Ident k') (Γ : Ctx R k n) (i : Fin n)
    (a : Option (Assm R k)) :
    (Γ.update i a).substNames σ = (Γ.substNames σ).update i (a.map (Assm.subst σ)) := by
  ext1
  · funext j
    by_cases h : j = i
    · subst h; simp [Ctx.update, Ctx.substNames]
    · simp [Ctx.update, Ctx.substNames, Function.update_of_ne h]
  · rfl

lemma update_comm (Γ : Ctx R k n) {i j : Fin n} (h : i ≠ j) (a b : Option (Assm R k)) :
    (Γ.update i a).update j b = (Γ.update j b).update i a := by
  ext1
  · exact Function.update_comm h a b Γ.vars
  · rfl

lemma update_vars_self (Γ : Ctx R k n) (i : Fin n) (a : Option (Assm R k)) :
    (Γ.update i a).vars i = a := by simp [Ctx.update]

lemma update_vars_ne (Γ : Ctx R k n) {i j : Fin n} (h : j ≠ i) (a : Option (Assm R k)) :
    (Γ.update i a).vars j = Γ.vars j := by simp [Ctx.update, Function.update_of_ne h]

lemma update_eq_self (Γ : Ctx R k n) (i : Fin n) : Γ.update i (Γ.vars i) = Γ := by
  ext1
  · exact Function.update_eq_self i Γ.vars
  · rfl

lemma update_update (Γ : Ctx R k n) (i : Fin n) (a b : Option (Assm R k)) :
    (Γ.update i a).update i b = Γ.update i b := by
  ext1
  · simp [Ctx.update]
  · rfl

end

end Ctx

lemma CtxAdd.update {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) (i : Fin n)
    {a b c : Option (Assm R k)} (habc : AssmAdd a b c) :
    CtxAdd (Γ₁.update i a) (Γ₂.update i b) (Γ.update i c) := by
  refine ⟨fun j => ?_, h.refs⟩
  by_cases hj : j = i
  · subst hj; simpa [Ctx.update] using habc
  · simpa [Ctx.update, Function.update_of_ne hj] using h.vars j

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
lemma CtxAdd.lin_split {k n : ℕ} {Γ₁ Γ₂ Γ : Ctx R k n} (h : CtxAdd Γ₁ Γ₂ Γ) {i : Fin n}
    {A : Ty R k} (hi : Γ.vars i = some (.lin A)) (g : Option (Assm R k)) :
    (Γ₁.vars i = some (.lin A) ∧ CtxAdd (Γ₁.update i g) Γ₂ (Γ.update i g)) ∨
    (Γ₂.vars i = some (.lin A) ∧ CtxAdd Γ₁ (Γ₂.update i g) (Γ.update i g)) := by
  have := h.vars i
  rw [hi] at this
  rcases this.lin_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    have := h.update i (a := g) (AssmAdd.noneRight' g)
    rwa [← h2, Ctx.update_eq_self] at this
  · refine Or.inr ⟨h2, ?_⟩
    have := h.update i (b := g) (AssmAdd.noneLeft g)
    rwa [← h1, Ctx.update_eq_self] at this

/-! ## Approximation of whole contexts -/

namespace HasTypeD

theorem approxCtx {k n : ℕ} {Γ Γ' : Ctx R k n} {t : Term R n} {B : Ty R k}
    (h : HasTypeD Γ t B) (hle : CtxLe Γ Γ') : HasTypeD Γ' t B := by
  classical
  suffices H : ∀ S : Finset (Fin n), ∀ Γ' : Ctx R k n, CtxLe Γ Γ' →
      (∀ j, j ∉ S → Γ'.vars j = Γ.vars j) → HasTypeD Γ' t B from
    H Finset.univ Γ' hle (fun j hj => absurd (Finset.mem_univ j) hj)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Γ' hle hS
    have e : Γ' = Γ := by
      ext1
      · funext j; exact hS j (Finset.notMem_empty j)
      · exact hle.refs
    rw [e]; exact h
  | insert j S hj ih =>
    intro Γ' hle hS
    have h₁ : HasTypeD (Γ'.update j (Γ.vars j)) t B := by
      refine ih _ ⟨fun i => ?_, hle.refs⟩ (fun i hi => ?_)
      · by_cases hij : i = j
        · subst hij; rw [Ctx.update_vars_self]; exact .refl _
        · rw [Ctx.update_vars_ne _ hij]; exact hle.vars i
      · by_cases hij : i = j
        · subst hij; rw [Ctx.update_vars_self]
        · rw [Ctx.update_vars_ne _ hij]
          exact hS i (by simp [hij, hi])
    rcases (hle.vars j).cases' with e | ⟨A, r, s, e₁, e₂, hrs⟩
    · rw [← e, Ctx.update_eq_self] at h₁; exact h₁
    · rw [e₁] at h₁
      have := HasTypeD.approx (i := j) (Ctx.update_vars_self _ _ _) hrs h₁
      rw [Ctx.update_update, ← e₂, Ctx.update_eq_self] at this
      exact this

/-! ## Dereliction is admissible -/

theorem der {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {B : Ty R k} (h : HasTypeD Γ t B) :
    ∀ {i : Fin n} {A : Ty R k}, Γ.vars i = some (.lin A) →
      HasTypeD (Γ.update i (some (.grd A 1))) t B := by
  induction h with
  | @var k n Γ j C hj hz =>
    intro i A hi
    by_cases hji : j = i
    · subst hji
      rw [hi] at hj; cases hj
      exact .varG (Ctx.update_vars_self _ _ _)
        (fun l hl => by rw [Ctx.update_vars_ne _ hl]; exact hz l hl)
    · have := hz i (Ne.symm hji); rw [hi] at this; exact this.elim
  | @varG k n Γ j C hj hz =>
    intro i A hi
    by_cases hji : j = i
    · subst hji; rw [hi] at hj; cases hj
    · have := hz i (Ne.symm hji); rw [hi] at this; exact this.elim
  | abs _ ih =>
    intro i A hi
    have := ih (i := i.succ) hi
    rw [Ctx.cons_update_succ] at this
    exact .abs this
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
    · have := ih₂ (i := i.succ) h2
      rw [Ctx.cons_update_succ] at this
      exact .elim h ‹_› this
  | tensorE hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .tensorE h (ih₁ h1) ‹_›
    · have := ih₂ (i := i.succ.succ) h2
      rw [Ctx.cons_update_succ, Ctx.cons_update_succ] at this
      exact .tensorE h ‹_› this
  | unpack hadd _ _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .unpack h (ih₁ h1) ‹_›
    · have := ih₂ (i := i.succ) (A := A.shift) (by simp [Ctx.shiftNames, Ctx.substNames, h2,
        Assm.subst, Ty.shift])
      rw [Ctx.cons_update_succ] at this
      refine .unpack h ‹_› ?_
      rw [Ctx.shiftNames, Ctx.substNames_update]
      exact this
  | clone ι hadd _ hr hc hA _ ih₁ ih₂ =>
    intro i A hi
    rcases hadd.lin_split hi (some (.grd A 1)) with ⟨h1, h⟩ | ⟨h2, h⟩
    · exact .clone ι h (ih₁ h1) hr hc hA ‹_›
    · have := ih₂ (i := i.succ) h2
      rw [Ctx.cons_update_succ] at this
      exact .clone ι h ‹_› hr hc hA this
  | pr hs _ _ _ =>
    intro i A hi
    have := hs.vars i; rw [hi] at this; exact this.not_lin_right.elim
  | @approx k n Γ t B j C r s hj hrs _ ih =>
    intro i A hi
    by_cases hji : j = i
    · subst hji; rw [Ctx.update_vars_self] at hi; cases hi
    · rw [Ctx.update_vars_ne _ (Ne.symm hji)] at hi
      have := HasTypeD.approx (i := j) (by rw [Ctx.update_vars_ne _ hji]; exact hj) hrs (ih hi)
      rwa [Ctx.update_comm _ (Ne.symm hji)] at this
  | pack ι _ ih => intro i A hi; exact .pack ι (ih hi)
  | share r _ ih => intro i A hi; exact .share r (ih hi)
  | split _ ih => intro i A hi; exact .split (ih hi)
  | push _ ih => intro i A hi; exact .push (ih hi)
  | pull _ ih => intro i A hi; exact .pull (ih hi)
  | unborrow _ ih => intro i A hi; exact .unborrow (ih hi)
  | unitI hz | nat _ hz | float _ hz | prim hz _ | nec _ hz _ _ | ref hz _ =>
    intro i A hi
    have := hz i; rw [hi] at this; exact this.elim

end HasTypeD

/-! ## Equivalence with `HasType` -/

theorem HasType.toD {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {B : Ty R k}
    (h : HasType Γ t B) : HasTypeD Γ t B := by
  induction h with
  | der hi _ ih => exact ih.der hi
  | var hi hz => exact .var hi hz
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

theorem HasTypeD.toHasType {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {B : Ty R k}
    (h : HasTypeD Γ t B) : HasType Γ t B := by
  induction h with
  | varG hi hz => exact .var' hi hz
  | var hi hz => exact .var hi hz
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
theorem hasType_iff_hasTypeD {k n : ℕ} {Γ : Ctx R k n} {t : Term R n} {B : Ty R k} :
    HasType Γ t B ↔ HasTypeD Γ t B := ⟨HasType.toD, HasTypeD.toHasType⟩

/-- Approximation of whole contexts, for the paper's judgment. -/
theorem HasType.approxCtx {k n : ℕ} {Γ Γ' : Ctx R k n} {t : Term R n} {B : Ty R k}
    (h : HasType Γ t B) (hle : CtxLe Γ Γ') : HasType Γ' t B :=
  (h.toD.approxCtx hle).toHasType

end FOFU
