module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas
public import Mathlib.Data.Fintype.Basic

/-!
# The dereliction-free typing judgment `HasTypeD`

The rules of `HasTypeD`, and lemmas about updating single entries of a context
(`TCtx.setVar`) used in the proofs of `TypingD/Equiv.lean`.  See
`RequestProject/FOFU/Sec3_CoreCalculus/TypingD.lean` for an overview.
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

end FOFU
