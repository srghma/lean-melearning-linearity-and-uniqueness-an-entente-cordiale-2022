module
public import RequestProject.FOFU.Sec3_CoreCalculus.Context
public import RequestProject.FOFU.Sec5_Fractional.Resources

/-!
# The typing judgment `Γ ⊢ t : A` (Sections 3–5 and §6.1)

`HasType Γ t A` collects the typing rules of the whole paper, in the order the paper
introduces them:

* §3 (core calculus): `var`, `abs`, `app`, `pr`, `elim`, `der`, `approx`, `tensorI`,
  `tensorE`, `unitI`, `unitE`, `pack`, `unpack`;
* §4 (uniqueness): `share`, `clone`;
* §5 (borrowing): `withBorrow`, `split`, `join`, `push`, `pull`, the literals and the
  resource primitives (`prim`, see `PrimTy`);
* §6.1 (runtime terms): `nec`, `unborrow`, `ref`.

## How the rules are encoded

* `0 · Γ, x : A` (rule `var`) is the structural judgment
  `Γ.vars.Pick ZeroAssm i (some (.lin A))`: the variable `i` is linear and every other
  variable is absent or graded by `0` (references are arbitrary, since `0 · _` keeps them).
  There is no side condition quantifying over the other variables.
* Premises `x : a ∈ Γ` and `ref : T ∈ Γ` are the inductive lookup judgment `Ctx.Lookup`.
* `der` and `approx` act on any variable (the paper writes the variable last; contexts
  are considered up to exchange).
* `pr` is the rule `[Γ] ⊢ t : A  ⟹  r · Γ ⊢ [t]_r : □_r A` with the side condition
  `¬ resourceAllocator(t)`.  The rule printed in §3 has premise `r · Γ ⊢ t` and
  conclusion `Γ ⊢ [t]`; we follow the paper's own restatement in §6.1 ("typing this
  grade-annotated version produces `r · Γ ⊢ [t]_r : □_r A`") and its explanation that
  the dependencies of `t` are scaled by `r`.
* `approx` turns `x : [A]_r` into `x : [A]_s` when `r ⊑ s`.  The printed side condition
  is `s ⊑ r`; with the order used everywhere else in the paper (`1 ⊑ r` in `Clone`,
  `s + r' ⊑ r` in the reduction of variables, and the remark that `≤` on ℕ gives
  "an upper bound on a term's usage") this direction would let a used variable be
  graded `0`, so we use the direction of Granule's original rule.
* `pack`/`unpack`: identifiers are de Bruijn (see `Syntax.lean`).  `pack` may
  instantiate the bound identifier with any identifier `ι`.  In `unpack` the body is
  typed in `Γ₂, id, x : A`, i.e. `Γ₂.shiftNames.cons (some (.lin A))`, at the shifted result
  type, which encodes `id ∉ fv(B)`.
* `clone`: the printed rule binds `x : *A` and gives the result type `∃ id̅. B`, while
  the reduction rule binds `x` to `pack ⟨id, *θ(v)⟩` and the paper's example
  (`exampleClone`) unpacks `x`.  We follow the semantics and the example: `x` has type
  `∃ id. *A'` where `A'` abstracts an identifier of `A` (`A'.inst ι = A`), and the
  result type is `B`.
* `withBorrow`: the printed rule types the *first* argument as `*A` and the second as
  the function, but the reduction rule (`withBorrow (λx. t) (*v)`), the equations of
  §5.1 and all examples (`withBorrow (\b -> ...) persimmon`) pass the function first.
  We follow the latter.
* `split`/`join` are only defined on fractional permissions; `join` requires the sum of
  the permissions to be at most `1` so that it is again a permission.
* `nec`: `γ ⊢ t : A  ⟹  0 · Γ, γ ⊢ *t : &_p A`, where the runtime context `γ` consists
  of the references of the conclusion (`TCtx.refsOnly`).
* Natural number and float literals are typed in any context `0 · Γ` (the paper uses
  them but gives no rule).
-/

@[expose] public section

namespace FOFU

open Ty

variable {R : Type} [Grades.PreorderedSemiring R]

/-- The typing judgment `Γ ⊢ t : A`. -/
inductive HasType : {k n ρ : ℕ} → TCtx R k n ρ → Term R n ρ → Ty R k → Prop where
  /-- `0 · Γ, x : A ⊢ x : A` -/
  | var {k n ρ : ℕ} {Γ : TCtx R k n ρ} {i : Var n} {A : Ty R k} :
      Γ.vars.Pick ZeroAssm i (some (.lin A)) → HasType Γ (.var i) A
  /-- `Γ, x : A ⊢ t : B  ⟹  Γ ⊢ λx. t : A ⊸ B` -/
  | abs {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R (n + 1) ρ} {A B : Ty R k} :
      HasType (Γ.cons (some (.lin A))) t B → HasType Γ (.lam t) (lolli A B)
  /-- `Γ₁ ⊢ t₁ : A ⊸ B,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ t₁ t₂ : B` -/
  | app {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (lolli A B) → HasType Γ₂ t₂ A → HasType Γ (.app t₁ t₂) B
  /-- `[Γ] ⊢ t : A,  ¬ resourceAllocator(t)  ⟹  r · Γ ⊢ [t]_r : □_r A` -/
  | pr {k n ρ : ℕ} {Γ₀ Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} {r : R} :
      CtxScale r Γ₀ Γ → HasType Γ₀ t A → ¬ t.Allocates → HasType Γ (.box r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : [A]_r ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ let [x] = t₁ in t₂ : B` -/
  | elim {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A B : Ty R k} {r : R} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (box r A) → HasType (Γ₂.cons (some (.grd A r))) t₂ B →
      HasType Γ (.letBox t₁ t₂) B
  /-- dereliction: `Γ, x : A ⊢ t : B  ⟹  Γ, x : [A]_1 ⊢ t : B` -/
  | der {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} {i : Var n} {A : Ty R k} :
      Γ.vars.Lookup i (some (.lin A)) → HasType Γ t B → HasType (Γ.setVar i (some (.grd A 1))) t B
  /-- approximation: `Γ, x : [A]_r ⊢ t : B,  r ⊑ s  ⟹  Γ, x : [A]_s ⊢ t : B` -/
  | approx {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {B : Ty R k} {i : Var n} {A : Ty R k}
      {r s : R} :
      Γ.vars.Lookup i (some (.grd A r)) → r ≤ s → HasType Γ t B →
      HasType (Γ.setVar i (some (.grd A s))) t B
  /-- `Γ₁ ⊢ t₁ : A,  Γ₂ ⊢ t₂ : B  ⟹  Γ₁ + Γ₂ ⊢ (t₁, t₂) : A ⊗ B` -/
  | tensorI {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ A → HasType Γ₂ t₂ B → HasType Γ (.pair t₁ t₂) (tensor A B)
  /-- `Γ₁ ⊢ t₁ : A ⊗ B,  Γ₂, x : A, y : B ⊢ t₂ : C  ⟹  Γ₁ + Γ₂ ⊢ let (x, y) = t₁ in t₂ : C` -/
  | tensorE {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 2) ρ}
      {A B C : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (tensor A B) →
      HasType ((Γ₂.cons (some (.lin A))).cons (some (.lin B))) t₂ C →
      HasType Γ (.letPair t₁ t₂) C
  /-- `0 · Γ ⊢ () : unit` -/
  | unitI {k n ρ : ℕ} {Γ : TCtx R k n ρ} : Γ.IsZero → HasType Γ .unit unit
  /-- `Γ₁ ⊢ t₁ : unit,  Γ₂ ⊢ t₂ : A  ⟹  Γ₁ + Γ₂ ⊢ let () = t₁ in t₂ : A` -/
  | unitE {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ unit → HasType Γ₂ t₂ A → HasType Γ (.letUnit t₁ t₂) A
  /-- `Γ ⊢ t : A [ι / id]  ⟹  Γ ⊢ pack ⟨ι, t⟩ : ∃ id. A` -/
  | pack {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R (k + 1)} (ι : Var k) :
      HasType Γ t (A.inst ι) → HasType Γ (.pack t) (ex A)
  /-- `Γ₁ ⊢ t₁ : ∃ id. A,  Γ₂, id, x : A ⊢ t₂ : B,  id ∉ fv(B)
      ⟹  Γ₁ + Γ₂ ⊢ unpack ⟨id, x⟩ = t₁ in t₂ : B` -/
  | unpack {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A : Ty R (k + 1)} {B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (ex A) →
      HasType (Γ₂.shiftNames.cons (some (.lin A))) t₂ B.shift →
      HasType Γ (.unpack t₁ t₂) B
  /-- `Γ ⊢ t : *A  ⟹  Γ ⊢ share t : □_r A` (§4) -/
  | share {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} (r : R) :
      HasType Γ t (star A) → HasType Γ (.share r t) (box r A)
  /-- `Γ₁ ⊢ t₁ : □_r A,  Γ₂, x : ∃ id. *A' ⊢ t₂ : B,  1 ⊑ r,  cloneable(A)
      ⟹  Γ₁ + Γ₂ ⊢ clone t₁ as x in t₂ : B` (§4), where `A'` abstracts an identifier
      of `A` -/
  | clone {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ : Term R n ρ} {t₂ : Term R (n + 1) ρ}
      {A : Ty R k} {A' : Ty R (k + 1)} {B : Ty R k} {r : R} (ι : Var k) :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (box r A) → 1 ≤ r → A.cloneable = true → A'.inst ι = A →
      HasType (Γ₂.cons (some (.lin (ex (star A'))))) t₂ B →
      HasType Γ (.clone t₁ t₂) B
  /-- `Γ₁ ⊢ t₁ : &₁ A ⊸ &₁ B,  Γ₂ ⊢ t₂ : *A  ⟹  Γ₁ + Γ₂ ⊢ withBorrow t₁ t₂ : *B` (§5) -/
  | withBorrow {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A B : Ty R k} :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (lolli (borrow Perm.one A) (borrow Perm.one B)) →
      HasType Γ₂ t₂ (star A) → HasType Γ (.withBorrow t₁ t₂) (star B)
  /-- `Γ ⊢ t : &_p A  ⟹  Γ ⊢ split t : &_(p/2) A ⊗ &_(p/2) A` (§5) -/
  | split {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} {f : Frac} :
      HasType Γ t (borrow (.frac f) A) →
      HasType Γ (.split t) (tensor (borrow (.frac f.half) A) (borrow (.frac f.half) A))
  /-- `Γ₁ ⊢ t₁ : &_p A,  Γ₂ ⊢ t₂ : &_q A  ⟹  Γ₁ + Γ₂ ⊢ join t₁ t₂ : &_(p+q) A` (§5) -/
  | join {k n ρ : ℕ} {Γ₁ Γ₂ Γ : TCtx R k n ρ} {t₁ t₂ : Term R n ρ} {A : Ty R k} {f g : Frac}
      (h : f.1 + g.1 ≤ 1) :
      CtxAdd Γ₁ Γ₂ Γ → HasType Γ₁ t₁ (borrow (.frac f) A) → HasType Γ₂ t₂ (borrow (.frac g) A) →
      HasType Γ (.join t₁ t₂) (borrow (.frac (f.add g h)) A)
  /-- `Γ ⊢ t : &_p (A ⊗ B)  ⟹  Γ ⊢ push t : &_p A ⊗ &_p B` (§5.2) -/
  | push {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A B : Ty R k} {p : Perm} :
      HasType Γ t (borrow p (tensor A B)) →
      HasType Γ (.push t) (tensor (borrow p A) (borrow p B))
  /-- `Γ ⊢ t : &_p A ⊗ &_p B  ⟹  Γ ⊢ pull t : &_p (A ⊗ B)` (§5.2) -/
  | pull {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A B : Ty R k} {p : Perm} :
      HasType Γ t (tensor (borrow p A) (borrow p B)) →
      HasType Γ (.pull t) (borrow p (tensor A B))
  /-- natural number literals: `0 · Γ ⊢ n : ℕ` -/
  | nat {k n ρ : ℕ} {Γ : TCtx R k n ρ} (m : ℕ) : Γ.IsZero → HasType Γ (.nat m) nat
  /-- float literals: `0 · Γ ⊢ x : 𝔽` -/
  | float {k n ρ : ℕ} {Γ : TCtx R k n ρ} (x : FloatLit) : Γ.IsZero → HasType Γ (.float x) float
  /-- the resource primitives: `0 · Γ ⊢ p : A` for the types `A` of `PrimTy` -/
  | prim {k n ρ : ℕ} {Γ : TCtx R k n ρ} {p : Prim} {A : Ty R k} :
      Γ.IsZero → PrimTy p A → HasType Γ (.prim p) A
  /-- `γ ⊢ t : A  ⟹  0 · Γ, γ ⊢ *t : &_p A` (§6.1) -/
  | nec {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} (p : Perm) :
      Γ.IsZero → HasType Γ.refsOnly t A → HasType Γ (.star t) (borrow p A)
  /-- `Γ ⊢ t : &₁ A  ⟹  Γ ⊢ unborrow t : *A` (§6.1) -/
  | unborrow {k n ρ : ℕ} {Γ : TCtx R k n ρ} {t : Term R n ρ} {A : Ty R k} :
      HasType Γ t (borrow Perm.one A) → HasType Γ (.unborrow t) (star A)
  /-- `0 · Γ, ref : Res_id A ⊢ ref : Res_id A` (§6.1) -/
  | ref {k n ρ : ℕ} {Γ : TCtx R k n ρ} {a : Var ρ} {T : RefTy R k} :
      Γ.IsZero → Γ.refs.Lookup a (some T) → HasType Γ (.ref a) T.toTy

end FOFU
