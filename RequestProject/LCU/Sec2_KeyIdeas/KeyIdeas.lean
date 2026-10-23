module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping

/-!
# The examples of Section 2 (Key Ideas) in the LCU calculus

Section 2 of the paper explains the relationship between linearity and uniqueness by
example.  Here we check the corresponding typing claims in the LCU calculus:

* the "impossible" programs `λc. (eat c, have c)` (Granule, linear `Cake`) and
  `λc. (drink c, keep c)` (Clean, unique `*Coffee`) are ill-typed: a linear or unique
  argument cannot be used twice (`not_hasType_lam_pair_dup`, `impossible_cake`,
  `impossible_coffee`);
* the "possible" programs are well-typed: `λlots. let! cake = lots in (eat cake, have cake)`
  of type `!Cake ⊸ Happy ⊗ Cake` (`possible_cake`), and the Granule program
  `sip fresh = let !coffee = &fresh in (keep coffee, drink coffee)` of type
  `*Coffee ⊸ Coffee ⊗ Awake` (`sip_hasType`);
* one can map out of the non-linear modality (dereliction, `!A ⊸ A`) and into the
  non-unique modality (borrowing, `*A ⊸ !A`), so in particular from unique to linear
  (`*A ⊸ A`);
* `!` is comonoidal (`!A ⊸ !A ⊗ !A` and `!A ⊸ 1`);
* the primitives `uniqueReturn : *A ⊸ !A` and `uniqueBind : (*A ⊸ !B) ⊸ !A ⊸ !B` of
  Section 4.1, which make `!` a relative monad over unique values, are definable.

The abstract types `Cake`, `Happy`, `Coffee`, `Awake` are arbitrary types, and the
functions `eat`, `have`, `drink`, `keep` are free (non-linear) variables.  All programs
are source programs: they mention no runtime array reference (`ρ = 0`).
-/

@[expose] public section

namespace LCU

open Term

/-! ## Variables have assumptions -/

/-- A variable that occurs free in a well-typed term has an assumption in the context. -/
theorem HasTypeD.ne_none_of_freeIn {n ρ : ℕ} {Γ : TCtx n ρ} {t : Term n ρ} {B : Ty}
    (ht : HasTypeD Γ t B) : ∀ {i : Var n}, FreeIn i t → Γ.vars.get i ≠ none := by
  induction ht with
  | var hi _ => intro i h; cases h; simp [hi.get]
  | abs _ ih =>
    intro i h; cases h with | op h => cases h with
    | head h => exact ih (i := .succ i) h
    | tail h => cases h
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | tensorE _ _ hadd ih₁ ih₂
  | unitE _ _ hadd ih₁ ih₂ | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro i h e
    have hx := hadd.vars.get i; rw [e] at hx
    obtain ⟨e₁, e₂⟩ := hx.eq_none
    cases h with | op h =>
    cases h with
    | head h => exact ih₁ h e₁
    | tail h =>
      cases h with
      | head h => exact ih₂ h e₂
      | tail h => cases h
  | bangI _ _ ih | borrow _ ih =>
    intro i h; cases h with | op h => cases h with
    | head h => exact ih h
    | tail h => cases h
  | nec _ _ ih =>
    intro i h; cases h with | op h => cases h with
    | head h => exact absurd (by simp) (ih h)
    | tail h => cases h
  | unitI _ | natI _ | floatI _ | prim _ | ref _ _ =>
    intro i h; cases h with | op h => cases h

/-! ## Impossible programs: no contraction of linear or unique values -/

/-- A linearly bound variable cannot be used in both components of a pair:
`λx. (t₁, t₂)` is ill-typed whenever `x` occurs in both `t₁` and `t₂`. -/
theorem not_hasType_lam_pair_dup {n ρ : ℕ} {Γ : TCtx n ρ} {t₁ t₂ : Term (n + 1) ρ} {T : Ty}
    (h₁ : FreeIn .zero t₁) (h₂ : FreeIn .zero t₂) : ¬ HasType Γ (lam (pair t₁ t₂)) T := by
  rw [hasType_iff_hasTypeD]
  intro ht
  cases ht with
  | abs ht =>
    cases ht with
    | tensorI g₁ g₂ hadd =>
      have hx := hadd.vars.get .zero
      have n₁ := g₁.ne_none_of_freeIn h₁
      have n₂ := g₂.ne_none_of_freeIn h₂
      have key : ∀ {a b c : Option (Hyp Ty)} {A : Ty}, HypAdd a b c → c = some (.lin A) →
          a ≠ none → b ≠ none → False := by
        intro a b c A h; cases h <;> simp
      exact key hx rfl n₁ n₂

/-- The context `eat : [Cake ⊸ Happy], have : [Cake ⊸ Cake]` (`have` is the variable `0`). -/
def cakeCtx (Cake Happy : Ty) : TCtx 2 0 :=
  ⟨.nil, Ctx.nil ,, some (.nonlin (Cake ⊸ Happy)) ,, some (.nonlin (Cake ⊸ Cake))⟩

/-- An occurrence of the variable `0` as the argument of an application. -/
private lemma freeIn_app_var_zero {n ρ : ℕ} (f : Term (n + 1) ρ) :
    FreeIn .zero (app f (var .zero)) := .op (.tail (.head .var))

/-- `impossible cake = (eat cake, have cake)` is ill-typed (at any type): the linear
`cake` would have to be duplicated. -/
theorem impossible_cake (Cake Happy T : Ty) :
    ¬ HasType (cakeCtx Cake Happy) (lam (pair (app (var 2) (var 0)) (app (var 1) (var 0)))) T :=
  not_hasType_lam_pair_dup (freeIn_app_var_zero _) (freeIn_app_var_zero _)

/-- The context `drink : [*Coffee ⊸ *Awake], keep : [*Coffee ⊸ *Coffee]`. -/
def coffeeCtx (Coffee Awake : Ty) : TCtx 2 0 :=
  ⟨.nil, Ctx.nil ,, some (.nonlin (.star Coffee ⊸ .star Awake)) ,,
    some (.nonlin (.star Coffee ⊸ .star Coffee))⟩

/-- `impossible coffee = (drink coffee, keep coffee)` is ill-typed (at any type, in
particular at `*Coffee ⊸ *Awake ⊗ *Coffee`): the unique `coffee` would have to be
duplicated. -/
theorem impossible_coffee (Coffee Awake T : Ty) :
    ¬ HasType (coffeeCtx Coffee Awake)
      (lam (pair (app (var 2) (var 0)) (app (var 1) (var 0)))) T :=
  not_hasType_lam_pair_dup (freeIn_app_var_zero _) (freeIn_app_var_zero _)

/-! ## Possible programs -/

section Possible

variable (A B : Ty)

private lemma var_nonlin {n ρ : ℕ} {Γ : TCtx n ρ} (hΓ : Γ.AllNonLin) {i : Var n} {h : Hyp Ty}
    (hi : Γ.vars.get i = some h) : HasTypeD Γ (var i) h.ty :=
  .var (Ctx.pick_iff.2 ⟨hi, fun j _ => hΓ.vars.get j⟩) hΓ.refs

private lemma allNonLin_cons_nonlin {n ρ : ℕ} {Γ : TCtx n ρ} (hΓ : Γ.AllNonLin) (A : Ty) :
    (Γ.cons (some (.nonlin A))).AllNonLin := TCtx.AllNonLin.cons hΓ (nonLin_nonlin A)

/-- Dereliction: `λx. let! y = x in y : !A ⊸ A`. -/
theorem derelict_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (letBang (var 0) (var 0))) (.bang A ⊸ A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (HasTypeD.var_zero_single (n := 1) (.nonlin A)) (TCtx.Add.empty_right _))

/-- Borrowing (Granule's `uniqueReturn`): `λx. &x : *A ⊸ !A`. -/
theorem uniqueReturn_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (borrow (var 0))) (.star A ⊸ .bang A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.borrow (HasTypeD.var_zero_single (.lin (.star A))))

/-- From unique to linear (via non-linear): `λx. let! y = &x in y : *A ⊸ A`. -/
theorem unique_to_linear_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (letBang (borrow (var 0)) (var 0))) (.star A ⊸ A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (.borrow (HasTypeD.var_zero_single (.lin (.star A))))
    (HasTypeD.var_zero_single (n := 1) (.nonlin A)) (TCtx.Add.empty_right _))

/-- Contraction for `!`: `λx. let! y = x in (!y, !y) : !A ⊸ !A ⊗ !A`. -/
theorem bang_contract_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (letBang (var 0) (pair (bang (var 0)) (bang (var 0)))))
      (.bang A ⊸ .bang A ⊗ .bang A) := by
  rw [hasType_iff_hasTypeD]
  have hΔ := allNonLin_cons_nonlin (TCtx.AllNonLin.empty (n := 1) (ρ := 0)) A
  have hv := HasTypeD.bangI hΔ (HasTypeD.var_zero_single (n := 1) (.nonlin A))
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (.tensorI hv hv (TCtx.Add.idem hΔ)) (TCtx.Add.empty_right _))

/-- Weakening for `!`: `λx. let! y = x in unit : !A ⊸ 1`. -/
theorem bang_weaken_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (letBang (var 0) unit)) (.bang A ⊸ .unit) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (.unitI (allNonLin_cons_nonlin (TCtx.AllNonLin.empty (n := 1)) A)) (TCtx.Add.empty_right _))

/-- Granule's `uniqueBind` (the `clone`/`copy` construct as a function):
`λf. λx. copy x as y in f y : (*A ⊸ !B) ⊸ !A ⊸ !B`. -/
theorem uniqueBind_hasType :
    HasType (TCtx.empty : TCtx 0 0) (lam (lam (copy (var 0) (app (var 2) (var 0)))))
      ((.star A ⊸ .bang B) ⊸ .bang A ⊸ .bang B) := by
  rw [hasType_iff_hasTypeD]
  have hf : HasTypeD ((((TCtx.empty : TCtx 0 0).cons (some (.lin (.star A ⊸ .bang B)))).cons
      none).cons none) (var 2) (.star A ⊸ .bang B) :=
    ((HasTypeD.var_zero_single (n := 0) (.lin (.star A ⊸ .bang B))).shift
      nonLin_none).shift nonLin_none
  refine .abs (.abs (.copy (Γ₂ := (((TCtx.empty : TCtx 0 0).cons
      (some (.lin (.star A ⊸ .bang B)))).cons none))
    (HasTypeD.var_zero_single (n := 1) (.lin (.bang A)))
    (.app hf (HasTypeD.var_zero_single (n := 2) (.lin (.star A))) ?_) ?_))
  · exact (TCtx.Add.empty_right _).cons (.noneLeft _)
  · exact (TCtx.Add.empty_left _).cons (.noneRight _)

/-- `possible lots = let! cake = lots in (eat cake, have cake)` is well-typed:
`eat : [Cake ⊸ Happy], have : [Cake ⊸ Cake] ⊢ possible : !Cake ⊸ Happy ⊗ Cake`. -/
theorem possible_cake (Cake Happy : Ty) :
    HasType (cakeCtx Cake Happy)
      (lam (letBang (var 0) (pair (app (var 3) (var 0)) (app (var 2) (var 0)))))
      (.bang Cake ⊸ Happy ⊗ Cake) := by
  rw [hasType_iff_hasTypeD]
  have hc : (cakeCtx Cake Happy).AllNonLin :=
    ⟨.nil, .snoc (.snoc .nil (.nonlin _)) (.nonlin _)⟩
  have hΘ := allNonLin_cons_nonlin hc.cons_none Cake
  refine .abs (.bangE (Γ₁ := (TCtx.empty : TCtx 2 0).cons (some (.lin (.bang Cake))))
    (HasTypeD.var_zero_single (n := 2) (.lin (.bang Cake)))
    (.tensorI (.app (var_nonlin hΘ (i := 3) rfl) (var_nonlin hΘ (i := 0) rfl) (TCtx.Add.idem hΘ))
      (.app (var_nonlin hΘ (i := 2) rfl) (var_nonlin hΘ (i := 0) rfl) (TCtx.Add.idem hΘ))
      (TCtx.Add.idem hΘ)) ((TCtx.Add.empty_left _).cons (.noneRight _)))

/-- Granule's `sip fresh = let !coffee = &fresh in (keep coffee, drink coffee)` is
well-typed: `drink : [Coffee ⊸ Awake], keep : [Coffee ⊸ Coffee] ⊢
sip : *Coffee ⊸ Coffee ⊗ Awake`. -/
theorem sip_hasType (Coffee Awake : Ty) :
    HasType (((TCtx.empty : TCtx 0 0).cons (some (.nonlin (Coffee ⊸ Awake)))).cons
        (some (.nonlin (Coffee ⊸ Coffee))))
      (lam (letBang (borrow (var 0)) (pair (app (var 2) (var 0)) (app (var 3) (var 0)))))
      (.star Coffee ⊸ Coffee ⊗ Awake) := by
  rw [hasType_iff_hasTypeD]
  have hc := allNonLin_cons_nonlin (allNonLin_cons_nonlin
    (TCtx.AllNonLin.empty (n := 0) (ρ := 0)) (Coffee ⊸ Awake)) (Coffee ⊸ Coffee)
  have hΘ := allNonLin_cons_nonlin hc.cons_none Coffee
  refine .abs (.bangE (Γ₁ := (TCtx.empty : TCtx 2 0).cons (some (.lin (.star Coffee))))
    (.borrow (HasTypeD.var_zero_single (n := 2) (.lin (.star Coffee))))
    (.tensorI (.app (var_nonlin hΘ (i := 2) rfl) (var_nonlin hΘ (i := 0) rfl) (TCtx.Add.idem hΘ))
      (.app (var_nonlin hΘ (i := 3) rfl) (var_nonlin hΘ (i := 0) rfl) (TCtx.Add.idem hΘ))
      (TCtx.Add.idem hΘ)) ((TCtx.Add.empty_left _).cons (.noneRight _)))

end Possible

end LCU
