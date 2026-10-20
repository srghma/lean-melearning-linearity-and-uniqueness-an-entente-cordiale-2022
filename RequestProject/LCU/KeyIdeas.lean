module
public import RequestProject.LCU.Equational

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
functions `eat`, `have`, `drink`, `keep` are free (non-linear) variables.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Variables have assumptions -/

/-- A variable that occurs free in a well-typed term has an assumption in the context. -/
theorem HasTypeD.ne_none_of_freeIn {n : ℕ} {Γ : Ctx n} {t : Term n} {B : Ty}
    (ht : HasTypeD Γ t B) : ∀ {i : Fin n}, FreeIn i t → Γ (.inl i) ≠ none := by
  induction ht with
  | var hi _ => intro i h; simp only [FreeIn] at h; subst h; simp [hi]
  | abs _ ih => intro i h; simpa using ih (i := i.succ) h
  | app _ _ hadd ih₁ ih₂ | tensorI _ _ hadd ih₁ ih₂ | unitE _ _ hadd ih₁ ih₂ =>
    intro i h e
    have hx := hadd (.inl i); rw [e] at hx
    obtain ⟨e₁, e₂⟩ := hx.eq_none
    rcases h with h | h
    · exact ih₁ h e₁
    · exact ih₂ h e₂
  | tensorE _ _ hadd ih₁ ih₂ =>
    intro i h e
    have hx := hadd (.inl i); rw [e] at hx
    obtain ⟨e₁, e₂⟩ := hx.eq_none
    rcases h with h | h
    · exact ih₁ h e₁
    · exact ih₂ (i := i.succ.succ) h (by simpa using e₂)
  | bangE _ _ hadd ih₁ ih₂ | copy _ _ hadd ih₁ ih₂ =>
    intro i h e
    have hx := hadd (.inl i); rw [e] at hx
    obtain ⟨e₁, e₂⟩ := hx.eq_none
    rcases h with h | h
    · exact ih₁ h e₁
    · exact ih₂ (i := i.succ) h (by simpa using e₂)
  | unitI _ => intro i h; exact h.elim
  | bangI _ _ ih => intro i h; exact ih h
  | borrow _ ih => intro i h; exact ih h
  | nec _ _ ih => intro i h; exact absurd rfl (ih h)
  | natI _ => intro i h; exact h.elim
  | floatI _ => intro i h; exact h.elim
  | prim _ => intro i h; exact h.elim
  | ref _ _ => intro i h; exact h.elim

/-! ## Impossible programs: no contraction of linear or unique values -/

/-- A linearly bound variable cannot be used in both components of a pair:
`λx. (t₁, t₂)` is ill-typed whenever `x` occurs in both `t₁` and `t₂`. -/
theorem not_hasType_lam_pair_dup {n : ℕ} {Γ : Ctx n} {t₁ t₂ : Term (n + 1)} {T : Ty}
    (h₁ : FreeIn 0 t₁) (h₂ : FreeIn 0 t₂) : ¬ HasType Γ (lam (pair t₁ t₂)) T := by
  rw [hasType_iff_hasTypeD]
  intro ht
  cases ht with
  | abs ht =>
    cases ht with
    | tensorI g₁ g₂ hadd =>
      have hx := hadd (.inl 0)
      simp only [Ctx.cons_inl_zero] at hx
      have n₁ := g₁.ne_none_of_freeIn h₁
      have n₂ := g₂.ne_none_of_freeIn h₂
      have key : ∀ {a b c : Option Hyp} {A : Ty}, HypAdd a b c → c = some (.lin A) →
          a ≠ none → b ≠ none → False := by
        intro a b c A h; cases h <;> simp
      exact key hx rfl n₁ n₂

/-- The context `eat : [Cake ⊸ Happy], have : [Cake ⊸ Cake]` (`have` is index `0`). -/
def cakeCtx (Cake Happy : Ty) : Ctx 2 :=
  ((Ctx.empty : Ctx 0).cons (some (.nonlin (Cake ⊸ Happy)))).cons (some (.nonlin (Cake ⊸ Cake)))

/-- `impossible cake = (eat cake, have cake)` is ill-typed (at any type): the linear
`cake` would have to be duplicated. -/
theorem impossible_cake (Cake Happy T : Ty) :
    ¬ HasType (cakeCtx Cake Happy) (lam (pair (app (var 2) (var 0)) (app (var 1) (var 0)))) T :=
  not_hasType_lam_pair_dup (Or.inr rfl) (Or.inr rfl)

/-- The context `drink : [*Coffee ⊸ *Awake], keep : [*Coffee ⊸ *Coffee]`. -/
def coffeeCtx (Coffee Awake : Ty) : Ctx 2 :=
  ((Ctx.empty : Ctx 0).cons (some (.nonlin (.star Coffee ⊸ .star Awake)))).cons
    (some (.nonlin (.star Coffee ⊸ .star Coffee)))

/-- `impossible coffee = (drink coffee, keep coffee)` is ill-typed (at any type, in
particular at `*Coffee ⊸ *Awake ⊗ *Coffee`): the unique `coffee` would have to be
duplicated. -/
theorem impossible_coffee (Coffee Awake T : Ty) :
    ¬ HasType (coffeeCtx Coffee Awake)
      (lam (pair (app (var 2) (var 0)) (app (var 1) (var 0)))) T :=
  not_hasType_lam_pair_dup (Or.inr rfl) (Or.inr rfl)

/-! ## Possible programs -/

section Possible

variable (A B : Ty)

private lemma var_nonlin {n : ℕ} {Γ : Ctx n} (hΓ : Γ.AllNonLin) {i : Fin n} {h : Hyp}
    (hi : Γ (.inl i) = some h) : HasTypeD Γ (var i) h.ty := by
  refine .var hi fun x => ?_
  by_cases hx : x = .inl i
  · subst hx; simp
  · rw [Ctx.set_ne _ _ hx]; exact hΓ x

private lemma allNonLin_cons_nonlin {n : ℕ} {Γ : Ctx n} (hΓ : Γ.AllNonLin) (A : Ty) :
    (Γ.cons (some (.nonlin A))).AllNonLin := Ctx.AllNonLin.cons hΓ (nonLin_nonlin A)

private lemma allNonLin_cons_none {n : ℕ} {Γ : Ctx n} (hΓ : Γ.AllNonLin) :
    (Γ.cons none).AllNonLin := Ctx.AllNonLin.cons hΓ nonLin_none

/-- Dereliction: `λx. let! y = x in y : !A ⊸ A`. -/
theorem derelict_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (letBang (var 0) (var 0))) (.bang A ⊸ A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (HasTypeD.var_zero_single (n := 1) (.nonlin A)) (Ctx.Add.empty_right _))

/-- Borrowing (Granule's `uniqueReturn`): `λx. &x : *A ⊸ !A`. -/
theorem uniqueReturn_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (borrow (var 0))) (.star A ⊸ .bang A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.borrow (HasTypeD.var_zero_single (.lin (.star A))))

/-- From unique to linear (via non-linear): `λx. let! y = &x in y : *A ⊸ A`. -/
theorem unique_to_linear_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (letBang (borrow (var 0)) (var 0))) (.star A ⊸ A) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (.borrow (HasTypeD.var_zero_single (.lin (.star A))))
    (HasTypeD.var_zero_single (n := 1) (.nonlin A)) (Ctx.Add.empty_right _))

/-- Contraction for `!`: `λx. let! y = x in (!y, !y) : !A ⊸ !A ⊗ !A`. -/
theorem bang_contract_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (letBang (var 0) (pair (bang (var 0)) (bang (var 0)))))
      (.bang A ⊸ .bang A ⊗ .bang A) := by
  rw [hasType_iff_hasTypeD]
  have hΔ := allNonLin_cons_nonlin (Ctx.AllNonLin.empty (n := 1)) A
  have hv := HasTypeD.bangI hΔ (HasTypeD.var_zero_single (n := 1) (.nonlin A))
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (.tensorI hv hv (Ctx.Add.idem hΔ)) (Ctx.Add.empty_right _))

/-- Weakening for `!`: `λx. let! y = x in unit : !A ⊸ 1`. -/
theorem bang_weaken_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (letBang (var 0) unit)) (.bang A ⊸ .unit) := by
  rw [hasType_iff_hasTypeD]
  exact .abs (.bangE (HasTypeD.var_zero_single (.lin (.bang A)))
    (.unitI (allNonLin_cons_nonlin (Ctx.AllNonLin.empty (n := 1)) A)) (Ctx.Add.empty_right _))

/-- Granule's `uniqueBind` (the `clone`/`copy` construct as a function):
`λf. λx. copy x as y in f y : (*A ⊸ !B) ⊸ !A ⊸ !B`. -/
theorem uniqueBind_hasType :
    HasType (Ctx.empty : Ctx 0) (lam (lam (copy (var 0) (app (var 2) (var 0)))))
      ((.star A ⊸ .bang B) ⊸ .bang A ⊸ .bang B) := by
  rw [hasType_iff_hasTypeD]
  have hf : HasTypeD ((((Ctx.empty : Ctx 0).cons (some (.lin (.star A ⊸ .bang B)))).cons
      none).cons none) (var 2) (.star A ⊸ .bang B) :=
    ((HasTypeD.var_zero_single (n := 0) (.lin (.star A ⊸ .bang B))).shift
      nonLin_none).shift nonLin_none
  refine .abs (.abs (.copy (Γ₂ := (((Ctx.empty : Ctx 0).cons
      (some (.lin (.star A ⊸ .bang B)))).cons none))
    (HasTypeD.var_zero_single (n := 1) (.lin (.bang A)))
    (.app hf (HasTypeD.var_zero_single (n := 2) (.lin (.star A))) ?_) ?_))
  · exact (Ctx.Add.empty_right _).cons (.noneLeft _)
  · exact (Ctx.Add.empty_left _).cons (.noneRight _)

/-- `possible lots = let! cake = lots in (eat cake, have cake)` is well-typed:
`eat : [Cake ⊸ Happy], have : [Cake ⊸ Cake] ⊢ possible : !Cake ⊸ Happy ⊗ Cake`. -/
theorem possible_cake (Cake Happy : Ty) :
    HasType (cakeCtx Cake Happy)
      (lam (letBang (var 0) (pair (app (var 3) (var 0)) (app (var 2) (var 0)))))
      (.bang Cake ⊸ Happy ⊗ Cake) := by
  rw [hasType_iff_hasTypeD]
  have hc : (cakeCtx Cake Happy).AllNonLin :=
    allNonLin_cons_nonlin (allNonLin_cons_nonlin Ctx.AllNonLin.empty _) _
  have hΘ := allNonLin_cons_nonlin (allNonLin_cons_none hc) Cake
  refine .abs (.bangE (Γ₁ := (Ctx.empty : Ctx 2).cons (some (.lin (.bang Cake))))
    (HasTypeD.var_zero_single (n := 2) (.lin (.bang Cake)))
    (.tensorI (.app (var_nonlin hΘ (i := 3) rfl) (var_nonlin hΘ (i := 0) rfl) (Ctx.Add.idem hΘ))
      (.app (var_nonlin hΘ (i := 2) rfl) (var_nonlin hΘ (i := 0) rfl) (Ctx.Add.idem hΘ))
      (Ctx.Add.idem hΘ)) ((Ctx.Add.empty_left _).cons (.noneRight _)))

/-- Granule's `sip fresh = let !coffee = &fresh in (keep coffee, drink coffee)` is
well-typed: `drink : [Coffee ⊸ Awake], keep : [Coffee ⊸ Coffee] ⊢
sip : *Coffee ⊸ Coffee ⊗ Awake`. -/
theorem sip_hasType (Coffee Awake : Ty) :
    HasType (((Ctx.empty : Ctx 0).cons (some (.nonlin (Coffee ⊸ Awake)))).cons
        (some (.nonlin (Coffee ⊸ Coffee))))
      (lam (letBang (borrow (var 0)) (pair (app (var 2) (var 0)) (app (var 3) (var 0)))))
      (.star Coffee ⊸ Coffee ⊗ Awake) := by
  rw [hasType_iff_hasTypeD]
  have hc := allNonLin_cons_nonlin (allNonLin_cons_nonlin
    (Ctx.AllNonLin.empty (n := 0)) (Coffee ⊸ Awake)) (Coffee ⊸ Coffee)
  have hΘ := allNonLin_cons_nonlin (allNonLin_cons_none hc) Coffee
  refine .abs (.bangE (Γ₁ := (Ctx.empty : Ctx 2).cons (some (.lin (.star Coffee))))
    (.borrow (HasTypeD.var_zero_single (n := 2) (.lin (.star Coffee))))
    (.tensorI (.app (var_nonlin hΘ (i := 2) rfl) (var_nonlin hΘ (i := 0) rfl) (Ctx.Add.idem hΘ))
      (.app (var_nonlin hΘ (i := 3) rfl) (var_nonlin hΘ (i := 0) rfl) (Ctx.Add.idem hΘ))
      (Ctx.Add.idem hΘ)) ((Ctx.Add.empty_left _).cons (.noneRight _)))

end Possible

end LCU
