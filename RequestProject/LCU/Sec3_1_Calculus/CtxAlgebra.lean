module
public import RequestProject.LCU.Sec3_1_Calculus.Typing

/-!
# Algebra of context addition

Context addition is a partial commutative monoid: `none` is the unit, `[A]` is
idempotent and linear assumptions cannot be combined with anything but `none`.

The laws are proved once for `HypAdd` on single (optional) hypotheses, and lifted to
contexts by the generic lemmas about pointwise relations of
`RequestProject/Common/Ctx.lean` (`Ctx.Forall₃.func`, `Ctx.Forall₃.assoc`, …): contexts
are lists, so every lifted law is a structural induction on the lists.
-/

@[expose] public section

namespace LCU

/-! ## Pointwise addition of hypotheses -/

namespace HypAdd

variable {T : Type} {a b c d ab bc abc a₁ a₂ b₁ b₂ : Option (Hyp T)}

/-- `none` is also a right unit. -/
lemma none_right (h : Option (Hyp T)) : HypAdd h none h := by
  cases h
  · exact .noneLeft none
  · exact .noneRight _

/-- Addition of hypotheses is commutative. -/
lemma comm (h : HypAdd a b c) : HypAdd b a c := by
  cases h
  · exact none_right _
  · exact .noneLeft _
  · exact .nonlin _

/-- Addition of hypotheses is a partial *function*: the sum is unique. -/
lemma func (h : HypAdd a b c) (h' : HypAdd a b d) : c = d := by
  cases h <;> cases h'
  all_goals rfl

/-- Non-linear (or absent) hypotheses can be duplicated: `[A] + [A] = [A]`. -/
lemma idem (h : NonLin a) : HypAdd a a a := by
  cases h
  · exact .noneLeft none
  · exact .nonlin _

/-- Internal tactic: close a goal `∃ x, HypAdd _ _ x ∧ ...` built from `HypAdd`
facts by greedily introducing witnesses and applying the constructors. -/
macro "hyp_add" : tactic => `(tactic| repeat' first
  | refine ⟨_, ?_⟩ | refine ⟨?_, ?_⟩
  | exact .noneLeft _ | exact .noneRight _ | exact .nonlin _ | exact none_right _)

/-- Associativity: `(a + b) + c = a + (b + c)`. -/
lemma assoc (h₁ : HypAdd a b ab) (h₂ : HypAdd ab c abc) :
    ∃ bc, HypAdd b c bc ∧ HypAdd a bc abc := by
  cases h₁ <;> cases h₂ <;> hyp_add

/-- Associativity, other direction: `a + (b + c) = (a + b) + c`. -/
lemma assoc' (h₁ : HypAdd b c bc) (h₂ : HypAdd a bc abc) :
    ∃ ab, HypAdd a b ab ∧ HypAdd ab c abc := by
  obtain ⟨x, hx1, hx2⟩ := assoc h₁.comm h₂.comm
  exact ⟨x, hx1.comm, hx2.comm⟩

/-- Interchange law: `(a₁ + a₂) + (b₁ + b₂) = (a₁ + b₁) + (a₂ + b₂)`. -/
lemma interchange (h₁ : HypAdd a₁ a₂ a) (h₂ : HypAdd b₁ b₂ b) (h : HypAdd a b c) :
    ∃ c₁ c₂, HypAdd a₁ b₁ c₁ ∧ HypAdd a₂ b₂ c₂ ∧ HypAdd c₁ c₂ c := by
  cases h₁ <;> cases h₂ <;> cases h <;> hyp_add

/-- A sum is non-linear iff both summands are. -/
lemma nonLin_iff (h : HypAdd a b c) : NonLin c ↔ NonLin a ∧ NonLin b := by
  cases h with
  | noneLeft => simp
  | noneRight h => cases h <;> simp
  | nonlin => simp

lemma nonLin_left (h : HypAdd a b c) (hc : NonLin c) : NonLin a := (h.nonLin_iff.1 hc).1
lemma nonLin_right (h : HypAdd a b c) (hc : NonLin c) : NonLin b := (h.nonLin_iff.1 hc).2
lemma nonLin_of (h : HypAdd a b c) (ha : NonLin a) (hb : NonLin b) : NonLin c :=
  h.nonLin_iff.2 ⟨ha, hb⟩

/-- Only `none + none = none`. -/
lemma eq_none (h : HypAdd a b none) : a = none ∧ b = none := by
  cases h; simp only [and_self]

/-- A linear hypothesis `x : A` comes from exactly one summand. -/
lemma eq_lin {A : T} (h : HypAdd a b (some (.lin A))) :
    (a = some (.lin A) ∧ b = none) ∨ (a = none ∧ b = some (.lin A)) := by
  cases h <;> simp

/-- Adding a non-linear (or absent) hypothesis to `some h` gives back `some h`. -/
lemma some_of_nonLin {h : Hyp T} (hx : HypAdd (some h) b c) (hb : NonLin b) : c = some h := by
  cases hx with
  | noneRight => rfl
  | nonlin => rfl

lemma some_of_nonLin' {h : Hyp T} (hx : HypAdd a (some h) c) (ha : NonLin a) : c = some h :=
  hx.comm.some_of_nonLin ha

/-- Sums with `none` on one side. -/
lemma left_none (h : HypAdd none b c) : b = c := by cases h; rfl
lemma right_none (h : HypAdd a none c) : a = c := by cases h; all_goals rfl

/-- Sums with a non-linear hypothesis `[A]` on the left. -/
lemma nonlin_left {A : T} (h : HypAdd (some (.nonlin A)) b c) :
    c = some (.nonlin A) ∧ (b = none ∨ b = some (.nonlin A)) := by
  cases h <;> simp

/-- Turning a linear assumption into a non-linear one in a sum. -/
lemma der {A : T} (h : HypAdd a b (some (.lin A))) :
    (HypAdd (some (.nonlin A)) b (some (.nonlin A)) ∧ a = some (.lin A)) ∨
    (HypAdd a (some (.nonlin A)) (some (.nonlin A)) ∧ b = some (.lin A)) := by
  cases h
  · right; exact ⟨.noneLeft _, rfl⟩
  · left; exact ⟨.noneRight _, rfl⟩

end HypAdd

/-! ## Context addition -/

namespace TCtx

variable {n ρ : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ' Δ Δ₁ Δ₂ : TCtx n ρ}

/-- Context addition is commutative. -/
lemma Add.comm (h : Γ₁.Add Γ₂ Γ) : Γ₂.Add Γ₁ Γ :=
  ⟨h.refs.swap HypAdd.comm, h.vars.swap HypAdd.comm⟩

/-- Context addition is functional. -/
lemma Add.func (h : Γ₁.Add Γ₂ Γ) (h' : Γ₁.Add Γ₂ Γ') : Γ = Γ' :=
  ext (h.refs.func h'.refs HypAdd.func) (h.vars.func h'.vars HypAdd.func)

/-- The empty context is a unit for context addition. -/
lemma Add.empty_left (Γ : TCtx n ρ) : (empty : TCtx n ρ).Add Γ Γ :=
  ⟨Ctx.Forall₃.replicate_left HypAdd.noneLeft _, Ctx.Forall₃.replicate_left HypAdd.noneLeft _⟩
lemma Add.empty_right (Γ : TCtx n ρ) : Γ.Add empty Γ :=
  ⟨Ctx.Forall₃.replicate_right HypAdd.none_right _,
    Ctx.Forall₃.replicate_right HypAdd.none_right _⟩

lemma Add.empty_left_iff : (empty : TCtx n ρ).Add Γ Γ' ↔ Γ = Γ' :=
  ⟨fun h => ext (h.refs.eq_of_replicate_left HypAdd.left_none)
    (h.vars.eq_of_replicate_left HypAdd.left_none), fun h => h ▸ Add.empty_left Γ⟩

lemma Add.empty_right_iff : Γ.Add empty Γ' ↔ Γ = Γ' :=
  ⟨fun h => ext (h.refs.eq_of_replicate_right HypAdd.right_none)
    (h.vars.eq_of_replicate_right HypAdd.right_none), fun h => h ▸ Add.empty_right Γ⟩

/-- `[Γ] + [Γ] = [Γ]`: non-linear contexts can be contracted. -/
lemma Add.idem (h : Γ.AllNonLin) : Γ.Add Γ Γ :=
  ⟨Ctx.Forall₃.of_all HypAdd.idem h.refs, Ctx.Forall₃.of_all HypAdd.idem h.vars⟩

/-- Associativity of context addition. -/
lemma Add.assoc (h₁ : Γ₁.Add Γ₂ Γ₁₂) (h₂ : Γ₁₂.Add Γ₃ Γ) :
    ∃ Γ₂₃, Γ₂.Add Γ₃ Γ₂₃ ∧ Γ₁.Add Γ₂₃ Γ := by
  obtain ⟨r, hr₁, hr₂⟩ := h₁.refs.assoc h₂.refs HypAdd.assoc
  obtain ⟨v, hv₁, hv₂⟩ := h₁.vars.assoc h₂.vars HypAdd.assoc
  exact ⟨⟨r, v⟩, ⟨hr₁, hv₁⟩, ⟨hr₂, hv₂⟩⟩

lemma Add.assoc' (h₁ : Γ₂.Add Γ₃ Γ₂₃) (h₂ : Γ₁.Add Γ₂₃ Γ) :
    ∃ Γ₁₂, Γ₁.Add Γ₂ Γ₁₂ ∧ Γ₁₂.Add Γ₃ Γ := by
  obtain ⟨x, hx1, hx2⟩ := Add.assoc h₁.comm h₂.comm
  exact ⟨x, hx1.comm, hx2.comm⟩

/-- Interchange law for context addition, used e.g. when splitting a context
between the two premises of a rule and a substituted term. -/
lemma Add.interchange {A₁ A₂ A B₁ B₂ B C : TCtx n ρ}
    (h₁ : A₁.Add A₂ A) (h₂ : B₁.Add B₂ B) (h : A.Add B C) :
    ∃ C₁ C₂, A₁.Add B₁ C₁ ∧ A₂.Add B₂ C₂ ∧ C₁.Add C₂ C := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := h₁.refs.interchange h₂.refs h.refs HypAdd.interchange
  obtain ⟨v₁, v₂, hv₁, hv₂, hv⟩ := h₁.vars.interchange h₂.vars h.vars HypAdd.interchange
  exact ⟨⟨r₁, v₁⟩, ⟨r₂, v₂⟩, ⟨hr₁, hv₁⟩, ⟨hr₂, hv₂⟩, ⟨hr, hv⟩⟩

/-! ## Non-linear contexts `[Γ]` and sums -/

lemma AllNonLin.of_add (h : Γ₁.Add Γ₂ Γ) (h₁ : Γ₁.AllNonLin) (h₂ : Γ₂.AllNonLin) :
    Γ.AllNonLin :=
  ⟨h.refs.all HypAdd.nonLin_of h₁.refs h₂.refs, h.vars.all HypAdd.nonLin_of h₁.vars h₂.vars⟩

lemma AllNonLin.left (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.AllNonLin) : Γ₁.AllNonLin :=
  ⟨h.refs.all_left HypAdd.nonLin_left hΓ.refs, h.vars.all_left HypAdd.nonLin_left hΓ.vars⟩

lemma AllNonLin.right (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.AllNonLin) : Γ₂.AllNonLin :=
  ⟨h.refs.all_right HypAdd.nonLin_right hΓ.refs, h.vars.all_right HypAdd.nonLin_right hΓ.vars⟩

lemma VarsNonLin.of_add (h : Γ₁.Add Γ₂ Γ) (h₁ : Γ₁.VarsNonLin) (h₂ : Γ₂.VarsNonLin) :
    Γ.VarsNonLin := h.vars.all HypAdd.nonLin_of h₁ h₂

lemma VarsNonLin.left (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.VarsNonLin) : Γ₁.VarsNonLin :=
  h.vars.all_left HypAdd.nonLin_left hΓ

lemma VarsNonLin.right (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.VarsNonLin) : Γ₂.VarsNonLin :=
  h.vars.all_right HypAdd.nonLin_right hΓ

lemma AllNonLin.varsNonLin (h : Γ.AllNonLin) : Γ.VarsNonLin := h.vars

lemma allNonLin_replicate {T : Type} (m : ℕ) : (Ctx.replicate m (none : Option (Hyp T))).All NonLin :=
  Ctx.all_replicate .none m

lemma AllNonLin.empty : (empty : TCtx n ρ).AllNonLin :=
  ⟨allNonLin_replicate _, allNonLin_replicate _⟩

lemma VarsNonLin.refsOnly (Γ : TCtx n ρ) : Γ.refsOnly.VarsNonLin := allNonLin_replicate _

lemma AllNonLin.refsOnly (h : Γ.AllNonLin) : Γ.refsOnly.AllNonLin :=
  ⟨h.refs, allNonLin_replicate _⟩

/-- Dropping all variable assumptions commutes with addition. -/
lemma Add.refsOnly (h : Γ₁.Add Γ₂ Γ) : Γ₁.refsOnly.Add Γ₂.refsOnly Γ.refsOnly :=
  ⟨h.refs, Ctx.Forall₃.replicate_left HypAdd.noneLeft _⟩

/-! ## Extending contexts -/

lemma Add.cons {h₁ h₂ h : Option (Hyp Ty)} (hΓ : Γ₁.Add Γ₂ Γ) (hh : HypAdd h₁ h₂ h) :
    (Γ₁.cons h₁).Add (Γ₂.cons h₂) (Γ.cons h) :=
  ⟨hΓ.refs, .snoc hΓ.vars hh⟩

lemma Add.cons_none (hΓ : Γ₁.Add Γ₂ Γ) (h₀ : Option (Hyp Ty)) :
    (Γ₁.cons h₀).Add (Γ₂.cons none) (Γ.cons h₀) :=
  hΓ.cons (HypAdd.none_right _)

lemma Add.of_cons {h₁ h₂ h : Option (Hyp Ty)}
    (hΓ : (Γ₁.cons h₁).Add (Γ₂.cons h₂) (Γ.cons h)) : Γ₁.Add Γ₂ Γ ∧ HypAdd h₁ h₂ h := by
  have := hΓ.vars; simp only [cons_vars, Ctx.forall₃_snoc] at this
  exact ⟨⟨hΓ.refs, this.1⟩, this.2⟩

lemma Add.setVar {i : Var n} {h₁ h₂ h : Option (Hyp Ty)} (hΓ : Γ₁.Add Γ₂ Γ)
    (hh : HypAdd h₁ h₂ h) : (Γ₁.setVar i h₁).Add (Γ₂.setVar i h₂) (Γ.setVar i h) :=
  ⟨hΓ.refs, hΓ.vars.set i hh⟩

lemma Add.setRef {a : Var ρ} {h₁ h₂ h : Option (Hyp ArrTy)} (hΓ : Γ₁.Add Γ₂ Γ)
    (hh : HypAdd h₁ h₂ h) : (Γ₁.setRef a h₁).Add (Γ₂.setRef a h₂) (Γ.setRef a h) :=
  ⟨hΓ.refs.set a hh, hΓ.vars⟩

/-- Every context with `n + 1` variables is an extension. -/
lemma eq_cons (Γ : TCtx (n + 1) ρ) : ∃ (Γ' : TCtx n ρ) (h : Option (Hyp Ty)), Γ = Γ'.cons h := by
  obtain ⟨r, v⟩ := Γ
  cases v with
  | snoc v h => exact ⟨⟨r, v⟩, h, rfl⟩

@[simp] lemma cons_inj {Γ Γ' : TCtx n ρ} {h h' : Option (Hyp Ty)} :
    Γ.cons h = Γ'.cons h' ↔ Γ = Γ' ∧ h = h' := by
  simp only [ext_iff', cons_refs, cons_vars, Ctx.snoc_inj]
  tauto

lemma cons_setVar_succ (Γ : TCtx n ρ) (h : Option (Hyp Ty)) (i : Var n) (h' : Option (Hyp Ty)) :
    (Γ.setVar i h').cons h = (Γ.cons h).setVar (.succ i) h' := rfl

lemma cons_setVar_zero (Γ : TCtx n ρ) (h h' : Option (Hyp Ty)) :
    Γ.cons h' = (Γ.cons h).setVar .zero h' := rfl

lemma cons_setRef (Γ : TCtx n ρ) (h : Option (Hyp Ty)) (a : Var ρ) (h' : Option (Hyp ArrTy)) :
    (Γ.setRef a h').cons h = (Γ.cons h).setRef a h' := rfl

lemma refsOnly_cons (Γ : TCtx n ρ) (h : Option (Hyp Ty)) :
    (Γ.cons h).refsOnly = Γ.refsOnly.cons none := rfl

lemma refsOnly_setRef (Γ : TCtx n ρ) (a : Var ρ) (h : Option (Hyp ArrTy)) :
    (Γ.setRef a h).refsOnly = Γ.refsOnly.setRef a h := rfl

lemma AllNonLin.cons {h : Option (Hyp Ty)} (hΓ : Γ.AllNonLin) (hh : NonLin h) :
    (Γ.cons h).AllNonLin := ⟨hΓ.refs, .snoc hΓ.vars hh⟩

lemma AllNonLin.cons_none (hΓ : Γ.AllNonLin) : (Γ.cons none).AllNonLin := hΓ.cons .none

lemma AllNonLin.of_cons {h : Option (Hyp Ty)} (hΓ : (Γ.cons h).AllNonLin) :
    Γ.AllNonLin ∧ NonLin h := by
  have := hΓ.vars; simp only [cons_vars, Ctx.all_snoc] at this
  exact ⟨⟨hΓ.refs, this.1⟩, this.2⟩

lemma AllNonLin.setVar (hΓ : Γ.AllNonLin) (i : Var n) {h : Option (Hyp Ty)} (hh : NonLin h) :
    (Γ.setVar i h).AllNonLin := ⟨hΓ.refs, hΓ.vars.set i hh⟩

lemma AllNonLin.setRef (hΓ : Γ.AllNonLin) (a : Var ρ) {h : Option (Hyp ArrTy)} (hh : NonLin h) :
    (Γ.setRef a h).AllNonLin := ⟨hΓ.refs.set a hh, hΓ.vars⟩

lemma VarsNonLin.setRef (hΓ : Γ.VarsNonLin) (a : Var ρ) (h : Option (Hyp ArrTy)) :
    (Γ.setRef a h).VarsNonLin := hΓ

/-- A non-linear list of hypotheses contains no linear assumption. -/
lemma _root_.LCU.not_lin_of_all {T : Type} {m : ℕ} {Δ : Ctx (Option (Hyp T)) m}
    (hΔ : Δ.All NonLin) {i : Var m} {A : T} (hi : Δ.get i = some (.lin A)) : False := by
  have := hΔ.get i; rw [hi] at this; exact this.elim

lemma setVar_setVar (Γ : TCtx n ρ) (i : Var n) (h h' : Option (Hyp Ty)) :
    (Γ.setVar i h).setVar i h' = Γ.setVar i h' := by simp [setVar]

lemma setVar_get (Γ : TCtx n ρ) (i : Var n) : Γ.setVar i (Γ.vars.get i) = Γ := by
  simp [setVar]

lemma setRef_get (Γ : TCtx n ρ) (a : Var ρ) : Γ.setRef a (Γ.refs.get a) = Γ := by
  simp [setRef]

end TCtx

end LCU
