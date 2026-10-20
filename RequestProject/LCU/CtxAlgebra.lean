module
public import RequestProject.LCU.Typing

/-!
# Algebra of context addition

Context addition is a partial commutative monoid: `none` is the unit, `[A]` is
idempotent and linear assumptions cannot be combined with anything but `none`.
-/

@[expose] public section

namespace LCU

namespace HypAdd

variable {a b c d ab bc abc a₁ a₂ b₁ b₂ : Option Hyp}

lemma none_right (h : Option Hyp) : HypAdd h none h := by
  cases h
  · exact .noneLeft none
  · exact .noneRight _

lemma comm (h : HypAdd a b c) : HypAdd b a c := by
  cases h
  · exact none_right _
  · exact .noneLeft _
  · exact .nonlin _

lemma func (h : HypAdd a b c) (h' : HypAdd a b d) : c = d := by
  cases h <;> cases h'
  all_goals rfl

lemma idem (h : NonLin a) : HypAdd a a a := by
  rcases a with _ | ⟨A | A⟩
  · exact .noneLeft none
  · exact absurd h (not_nonLin_lin A)
  · exact .nonlin A

/-- Internal tactic: close a goal `∃ x, HypAdd _ _ x ∧ HypAdd _ _ _` by trying
all combinations of constructors. -/
macro "hyp_add2" : tactic => `(tactic| first | exact ⟨_, HypAdd.noneLeft _, HypAdd.noneLeft _⟩ | exact ⟨_, HypAdd.noneLeft _, HypAdd.noneRight _⟩ | exact ⟨_, HypAdd.noneLeft _, HypAdd.nonlin _⟩ | exact ⟨_, HypAdd.noneLeft _, HypAdd.none_right _⟩ | exact ⟨_, HypAdd.noneRight _, HypAdd.noneLeft _⟩ | exact ⟨_, HypAdd.noneRight _, HypAdd.noneRight _⟩ | exact ⟨_, HypAdd.noneRight _, HypAdd.nonlin _⟩ | exact ⟨_, HypAdd.noneRight _, HypAdd.none_right _⟩ | exact ⟨_, HypAdd.nonlin _, HypAdd.noneLeft _⟩ | exact ⟨_, HypAdd.nonlin _, HypAdd.noneRight _⟩ | exact ⟨_, HypAdd.nonlin _, HypAdd.nonlin _⟩ | exact ⟨_, HypAdd.nonlin _, HypAdd.none_right _⟩ | exact ⟨_, HypAdd.none_right _, HypAdd.noneLeft _⟩ | exact ⟨_, HypAdd.none_right _, HypAdd.noneRight _⟩ | exact ⟨_, HypAdd.none_right _, HypAdd.nonlin _⟩ | exact ⟨_, HypAdd.none_right _, HypAdd.none_right _⟩)

/-- Internal tactic: as `hyp_add2` with two witnesses and three summands. -/
macro "hyp_add3" : tactic => `(tactic| first | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneLeft _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneLeft _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneLeft _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneLeft _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneRight _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneRight _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneRight _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.noneRight _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.nonlin _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.nonlin _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.nonlin _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.nonlin _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.none_right _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.none_right _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.none_right _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneLeft _, HypAdd.none_right _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneLeft _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneLeft _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneLeft _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneLeft _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneRight _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneRight _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneRight _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.noneRight _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.nonlin _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.nonlin _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.nonlin _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.nonlin _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.none_right _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.none_right _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.none_right _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.noneRight _, HypAdd.none_right _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneLeft _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneLeft _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneLeft _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneLeft _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneRight _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneRight _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneRight _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.noneRight _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.nonlin _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.nonlin _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.nonlin _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.nonlin _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.none_right _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.none_right _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.none_right _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.nonlin _, HypAdd.none_right _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneLeft _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneLeft _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneLeft _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneLeft _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneRight _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneRight _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneRight _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.noneRight _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.nonlin _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.nonlin _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.nonlin _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.nonlin _, HypAdd.none_right _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.none_right _, HypAdd.noneLeft _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.none_right _, HypAdd.noneRight _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.none_right _, HypAdd.nonlin _⟩ | exact ⟨_, _, HypAdd.none_right _, HypAdd.none_right _, HypAdd.none_right _⟩)

lemma assoc (h₁ : HypAdd a b ab) (h₂ : HypAdd ab c abc) :
    ∃ bc, HypAdd b c bc ∧ HypAdd a bc abc := by
  cases h₁ <;> cases h₂ <;> hyp_add2

lemma assoc' (h₁ : HypAdd b c bc) (h₂ : HypAdd a bc abc) :
    ∃ ab, HypAdd a b ab ∧ HypAdd ab c abc := by
  obtain ⟨x, hx1, hx2⟩ := assoc h₁.comm h₂.comm
  exact ⟨x, hx1.comm, hx2.comm⟩

lemma interchange (h₁ : HypAdd a₁ a₂ a) (h₂ : HypAdd b₁ b₂ b) (h : HypAdd a b c) :
    ∃ c₁ c₂, HypAdd a₁ b₁ c₁ ∧ HypAdd a₂ b₂ c₂ ∧ HypAdd c₁ c₂ c := by
  cases h₁ <;> cases h₂ <;> cases h <;> hyp_add3

lemma nonLin_iff (h : HypAdd a b c) : NonLin c ↔ NonLin a ∧ NonLin b := by
  cases h <;> simp

lemma nonLin_left (h : HypAdd a b c) (hc : NonLin c) : NonLin a := (h.nonLin_iff.1 hc).1
lemma nonLin_right (h : HypAdd a b c) (hc : NonLin c) : NonLin b := (h.nonLin_iff.1 hc).2
lemma nonLin_of (h : HypAdd a b c) (ha : NonLin a) (hb : NonLin b) : NonLin c :=
  h.nonLin_iff.2 ⟨ha, hb⟩

lemma eq_none (h : HypAdd a b none) : a = none ∧ b = none := by
  cases h; simp only [and_self]

lemma eq_lin {A : Ty} (h : HypAdd a b (some (.lin A))) :
    (a = some (.lin A) ∧ b = none) ∨ (a = none ∧ b = some (.lin A)) := by
  cases h <;> simp

lemma left_none (h : HypAdd none b c) : b = c := by cases h; rfl
lemma right_none (h : HypAdd a none c) : a = c := by cases h; all_goals rfl

/-- Sums with a non-linear hypothesis `[A]` on the left. -/
lemma nonlin_left {A : Ty} (h : HypAdd (some (.nonlin A)) b c) :
    c = some (.nonlin A) ∧ (b = none ∨ b = some (.nonlin A)) := by
  cases h <;> simp

/-- Turning a linear assumption into a non-linear one in a sum. -/
lemma der {A : Ty} (h : HypAdd a b (some (.lin A))) :
    (HypAdd (some (.nonlin A)) b (some (.nonlin A)) ∧ a = some (.lin A)) ∨
    (HypAdd a (some (.nonlin A)) (some (.nonlin A)) ∧ b = some (.lin A)) := by
  cases h
  · right; exact ⟨.noneLeft _, rfl⟩
  · left; exact ⟨.noneRight _, rfl⟩

end HypAdd

namespace Ctx

variable {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ' Δ Δ₁ Δ₂ : Ctx n}

lemma Add.comm (h : Γ₁.Add Γ₂ Γ) : Γ₂.Add Γ₁ Γ := fun x => (h x).comm

lemma Add.func (h : Γ₁.Add Γ₂ Γ) (h' : Γ₁.Add Γ₂ Γ') : Γ = Γ' :=
  funext fun x => (h x).func (h' x)

lemma Add.empty_left (Γ : Ctx n) : (empty : Ctx n).Add Γ Γ := fun _ => .noneLeft _
lemma Add.empty_right (Γ : Ctx n) : Γ.Add empty Γ := fun _ => HypAdd.none_right _

lemma Add.empty_left_iff : (empty : Ctx n).Add Γ Γ' ↔ Γ = Γ' :=
  ⟨fun h => funext fun x => (h x).left_none, fun h => h ▸ Add.empty_left Γ⟩

lemma Add.empty_right_iff : Γ.Add empty Γ' ↔ Γ = Γ' :=
  ⟨fun h => funext fun x => (h x).right_none, fun h => h ▸ Add.empty_right Γ⟩

lemma Add.idem (h : Γ.AllNonLin) : Γ.Add Γ Γ := fun x => HypAdd.idem (h x)

lemma Add.assoc (h₁ : Γ₁.Add Γ₂ Γ₁₂) (h₂ : Γ₁₂.Add Γ₃ Γ) :
    ∃ Γ₂₃, Γ₂.Add Γ₃ Γ₂₃ ∧ Γ₁.Add Γ₂₃ Γ := by
  have := fun x => HypAdd.assoc (h₁ x) (h₂ x)
  choose f hf1 hf2 using this
  exact ⟨f, hf1, hf2⟩

lemma Add.assoc' (h₁ : Γ₂.Add Γ₃ Γ₂₃) (h₂ : Γ₁.Add Γ₂₃ Γ) :
    ∃ Γ₁₂, Γ₁.Add Γ₂ Γ₁₂ ∧ Γ₁₂.Add Γ₃ Γ := by
  have := fun x => HypAdd.assoc' (h₁ x) (h₂ x)
  choose f hf1 hf2 using this
  exact ⟨f, hf1, hf2⟩

lemma Add.interchange {A₁ A₂ A B₁ B₂ B C : Ctx n}
    (h₁ : A₁.Add A₂ A) (h₂ : B₁.Add B₂ B) (h : A.Add B C) :
    ∃ C₁ C₂, A₁.Add B₁ C₁ ∧ A₂.Add B₂ C₂ ∧ C₁.Add C₂ C := by
  have := fun x => HypAdd.interchange (h₁ x) (h₂ x) (h x)
  choose f g hf hg hfg using this
  exact ⟨f, g, hf, hg, hfg⟩

lemma AllNonLin.of_add (h : Γ₁.Add Γ₂ Γ) (h₁ : Γ₁.AllNonLin) (h₂ : Γ₂.AllNonLin) :
    Γ.AllNonLin := fun x => (h x).nonLin_of (h₁ x) (h₂ x)

lemma AllNonLin.left (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.AllNonLin) : Γ₁.AllNonLin :=
  fun x => (h x).nonLin_left (hΓ x)

lemma AllNonLin.right (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.AllNonLin) : Γ₂.AllNonLin :=
  fun x => (h x).nonLin_right (hΓ x)

lemma VarsNonLin.of_add (h : Γ₁.Add Γ₂ Γ) (h₁ : Γ₁.VarsNonLin) (h₂ : Γ₂.VarsNonLin) :
    Γ.VarsNonLin := fun i => (h (.inl i)).nonLin_of (h₁ i) (h₂ i)

lemma VarsNonLin.left (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.VarsNonLin) : Γ₁.VarsNonLin :=
  fun i => (h (.inl i)).nonLin_left (hΓ i)

lemma VarsNonLin.right (h : Γ₁.Add Γ₂ Γ) (hΓ : Γ.VarsNonLin) : Γ₂.VarsNonLin :=
  fun i => (h (.inl i)).nonLin_right (hΓ i)

lemma AllNonLin.varsNonLin (h : Γ.AllNonLin) : Γ.VarsNonLin := fun i => h (.inl i)

lemma AllNonLin.empty : (empty : Ctx n).AllNonLin := fun _ => trivial

lemma AllNonLin.refsOnly (h : Γ.AllNonLin) : Γ.refsOnly.AllNonLin := by
  rintro (i | a)
  · trivial
  · exact h (.inr a)

lemma Add.refsOnly (h : Γ₁.Add Γ₂ Γ) : Γ₁.refsOnly.Add Γ₂.refsOnly Γ.refsOnly := by
  rintro (i | a)
  · exact .noneLeft _
  · exact h (.inr a)

lemma Add.cons {h₁ h₂ h : Option Hyp} (hΓ : Γ₁.Add Γ₂ Γ) (hh : HypAdd h₁ h₂ h) :
    (Γ₁.cons h₁).Add (Γ₂.cons h₂) (Γ.cons h) := by
  rintro (i | a)
  · cases i using Fin.cases
    · exact hh
    · exact hΓ _
  · exact hΓ _

lemma Add.of_cons {h₁ h₂ h : Option Hyp} (hΓ : (Γ₁.cons h₁).Add (Γ₂.cons h₂) (Γ.cons h)) :
    Γ₁.Add Γ₂ Γ ∧ HypAdd h₁ h₂ h := by
  refine ⟨?_, hΓ (.inl 0)⟩
  rintro (i | a)
  · exact hΓ (.inl i.succ)
  · exact hΓ (.inr a)

lemma Add.set {x : Fin n ⊕ ℕ} {h₁ h₂ h : Option Hyp} (hΓ : Γ₁.Add Γ₂ Γ)
    (hh : HypAdd h₁ h₂ h) : (Γ₁.set x h₁).Add (Γ₂.set x h₂) (Γ.set x h) := by
  intro y
  by_cases hy : y = x
  · subst hy; simpa using hh
  · simp only [Ctx.set, Function.update_of_ne hy]; exact hΓ y

/-- The tail of a context (dropping variable `0`). -/
def tail (Γ : Ctx (n + 1)) : Ctx n := Sum.elim (fun i => Γ (.inl i.succ)) (fun a => Γ (.inr a))

@[simp] lemma tail_cons (Γ : Ctx n) (h : Option Hyp) : (Γ.cons h).tail = Γ := by
  funext x; rcases x with i | a <;> rfl

lemma cons_tail (Γ : Ctx (n + 1)) : Γ.tail.cons (Γ (.inl 0)) = Γ := by
  funext x; rcases x with i | a
  · cases i using Fin.cases <;> rfl
  · rfl

lemma cons_injective {Γ Γ' : Ctx n} {h h' : Option Hyp} (e : Γ.cons h = Γ'.cons h') :
    Γ = Γ' ∧ h = h' := by
  refine ⟨?_, congrFun e (.inl 0)⟩
  have := congrArg tail e
  simpa using this

lemma cons_set_succ (Γ : Ctx n) (h : Option Hyp) (i : Fin n) (h' : Option Hyp) :
    (Γ.set (.inl i) h').cons h = (Γ.cons h).set (.inl i.succ) h' := by
  funext x; rcases x with j | a
  · cases j using Fin.cases with
    | zero =>
      rw [cons_inl_zero, set_ne _ _ (by simpa using (Fin.succ_ne_zero i).symm)]; rfl
    | succ j =>
      by_cases hj : j = i
      · subst hj; simp
      · rw [cons_inl_succ, set_ne _ _ (by simpa using hj), set_ne _ _ (by simpa using hj)]
        rfl
  · simp [Ctx.set]

lemma cons_set_zero (Γ : Ctx n) (h h' : Option Hyp) :
    Γ.cons h' = (Γ.cons h).set (.inl 0) h' := by
  funext x; rcases x with j | a
  · cases j using Fin.cases with
    | zero => simp
    | succ j => rw [set_ne _ _ (by simp)]; rfl
  · simp [Ctx.set]

lemma refsOnly_cons (Γ : Ctx n) (h : Option Hyp) : (Γ.cons h).refsOnly = Γ.refsOnly.cons none := by
  funext x; rcases x with j | a
  · cases j using Fin.cases <;> rfl
  · rfl

lemma AllNonLin.cons {h : Option Hyp} (hΓ : Γ.AllNonLin) (hh : NonLin h) :
    (Γ.cons h).AllNonLin := by
  rintro (i | a)
  · cases i using Fin.cases
    · exact hh
    · exact hΓ _
  · exact hΓ _

lemma AllNonLin.of_cons {h : Option Hyp} (hΓ : (Γ.cons h).AllNonLin) :
    Γ.AllNonLin ∧ NonLin h := by
  refine ⟨?_, hΓ (.inl 0)⟩
  rintro (i | a)
  · exact hΓ (.inl i.succ)
  · exact hΓ (.inr a)

lemma set_set (Γ : Ctx n) (x : Fin n ⊕ ℕ) (h h' : Option Hyp) :
    (Γ.set x h).set x h' = Γ.set x h' := by
  simp [Ctx.set]

lemma set_eq_self {Γ : Ctx n} {x : Fin n ⊕ ℕ} {h : Option Hyp} (e : Γ x = h) :
    Γ.set x h = Γ := by
  subst e; simp [Ctx.set]

lemma set_comm (Γ : Ctx n) {x y : Fin n ⊕ ℕ} (hxy : x ≠ y) (h h' : Option Hyp) :
    (Γ.set x h).set y h' = (Γ.set y h').set x h := by
  simp [Ctx.set, Function.update_comm hxy]

end Ctx

end LCU
