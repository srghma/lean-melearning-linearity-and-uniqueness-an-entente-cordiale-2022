module
public import RequestProject.Common.Ctx.Basic

/-!
# Length-indexed contexts: pointwise predicates and relations

`Ctx.All P Γ`, `Ctx.Forall₂ R Γ Δ`, `Ctx.Forall₃ R Γ₁ Γ₂ Γ`, and the judgment
`Ctx.Pick P Γ i a` ("`Γ` is `Γ'` with `i : a`, all other entries satisfy `P`").
-/

@[expose] public section

namespace Ctx

variable {α β γ δ : Type} {n m : ℕ}

/-! ## Pointwise predicates and relations -/

/-- Every entry satisfies `P`. -/
inductive All (P : α → Prop) : {n : ℕ} → Ctx α n → Prop where
  | nil : All P nil
  | snoc {n : ℕ} {Γ : Ctx α n} {a : α} : All P Γ → P a → All P (Γ ,, a)

@[simp] lemma all_nil (P : α → Prop) : All P (nil : Ctx α 0) := .nil
@[simp] lemma all_snoc {P : α → Prop} {Γ : Ctx α n} {a : α} : All P (Γ ,, a) ↔ All P Γ ∧ P a :=
  ⟨fun h => by cases h with | snoc h ha => exact ⟨h, ha⟩, fun ⟨h, ha⟩ => .snoc h ha⟩

lemma all_iff {P : α → Prop} {Γ : Ctx α n} : All P Γ ↔ ∀ i, P (Γ.get i) := by
  induction Γ with
  | nil => exact ⟨fun _ i => (nomatch i), fun _ => .nil⟩
  | snoc Γ a ih =>
    rw [all_snoc, ih]
    exact ⟨fun ⟨h, ha⟩ i => by cases i with | zero => exact ha | succ i => exact h i,
      fun h => ⟨fun i => h (.succ i), h .zero⟩⟩

lemma All.get {P : α → Prop} {Γ : Ctx α n} (h : All P Γ) (i : Var n) : P (Γ.get i) :=
  all_iff.1 h i

lemma All.imp {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {Γ : Ctx α n} (h : All P Γ) : All Q Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ ha ih => exact .snoc ih (hPQ _ ha)

lemma all_replicate {P : α → Prop} {a : α} (ha : P a) : (n : ℕ) → All P (replicate n a)
  | 0 => .nil
  | n + 1 => .snoc (all_replicate ha n) ha

lemma All.set {P : α → Prop} {Γ : Ctx α n} (h : All P Γ) (i : Var n) {b : α} (hb : P b) :
    All P (Γ.set i b) :=
  all_iff.2 fun j => by rw [get_set]; split_ifs; exacts [hb, h.get j]

/-- Pointwise relation between two contexts. -/
inductive Forall₂ (R : α → β → Prop) : {n : ℕ} → Ctx α n → Ctx β n → Prop where
  | nil : Forall₂ R nil nil
  | snoc {n : ℕ} {Γ : Ctx α n} {Δ : Ctx β n} {a : α} {b : β} :
      Forall₂ R Γ Δ → R a b → Forall₂ R (Γ ,, a) (Δ ,, b)

@[simp] lemma forall₂_snoc {R : α → β → Prop} {Γ : Ctx α n} {Δ : Ctx β n} {a : α} {b : β} :
    Forall₂ R (Γ ,, a) (Δ ,, b) ↔ Forall₂ R Γ Δ ∧ R a b :=
  ⟨fun h => by cases h with | snoc h hab => exact ⟨h, hab⟩, fun ⟨h, hab⟩ => .snoc h hab⟩

lemma forall₂_iff {R : α → β → Prop} {Γ : Ctx α n} {Δ : Ctx β n} :
    Forall₂ R Γ Δ ↔ ∀ i, R (Γ.get i) (Δ.get i) := by
  induction Γ with
  | nil => cases Δ; exact ⟨fun _ i => (nomatch i), fun _ => .nil⟩
  | snoc Γ a ih =>
    cases Δ with
    | snoc Δ b =>
      rw [forall₂_snoc, ih]
      exact ⟨fun ⟨h, hab⟩ i => by cases i with | zero => exact hab | succ i => exact h i,
        fun h => ⟨fun i => h (.succ i), h .zero⟩⟩

lemma Forall₂.get {R : α → β → Prop} {Γ : Ctx α n} {Δ : Ctx β n} (h : Forall₂ R Γ Δ) (i : Var n) :
    R (Γ.get i) (Δ.get i) :=
  forall₂_iff.1 h i

lemma Forall₂.imp {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) {Γ : Ctx α n} {Δ : Ctx β n}
    (h : Forall₂ R Γ Δ) : Forall₂ S Γ Δ := by
  induction h with
  | nil => exact .nil
  | snoc _ hab ih => exact .snoc ih (hRS _ _ hab)

/-- Pointwise relation between three contexts. -/
inductive Forall₃ (R : α → β → γ → Prop) : {n : ℕ} → Ctx α n → Ctx β n → Ctx γ n → Prop where
  | nil : Forall₃ R nil nil nil
  | snoc {n : ℕ} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n} {a : α} {b : β} {c : γ} :
      Forall₃ R Γ₁ Γ₂ Γ → R a b c → Forall₃ R (Γ₁ ,, a) (Γ₂ ,, b) (Γ ,, c)

@[simp] lemma forall₃_snoc {R : α → β → γ → Prop} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n}
    {a : α} {b : β} {c : γ} :
    Forall₃ R (Γ₁ ,, a) (Γ₂ ,, b) (Γ ,, c) ↔ Forall₃ R Γ₁ Γ₂ Γ ∧ R a b c :=
  ⟨fun h => by cases h with | snoc h habc => exact ⟨h, habc⟩, fun ⟨h, habc⟩ => .snoc h habc⟩

lemma forall₃_iff {R : α → β → γ → Prop} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n} :
    Forall₃ R Γ₁ Γ₂ Γ ↔ ∀ i, R (Γ₁.get i) (Γ₂.get i) (Γ.get i) := by
  induction Γ₁ with
  | nil => cases Γ₂; cases Γ; exact ⟨fun _ i => (nomatch i), fun _ => .nil⟩
  | snoc Γ₁ a ih =>
    cases Γ₂ with
    | snoc Γ₂ b =>
      cases Γ with
      | snoc Γ c =>
        rw [forall₃_snoc, ih]
        exact ⟨fun ⟨h, habc⟩ i => by cases i with | zero => exact habc | succ i => exact h i,
          fun h => ⟨fun i => h (.succ i), h .zero⟩⟩

lemma Forall₃.get {R : α → β → γ → Prop} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) (i : Var n) : R (Γ₁.get i) (Γ₂.get i) (Γ.get i) :=
  forall₃_iff.1 h i

lemma Forall₃.imp {R S : α → β → γ → Prop} (hRS : ∀ a b c, R a b c → S a b c)
    {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n} (h : Forall₃ R Γ₁ Γ₂ Γ) : Forall₃ S Γ₁ Γ₂ Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => exact .snoc ih (hRS _ _ _ habc)

lemma Forall₃.swap {R : α → α → γ → Prop} {Γ₁ Γ₂ : Ctx α n} {Γ : Ctx γ n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) (hR : ∀ {a b c}, R a b c → R b a c) : Forall₃ R Γ₂ Γ₁ Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => exact .snoc ih (hR habc)

lemma Forall₃.set {R : α → β → γ → Prop} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) (i : Var n) {a : α} {b : β} {c : γ} (habc : R a b c) :
    Forall₃ R (Γ₁.set i a) (Γ₂.set i b) (Γ.set i c) :=
  forall₃_iff.2 fun j => by simp only [get_set]; split_ifs; exacts [habc, h.get j]


/-! ## Picking one entry

`Pick P Γ i a` says that `Γ` has the shape "`Γ'` with `i : a`" in which every *other*
entry satisfies `P`.  It is the shape of the contexts of variable rules, such as
`[Γ], x : A ⊢ x : A` or `0 · Γ, x : A ⊢ x : A`. -/

/-- `Γ` is `Γ'` extended by `i ↦ a`, where every other entry satisfies `P`. -/
inductive Pick (P : α → Prop) : {n : ℕ} → Ctx α n → Var n → α → Prop where
  | here {n : ℕ} {Γ : Ctx α n} {a : α} : All P Γ → Pick P (Γ ,, a) .zero a
  | there {n : ℕ} {Γ : Ctx α n} {i : Var n} {a b : α} :
      Pick P Γ i a → P b → Pick P (Γ ,, b) (.succ i) a

lemma pick_iff {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a : α} :
    Pick P Γ i a ↔ Γ.get i = a ∧ ∀ j, j ≠ i → P (Γ.get j) := by
  constructor
  · intro h
    induction h with
    | here hΓ => exact ⟨rfl, fun j hj => by cases j with | zero => exact absurd rfl hj | succ j => exact hΓ.get j⟩
    | there _ hb ih =>
      refine ⟨ih.1, fun j hj => ?_⟩
      cases j with
      | zero => exact hb
      | succ j => exact ih.2 j (fun e => hj (e ▸ rfl))
  · rintro ⟨rfl, h⟩
    induction Γ with
    | nil => exact nomatch i
    | snoc Γ b ih =>
      cases i with
      | zero => exact .here (all_iff.2 fun j => h (.succ j) (Var.succ_ne_zero j))
      | succ i =>
        exact .there (ih (i := i) (fun j hj => h (.succ j) (fun e => hj (Var.succ_injective e))))
          (h .zero (Var.zero_ne_succ i))

lemma Pick.get {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a : α} (h : Pick P Γ i a) :
    Γ.get i = a := (pick_iff.1 h).1

lemma Pick.other {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a : α} (h : Pick P Γ i a) {j : Var n}
    (hj : j ≠ i) : P (Γ.get j) := (pick_iff.1 h).2 j hj

/-- In a context picked at `i`, the context with `i` updated to an entry satisfying `P`
satisfies `P` everywhere. -/
lemma Pick.all_set {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a b : α} (h : Pick P Γ i a)
    (hb : P b) : All P (Γ.set i b) :=
  all_iff.2 fun j => by rw [get_set]; split_ifs with hj; exacts [hb, h.other hj]


/-- Updating the picked entry keeps the shape. -/
lemma Pick.set {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a : α} (h : Pick P Γ i a) (b : α) :
    Pick P (Γ.set i b) i b :=
  pick_iff.2 ⟨get_set_same Γ i b, fun j hj => by rw [get_set_ne Γ b hj]; exact h.other hj⟩

/-- An entry not satisfying `P` in a picked context is the picked one. -/
lemma Pick.eq_of_not {P : α → Prop} {Γ : Ctx α n} {i j : Var n} {a : α} (h : Pick P Γ i a)
    (hj : ¬ P (Γ.get j)) : j = i := by
  by_contra hne; exact hj (h.other hne)

/-- Lifting a picked context under a binder. -/
lemma Pick.snoc {P : α → Prop} {Γ : Ctx α n} {i : Var n} {a b : α} (h : Pick P Γ i a) (hb : P b) :
    Pick P (Γ ,, b) (.succ i) a := .there h hb


/-- Restricting a picked context along an injective renaming whose image contains the
picked variable. -/
lemma Pick.comp {P : α → Prop} {Γ : Ctx α m} {r : Var n → Var m} (hr : Function.Injective r)
    {j : Var n} {a : α} (h : Pick P Γ (r j) a) : Pick P (ofFn (fun k => Γ.get (r k))) j a :=
  pick_iff.2 ⟨by rw [get_ofFn, h.get], fun k hk => by rw [get_ofFn]; exact h.other (hr.ne hk)⟩

/-- If the variable `i` is picked with an entry not satisfying `P`, it is the only such
variable. -/
lemma Pick.unique {P : α → Prop} {Γ : Ctx α n} {i j : Var n} {a b : α} (hi : Pick P Γ i a)
    (hj : Pick P Γ j b) (ha : ¬ P a) : i = j ∧ a = b := by
  by_contra hne
  by_cases hij : i = j
  · subst hij; exact hne ⟨rfl, hi.get.symm.trans hj.get⟩
  · exact ha (hi.get ▸ hj.other hij)

end Ctx
