module
public import RequestProject.Common.Var

/-!
# Length-indexed contexts

Contexts, heaps and stores of both formalisations are *lists* whose length is the number of
variables (or runtime names) in scope: `Ctx α n` is a snoc list of `n` entries of type
`α`.  The entry for `Var.zero` is the last one (the most recently bound variable).

* `Ctx.nil : Ctx α 0` and `Ctx.snoc Γ a : Ctx α (n + 1)` (notation `Γ ,, a`);
* `Γ.get i`: the entry of the variable `i`, by recursion on the context;
* `Ctx.Lookup Γ i a`: the inductive lookup judgment (`here` / `there`);
* `Ctx.map`, `Ctx.set`, `Ctx.replicate`, `Ctx.ofFn`;
* `Ctx.All P Γ`, `Ctx.Forall₂ R Γ Δ`, `Ctx.Forall₃ R Γ₁ Γ₂ Γ`: pointwise predicates and
  relations, defined by recursion on the contexts (`nil` / `snoc`).  Context addition and
  scaling of both papers are instances of `Forall₃` and `Forall₂`.

Equality of contexts is equality of lists: two contexts are equal when their entries are
(`Ctx.ext`), and `snoc` is injective (`Ctx.snoc_inj`).  There is no function extensionality
involved.
-/

@[expose] public section

/-- Contexts with exactly `n` entries. The last entry belongs to `Var.zero`. -/
inductive Ctx (α : Type) : ℕ → Type where
  | nil : Ctx α 0
  | snoc {n : ℕ} : Ctx α n → α → Ctx α (n + 1)
  deriving DecidableEq

@[inherit_doc] infixl:65 " ,, " => Ctx.snoc

namespace Ctx

variable {α β γ δ : Type} {n m : ℕ}

@[simp] lemma snoc_inj {Γ Δ : Ctx α n} {a b : α} : Γ ,, a = Δ ,, b ↔ Γ = Δ ∧ a = b := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma eq_nil (Γ : Ctx α 0) : Γ = .nil := by cases Γ; rfl

/-- The entry of a variable. -/
def get : {n : ℕ} → Ctx α n → Var n → α
  | _, snoc _ a, .zero => a
  | _, snoc Γ _, .succ i => Γ.get i

@[simp] lemma get_snoc_zero (Γ : Ctx α n) (a : α) : (Γ ,, a).get .zero = a := rfl
@[simp] lemma get_snoc_succ (Γ : Ctx α n) (a : α) (i : Var n) : (Γ ,, a).get (.succ i) = Γ.get i :=
  rfl

/-- The context with the given entries. -/
def ofFn : {n : ℕ} → (Var n → α) → Ctx α n
  | 0, _ => nil
  | _ + 1, f => ofFn (fun i => f (.succ i)) ,, f .zero

@[simp] lemma get_ofFn : {n : ℕ} → (f : Var n → α) → (i : Var n) → (ofFn f).get i = f i
  | _ + 1, _, .zero => rfl
  | _ + 1, f, .succ i => get_ofFn (fun i => f (.succ i)) i

/-- Contexts are determined by their entries. -/
lemma ext : {n : ℕ} → {Γ Δ : Ctx α n} → (∀ i, Γ.get i = Δ.get i) → Γ = Δ
  | 0, Γ, Δ, _ => by rw [eq_nil Γ, eq_nil Δ]
  | _ + 1, snoc Γ a, snoc Δ b, h => by
    rw [snoc_inj]
    exact ⟨ext (fun i => h (.succ i)), h .zero⟩

lemma ext_iff {Γ Δ : Ctx α n} : Γ = Δ ↔ ∀ i, Γ.get i = Δ.get i :=
  ⟨fun h _ => h ▸ rfl, ext⟩

@[simp] lemma ofFn_get (Γ : Ctx α n) : ofFn Γ.get = Γ := ext (by simp)

/-- Choice for contexts: pointwise existence of entries gives a context. -/
lemma exists_of_forall {Q : Var n → α → Prop} (h : ∀ i, ∃ a, Q i a) : ∃ Γ : Ctx α n, ∀ i, Q i (Γ.get i) := by
  choose f hf using h
  exact ⟨ofFn f, fun i => by rw [get_ofFn]; exact hf i⟩

/-! ## The lookup judgment -/

/-- `Γ ∋ i ↦ a`: in the context `Γ`, the variable `i` carries `a`. -/
inductive Lookup : {n : ℕ} → Ctx α n → Var n → α → Prop where
  | here {n : ℕ} {Γ : Ctx α n} {a : α} : Lookup (Γ ,, a) .zero a
  | there {n : ℕ} {Γ : Ctx α n} {i : Var n} {a b : α} : Lookup Γ i a → Lookup (Γ ,, b) (.succ i) a

lemma Lookup.eq {Γ : Ctx α n} {i : Var n} {a : α} (h : Γ.Lookup i a) : Γ.get i = a := by
  induction h with
  | here => rfl
  | there _ ih => exact ih

lemma Lookup.of_eq : {n : ℕ} → {Γ : Ctx α n} → {i : Var n} → {a : α} → Γ.get i = a →
    Γ.Lookup i a
  | _, snoc _ _, .zero, _, h => h ▸ .here
  | _, snoc _ _, .succ _, _, h => .there (Lookup.of_eq h)

@[simp] lemma lookup_iff {Γ : Ctx α n} {i : Var n} {a : α} : Γ.Lookup i a ↔ Γ.get i = a :=
  ⟨Lookup.eq, Lookup.of_eq⟩

lemma Lookup.unique {Γ : Ctx α n} {i : Var n} {a b : α} (h : Γ.Lookup i a) (h' : Γ.Lookup i b) :
    a = b := h.eq.symm.trans h'.eq

/-! ## Map, update and constant contexts -/

/-- Apply a function to every entry. -/
def map (f : α → β) : {n : ℕ} → Ctx α n → Ctx β n
  | _, nil => nil
  | _, snoc Γ a => snoc (Γ.map f) (f a)

@[simp] lemma map_nil (f : α → β) : (nil : Ctx α 0).map f = nil := rfl
@[simp] lemma map_snoc (f : α → β) (Γ : Ctx α n) (a : α) : (Γ ,, a).map f = Γ.map f ,, f a := rfl
@[simp] lemma get_map (f : α → β) : {n : ℕ} → (Γ : Ctx α n) → (i : Var n) →
    (Γ.map f).get i = f (Γ.get i)
  | _, snoc _ _, .zero => rfl
  | _, snoc Γ _, .succ i => get_map f Γ i

lemma map_map (f : α → β) (g : β → γ) (Γ : Ctx α n) : (Γ.map f).map g = Γ.map (g ∘ f) := by
  induction Γ with
  | nil => rfl
  | snoc Γ a ih => simp [ih]

@[simp] lemma map_id (Γ : Ctx α n) : Γ.map id = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ a ih => simp [ih]

/-- The context with all `n` entries equal to `a`. -/
def replicate : (n : ℕ) → α → Ctx α n
  | 0, _ => nil
  | n + 1, a => replicate n a ,, a

@[simp] lemma get_replicate : {n : ℕ} → (a : α) → (i : Var n) → (replicate n a).get i = a
  | _ + 1, _, .zero => rfl
  | _ + 1, a, .succ i => get_replicate a i

/-- Update the entry of a variable. -/
def set : {n : ℕ} → Ctx α n → Var n → α → Ctx α n
  | _, snoc Γ _, .zero, b => Γ ,, b
  | _, snoc Γ a, .succ i, b => Γ.set i b ,, a

@[simp] lemma set_snoc_zero (Γ : Ctx α n) (a b : α) : (Γ ,, a).set .zero b = Γ ,, b := rfl
@[simp] lemma set_snoc_succ (Γ : Ctx α n) (a b : α) (i : Var n) :
    (Γ ,, a).set (.succ i) b = Γ.set i b ,, a := rfl

@[simp] lemma get_set_same : {n : ℕ} → (Γ : Ctx α n) → (i : Var n) → (b : α) →
    (Γ.set i b).get i = b
  | _, snoc _ _, .zero, _ => rfl
  | _, snoc Γ _, .succ i, b => get_set_same Γ i b

lemma get_set_ne : {n : ℕ} → (Γ : Ctx α n) → {i j : Var n} → (b : α) → j ≠ i →
    (Γ.set i b).get j = Γ.get j
  | _, snoc _ _, .zero, .zero, _, h => absurd rfl h
  | _, snoc _ _, .zero, .succ _, _, _ => rfl
  | _, snoc _ _, .succ _, .zero, _, _ => rfl
  | _, snoc Γ _, .succ _, .succ _, b, h => get_set_ne Γ b (fun e => h (e ▸ rfl))

lemma get_set (Γ : Ctx α n) (i j : Var n) (b : α) :
    (Γ.set i b).get j = if j = i then b else Γ.get j := by
  split_ifs with h
  · subst h; exact get_set_same Γ j b
  · exact get_set_ne Γ b h

@[simp] lemma set_get (Γ : Ctx α n) (i : Var n) : Γ.set i (Γ.get i) = Γ :=
  ext fun j => by rw [get_set]; split_ifs with h <;> simp [h]

@[simp] lemma set_set (Γ : Ctx α n) (i : Var n) (a b : α) : (Γ.set i a).set i b = Γ.set i b :=
  ext fun j => by simp only [get_set]; split_ifs <;> rfl

lemma set_comm (Γ : Ctx α n) {i j : Var n} (h : i ≠ j) (a b : α) :
    (Γ.set i a).set j b = (Γ.set j b).set i a :=
  ext fun k => by
    simp only [get_set]; split_ifs with h₁ h₂ <;> first | rfl | (subst h₁; subst h₂; exact absurd rfl h)

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


/-! ## Algebra of pointwise relations

Laws of a relation `R a b c` (read `a + b = c`) on entries lift to the pointwise relation
`Forall₃ R` on contexts.  These are used for context addition in both papers. -/

section Forall₃Algebra

variable {R : α → α → α → Prop}

/-- A functional relation lifts to a functional relation. -/
lemma Forall₃.func {Γ₁ Γ₂ Γ Γ' : Ctx α n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) (h' : Forall₃ R Γ₁ Γ₂ Γ')
    (hR : ∀ {a b c c'}, R a b c → R a b c' → c = c') : Γ = Γ' := by
  induction h with
  | nil => cases h'; rfl
  | snoc _ habc ih => cases h' with | snoc h' habc' => rw [ih h', hR habc habc']

/-- Associativity lifts. -/
lemma Forall₃.assoc
    {Γ₁ Γ₂ Γ₃ Γ₁₂ Γ : Ctx α n} (h₁ : Forall₃ R Γ₁ Γ₂ Γ₁₂) (h₂ : Forall₃ R Γ₁₂ Γ₃ Γ)
    (hR : ∀ {a b ab c abc}, R a b ab → R ab c abc → ∃ bc, R b c bc ∧ R a bc abc) :
    ∃ Γ₂₃, Forall₃ R Γ₂ Γ₃ Γ₂₃ ∧ Forall₃ R Γ₁ Γ₂₃ Γ := by
  induction h₁ with
  | nil => cases Γ₃; cases Γ; exact ⟨Ctx.nil, .nil, .nil⟩
  | snoc _ habc ih =>
    cases h₂ with
    | snoc h₂ h' =>
      obtain ⟨Δ, hΔ₁, hΔ₂⟩ := ih h₂
      obtain ⟨x, hx₁, hx₂⟩ := hR habc h'
      exact ⟨Δ ,, x, .snoc hΔ₁ hx₁, .snoc hΔ₂ hx₂⟩

/-- The interchange law lifts. -/
lemma Forall₃.interchange
    {A₁ A₂ A B₁ B₂ B C : Ctx α n} (h₁ : Forall₃ R A₁ A₂ A) (h₂ : Forall₃ R B₁ B₂ B)
    (h : Forall₃ R A B C)
    (hR : ∀ {a₁ a₂ a b₁ b₂ b c}, R a₁ a₂ a → R b₁ b₂ b → R a b c →
      ∃ c₁ c₂, R a₁ b₁ c₁ ∧ R a₂ b₂ c₂ ∧ R c₁ c₂ c) :
    ∃ C₁ C₂, Forall₃ R A₁ B₁ C₁ ∧ Forall₃ R A₂ B₂ C₂ ∧ Forall₃ R C₁ C₂ C := by
  induction h₁ with
  | nil => cases h₂; cases h; exact ⟨Ctx.nil, Ctx.nil, .nil, .nil, .nil⟩
  | snoc _ ha ih =>
    cases h₂ with
    | snoc h₂ hb =>
      cases h with
      | snoc h hc =>
        obtain ⟨C₁, C₂, h₁', h₂', h'⟩ := ih h₂ h
        obtain ⟨c₁, c₂, hc₁, hc₂, hc'⟩ := hR ha hb hc
        exact ⟨C₁ ,, c₁, C₂ ,, c₂, .snoc h₁' hc₁, .snoc h₂' hc₂, .snoc h' hc'⟩

/-- A property preserved by the relation lifts. -/
lemma Forall₃.all {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P a → P b → P c) (h₁ : All P Γ₁) (h₂ : All P Γ₂) : All P Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih =>
    rw [all_snoc] at h₁ h₂
    exact .snoc (ih h₁.1 h₂.1) (hR habc h₁.2 h₂.2)

/-- A property reflected by the relation (on the left) lifts. -/
lemma Forall₃.all_left {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P c → P a) (hΓ : All P Γ) : All P Γ₁ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => rw [all_snoc] at hΓ; exact .snoc (ih hΓ.1) (hR habc hΓ.2)

/-- A property reflected by the relation (on the right) lifts. -/
lemma Forall₃.all_right {P : α → Prop} {Γ₁ Γ₂ Γ : Ctx α n} (h : Forall₃ R Γ₁ Γ₂ Γ)
    (hR : ∀ {a b c}, R a b c → P c → P b) (hΓ : All P Γ) : All P Γ₂ := by
  induction h with
  | nil => exact .nil
  | snoc _ habc ih => rw [all_snoc] at hΓ; exact .snoc (ih hΓ.1) (hR habc hΓ.2)

/-- A relation that is reflexive on entries satisfying `P` is reflexive on contexts whose
entries satisfy `P`. -/
lemma Forall₃.of_all {P : α → Prop} (hR : ∀ {a}, P a → R a a a) {Γ : Ctx α n} (h : All P Γ) :
    Forall₃ R Γ Γ Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ ha ih => exact .snoc ih (hR ha)

/-- A unit on entries gives a unit on contexts. -/
lemma Forall₃.replicate_left {e : α} (hR : ∀ a, R e a a) (Γ : Ctx α n) :
    Forall₃ R (replicate n e) Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ a ih => exact .snoc ih (hR a)

lemma Forall₃.replicate_right {e : α} (hR : ∀ a, R a e a) (Γ : Ctx α n) :
    Forall₃ R Γ (replicate n e) Γ := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ a ih => exact .snoc ih (hR a)

lemma Forall₃.eq_of_replicate_left {e : α} {Γ Γ' : Ctx α n}
    (h : Forall₃ R (replicate n e) Γ Γ') (hR : ∀ {a c}, R e a c → a = c) : Γ = Γ' := by
  induction Γ with
  | nil => cases Γ'; rfl
  | snoc Γ a ih =>
    cases Γ' with
    | snoc Γ' c =>
      rw [replicate, forall₃_snoc] at h
      rw [ih h.1, hR h.2]

lemma Forall₃.eq_of_replicate_right {e : α} {Γ Γ' : Ctx α n}
    (h : Forall₃ R Γ (replicate n e) Γ') (hR : ∀ {a c}, R a e c → a = c) : Γ = Γ' := by
  induction Γ with
  | nil => cases Γ'; rfl
  | snoc Γ a ih =>
    cases Γ' with
    | snoc Γ' c =>
      rw [replicate, forall₃_snoc] at h
      rw [ih h.1, hR h.2]

end Forall₃Algebra


/-! ## Renaming contexts

`Ren P r Γ Δ` says that `Δ` is `Γ` renamed along the injective renaming `r`, with entries
satisfying `P` at the variables outside the image of `r`.  Typing is preserved by such
renamings when `P` describes the entries that can be weakened away (non-linear or absent
hypotheses, zero-graded assumptions, …). -/

/-- `Δ` is `Γ` renamed along the injective `r`, with `P`-entries elsewhere. -/
structure Ren (P : α → Prop) (r : Var n → Var m) (Γ : Ctx α n) (Δ : Ctx α m) : Prop where
  inj : Function.Injective r
  map : ∀ i, Δ.get (r i) = Γ.get i
  off : ∀ j, (∀ i, r i ≠ j) → P (Δ.get j)

namespace Ren

variable {P : α → Prop} {r : Var n → Var m} {Γ : Ctx α n} {Δ : Ctx α m}

/-- Renamings extend under binders. -/
lemma up (h : Ren P r Γ Δ) (a : α) : Ren P (Ren.up r) (Γ ,, a) (Δ ,, a) where
  inj := _root_.Ren.up_injective h.inj
  map i := by cases i with | zero => rfl | succ i => exact h.map i
  off j hj := by
    cases j with
    | zero => exact absurd rfl (hj .zero)
    | succ j => exact h.off j (fun i e => hj (.succ i) (by simp [e]))

/-- Weakening by a new variable `Var.zero` whose entry satisfies `P`. -/
lemma succ (Γ : Ctx α n) {a : α} (ha : P a) : Ren P Var.succ Γ (Γ ,, a) where
  inj := Var.succ_injective
  map _ := rfl
  off j hj := by
    cases j with
    | zero => exact ha
    | succ j => exact absurd rfl (hj j)

/-- The identity renaming. -/
lemma refl (Γ : Ctx α n) : Ren P id Γ Γ where
  inj := Function.injective_id
  map _ := rfl
  off j hj := absurd rfl (hj j)

lemma all (h : Ren P r Γ Δ) (hΓ : All P Γ) : All P Δ :=
  all_iff.2 fun j => by
    by_cases hj : ∃ i, r i = j
    · obtain ⟨i, rfl⟩ := hj; rw [h.map]; exact hΓ.get i
    · exact h.off j (fun i e => hj ⟨i, e⟩)

lemma set (h : Ren P r Γ Δ) (i : Var n) (a : α) : Ren P r (Γ.set i a) (Δ.set (r i) a) where
  inj := h.inj
  map k := by
    by_cases hk : k = i
    · subst hk; simp
    · rw [get_set_ne _ _ (h.inj.ne hk), get_set_ne _ _ hk, h.map]
  off j hj := by
    rw [get_set_ne _ _ (fun e => hj i e.symm)]
    exact h.off j hj

/-- Picked contexts are transported along renamings. -/
lemma pick (h : Ren P r Γ Δ) {i : Var n} {a : α} (hi : Pick P Γ i a) : Pick P Δ (r i) a :=
  pick_iff.2 ⟨by rw [h.map, hi.get], fun j hj => by
    by_cases hj' : ∃ k, r k = j
    · obtain ⟨k, rfl⟩ := hj'
      rw [h.map]; exact hi.other (fun e => hj (e ▸ rfl))
    · exact h.off j (fun k e => hj' ⟨k, e⟩)⟩

open Classical in
/-- A splitting `Γ₁ + Γ₂ = Γ` of the source context can be transported to a splitting of
the renamed context, when the relation is reflexive on `P`-entries: the extra entries are
given to both parts. -/
lemma split {R : α → α → α → Prop} (hR : ∀ {a}, P a → R a a a) (h : Ren P r Γ Δ)
    {Γ₁ Γ₂ : Ctx α n} (hadd : Forall₃ R Γ₁ Γ₂ Γ) :
    ∃ Δ₁ Δ₂, Ren P r Γ₁ Δ₁ ∧ Ren P r Γ₂ Δ₂ ∧ Forall₃ R Δ₁ Δ₂ Δ := by
  let mk : Ctx α n → Ctx α m := fun Θ =>
    ofFn (fun j => if hj : ∃ i, r i = j then Θ.get hj.choose else Δ.get j)
  have hmap : ∀ Θ i, (mk Θ).get (r i) = Θ.get i := fun Θ i => by
    have hex : ∃ i', r i' = r i := ⟨i, rfl⟩
    simp only [mk, get_ofFn, dif_pos hex]
    rw [h.inj hex.choose_spec]
  have hoff : ∀ Θ j, (∀ i, r i ≠ j) → (mk Θ).get j = Δ.get j := fun Θ j hj => by
    simp only [mk, get_ofFn, dif_neg (show ¬ ∃ i, r i = j from fun ⟨i, e⟩ => hj i e)]
  refine ⟨mk Γ₁, mk Γ₂, ⟨h.inj, hmap Γ₁, fun j hj => by rw [hoff _ j hj]; exact h.off j hj⟩,
    ⟨h.inj, hmap Γ₂, fun j hj => by rw [hoff _ j hj]; exact h.off j hj⟩, ?_⟩
  refine forall₃_iff.2 fun j => ?_
  by_cases hj : ∃ i, r i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [hmap, hmap, h.map]; exact hadd.get i
  · have hj' : ∀ i, r i ≠ j := fun i e => hj ⟨i, e⟩
    rw [hoff _ j hj', hoff _ j hj']
    exact hR (h.off j hj')

end Ren

/-! ## Padding and pointwise combination

A runtime configuration grows *at index zero*: the new variables (or runtime names) of a
reduction step are the most recent ones.  `Γ.pad a d` extends `Γ` by `d` new entries `a`;
the old entries are found at `Var.shiftN d i`. -/

/-- Extend a context by `d` new entries `a` (bound at the indices `0, …, d-1`). -/
def pad (Γ : Ctx α n) (a : α) : (d : ℕ) → Ctx α (n + d)
  | 0 => Γ
  | d + 1 => pad Γ a d ,, a

@[simp] lemma pad_zero (Γ : Ctx α n) (a : α) : Γ.pad a 0 = Γ := rfl
@[simp] lemma pad_succ (Γ : Ctx α n) (a : α) (d : ℕ) : Γ.pad a (d + 1) = Γ.pad a d ,, a := rfl

@[simp] lemma get_pad_shiftN (Γ : Ctx α n) (a : α) : (d : ℕ) → (i : Var n) →
    (Γ.pad a d).get (Var.shiftN d i) = Γ.get i
  | 0, _ => rfl
  | d + 1, i => get_pad_shiftN Γ a d i

lemma get_pad_new (Γ : Ctx α n) (a : α) : (d : ℕ) → (j : Var (n + d)) →
    (∀ i, Var.shiftN d i ≠ j) → (Γ.pad a d).get j = a
  | 0, j, h => absurd rfl (h j)
  | d + 1, j, h => by
    change Var (n + d + 1) at j
    cases j with
    | zero => rfl
    | succ j => exact get_pad_new Γ a d j (fun i e => h i (by simp [e]))

lemma map_pad (f : α → β) (Γ : Ctx α n) (a : α) : (d : ℕ) →
    (Γ.pad a d).map f = (Γ.map f).pad (f a) d
  | 0 => rfl
  | d + 1 => by simp [map_pad f Γ a d]

@[simp] lemma pad_replicate (a : α) : (d : ℕ) → (replicate n a).pad a d = replicate (n + d) a
  | 0 => rfl
  | d + 1 => by simp only [pad_succ, pad_replicate a d]; rfl

lemma pad_set (Γ : Ctx α n) (a : α) (d : ℕ) (i : Var n) (b : α) :
    (Γ.set i b).pad a d = (Γ.pad a d).set (Var.shiftN d i) b := by
  induction d with
  | zero => rfl
  | succ d ih => simp [ih]

/-- Padding is a renaming along `Var.shiftN d`, when the new entries satisfy `P`. -/
lemma Ren.pad {P : α → Prop} (Γ : Ctx α n) {a : α} (ha : P a) (d : ℕ) :
    Ren P (Var.shiftN d) Γ (Γ.pad a d) where
  inj := Var.shiftN_injective d
  map := get_pad_shiftN Γ a d
  off j hj := by rw [get_pad_new Γ a d j hj]; exact ha

lemma All.pad {P : α → Prop} {Γ : Ctx α n} (h : All P Γ) {a : α} (ha : P a) (d : ℕ) :
    All P (Γ.pad a d) := (Ren.pad Γ ha d).all h

lemma Forall₃.pad {R : α → β → γ → Prop} {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n}
    (h : Forall₃ R Γ₁ Γ₂ Γ) {a : α} {b : β} {c : γ} (habc : R a b c) (d : ℕ) :
    Forall₃ R (Γ₁.pad a d) (Γ₂.pad b d) (Γ.pad c d) := by
  induction d with
  | zero => exact h
  | succ d ih => exact .snoc ih habc

/-- Pointwise combination of two contexts. -/
def zipWith (f : α → β → γ) : {n : ℕ} → Ctx α n → Ctx β n → Ctx γ n
  | _, nil, nil => nil
  | _, snoc Γ a, snoc Δ b => snoc (zipWith f Γ Δ) (f a b)

@[simp] lemma zipWith_snoc (f : α → β → γ) (Γ : Ctx α n) (Δ : Ctx β n) (a : α) (b : β) :
    zipWith f (Γ ,, a) (Δ ,, b) = zipWith f Γ Δ ,, f a b := rfl

@[simp] lemma get_zipWith (f : α → β → γ) : {n : ℕ} → (Γ : Ctx α n) → (Δ : Ctx β n) →
    (i : Var n) → (zipWith f Γ Δ).get i = f (Γ.get i) (Δ.get i)
  | _, snoc _ _, snoc _ _, .zero => rfl
  | _, snoc Γ _, snoc Δ _, .succ i => get_zipWith f Γ Δ i

/-- Appending contexts: the entries of `Δ` are the most recent ones. -/
def append (Γ : Ctx α n) : {m : ℕ} → Ctx α m → Ctx α (n + m)
  | _, nil => Γ
  | _, snoc Δ a => snoc (append Γ Δ) a

@[simp] lemma get_append_shiftN (Γ : Ctx α n) : {m : ℕ} → (Δ : Ctx α m) → (i : Var n) →
    (Γ.append Δ).get (Var.shiftN m i) = Γ.get i
  | _, nil, _ => rfl
  | _, snoc Δ _, i => get_append_shiftN Γ Δ i

@[simp] lemma get_append_lowAdd (Γ : Ctx α n) : {m : ℕ} → (Δ : Ctx α m) → (i : Var m) →
    (Γ.append Δ).get (Var.lowAdd i) = Δ.get i
  | _, snoc _ _, .zero => rfl
  | _, snoc Δ _, .succ i => get_append_lowAdd Γ Δ i

lemma All.append {P : α → Prop} {Γ : Ctx α n} {Δ : Ctx α m} (hΓ : All P Γ) (hΔ : All P Δ) :
    All P (Γ.append Δ) := by
  induction hΔ with
  | nil => exact hΓ
  | snoc _ ha ih => exact .snoc ih ha

/-! ## Mapping and pointwise judgments -/

@[simp] lemma map_replicate (f : α → β) (a : α) : (k : ℕ) → (replicate k a).map f = replicate k (f a)
  | 0 => rfl
  | k + 1 => by simp only [replicate, map_snoc, map_replicate f a k]

lemma Lookup.map (f : α → β) {Γ : Ctx α n} {i : Var n} {a : α} (h : Γ.Lookup i a) :
    (Γ.map f).Lookup i (f a) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

lemma All.map {P : α → Prop} {Q : β → Prop} (f : α → β) (hf : ∀ a, P a → Q (f a)) {Γ : Ctx α n}
    (h : All P Γ) : All Q (Γ.map f) := by
  induction h with
  | nil => exact .nil
  | snoc _ ha ih => exact .snoc ih (hf _ ha)

lemma Pick.map {P : α → Prop} {Q : β → Prop} (f : α → β) (hf : ∀ a, P a → Q (f a))
    {Γ : Ctx α n} {i : Var n} {a : α} (h : Pick P Γ i a) : Pick Q (Γ.map f) i (f a) := by
  induction h with
  | here hΓ => exact .here (hΓ.map f hf)
  | there _ hb ih => exact .there ih (hf _ hb)

lemma Forall₂.map {R : α → β → Prop} {S : γ → δ → Prop} (f : α → γ) (g : β → δ)
    (hfg : ∀ a b, R a b → S (f a) (g b)) {Γ : Ctx α n} {Δ : Ctx β n} (h : Forall₂ R Γ Δ) :
    Forall₂ S (Γ.map f) (Δ.map g) := by
  induction h with
  | nil => exact .nil
  | snoc _ hab ih => exact .snoc ih (hfg _ _ hab)

lemma Forall₃.map {α' β' γ' : Type} {R : α → β → γ → Prop} {S : α' → β' → γ' → Prop}
    (f : α → α') (g : β → β') (h : γ → γ') (hfgh : ∀ a b c, R a b c → S (f a) (g b) (h c))
    {Γ₁ : Ctx α n} {Γ₂ : Ctx β n} {Γ : Ctx γ n} (hR : Forall₃ R Γ₁ Γ₂ Γ) :
    Forall₃ S (Γ₁.map f) (Γ₂.map g) (Γ.map h) := by
  induction hR with
  | nil => exact .nil
  | snoc _ habc ih => exact .snoc ih (hfgh _ _ _ habc)

lemma Ren.mapCtx {P : α → Prop} {Q : β → Prop} (f : α → β) (hf : ∀ a, P a → Q (f a))
    {r : Var n → Var m} {Γ : Ctx α n} {Δ : Ctx α m} (h : Ren P r Γ Δ) :
    Ren Q r (Γ.map f) (Δ.map f) where
  inj := h.inj
  map i := by simp [h.map]
  off j hj := by rw [get_map]; exact hf _ (h.off j hj)

lemma Ren.replicate {P : α → Prop} {a : α} (ha : P a) {r : Var n → Var m}
    (hr : Function.Injective r) : Ren P r (replicate n a) (replicate m a) where
  inj := hr
  map i := by simp
  off j _ := by rw [get_replicate]; exact ha

end Ctx
