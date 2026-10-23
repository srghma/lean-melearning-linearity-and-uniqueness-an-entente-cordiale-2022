module
public import RequestProject.Common.Var

/-!
# Length-indexed contexts: basic operations

The type `Ctx α n` of snoc lists with `n` entries, `get`, extensionality, the lookup
judgment `Ctx.Lookup`, and `map`, `replicate`, `set`.  See `RequestProject/Common/Ctx.lean`
for an overview.
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

end Ctx
