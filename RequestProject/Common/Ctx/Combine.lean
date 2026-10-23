module
public import RequestProject.Common.Ctx.Ren

/-!
# Length-indexed contexts: padding, combination and mapping

`Ctx.pad`, `Ctx.zipWith`, `Ctx.append`, and how `Ctx.map` interacts with the pointwise
judgments and with `Ctx.Ren`.
-/

@[expose] public section

namespace Ctx

variable {α β γ δ : Type} {n m : ℕ}

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
