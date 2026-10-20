module
public import RequestProject.LCU.RefShift

/-!
# A store-based semantics for the array primitives, and type safety

`CbnSemantics.lean` gives a substitution-based call-by-name semantics for the fragment
without array primitives.  Here we extend it with a *store* of mutable floating-point
arrays, following the array rules of the heap model (Section 3.4):

* `newArray k ⟶ *a` allocates a fresh array `a` (filled with `0`);
* `readArray (*a) k ⟶ (arr[k], *a)` reads the array;
* `writeArray (*a) k x ⟶ *a` destructively updates the array in the store;
* `deleteArray (*a) ⟶ unit`;
* `copy !u as x in t ⟶ [*θ(u)/x]t`, where `θ` renames the array references of `u` to
  fresh references pointing to copies of the arrays (rule `copy_β`); concretely `θ`
  maps `a` to `N + a` for a bound `N` above all allocated references;
* the arguments of primitives are evaluated (also under `*`), and otherwise the rules
  are those of `CbnStep`.

We prove **subject reduction** (`AStep.preserves`) and **progress** (`astep_progress`),
and hence **syntactic type safety** for closed programs (`array_type_safety`): a
well-typed closed program, started in the empty store, never gets stuck, even with
arrays and in-place updates.

**Caveat.** `deleteArray` does not free memory in this semantics: the array stays in the
store.  Safe deallocation needs the uniqueness guarantee (no other reference to the
deleted array survives), and this file does not prove that guarantee. Here array
references are typed non-linearly throughout.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Stores -/

/-- A store maps array references to arrays of floats (`none`: unallocated).
Out-of-bounds accesses are ignored, as in the paper, so arrays are total functions.
Stores are finite by construction: only finitely many references are allocated. -/
structure Store where
  /-- the array allocated at a reference, if any -/
  get : ℕ → Option (ℕ → Float)
  /-- only finitely many references are allocated -/
  finite : ∃ N, ∀ b, N ≤ b → get b = none

instance : CoeFun Store (fun _ => ℕ → Option (ℕ → Float)) := ⟨Store.get⟩

namespace Store

/-- All references from `N` on are unallocated. -/
def FreshFrom (σ : Store) (N : ℕ) : Prop := ∀ b, N ≤ b → σ b = none

/-- Update the array allocated at a reference. -/
def set (σ : Store) (a : ℕ) (v : Option (ℕ → Float)) : Store where
  get := Function.update σ.get a v
  finite := by
    obtain ⟨N, hN⟩ := σ.finite
    refine ⟨max N (a + 1), fun b hb => ?_⟩
    rw [Function.update_of_ne (by omega)]
    exact hN b (by omega)

@[simp] lemma set_apply (σ : Store) (a : ℕ) (v : Option (ℕ → Float)) (b : ℕ) :
    σ.set a v b = Function.update σ.get a v b := rfl

/-- Extend a store (whose references from `N` on are unallocated) with a copy of every
array: the copy of `a` lives at `N + a`. -/
def copyShift (σ : Store) (N : ℕ) : Store where
  get b := if N ≤ b then σ (b - N) else σ b
  finite := by
    obtain ⟨M, hM⟩ := σ.finite
    refine ⟨N + M, fun b hb => ?_⟩
    simp only [show N ≤ b by omega, if_true]
    exact hM _ (by omega)

@[simp] lemma copyShift_apply (σ : Store) (N b : ℕ) :
    σ.copyShift N b = if N ≤ b then σ (b - N) else σ b := rfl

/-- The empty store. -/
def empty : Store := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

@[simp] lemma empty_apply (b : ℕ) : Store.empty b = none := rfl

/-- Every store has a fresh bound. -/
lemma exists_freshFrom (σ : Store) : ∃ N, σ.FreshFrom N := σ.finite

end Store

/-! ## Reduction -/

/-- Partially applied primitives whose already supplied arguments are fully evaluated
(the array argument to a reference `*a`, the index to a literal `k`); the next argument
of such a term is evaluated.  This is a sub-grammar of the partially applied primitives
`PrimFun` of the paper. -/
inductive ReadyPrim (n : ℕ) : Type where
  /-- a primitive applied to no argument -/
  | const (p : Prim)
  /-- `readArray (*a)` -/
  | read₁ (a : ℕ)
  /-- `writeArray (*a)` -/
  | write₁ (a : ℕ)
  /-- `writeArray (*a) k` -/
  | write₂ (a k : ℕ)

namespace ReadyPrim

variable {n : ℕ}

/-- The embedding into terms. -/
@[simp] def toTerm : ReadyPrim n → Term n
  | const p => .prim p
  | read₁ a => .app (.prim .readArray) (.star (.ref a))
  | write₁ a => .app (.prim .writeArray) (.star (.ref a))
  | write₂ a k => .app (.app (.prim .writeArray) (.star (.ref a))) (.nat k)

/-- The embedding into the partially applied primitives of the paper. -/
def toPrimFun : ReadyPrim n → PrimFun n
  | const p => .const p
  | read₁ a => .readArray₁ (.star (.ref a))
  | write₁ a => .writeArray₁ (.star (.ref a))
  | write₂ a k => .writeArray₂ (.star (.ref a)) (.nat k)

@[simp] lemma toPrimFun_toTerm (p : ReadyPrim n) : p.toPrimFun.toTerm = p.toTerm := by
  cases p <;> rfl

end ReadyPrim

/-- `t` is (the embedding of) an element of the grammar `ReadyPrim n`. -/
def PrimReady {n : ℕ} (t : Term n) : Prop := ∃ p : ReadyPrim n, p.toTerm = t

namespace PrimReady

variable {n : ℕ}

lemma prim (p : Prim) : PrimReady (Term.prim p : Term n) := ⟨.const p, rfl⟩
lemma read₁ (a : ℕ) : PrimReady (app (Term.prim .readArray) (star (ref a)) : Term n) :=
  ⟨.read₁ a, rfl⟩
lemma write₁ (a : ℕ) : PrimReady (app (Term.prim .writeArray) (star (ref a)) : Term n) :=
  ⟨.write₁ a, rfl⟩
lemma write₂ (a k : ℕ) :
    PrimReady (app (app (Term.prim .writeArray) (star (ref a))) (nat k) : Term n) :=
  ⟨.write₂ a k, rfl⟩

lemma isPrimFun {t : Term n} : PrimReady t → IsPrimFun t
  | ⟨p, hp⟩ => ⟨p.toPrimFun, by rw [ReadyPrim.toPrimFun_toTerm, hp]⟩

end PrimReady

/-- Single-step reduction `σ ⊢ t ⟶ σ' ⊢ t'` of the store-based semantics. -/
inductive AStep : {n : ℕ} → Store → Term n → Store → Term n → Prop where
  | betaLolli {n : ℕ} (σ : Store) (t : Term (n + 1)) (u : Term n) :
      AStep σ (app (lam t) u) σ (subst1 u t)
  | betaTensor {n : ℕ} (σ : Store) (t₁ t₂ : Term n) (t : Term (n + 2)) :
      AStep σ (letPair (pair t₁ t₂) t) σ (subst2 t₁ t₂ t)
  | betaUnit {n : ℕ} (σ : Store) (t : Term n) : AStep σ (letUnit unit t) σ t
  | betaBang {n : ℕ} (σ : Store) (u : Term n) (t : Term (n + 1)) :
      AStep σ (letBang (bang u) t) σ (subst1 u t)
  | betaBorrow {n : ℕ} (σ : Store) (t : Term n) : AStep σ (borrow (star t)) σ (bang t)
  /-- `copy_β`: the arrays of `u` are copied to the fresh references `N + a`. -/
  | betaCopy {n : ℕ} (σ : Store) (N : ℕ) (u : Term n) (t : Term (n + 1)) :
      σ.FreshFrom N → AStep σ (copy (bang u) t) (σ.copyShift N) (subst1 (star (u.shiftRefs N)) t)
  | app {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term n) :
      AStep σ t σ' t' → AStep σ (app t u) σ' (app t' u)
  | letPair {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 2)) :
      AStep σ t σ' t' → AStep σ (letPair t u) σ' (letPair t' u)
  | letUnit {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term n) :
      AStep σ t σ' t' → AStep σ (letUnit t u) σ' (letUnit t' u)
  | letBang {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 1)) :
      AStep σ t σ' t' → AStep σ (letBang t u) σ' (letBang t' u)
  | borrow {n : ℕ} {σ σ' : Store} {t t' : Term n} :
      AStep σ t σ' t' → AStep σ (borrow t) σ' (borrow t')
  | copy {n : ℕ} {σ σ' : Store} {t t' : Term n} (u : Term (n + 1)) :
      AStep σ t σ' t' → AStep σ (copy t u) σ' (copy t' u)
  /-- evaluation of the next argument of a primitive -/
  | primArg {n : ℕ} {σ σ' : Store} {f t t' : Term n} :
      PrimReady f → AStep σ t σ' t' → AStep σ (app f t) σ' (app f t')
  /-- evaluation under `*` of the (unique) array argument of a primitive -/
  | primStar {n : ℕ} {σ σ' : Store} (p : Prim) {s s' : Term n} :
      AStep σ s σ' s' → AStep σ (app (prim p) (star s)) σ' (app (prim p) (star s'))
  | newArray {n : ℕ} (σ : Store) (k a : ℕ) : σ a = none →
      AStep σ (app (prim .newArray) (nat k) : Term n) (σ.set a (some fun _ => 0))
        (star (ref a))
  | readArray {n : ℕ} (σ : Store) (a k : ℕ) (arr : ℕ → Float) : σ a = some arr →
      AStep σ (app (app (prim .readArray) (star (ref a))) (nat k) : Term n) σ
        (pair (float (arr k)) (star (ref a)))
  | writeArray {n : ℕ} (σ : Store) (a k : ℕ) (x : Float) (arr : ℕ → Float) : σ a = some arr →
      AStep σ (app (app (app (prim .writeArray) (star (ref a))) (nat k)) (float x) : Term n)
        (σ.set a (some (Function.update arr k x))) (star (ref a))
  | deleteArray {n : ℕ} (σ : Store) (a : ℕ) :
      AStep σ (app (prim .deleteArray) (star (ref a)) : Term n) σ unit

/-- Multi-step reduction `σ ⊢ t ⟶* σ' ⊢ t'`. -/
inductive ASteps {n : ℕ} : Store → Term n → Store → Term n → Prop where
  | refl (σ : Store) (t : Term n) : ASteps σ t σ t
  | tail {σ σ' σ'' : Store} {t t' t'' : Term n} :
      ASteps σ t σ' t' → AStep σ' t' σ'' t'' → ASteps σ t σ'' t''

/-! ## Well-typed configurations -/

/-- A typing context `Γ` is compatible with the store `σ`: there are no variable
assumptions, array references are non-linear, and every typed reference is allocated. -/
structure ConfOK {n : ℕ} (σ : Store) (Γ : Ctx n) : Prop where
  noVars : Γ.NoVars
  refsNonLin : Γ.RefsNonLin
  alloc : ∀ a h, Γ (.inr a) = some h → σ a ≠ none

lemma ConfOK.allNonLin {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) : Γ.AllNonLin :=
  h.noVars.allNonLin h.refsNonLin

lemma ConfOK.not_alloc {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) {a : ℕ}
    (ha : σ a = none) : Γ (.inr a) = none := by
  by_contra hne
  obtain ⟨h', e⟩ := Option.ne_none_iff_exists'.1 hne
  exact h.alloc a h' e ha

/-! ## Inversion lemmas in non-linear contexts -/

section Inversion

variable {n : ℕ} {Γ : Ctx n}

lemma HasTypeD.inv_app (hΓ : Γ.AllNonLin) {f x : Term n} {B : Ty}
    (ht : HasTypeD Γ (Term.app f x) B) : ∃ A, HasTypeD Γ f (A ⊸ B) ∧ HasTypeD Γ x A := by
  cases ht with
  | app h₁ h₂ hadd =>
    exact ⟨_, h₁.mono (Ctx.Sub.of_add_left hadd) hΓ, h₂.mono (Ctx.Sub.of_add_right hadd) hΓ⟩

lemma HasTypeD.app_of (hΓ : Γ.AllNonLin) {f x : Term n} {A B : Ty}
    (h₁ : HasTypeD Γ f (A ⊸ B)) (h₂ : HasTypeD Γ x A) : HasTypeD Γ (Term.app f x) B :=
  .app h₁ h₂ (Ctx.Add.idem hΓ)

lemma HasTypeD.inv_prim {p : Prim} {T : Ty} (ht : HasTypeD Γ (Term.prim p) T) : T = p.ty := by
  cases ht; rfl

lemma HasTypeD.inv_star (hΓ : Γ.NoVars) {s : Term n} {T : Ty} (ht : HasTypeD Γ (Term.star s) T) :
    ∃ A, T = .star A ∧ HasTypeD Γ s A := by
  cases ht with
  | nec h _ => rw [hΓ.refsOnly_eq] at h; exact ⟨_, rfl, h⟩

lemma HasTypeD.star_of (hΓ : Γ.NoVars) {s : Term n} {A : Ty} (ht : HasTypeD Γ s A) :
    HasTypeD Γ (Term.star s) (.star A) :=
  .nec (by rw [hΓ.refsOnly_eq]; exact ht) (fun i => by rw [hΓ i]; trivial)

lemma HasTypeD.inv_ref {a : ℕ} {T : Ty} (ht : HasTypeD Γ (Term.ref a) T) :
    ∃ h, Γ (.inr a) = some h ∧ T = .array h.ty := by
  cases ht with
  | ref ha _ => exact ⟨_, ha, rfl⟩

end Inversion

/-! ## Subject reduction -/

lemma Store.FreshFrom.copyShift {σ : Store} {N : ℕ} (h : σ.FreshFrom N) :
    (σ.copyShift N).FreshFrom (N + N) := by
  intro b hb
  simp only [Store.copyShift_apply, show N ≤ b by omega, if_true]
  exact h _ (by omega)

/-- Reduction never deallocates arrays. -/
lemma AStep.alloc_mono {n : ℕ} {σ σ' : Store} {t t' : Term n} (hs : AStep σ t σ' t') :
    ∀ a, σ a ≠ none → σ' a ≠ none := by
  induction hs with
  | betaCopy N u t hN =>
    intro a ha
    simp only [Store.copyShift_apply]
    split_ifs with h
    · exact absurd (hN a h) ha
    · exact ha
  | newArray k b hb =>
    intro a ha
    by_cases hab : a = b
    · subst hab; simp
    · rw [Store.set_apply, Function.update_of_ne hab]; exact ha
  | writeArray b k x arr hb =>
    intro a ha
    by_cases hab : a = b
    · subst hab; simp
    · rw [Store.set_apply, Function.update_of_ne hab]; exact ha
  | app _ _ ih | letPair _ _ ih | letUnit _ _ ih | letBang _ _ ih | borrow _ ih | copy _ _ ih
  | primArg _ _ ih | primStar _ _ ih => exact ih
  | _ => exact fun _ h => h

lemma ConfOK.mono_store {n : ℕ} {σ σ' : Store} {Γ : Ctx n} (h : ConfOK σ Γ)
    (hm : ∀ a, σ a ≠ none → σ' a ≠ none) : ConfOK σ' Γ :=
  ⟨h.noVars, h.refsNonLin, fun a h' ha => hm a (h.alloc a h' ha)⟩

/-- Typing a primitive-free reduct of a `CbnStep`-rule in the same context. -/
private lemma preserves_cbn {n : ℕ} {σ : Store} {Γ : Ctx n} {t t' : Term n} {A : Ty}
    (hc : CbnStep t t') (hΓ : ConfOK σ Γ) (ht : HasTypeD Γ t A) :
    ∃ Γ', Γ.Sub Γ' ∧ ConfOK σ Γ' ∧ HasTypeD Γ' t' A :=
  ⟨Γ, Ctx.Sub.refl Γ, hΓ, hasType_iff_hasTypeD.1
    (hc.preserves hΓ.noVars hΓ.refsNonLin (hasType_iff_hasTypeD.2 ht))⟩

/-- The context extension for a freshly allocated array. -/
private lemma newArray_ctx {n : ℕ} {σ : Store} {Γ : Ctx n} (hΓ : ConfOK σ Γ) {a : ℕ}
    (ha : σ a = none) (arr : ℕ → Float) :
    Γ.Sub (Γ.set (.inr a) (some (.nonlin .float))) ∧
    ConfOK (σ.set a (some arr)) (Γ.set (.inr a) (some (.nonlin .float))) ∧
    HasTypeD (Γ.set (.inr a) (some (.nonlin .float))) (Term.star (Term.ref a))
      (.star (.array .float)) := by
  have hfresh := hΓ.not_alloc ha
  have hsub : Γ.Sub (Γ.set (.inr a) (some (.nonlin .float))) := by
    intro x h e
    by_cases hx : x = .inr a
    · subst hx; rw [hfresh] at e; cases e
    · rw [Ctx.set_ne _ _ hx]; exact e
  have hΓ' : ConfOK (σ.set a (some arr)) (Γ.set (.inr a) (some (.nonlin .float))) := by
    refine ⟨fun i => by rw [Ctx.set_ne _ _ (by simp)]; exact hΓ.noVars i, fun b => ?_,
      fun b h e => ?_⟩
    · by_cases hb : b = a
      · subst hb; simp
      · rw [Ctx.set_ne _ _ (by simpa using hb)]; exact hΓ.refsNonLin b
    · by_cases hb : b = a
      · subst hb; simp
      · rw [Store.set_apply, Function.update_of_ne hb]
        rw [Ctx.set_ne _ _ (by simpa using hb)] at e
        exact hΓ.alloc b h e
  refine ⟨hsub, hΓ', HasTypeD.star_of hΓ'.noVars ?_⟩
  refine HasTypeD.ref (h := .nonlin .float) (by simp) ?_
  rw [Ctx.set_set]
  intro x
  by_cases hx : x = .inr a
  · subst hx; simp
  · rw [Ctx.set_ne _ _ hx]; exact hΓ.allNonLin x

/-- **Subject reduction** for the store-based semantics: a reduction step of a term that
is well-typed in a context compatible with the store yields a term of the same type, in
a (possibly larger) context compatible with the new store. -/
theorem AStep.preserves {n : ℕ} {σ σ' : Store} {t t' : Term n} (hs : AStep σ t σ' t')
    {Γ : Ctx n} {A : Ty} (hΓ : ConfOK σ Γ) (ht : HasTypeD Γ t A) :
    ∃ Γ', Γ.Sub Γ' ∧ ConfOK σ' Γ' ∧ HasTypeD Γ' t' A := by
  induction hs generalizing Γ A with
  | betaLolli t u => exact preserves_cbn (.betaLolli t u) hΓ ht
  | betaTensor t₁ t₂ t => exact preserves_cbn (.betaTensor t₁ t₂ t) hΓ ht
  | betaUnit t => exact preserves_cbn (.betaUnit t) hΓ ht
  | betaBang u t => exact preserves_cbn (.betaBang u t) hΓ ht
  | betaBorrow t => exact preserves_cbn (.betaBorrow t) hΓ ht
  | betaCopy N u t hN =>
    cases ht with
    | copy h₁ h₂ hadd =>
      cases h₁ with
      | bangI _ hu =>
        -- the new context: copies of all references at `N + a`
        let Γ' : Ctx n := Sum.elim (fun i => Γ (.inl i))
          (fun b => if N ≤ b then Γ (.inr (b - N)) else Γ (.inr b))
        have hfresh : ∀ b, N ≤ b → Γ (.inr b) = none := fun b hb => hΓ.not_alloc (hN b hb)
        have hsub : Γ.Sub Γ' := by
          rintro (i | b) h e
          · exact e
          · simp only [Γ', Sum.elim_inr]
            split_ifs with hb
            · rw [hfresh b hb] at e; cases e
            · exact e
        have hΓ' : ConfOK (σ.copyShift N) Γ' := by
          refine ⟨fun i => hΓ.noVars i, fun b => ?_, fun b h e => ?_⟩
          · simp only [Γ', Sum.elim_inr]; split_ifs <;> exact hΓ.refsNonLin _
          · simp only [Γ', Sum.elim_inr] at e
            simp only [Store.copyShift_apply]
            split_ifs at e ⊢ <;> exact hΓ.alloc _ _ e
        have hall := hΓ'.allNonLin
        have hshift : Ctx.RefShift N Γ Γ' :=
          { vars := fun i => rfl
            map := fun a => by simp [Γ']
            low := fun b hb => by
              simp only [Γ', Sum.elim_inr, not_le.2 hb, if_false]; exact hΓ.refsNonLin b }
        have hu' : HasTypeD Γ' (u.shiftRefs N) _ :=
          (hu.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin).shiftRefs hshift
        have hb := h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hall
        refine ⟨Γ', hsub, hΓ', ?_⟩
        exact hasType_iff_hasTypeD.1 (HasType.subst_lin
          (hasType_iff_hasTypeD.2 (HasTypeD.star_of hΓ'.noVars hu'))
          (hasType_iff_hasTypeD.2 hb) (Ctx.Add.idem hall))
  | app u _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ h₁
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin h₁' (h₂.mono hsub hΓ'.allNonLin)⟩
  | letPair u _ ih =>
    cases ht with
    | tensorE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .tensorE h₁'
        (h₂.mono_cons₂ ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | letUnit u _ ih =>
    cases ht with
    | unitE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .unitE h₁'
        (h₂.mono ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | letBang u _ ih =>
    cases ht with
    | bangE h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .bangE h₁'
        (h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | borrow _ ih =>
    cases ht with
    | borrow h =>
      obtain ⟨Γ', hsub, hΓ', h'⟩ := ih hΓ h
      exact ⟨Γ', hsub, hΓ', .borrow h'⟩
  | copy u _ ih =>
    cases ht with
    | copy h₁ h₂ hadd =>
      obtain ⟨Γ', hsub, hΓ', h₁'⟩ := ih hΓ (h₁.mono (Ctx.Sub.of_add_left hadd) hΓ.allNonLin)
      exact ⟨Γ', hsub, hΓ', .copy h₁'
        (h₂.mono_cons ((Ctx.Sub.of_add_right hadd).trans hsub) hΓ'.allNonLin)
        (Ctx.Add.idem hΓ'.allNonLin)⟩
  | primArg _ _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨Γ', hsub, hΓ', h₂'⟩ := ih hΓ h₂
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin (h₁.mono hsub hΓ'.allNonLin) h₂'⟩
  | primStar p _ ih =>
    obtain ⟨B, h₁, h₂⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, rfl, hs⟩ := h₂.inv_star hΓ.noVars
    obtain ⟨Γ', hsub, hΓ', hs'⟩ := ih hΓ hs
    exact ⟨Γ', hsub, hΓ', .app_of hΓ'.allNonLin (h₁.mono hsub hΓ'.allNonLin)
      (.star_of hΓ'.noVars hs')⟩
  | newArray k a ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h₁, h₂, h₃⟩ := newArray_ctx hΓ ha (fun _ => 0)
    exact ⟨_, h₁, h₂, h₃⟩
  | readArray a k arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, h₄⟩ := h₁.inv_app hΓ.allNonLin
    have e := h₃.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ, .tensorI (.floatI hΓ.allNonLin) h₄
      (Ctx.Add.idem hΓ.allNonLin)⟩
  | writeArray a k x arr ha =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ.allNonLin
    obtain ⟨D, h₅, h₆⟩ := h₃.inv_app hΓ.allNonLin
    have e := h₅.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ.mono_store (AStep.writeArray (n := n) σ a k x arr ha).alloc_mono,
      h₆⟩
  | deleteArray a =>
    obtain ⟨B, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨Γ, Ctx.Sub.refl Γ, hΓ, .unitI hΓ.allNonLin⟩

end LCU

namespace LCU

open Term

/-! ## Progress -/

/-- Values of the store-based semantics: the values of the paper (Theorem 6), where the
partially applied primitives have their arguments evaluated (`ReadyPrim`). -/
inductive StoreValue (n : ℕ) : Type where
  | lam (t : Term (n + 1))
  | pair (t₁ t₂ : Term n)
  | unit
  | bang (t : Term n)
  | star (t : Term n)
  | nat (k : ℕ)
  | float (x : Float)
  | ref (a : ℕ)
  | ready (p : ReadyPrim n)

namespace StoreValue

variable {n : ℕ}

/-- The embedding into terms. -/
@[simp] def toTerm : StoreValue n → Term n
  | lam t => .lam t
  | pair t₁ t₂ => .pair t₁ t₂
  | unit => .unit
  | bang t => .bang t
  | star t => .star t
  | nat k => .nat k
  | float x => .float x
  | ref a => .ref a
  | ready p => p.toTerm

/-- The embedding into the values of the paper. -/
def toValue : StoreValue n → Value n
  | lam t => .lam t
  | pair t₁ t₂ => .pair t₁ t₂
  | unit => .unit
  | bang t => .bang t
  | star t => .star t
  | nat k => .nat k
  | float x => .float x
  | ref a => .ref a
  | ready p => .prim p.toPrimFun

@[simp] lemma toValue_toTerm (v : StoreValue n) : v.toValue.toTerm = v.toTerm := by
  cases v <;> simp [toValue]

end StoreValue

/-- `t` is a value of the store-based semantics, i.e. (the embedding of) an element of the
grammar `StoreValue n`. -/
def AValue {n : ℕ} (t : Term n) : Prop := ∃ v : StoreValue n, v.toTerm = t

namespace AValue

variable {n : ℕ}

lemma lam (t : Term (n + 1)) : AValue (Term.lam t) := ⟨.lam t, rfl⟩
lemma pair (t₁ t₂ : Term n) : AValue (Term.pair t₁ t₂) := ⟨.pair t₁ t₂, rfl⟩
lemma unit : AValue (Term.unit : Term n) := ⟨.unit, rfl⟩
lemma bang (t : Term n) : AValue (Term.bang t) := ⟨.bang t, rfl⟩
lemma star (t : Term n) : AValue (Term.star t) := ⟨.star t, rfl⟩
lemma nat (k : ℕ) : AValue (Term.nat k : Term n) := ⟨.nat k, rfl⟩
lemma float (x : Float) : AValue (Term.float x : Term n) := ⟨.float x, rfl⟩
lemma ref (a : ℕ) : AValue (Term.ref a : Term n) := ⟨.ref a, rfl⟩
lemma prim (p : Prim) : AValue (Term.prim p : Term n) := ⟨.ready (.const p), rfl⟩
lemma read₁ (a : ℕ) : AValue (app (Term.prim .readArray) (Term.star (Term.ref a)) : Term n) :=
  ⟨.ready (.read₁ a), rfl⟩
lemma write₁ (a : ℕ) : AValue (app (Term.prim .writeArray) (Term.star (Term.ref a)) : Term n) :=
  ⟨.ready (.write₁ a), rfl⟩
lemma write₂ (a k : ℕ) :
    AValue (app (app (Term.prim .writeArray) (Term.star (Term.ref a))) (Term.nat k) : Term n) :=
  ⟨.ready (.write₂ a k), rfl⟩

/-- Values of the store-based semantics are values of the paper. -/
lemma isValue {t : Term n} : AValue t → IsValue t
  | ⟨v, hv⟩ => ⟨v.toValue, by rw [StoreValue.toValue_toTerm, hv]⟩

/-- Case analysis on the values of the store-based semantics. -/
@[elab_as_elim]
theorem cases' {motive : (t : Term n) → AValue t → Prop}
    (lam : ∀ t : Term (n + 1), motive (.lam t) (.lam t))
    (pair : ∀ t₁ t₂ : Term n, motive (.pair t₁ t₂) (.pair t₁ t₂))
    (unit : motive .unit .unit)
    (bang : ∀ t : Term n, motive (.bang t) (.bang t))
    (star : ∀ t : Term n, motive (.star t) (.star t))
    (nat : ∀ k : ℕ, motive (.nat k) (.nat k))
    (float : ∀ x : Float, motive (.float x) (.float x))
    (ref : ∀ a : ℕ, motive (.ref a) (.ref a))
    (prim : ∀ p : Prim, motive (.prim p) (.prim p))
    (read₁ : ∀ a : ℕ, motive _ (.read₁ a))
    (write₁ : ∀ a : ℕ, motive _ (.write₁ a))
    (write₂ : ∀ a k : ℕ, motive _ (.write₂ a k))
    {t : Term n} (h : AValue t) : motive t h := by
  obtain ⟨v, rfl⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | (_ | _ | _ | _)
  exacts [lam _, pair _ _, unit, bang _, star _, nat _, float _, ref _, prim _, read₁ _,
    write₁ _, write₂ _ _]

end AValue

/-- The shape of a value determined by its type (canonical forms). -/
def ValShape {n : ℕ} : Ty → Term n → Prop
  | .lolli _ _, _ => True
  | .tensor _ _, v => ∃ t₁ t₂, v = pair t₁ t₂
  | .unit, v => v = unit
  | .bang _, v => ∃ u, v = bang u
  | .star _, v => ∃ u, v = star u
  | .array _, v => ∃ a, v = ref a
  | .nat, v => ∃ k, v = nat k
  | .float, v => ∃ x, v = float x

/-- **Canonical forms.** -/
lemma AValue.shape {n : ℕ} {σ : Store} {Γ : Ctx n} (hΓ : ConfOK σ Γ) {v : Term n} {T : Ty}
    (hv : AValue v) (ht : HasTypeD Γ v T) : ValShape T v := by
  cases hv using AValue.cases' with
  | read₁ a =>
    obtain ⟨C, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨-, rfl⟩ := e; trivial
  | write₁ a =>
    obtain ⟨C, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    have e := h₁.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨-, rfl⟩ := e; trivial
  | write₂ a k =>
    obtain ⟨C, h₁, -⟩ := ht.inv_app hΓ.allNonLin
    obtain ⟨D, h₂, -⟩ := h₁.inv_app hΓ.allNonLin
    have e := h₂.inv_prim
    simp only [Prim.ty, Ty.lolli.injEq] at e
    obtain ⟨-, -, rfl⟩ := e; trivial
  | prim p => rw [ht.inv_prim]; cases p <;> trivial
  | _ =>
    cases ht
    first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | rfl | trivial

lemma ConfOK.left {n : ℕ} {σ : Store} {Γ₁ Γ₂ Γ : Ctx n} (h : ConfOK σ Γ) (hadd : Γ₁.Add Γ₂ Γ) :
    ConfOK σ Γ₁ :=
  ⟨h.noVars.left hadd, h.refsNonLin.left hadd,
    fun a h' e => h.alloc a h' (Ctx.Sub.of_add_left hadd _ _ e)⟩

lemma ConfOK.right {n : ℕ} {σ : Store} {Γ₁ Γ₂ Γ : Ctx n} (h : ConfOK σ Γ) (hadd : Γ₁.Add Γ₂ Γ) :
    ConfOK σ Γ₂ := h.left hadd.comm

lemma ConfOK.refsOnly {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) : ConfOK σ Γ.refsOnly :=
  ⟨fun _ => rfl, fun a => h.refsNonLin a, fun a h' e => h.alloc a h' e⟩

lemma ConfOK.alloc_of_ref {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) {a : ℕ} {T : Ty}
    (ht : HasTypeD Γ (Term.ref a) T) : ∃ arr, σ a = some arr := by
  obtain ⟨h', e, -⟩ := ht.inv_ref
  exact Option.ne_none_iff_exists'.1 (h.alloc a h' e)

/-- Typing of the array argument of a partially applied primitive. -/
lemma ConfOK.alloc_of_app_star {n : ℕ} {σ : Store} {Γ : Ctx n} (h : ConfOK σ Γ) {p : Prim}
    {a : ℕ} {T : Ty} (ht : HasTypeD Γ (Term.app (Term.prim p) (Term.star (Term.ref a))) T) :
    ∃ arr, σ a = some arr := by
  obtain ⟨C, -, h₂⟩ := ht.inv_app h.allNonLin
  obtain ⟨D, -, h₃⟩ := h₂.inv_star h.noVars
  exact h.alloc_of_ref h₃

/-- `t` is a value or can take a step. -/
def AProg {n : ℕ} (σ : Store) (t : Term n) : Prop := AValue t ∨ ∃ σ' t', AStep σ t σ' t'

private lemma progress_aux {n : ℕ} {σ : Store} {Γ : Ctx n} {t : Term n}
    {A : Ty} (ht : HasTypeD Γ t A) (hΓ : ConfOK σ Γ) :
    AProg σ t ∧ ∀ s, t = star s → AProg σ s := by
  induction ht with
  | var hi _ => rw [hΓ.noVars] at hi; cases hi
  | abs _ _ => exact ⟨.inl (.lam _), fun _ h => by cases h⟩
  | tensorI _ _ _ _ _ => exact ⟨.inl (.pair _ _), fun _ h => by cases h⟩
  | unitI _ => exact ⟨.inl .unit, fun _ h => by cases h⟩
  | bangI _ _ _ => exact ⟨.inl (.bang _), fun _ h => by cases h⟩
  | natI _ => exact ⟨.inl (.nat _), fun _ h => by cases h⟩
  | floatI _ => exact ⟨.inl (.float _), fun _ h => by cases h⟩
  | prim _ => exact ⟨.inl (.prim _), fun _ h => by cases h⟩
  | ref _ _ => exact ⟨.inl (.ref _), fun _ h => by cases h⟩
  | nec _ _ ih =>
    refine ⟨.inl (.star _), fun s h => ?_⟩
    cases h
    exact (ih hΓ.refsOnly).1
  | borrow h₁ ih =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih hΓ).1 with hv | ⟨σ', t', hs⟩
    · obtain ⟨u, rfl⟩ := hv.shape hΓ h₁
      exact ⟨_, _, .betaBorrow _ _⟩
    · exact ⟨_, _, .borrow hs⟩
  | tensorE h₁ _ hadd ih₁ _ =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih₁ (hΓ.left hadd)).1 with hv | ⟨σ', t', hs⟩
    · obtain ⟨u₁, u₂, rfl⟩ := hv.shape (hΓ.left hadd) h₁
      exact ⟨_, _, .betaTensor _ _ _ _⟩
    · exact ⟨_, _, .letPair _ hs⟩
  | unitE h₁ _ hadd ih₁ _ =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih₁ (hΓ.left hadd)).1 with hv | ⟨σ', t', hs⟩
    · have e : _ = _ := hv.shape (hΓ.left hadd) h₁
      subst e
      exact ⟨_, _, .betaUnit _ _⟩
    · exact ⟨_, _, .letUnit _ hs⟩
  | bangE h₁ _ hadd ih₁ _ =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih₁ (hΓ.left hadd)).1 with hv | ⟨σ', t', hs⟩
    · obtain ⟨u, rfl⟩ := hv.shape (hΓ.left hadd) h₁
      exact ⟨_, _, .betaBang _ _ _⟩
    · exact ⟨_, _, .letBang _ hs⟩
  | copy h₁ _ hadd ih₁ _ =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih₁ (hΓ.left hadd)).1 with hv | ⟨σ', t', hs⟩
    · obtain ⟨u, rfl⟩ := hv.shape (hΓ.left hadd) h₁
      obtain ⟨N, hN⟩ := σ.exists_freshFrom
      exact ⟨_, _, .betaCopy _ N _ _ hN⟩
    · exact ⟨_, _, .copy _ hs⟩
  | app h₁ h₂ hadd ih₁ ih₂ =>
    refine ⟨?_, fun _ h => by cases h⟩
    have hΓ₁ := hΓ.left hadd
    have hΓ₂ := hΓ.right hadd
    rcases (ih₁ hΓ₁).1 with hv | ⟨σ', t', hs⟩
    · rcases (ih₂ hΓ₂).1 with hv₂ | ⟨σ', t', hs₂⟩
      · cases hv using AValue.cases' with
        | lam => exact .inr ⟨_, _, .betaLolli _ _ _⟩
        | prim p =>
          have e := h₁.inv_prim
          cases p with
          | newArray =>
            simp only [Prim.ty, Ty.lolli.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨k, rfl⟩ := hv₂.shape hΓ₂ h₂
            obtain ⟨N, hN⟩ := σ.exists_freshFrom
            exact .inr ⟨_, _, .newArray _ k N (hN N le_rfl)⟩
          | readArray | writeArray | deleteArray =>
            simp only [Prim.ty, Ty.lolli.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨s, rfl⟩ := hv₂.shape hΓ₂ h₂
            obtain ⟨C, e, hs⟩ := h₂.inv_star hΓ₂.noVars
            cases e
            rcases (ih₂ hΓ₂).2 s rfl with hvs | ⟨σ', s', hs'⟩
            · obtain ⟨a, rfl⟩ := hvs.shape hΓ₂ hs
              first
                | exact .inl (.read₁ a)
                | exact .inl (.write₁ a)
                | exact .inr ⟨_, _, .deleteArray _ a⟩
            · exact .inr ⟨_, _, .primStar _ hs'⟩
        | read₁ a =>
          obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ₁.allNonLin
          have e := h₃.inv_prim
          simp only [Prim.ty, Ty.lolli.injEq] at e
          obtain ⟨-, rfl, rfl⟩ := e
          obtain ⟨k, rfl⟩ := hv₂.shape hΓ₂ h₂
          obtain ⟨arr, harr⟩ := hΓ₁.alloc_of_app_star h₁
          exact .inr ⟨_, _, .readArray _ a k arr harr⟩
        | write₁ a =>
          obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ₁.allNonLin
          have e := h₃.inv_prim
          simp only [Prim.ty, Ty.lolli.injEq] at e
          obtain ⟨-, rfl, rfl⟩ := e
          obtain ⟨k, rfl⟩ := hv₂.shape hΓ₂ h₂
          exact .inl (.write₂ a k)
        | write₂ a k =>
          obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ₁.allNonLin
          obtain ⟨D, h₄, -⟩ := h₃.inv_app hΓ₁.allNonLin
          have e := h₄.inv_prim
          simp only [Prim.ty, Ty.lolli.injEq] at e
          obtain ⟨-, -, rfl, rfl⟩ := e
          obtain ⟨x, rfl⟩ := hv₂.shape hΓ₂ h₂
          obtain ⟨arr, harr⟩ := hΓ₁.alloc_of_app_star h₃
          exact .inr ⟨_, _, .writeArray _ a k x arr harr⟩
        | _ => cases h₁
      · cases hv using AValue.cases' with
        | lam => exact .inr ⟨_, _, .betaLolli _ _ _⟩
        | prim p => exact .inr ⟨_, _, .primArg (.prim p) hs₂⟩
        | read₁ a => exact .inr ⟨_, _, .primArg (.read₁ a) hs₂⟩
        | write₁ a => exact .inr ⟨_, _, .primArg (.write₁ a) hs₂⟩
        | write₂ a k => exact .inr ⟨_, _, .primArg (.write₂ a k) hs₂⟩
        | _ => cases h₁
    · exact .inr ⟨_, _, .app _ hs⟩

/-- **Progress** for the store-based semantics: a term that is well-typed in a context
compatible with a (necessarily finite) store is a value or can take a step. -/
theorem astep_progress {n : ℕ} {σ : Store} {Γ : Ctx n} {t : Term n} {A : Ty}
    (hΓ : ConfOK σ Γ) (ht : HasType Γ t A) : AValue t ∨ ∃ σ' t', AStep σ t σ' t' :=
  (progress_aux (hasType_iff_hasTypeD.1 ht) hΓ).1

/-- Subject reduction along reduction sequences. -/
theorem ASteps.preserves {n : ℕ} {σ σ' : Store} {t t' : Term n} (hs : ASteps σ t σ' t')
    {Γ : Ctx n} {A : Ty} (hΓ : ConfOK σ Γ) (ht : HasType Γ t A) :
    ∃ Γ', Γ.Sub Γ' ∧ ConfOK σ' Γ' ∧ HasType Γ' t' A := by
  induction hs with
  | refl => exact ⟨Γ, Ctx.Sub.refl Γ, hΓ, ht⟩
  | tail _ hstep ih =>
    obtain ⟨Γ', hsub, hΓ', ht'⟩ := ih ht
    obtain ⟨Γ'', hsub', hΓ'', ht''⟩ := hstep.preserves hΓ' (hasType_iff_hasTypeD.1 ht')
    exact ⟨Γ'', hsub.trans hsub', hΓ'', hasType_iff_hasTypeD.2 ht''⟩

/-- `ConfOK` holds for the empty store and the empty context. -/
lemma ConfOK.empty {n : ℕ} : ConfOK Store.empty (Ctx.empty : Ctx n) :=
  ⟨fun _ => rfl, fun _ => trivial, fun _ _ e => by cases e⟩

/-- **Syntactic type safety with arrays.** A well-typed closed program, run from the
empty store, never gets stuck: every reachable configuration is well-typed (in a
context compatible with the store) and is either a value or can take another step. -/
theorem array_type_safety {t t' : Term 0} {A : Ty} {σ : Store}
    (ht : HasType (Ctx.empty : Ctx 0) t A) (hs : ASteps Store.empty t σ t') :
    (∃ Γ, ConfOK σ Γ ∧ HasType Γ t' A) ∧ (AValue t' ∨ ∃ σ'' t'', AStep σ t' σ'' t'') := by
  obtain ⟨Γ, -, hΓ, ht'⟩ := hs.preserves ConfOK.empty ht
  exact ⟨⟨Γ, hΓ, ht'⟩, astep_progress hΓ ht'⟩

end LCU
