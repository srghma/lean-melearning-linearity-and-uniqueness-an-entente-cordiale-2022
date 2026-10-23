module
public import RequestProject.LCU.Ext2_MutableArrays.ArrayPreservation

/-!
# Progress and type safety for the store-based array semantics

## Main results

* `astep_progress`: a well-typed term in a configuration compatible with the store is a
  value (`AValue`) or can take a step.  Unlike `cbn_progress`, this covers *all* terms,
  including the array primitives.
* `ASteps.preserves`: subject reduction for many steps.
* `array_type_safety`: a well-typed closed program, started in the empty store, never
  gets stuck.

## Overview

* `StoreValue n ρ` is the value grammar of this semantics: the paper's values, except
  that partially applied primitives must have *evaluated* arguments (`ReadyPrim`).
* `AValue.shape` is the canonical-forms lemma: a well-typed value has the shape
  dictated by its type (`ValShape`).
* `progress_aux` is the main induction on typing derivations.
-/

@[expose] public section

namespace LCU

open Term

/-! ## Progress -/

/-- Values of the store-based semantics: the values of the paper (Theorem 6), where the
partially applied primitives have their arguments evaluated (`ReadyPrim`). -/
inductive StoreValue (n ρ : ℕ) : Type where
  | lam (t : Term (n + 1) ρ)
  | pair (t₁ t₂ : Term n ρ)
  | unit
  | bang (t : Term n ρ)
  | star (t : Term n ρ)
  | nat (k : ℕ)
  | float (x : FloatLit)
  | ref (a : Var ρ)
  | ready (p : ReadyPrim n ρ)

namespace StoreValue

variable {n ρ : ℕ}

/-- The embedding into terms. -/
@[simp] def toTerm : StoreValue n ρ → Term n ρ
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
def toValue : StoreValue n ρ → Value n ρ
  | lam t => .lam t
  | pair t₁ t₂ => .pair t₁ t₂
  | unit => .unit
  | bang t => .bang t
  | star t => .star t
  | nat k => .nat k
  | float x => .float x
  | ref a => .ref a
  | ready p => .prim p.toPrimFun

@[simp] lemma toValue_toTerm (v : StoreValue n ρ) : v.toValue.toTerm = v.toTerm := by
  cases v <;> simp [toValue]

end StoreValue

/-- `t` is a value of the store-based semantics, i.e. (the embedding of) an element of the
grammar `StoreValue n ρ`. -/
def AValue {n ρ : ℕ} (t : Term n ρ) : Prop := ∃ v : StoreValue n ρ, v.toTerm = t

namespace AValue

variable {n ρ : ℕ}

/-- Introduction lemmas for `AValue`, one per production. -/
lemma lam (t : Term (n + 1) ρ) : AValue (Term.lam t) := ⟨.lam t, rfl⟩
lemma pair (t₁ t₂ : Term n ρ) : AValue (Term.pair t₁ t₂) := ⟨.pair t₁ t₂, rfl⟩
lemma unit : AValue (Term.unit : Term n ρ) := ⟨.unit, rfl⟩
lemma bang (t : Term n ρ) : AValue (Term.bang t) := ⟨.bang t, rfl⟩
lemma star (t : Term n ρ) : AValue (Term.star t) := ⟨.star t, rfl⟩
lemma nat (k : ℕ) : AValue (Term.nat k : Term n ρ) := ⟨.nat k, rfl⟩
lemma float (x : FloatLit) : AValue (Term.float x : Term n ρ) := ⟨.float x, rfl⟩
lemma ref (a : Var ρ) : AValue (Term.ref a : Term n ρ) := ⟨.ref a, rfl⟩
lemma prim (p : Prim) : AValue (Term.prim p : Term n ρ) := ⟨.ready (.const p), rfl⟩
lemma read₁ (a : Var ρ) : AValue (app (Term.prim .readArray) (Term.star (Term.ref a)) : Term n ρ) :=
  ⟨.ready (.read₁ a), rfl⟩
lemma write₁ (a : Var ρ) :
    AValue (app (Term.prim .writeArray) (Term.star (Term.ref a)) : Term n ρ) :=
  ⟨.ready (.write₁ a), rfl⟩
lemma write₂ (a : Var ρ) (k : ℕ) :
    AValue (app (app (Term.prim .writeArray) (Term.star (Term.ref a))) (Term.nat k) : Term n ρ) :=
  ⟨.ready (.write₂ a k), rfl⟩

/-- Values of the store-based semantics are values of the paper. -/
lemma isValue {t : Term n ρ} : AValue t → IsValue t
  | ⟨v, hv⟩ => ⟨v.toValue, by rw [StoreValue.toValue_toTerm, hv]⟩

/-- Case analysis on the values of the store-based semantics. -/
@[elab_as_elim]
theorem cases' {motive : (t : Term n ρ) → AValue t → Prop}
    (lam : ∀ t : Term (n + 1) ρ, motive (.lam t) (.lam t))
    (pair : ∀ t₁ t₂ : Term n ρ, motive (.pair t₁ t₂) (.pair t₁ t₂))
    (unit : motive .unit .unit)
    (bang : ∀ t : Term n ρ, motive (.bang t) (.bang t))
    (star : ∀ t : Term n ρ, motive (.star t) (.star t))
    (nat : ∀ k : ℕ, motive (.nat k) (.nat k))
    (float : ∀ x : FloatLit, motive (.float x) (.float x))
    (ref : ∀ a : Var ρ, motive (.ref a) (.ref a))
    (prim : ∀ p : Prim, motive (.prim p) (.prim p))
    (read₁ : ∀ a : Var ρ, motive _ (.read₁ a))
    (write₁ : ∀ a : Var ρ, motive _ (.write₁ a))
    (write₂ : ∀ (a : Var ρ) (k : ℕ), motive _ (.write₂ a k))
    {t : Term n ρ} (h : AValue t) : motive t h := by
  obtain ⟨v, rfl⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | (_ | _ | _ | _)
  exacts [lam _, pair _ _, unit, bang _, star _, nat _, float _, ref _, prim _, read₁ _,
    write₁ _, write₂ _ _]

end AValue

/-- The shape of a value determined by its type (canonical forms). -/
def ValShape {n ρ : ℕ} : Ty → Term n ρ → Prop
  | .lolli _ _, _ => True
  | .tensor _ _, v => ∃ t₁ t₂, v = pair t₁ t₂
  | .unit, v => v = unit
  | .bang _, v => ∃ u, v = bang u
  | .star _, v => ∃ u, v = star u
  | .array _, v => ∃ a, v = ref a
  | .nat, v => ∃ k, v = nat k
  | .float, v => ∃ x, v = float x

/-- **Canonical forms.** -/
lemma AValue.shape {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} (hΓ : ConfOK σ Γ) {v : Term n ρ}
    {T : Ty}
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

/-- Compatibility passes to the summands of a context. -/
lemma ConfOK.left {n ρ : ℕ} {σ : Store ρ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : ConfOK σ Γ)
    (hadd : Γ₁.Add Γ₂ Γ) : ConfOK σ Γ₁ := by
  refine ⟨h.noVars.left hadd, h.refsNonLin.left hadd, fun a h' e => h.alloc a h' ?_⟩
  have := hadd.refs.get a
  rw [e] at this
  exact this.some_of_nonLin (Ctx.all_iff.1 (TCtx.AllNonLin.right hadd h.allNonLin).refs a)

lemma ConfOK.right {n ρ : ℕ} {σ : Store ρ} {Γ₁ Γ₂ Γ : TCtx n ρ} (h : ConfOK σ Γ)
    (hadd : Γ₁.Add Γ₂ Γ) : ConfOK σ Γ₂ := h.left hadd.comm

/-- Compatibility passes to the context without variables. -/
lemma ConfOK.refsOnly {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} (h : ConfOK σ Γ) :
    ConfOK σ Γ.refsOnly :=
  ⟨rfl, h.refsNonLin, h.alloc⟩

/-- A well-typed array reference is allocated in the store. -/
lemma ConfOK.alloc_of_ref {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} (h : ConfOK σ Γ) {a : Var ρ}
    {T : Ty} (ht : HasTypeD Γ (Term.ref a) T) : ∃ arr, σ.get a = some arr := by
  obtain ⟨h', e, -⟩ := ht.inv_ref
  exact Option.ne_none_iff_exists'.1 (h.alloc a h' e)

/-- Typing of the array argument of a partially applied primitive. -/
lemma ConfOK.alloc_of_app_star {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} (h : ConfOK σ Γ)
    {p : Prim} {a : Var ρ} {T : Ty}
    (ht : HasTypeD Γ (Term.app (Term.prim p) (Term.star (Term.ref a))) T) :
    ∃ arr, σ.get a = some arr := by
  obtain ⟨C, -, h₂⟩ := ht.inv_app h.allNonLin
  obtain ⟨D, -, h₃⟩ := h₂.inv_star h.noVars
  exact h.alloc_of_ref h₃

/-- `t` is a value or can take a step. -/
def AProg {n ρ : ℕ} (σ : Store ρ) (t : Term n ρ) : Prop :=
  AValue t ∨ ∃ e σ' t', AStep σ t e σ' t'

/-- The main induction for progress.  It proves progress for `t` and, when `t = *s`,
also for `s`; the second part is needed because primitives evaluate their arguments
under `*`. -/
private lemma progress_aux {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} {t : Term n ρ}
    {A : Ty} (ht : HasTypeD Γ t A) (hΓ : ConfOK σ Γ) :
    AProg σ t ∧ ∀ s, t = star s → AProg σ s := by
  induction ht with
  | var hi _ =>
    have := hi.get; rw [show _ = _ from hΓ.noVars, Ctx.get_replicate] at this; cases this
  | abs _ _ | tensorI _ _ _ _ _ | unitI _ | bangI _ _ _ | natI _ | floatI _ | prim _ | ref _ _ =>
    refine ⟨.inl ?_, fun _ h => by cases h⟩
    first
      | exact .lam _ | exact .pair _ _ | exact .unit | exact .bang _
      | exact .nat _ | exact .float _ | exact .prim _ | exact .ref _
  | nec _ _ ih =>
    refine ⟨.inl (.star _), fun s h => ?_⟩
    cases h
    exact (ih hΓ.refsOnly).1
  | borrow h₁ ih =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih hΓ).1 with hv | ⟨e, σ', t', hs⟩
    · obtain ⟨u, rfl⟩ := hv.shape hΓ h₁
      exact ⟨_, _, _, .betaBorrow _ _⟩
    · exact ⟨_, _, _, .borrow hs⟩
  | tensorE h₁ _ hadd ih₁ _ | unitE h₁ _ hadd ih₁ _ | bangE h₁ _ hadd ih₁ _
  | copy h₁ _ hadd ih₁ _ =>
    refine ⟨.inr ?_, fun _ h => by cases h⟩
    rcases (ih₁ (hΓ.left hadd)).1 with hv | ⟨e, σ', t', hs⟩
    · have hshape := hv.shape (hΓ.left hadd) h₁
      -- `hshape` determines the head constructor of the value
      obtain ⟨_, _, rfl⟩ := hshape
      exact ⟨_, _, _, by constructor⟩
    · exact ⟨_, _, _, by constructor; exact hs⟩
  | app h₁ h₂ hadd ih₁ ih₂ =>
    refine ⟨?_, fun _ h => by cases h⟩
    have hΓ₁ := hΓ.left hadd
    have hΓ₂ := hΓ.right hadd
    rcases (ih₁ hΓ₁).1 with hv | ⟨e, σ', t', hs⟩
    · rcases (ih₂ hΓ₂).1 with hv₂ | ⟨e, σ', t', hs₂⟩
      · cases hv using AValue.cases' with
        | lam => exact .inr ⟨_, _, _, .betaLolli _ _ _⟩
        | prim p =>
          have e := h₁.inv_prim
          cases p with
          | newArray =>
            simp only [Prim.ty, Ty.lolli.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨k, rfl⟩ := hv₂.shape hΓ₂ h₂
            exact .inr ⟨_, _, _, .newArray _ k⟩
          | readArray | writeArray | deleteArray =>
            simp only [Prim.ty, Ty.lolli.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨s, rfl⟩ := hv₂.shape hΓ₂ h₂
            obtain ⟨C, e, hs⟩ := h₂.inv_star hΓ₂.noVars
            cases e
            rcases (ih₂ hΓ₂).2 s rfl with hvs | ⟨e, σ', s', hs'⟩
            · obtain ⟨a, rfl⟩ := hvs.shape hΓ₂ hs
              first
                | exact .inl (.read₁ a)
                | exact .inl (.write₁ a)
                | exact .inr ⟨_, _, _, .deleteArray _ a⟩
            · exact .inr ⟨_, _, _, .primStar _ hs'⟩
        | read₁ a =>
          obtain ⟨C, h₃, -⟩ := h₁.inv_app hΓ₁.allNonLin
          have e := h₃.inv_prim
          simp only [Prim.ty, Ty.lolli.injEq] at e
          obtain ⟨-, rfl, rfl⟩ := e
          obtain ⟨k, rfl⟩ := hv₂.shape hΓ₂ h₂
          obtain ⟨arr, harr⟩ := hΓ₁.alloc_of_app_star h₁
          exact .inr ⟨_, _, _, .readArray _ a k arr (Store.at_iff.2 harr)⟩
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
          exact .inr ⟨_, _, _, .writeArray _ a k x arr (Store.at_iff.2 harr)⟩
        | _ => cases h₁
      · cases hv using AValue.cases' with
        | lam => exact .inr ⟨_, _, _, .betaLolli _ _ _⟩
        | prim p => exact .inr ⟨_, _, _, .primArg (.prim p) hs₂⟩
        | read₁ a => exact .inr ⟨_, _, _, .primArg (.read₁ a) hs₂⟩
        | write₁ a => exact .inr ⟨_, _, _, .primArg (.write₁ a) hs₂⟩
        | write₂ a k => exact .inr ⟨_, _, _, .primArg (.write₂ a k) hs₂⟩
        | _ => cases h₁
    · exact .inr ⟨_, _, _, .app _ hs⟩

/-- **Progress** for the store-based semantics: a term that is well-typed in a context
compatible with a store is a value or can take a step. -/
theorem astep_progress {n ρ : ℕ} {σ : Store ρ} {Γ : TCtx n ρ} {t : Term n ρ} {A : Ty}
    (hΓ : ConfOK σ Γ) (ht : HasType Γ t A) : AValue t ∨ ∃ e σ' t', AStep σ t e σ' t' :=
  (progress_aux (hasType_iff_hasTypeD.1 ht) hΓ).1

/-- Subject reduction along reduction sequences. -/
theorem ASteps.preserves {n ρ ρ' : ℕ} {σ : Store ρ} {σ' : Store ρ'} {t : Term n ρ}
    {t' : Term n ρ'} (hs : ASteps σ t σ' t') {Γ : TCtx n ρ} {A : Ty} (hΓ : ConfOK σ Γ)
    (ht : HasType Γ t A) : ∃ Γ' : TCtx n ρ', ConfOK σ' Γ' ∧ HasType Γ' t' A := by
  induction hs with
  | refl => exact ⟨Γ, hΓ, ht⟩
  | tail _ hstep ih =>
    obtain ⟨Γ', hΓ', ht'⟩ := ih
    obtain ⟨Γ'', -, hΓ'', ht''⟩ := hstep.preserves hΓ' (hasType_iff_hasTypeD.1 ht')
    exact ⟨Γ'', hΓ'', hasType_iff_hasTypeD.2 ht''⟩

/-- `ConfOK` holds for the empty store and the empty context. -/
lemma ConfOK.empty {n : ℕ} : ConfOK Store.empty (TCtx.empty : TCtx n 0) :=
  ⟨rfl, .nil, fun a => a.elim0⟩

/-- **Syntactic type safety with arrays.** A well-typed closed program, run from the
empty store, never gets stuck: every reachable configuration is well-typed (in a
context compatible with the store) and is either a value or can take another step. -/
theorem array_type_safety {ρ : ℕ} {t : Term 0 0} {t' : Term 0 ρ} {A : Ty} {σ : Store ρ}
    (ht : HasType (TCtx.empty : TCtx 0 0) t A) (hs : ASteps Store.empty t σ t') :
    (∃ Γ, ConfOK σ Γ ∧ HasType Γ t' A) ∧ (AValue t' ∨ ∃ e σ'' t'', AStep σ t' e σ'' t'') := by
  obtain ⟨Γ, hΓ, ht'⟩ := hs.preserves ConfOK.empty ht
  exact ⟨⟨Γ, hΓ, ht'⟩, astep_progress hΓ ht'⟩

end LCU
