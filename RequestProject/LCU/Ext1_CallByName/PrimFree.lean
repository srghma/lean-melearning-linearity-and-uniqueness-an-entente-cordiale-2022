module
public import RequestProject.LCU.Sec3_2_Equational.EqAxiomTyping

/-!
# Primitive-free terms

`Term.PrimFree t`: no array primitive occurs in `t`.  Simplification lemmas for every
constructor, and preservation under renaming and substitution.  Progress of the
call-by-name semantics (`CbnSemantics.lean`) holds for primitive-free terms.
-/

@[expose] public section

namespace LCU

open Term

/-- The operators that are array primitives. -/
def Op.IsPrim {ρ : ℕ} (o : Op ρ) : Prop := ∃ p, o = Op.prim p

/-- A term is primitive-free if it contains no array primitive `newArray`,
`readArray`, `writeArray`, `deleteArray`. -/
def Term.PrimFree {n ρ : ℕ} (t : Term n ρ) : Prop := ¬ Binding.Tm.HasOp Op.IsPrim t

section PrimFree

variable {n ρ : ℕ}

open Binding in
/-- Unfolding `PrimFree` on an operator application. -/
lemma Term.primFree_op {o : Op ρ} {as : Args (sig ρ) n (Op.arity o)} :
    Term.PrimFree (Tm.op o as : Term n ρ) ↔ ¬ o.IsPrim ∧ ¬ Args.HasOp Op.IsPrim as := by
  simp [Term.PrimFree, Tm.hasOp_op_iff]

open Binding in
lemma Term.primFree_args {k : ℕ} {ks : List ℕ} {t : Tm (sig ρ) (n + k)}
    {as : Args (sig ρ) n ks} :
    ¬ Args.HasOp Op.IsPrim (.cons t as) ↔ Term.PrimFree t ∧ ¬ Args.HasOp Op.IsPrim as := by
  simp [Term.PrimFree, Args.hasOp_cons_iff]

@[simp] lemma Term.primFree_var (i : Var n) : (var i : Term n ρ).PrimFree := nofun

@[simp] lemma Term.primFree_lam (t : Term (n + 1) ρ) : (lam t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_app (t₁ t₂ : Term n ρ) :
    (app t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_pair (t₁ t₂ : Term n ρ) :
    (pair t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_letPair (t₁ : Term n ρ) (t₂ : Term (n + 2) ρ) :
    (letPair t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_unit : (unit : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_letUnit (t₁ t₂ : Term n ρ) :
    (letUnit t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_bang (t : Term n ρ) : (bang t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_letBang (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (letBang t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_borrow (t : Term n ρ) : (borrow t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_copy (t₁ : Term n ρ) (t₂ : Term (n + 1) ρ) :
    (copy t₁ t₂).PrimFree ↔ t₁.PrimFree ∧ t₂.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_star (t : Term n ρ) : (star t).PrimFree ↔ t.PrimFree := by
  simp [Term.primFree_op, Term.primFree_args, Op.IsPrim]
@[simp] lemma Term.primFree_nat (k : ℕ) : (nat k : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_float (x : FloatLit) : (float x : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.primFree_ref (a : Var ρ) : (ref a : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]
@[simp] lemma Term.not_primFree_prim (p : Prim) : ¬ (prim p : Term n ρ).PrimFree := by
  simp [Term.primFree_op, Op.IsPrim]

end PrimFree

/-- Renaming preserves being primitive-free. -/
lemma Term.PrimFree.rename {n m ρ : ℕ} {t : Term n ρ} (ht : t.PrimFree) (r : Var n → Var m) :
    (t.rename r).PrimFree := fun h => ht (Binding.Tm.HasOp.of_ren h)

/-- Substituting primitive-free terms preserves being primitive-free. -/
lemma Term.PrimFree.subst {n m ρ : ℕ} {t : Term n ρ} (ht : t.PrimFree) {σ : Var n → Term m ρ}
    (hσ : ∀ i, (σ i).PrimFree) : (t.subst σ).PrimFree := fun h =>
  (Binding.Tm.HasOp.of_subst h).elim ht fun ⟨i, hi⟩ => hσ i hi

lemma Term.PrimFree.subst1 {n ρ : ℕ} {s : Term n ρ} {t : Term (n + 1) ρ} (ht : t.PrimFree)
    (hs : s.PrimFree) : (t.subst1 s).PrimFree :=
  ht.subst fun i => by cases i with | zero => exact hs | succ i => exact Term.primFree_var i

lemma Term.PrimFree.subst2 {n ρ : ℕ} {s₁ s₂ : Term n ρ} {t : Term (n + 2) ρ} (ht : t.PrimFree)
    (hs₁ : s₁.PrimFree) (hs₂ : s₂.PrimFree) : (t.subst2 s₁ s₂).PrimFree :=
  ht.subst fun i => by
    cases i with
    | zero => exact hs₂
    | succ i =>
      cases i with
      | zero => exact hs₁
      | succ i => exact Term.primFree_var i

end LCU
