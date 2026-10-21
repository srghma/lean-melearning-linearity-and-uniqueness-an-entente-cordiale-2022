module
public import RequestProject.LCU.Sec3_1_Calculus.Syntax

/-!
# Renaming and substitution of de Bruijn terms

Parallel renaming `Term.rename ρ` (with `ρ : Fin n → Fin m`) and parallel substitution
`Term.subst σ` (with `σ : Fin n → Term m`) for the intrinsically scoped terms
`Term n`.  Going under a binder shifts the map with `Ren.up` / `Subst.up`, which keep
index `0` fixed and shift all other indices by one.

* `Term.subst1 s t` is the single substitution `[s/x]t` for the variable bound by a
  one-variable binder (index `0` of `t : Term (n + 1)`).
* `Term.subst2 s₁ s₂ t` is the double substitution `[s₁/x, s₂/y]t` used by
  `let (x, y) = …`, where `y` is index `0` and `x` is index `1`.
* `renameRefs θ t` renames the runtime array references (not variables) of `t`; it is
  the renaming `θ` of the heap rule `copy_β`.

The usual laws (`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`,
`subst_var`, ...) are proved by induction on terms after proving the corresponding
law for the lifted maps.
-/

@[expose] public section

namespace LCU

namespace Term

/-! ## Renaming -/

/-- Lifting a renaming under a binder. -/
def Ren.up {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] lemma Ren.up_zero {n m : ℕ} (ρ : Fin n → Fin m) : Ren.up ρ 0 = 0 := rfl
@[simp] lemma Ren.up_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    Ren.up ρ i.succ = (ρ i).succ := rfl

/-- Simultaneous renaming of free variables. -/
def rename : {n m : ℕ} → (Fin n → Fin m) → Term n → Term m
  | _, _, ρ, var i => var (ρ i)
  | _, _, ρ, lam t => lam (rename (Ren.up ρ) t)
  | _, _, ρ, app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, pair t₁ t₂ => pair (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, letPair t₁ t₂ => letPair (rename ρ t₁) (rename (Ren.up (Ren.up ρ)) t₂)
  | _, _, _, unit => unit
  | _, _, ρ, letUnit t₁ t₂ => letUnit (rename ρ t₁) (rename ρ t₂)
  | _, _, ρ, bang t => bang (rename ρ t)
  | _, _, ρ, letBang t₁ t₂ => letBang (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, borrow t => borrow (rename ρ t)
  | _, _, ρ, copy t₁ t₂ => copy (rename ρ t₁) (rename (Ren.up ρ) t₂)
  | _, _, ρ, star t => star (rename ρ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, _, ref a => ref a

/-! ## Substitution -/

/-- Lifting a substitution under a binder. -/
def Subst.up {n m : ℕ} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (var 0) (fun i => rename Fin.succ (σ i))

@[simp] lemma Subst.up_zero {n m : ℕ} (σ : Fin n → Term m) : Subst.up σ 0 = var 0 := rfl
@[simp] lemma Subst.up_succ {n m : ℕ} (σ : Fin n → Term m) (i : Fin n) :
    Subst.up σ i.succ = rename Fin.succ (σ i) := rfl

/-- Simultaneous (capture-avoiding) substitution of free variables. -/
def subst : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
  | _, _, σ, var i => σ i
  | _, _, σ, lam t => lam (subst (Subst.up σ) t)
  | _, _, σ, app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | _, _, σ, pair t₁ t₂ => pair (subst σ t₁) (subst σ t₂)
  | _, _, σ, letPair t₁ t₂ => letPair (subst σ t₁) (subst (Subst.up (Subst.up σ)) t₂)
  | _, _, _, unit => unit
  | _, _, σ, letUnit t₁ t₂ => letUnit (subst σ t₁) (subst σ t₂)
  | _, _, σ, bang t => bang (subst σ t)
  | _, _, σ, letBang t₁ t₂ => letBang (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, borrow t => borrow (subst σ t)
  | _, _, σ, copy t₁ t₂ => copy (subst σ t₁) (subst (Subst.up σ) t₂)
  | _, _, σ, star t => star (subst σ t)
  | _, _, _, nat k => nat k
  | _, _, _, float x => float x
  | _, _, _, prim p => prim p
  | _, _, _, ref a => ref a

/-- Single substitution `[s/x]t` of `s` for the variable `x = 0` bound in `t`. -/
def subst1 {n : ℕ} (s : Term n) (t : Term (n + 1)) : Term n :=
  subst (Fin.cons s var) t

/-- Double substitution `[s₁/x, s₂/y]t` for `t` the body of a `let (x, y) = _ in t`
(so `y` is index `0` and `x` is index `1`). -/
def subst2 {n : ℕ} (s₁ s₂ : Term n) (t : Term (n + 2)) : Term n :=
  subst (Fin.cons s₂ (Fin.cons s₁ var)) t

/-! ## Basic lemmas about renaming and substitution -/

lemma Ren.up_id {n : ℕ} : Ren.up (id : Fin n → Fin n) = id := by
  funext i; cases i using Fin.cases <;> rfl

lemma Ren.up_comp {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    Ren.up (ρ' ∘ ρ) = Ren.up ρ' ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

/-- Renaming along the identity does nothing. -/
lemma rename_id {n : ℕ} (t : Term n) : rename id t = t := by
  induction t <;> simp only [rename, Ren.up_id, id_eq, *]

/-- Renamings compose. -/
lemma rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Term n) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m k <;> simp only [rename, Ren.up_comp, Function.comp_apply, *]

lemma Subst.up_var {n : ℕ} : Subst.up (var : Fin n → Term n) = var := by
  funext i; cases i using Fin.cases <;> rfl

/-- Substituting every variable by itself does nothing. -/
lemma subst_var {n : ℕ} (t : Term n) : subst var t = t := by
  induction t <;> simp only [subst, Subst.up_var, *]

lemma Subst.up_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    Subst.up (var ∘ ρ) = var ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

/-- A renaming is a special substitution (by variables). -/
lemma subst_ren {n m : ℕ} (ρ : Fin n → Fin m) (t : Term n) :
    subst (var ∘ ρ) t = rename ρ t := by
  induction t generalizing m <;> simp only [subst, rename, Subst.up_ren, Function.comp_apply, *]

lemma Subst.up_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    Subst.up (σ ∘ ρ) = Subst.up σ ∘ Ren.up ρ := by
  funext i; cases i using Fin.cases <;> rfl

/-- Substitution after renaming is substitution along the composite. -/
lemma subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) (t : Term n) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m k <;> simp only [subst, rename, Subst.up_rename, Function.comp_apply, *]

lemma Subst.up_rename' {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    Subst.up (rename ρ ∘ σ) = rename (Ren.up ρ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp [Subst.up, rename_rename]; rfl

/-- Renaming after substitution is substitution along the renamed map. -/
lemma rename_subst {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) (t : Term n) :
    rename ρ (subst σ t) = subst (rename ρ ∘ σ) t := by
  induction t generalizing m k <;> simp only [subst, rename, Subst.up_rename', Function.comp_apply, *]

lemma Subst.up_comp {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) :
    Subst.up (subst τ ∘ σ) = subst (Subst.up τ) ∘ Subst.up σ := by
  funext i; cases i using Fin.cases
  · rfl
  · simp only [Function.comp, Subst.up_succ, rename_subst, subst_rename]
    rfl

/-- Substitutions compose. -/
lemma subst_subst {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) (t : Term n) :
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t generalizing m k <;> simp only [subst, Subst.up_comp, Function.comp_apply, *]

/-- Substituting into a weakened term has no effect. -/
@[simp] lemma subst1_rename_succ {n : ℕ} (s t : Term n) :
    subst1 s (rename Fin.succ t) = t := by
  simp [subst1, subst_rename]
  conv_rhs => rw [← subst_var t]
  rfl

/-- The double substitution is the composition of two single substitutions. -/
lemma subst2_eq {n : ℕ} (s₁ s₂ : Term n) (t : Term (n + 2)) :
    subst2 s₁ s₂ t = subst1 s₁ (subst1 (rename Fin.succ s₂) t) := by
  simp only [subst2, subst1, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact (subst1_rename_succ s₁ s₂).symm
  | succ i =>
    cases i using Fin.cases <;> simp [subst]

end Term

/-! ## Renaming array references -/

/-- Renaming of array references `θ(t)`. -/
def renameRefs (θ : ℕ → ℕ) : {n : ℕ} → Term n → Term n
  | _, .var i => .var i
  | _, .lam t => .lam (renameRefs θ t)
  | _, .app t₁ t₂ => .app (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .pair t₁ t₂ => .pair (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .letPair t₁ t₂ => .letPair (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .unit => .unit
  | _, .letUnit t₁ t₂ => .letUnit (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .bang t => .bang (renameRefs θ t)
  | _, .letBang t₁ t₂ => .letBang (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .borrow t => .borrow (renameRefs θ t)
  | _, .copy t₁ t₂ => .copy (renameRefs θ t₁) (renameRefs θ t₂)
  | _, .star t => .star (renameRefs θ t)
  | _, .nat k => .nat k
  | _, .float x => .float x
  | _, .prim p => .prim p
  | _, .ref a => .ref (θ a)

end LCU
