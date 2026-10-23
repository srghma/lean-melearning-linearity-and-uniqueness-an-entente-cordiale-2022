module
public import RequestProject.Common.Syntax.RenSubst

/-!
# Generic binding layer: mapping operators

`Tm.mapOp f` applies an arity-preserving map `f : SigHom S S'` to every operator of a term.
It commutes with renaming and substitution, and it is injective when `f` is.
-/

@[expose] public section

namespace Binding

variable {S : Sig}

/-- An arity-preserving map between the operators of two signatures. -/
structure SigHom (S S' : Sig) where
  /-- the map on operators -/
  map : S.Op → S'.Op
  /-- operators keep their binding arities -/
  arity_map : ∀ o, S'.arity (map o) = S.arity o

variable {S' : Sig}

mutual
/-- Apply a map to every operator of a term. -/
def Tm.mapOp (f : SigHom S S') {n : ℕ} : Tm S n → Tm S' n
  | .var i => .var i
  | .op o as => .op (f.map o) ((f.arity_map o).symm ▸ as.mapOp f)

/-- Apply a map to every operator of an argument list. -/
def Args.mapOp (f : SigHom S S') {n : ℕ} {ks : List ℕ} : Args S n ks → Args S' n ks
  | .nil => .nil
  | .cons t as => .cons (t.mapOp f) (as.mapOp f)
end

lemma Args.ren_cast {n m : ℕ} (ρ : Var n → Var m) {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : (h ▸ as).ren ρ = h ▸ (as.ren ρ) := by
  subst h; rfl

lemma Args.subst_cast {n m : ℕ} (σ : Var n → Tm S m) {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : (h ▸ as).subst σ = h ▸ (as.subst σ) := by
  subst h; rfl

mutual
/-- Mapping operators commutes with renaming. -/
theorem Tm.mapOp_ren (f : SigHom S S') {n m : ℕ} (ρ : Var n → Var m) :
    (t : Tm S n) → (t.ren ρ).mapOp f = (t.mapOp f).ren ρ
  | .var _ => rfl
  | .op o as => by
    rw [Tm.ren_op, Tm.mapOp, Tm.mapOp, Tm.ren_op, Args.ren_cast, Args.mapOp_ren]
theorem Args.mapOp_ren (f : SigHom S S') {n m : ℕ} {ks : List ℕ} (ρ : Var n → Var m) :
    (as : Args S n ks) → (as.ren ρ).mapOp f = (as.mapOp f).ren ρ
  | .nil => rfl
  | .cons t as => by
    rw [Args.ren_cons, Args.mapOp, Args.mapOp, Args.ren_cons, Tm.mapOp_ren, Args.mapOp_ren]
end

lemma Subst.up_mapOp {n m : ℕ} (f : SigHom S S') (σ : Var n → Tm S m) :
    Subst.up (Tm.mapOp f ∘ σ) = Tm.mapOp f ∘ Subst.up σ := by
  funext i; cases i with
  | zero => rfl
  | succ i => exact (Tm.mapOp_ren f .succ (σ i)).symm

lemma Subst.upN_mapOp {n m : ℕ} (f : SigHom S S') (σ : Var n → Tm S m) :
    (k : ℕ) → Subst.upN k (Tm.mapOp f ∘ σ) = Tm.mapOp f ∘ Subst.upN k σ
  | 0 => rfl
  | k + 1 => by rw [Subst.upN_succ, Subst.upN_mapOp f σ k, Subst.up_mapOp]; rfl

mutual
/-- Mapping operators commutes with substitution. -/
theorem Tm.mapOp_subst (f : SigHom S S') {n m : ℕ} (σ : Var n → Tm S m) :
    (t : Tm S n) → (t.subst σ).mapOp f = (t.mapOp f).subst (Tm.mapOp f ∘ σ)
  | .var _ => rfl
  | .op o as => by
    rw [Tm.subst_op, Tm.mapOp, Tm.mapOp, Tm.subst_op, Args.subst_cast, Args.mapOp_subst]
theorem Args.mapOp_subst (f : SigHom S S') {n m : ℕ} {ks : List ℕ} (σ : Var n → Tm S m) :
    (as : Args S n ks) → (as.subst σ).mapOp f = (as.mapOp f).subst (Tm.mapOp f ∘ σ)
  | .nil => rfl
  | .cons (k := k) t as => by
    rw [Args.subst_cons, Args.mapOp, Args.mapOp, Args.subst_cons, Tm.mapOp_subst,
      Args.mapOp_subst, Subst.upN_mapOp]
end

end Binding

namespace Binding

variable {S S' : Sig}

lemma Args.cast_heq {n : ℕ} {ks ks' : List ℕ} (h : ks = ks') (as : Args S n ks) :
    HEq (h ▸ as) as := by
  subst h; rfl

mutual
/-- Mapping operators along an injective map is injective. -/
theorem Tm.mapOp_inj (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} :
    (t t' : Tm S n) → t.mapOp f = t'.mapOp f → t = t'
  | .var i, .var j, h => by
    simp only [Tm.mapOp, Tm.var_inj] at h; rw [h]
  | .var _, .op _ _, h => by simp [Tm.mapOp] at h
  | .op _ _, .var _, h => by simp [Tm.mapOp] at h
  | .op o as, .op o' as', h => by
    simp only [Tm.mapOp, Tm.op_eq_op_iff] at h
    obtain ⟨ho, hh⟩ := h
    have := hf ho; subst this
    have : as.mapOp f = as'.mapOp f :=
      eq_of_heq ((Args.cast_heq _ _).symm.trans (hh.trans (Args.cast_heq _ _)))
    rw [Args.mapOp_inj f hf as as' this]
theorem Args.mapOp_inj (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} {ks : List ℕ} :
    (as as' : Args S n ks) → as.mapOp f = as'.mapOp f → as = as'
  | .nil, .nil, _ => rfl
  | .cons t as, .cons t' as', h => by
    simp only [Args.mapOp, Args.cons_inj] at h
    rw [Tm.mapOp_inj f hf t t' h.1, Args.mapOp_inj f hf as as' h.2]
end

lemma Tm.mapOp_injective (f : SigHom S S') (hf : Function.Injective f.map) {n : ℕ} :
    Function.Injective (Tm.mapOp f : Tm S n → Tm S' n) :=
  fun t t' h => Tm.mapOp_inj f hf t t' h

end Binding
