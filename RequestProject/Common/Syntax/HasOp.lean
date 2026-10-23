module
public import RequestProject.Common.Syntax.MapOp
public import RequestProject.Common.Syntax.Occurs

/-!
# Generic binding layer: operators occurring in a term

`Tm.HasOp P t`: some operator satisfying `P` occurs in `t` (possibly under binders), its
behaviour under renaming, substitution and `mapOp`, and a decision procedure.
-/

@[expose] public section

namespace Binding

variable {S : Sig}

mutual
/-- `Tm.HasOp P t`: some operator satisfying `P` occurs in `t` (possibly under binders). -/
inductive Tm.HasOp (P : S.Op → Prop) : {n : ℕ} → Tm S n → Prop where
  | here {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} : P o → Tm.HasOp P (.op o as)
  | arg {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} : Args.HasOp P as → Tm.HasOp P (.op o as)

/-- `Args.HasOp P as`: some operator satisfying `P` occurs in one of the arguments. -/
inductive Args.HasOp (P : S.Op → Prop) : {n : ℕ} → {ks : List ℕ} → Args S n ks → Prop where
  | head {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)} {as : Args S n ks} :
      Tm.HasOp P t → Args.HasOp P (.cons t as)
  | tail {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)} {as : Args S n ks} :
      Args.HasOp P as → Args.HasOp P (.cons t as)
end

@[simp] lemma Tm.not_hasOp_var {P : S.Op → Prop} {n : ℕ} {i : Var n} :
    ¬ Tm.HasOp P (.var i : Tm S n) := nofun

lemma Tm.hasOp_op_iff {P : S.Op → Prop} {n : ℕ} {o : S.Op} {as : Args S n (S.arity o)} :
    Tm.HasOp P (.op o as) ↔ P o ∨ Args.HasOp P as :=
  ⟨fun h => by cases h with | here h => exact .inl h | arg h => exact .inr h,
   fun h => h.elim .here .arg⟩

@[simp] lemma Args.not_hasOp_nil {P : S.Op → Prop} {n : ℕ} :
    ¬ Args.HasOp P (.nil : Args S n []) := nofun

lemma Args.hasOp_cons_iff {P : S.Op → Prop} {n k : ℕ} {ks : List ℕ} {t : Tm S (n + k)}
    {as : Args S n ks} : Args.HasOp P (.cons t as) ↔ Tm.HasOp P t ∨ Args.HasOp P as :=
  ⟨fun h => by cases h with | head h => exact .inl h | tail h => exact .inr h,
   fun h => h.elim .head .tail⟩

mutual
theorem Tm.HasOp.of_ren {P : S.Op → Prop} {n m : ℕ} {r : Var n → Var m} :
    {t : Tm S n} → Tm.HasOp P (t.ren r) → Tm.HasOp P t
  | .var _, h => by cases h
  | .op o as, h => by
    cases h with
    | here h => exact .here h
    | arg h => exact .arg (Args.HasOp.of_ren h)
theorem Args.HasOp.of_ren {P : S.Op → Prop} {n m : ℕ} {r : Var n → Var m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.ren r) → Args.HasOp P as
  | _, .cons t as, h => by
    cases h with
    | head h => exact .head (Tm.HasOp.of_ren h)
    | tail h => exact .tail (Args.HasOp.of_ren h)
end

/-- An operator occurring in a lifted substitution occurs in the substitution. -/
lemma Subst.hasOp_upN {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    (k : ℕ) → (x : Var (n + k)) → Tm.HasOp P (Subst.upN k σ x) → ∃ i, Tm.HasOp P (σ i)
  | 0, x, h => ⟨x, h⟩
  | k + 1, x, h => by
    cases x with
    | zero => cases h
    | succ x => exact Subst.hasOp_upN k x (Tm.HasOp.of_ren h)

mutual
theorem Tm.HasOp.of_subst {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {t : Tm S n} → Tm.HasOp P (t.subst σ) → Tm.HasOp P t ∨ ∃ i, Tm.HasOp P (σ i)
  | .var i, h => .inr ⟨i, h⟩
  | .op o as, h => by
    cases h with
    | here h => exact .inl (.here h)
    | arg h => exact (Args.HasOp.of_subst h).imp .arg id
theorem Args.HasOp.of_subst {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.subst σ) →
      Args.HasOp P as ∨ ∃ i, Tm.HasOp P (σ i)
  | _, .cons (k := k) t as, h => by
    cases h with
    | head h =>
      rcases Tm.HasOp.of_subst h with h | ⟨x, hx⟩
      · exact .inl (.head h)
      · exact .inr (Subst.hasOp_upN k x hx)
    | tail h => exact (Args.HasOp.of_subst h).imp .tail id
end

/-- An operator occurring in a lifted substitution at `x` occurs in the substitution at a
variable `i` with `x = Var.shiftN k i`. -/
lemma Subst.hasOp_upN' {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    (k : ℕ) → (x : Var (n + k)) → Tm.HasOp P (Subst.upN k σ x) →
      ∃ i, x = Var.shiftN k i ∧ Tm.HasOp P (σ i)
  | 0, x, h => ⟨x, rfl, h⟩
  | k + 1, x, h => by
    cases x with
    | zero => cases h
    | succ x =>
      obtain ⟨i, rfl, hi⟩ := Subst.hasOp_upN' k x (Tm.HasOp.of_ren h)
      exact ⟨i, rfl, hi⟩

mutual
/-- If an operator occurs in `t[σ]`, it occurs in `t` or in `σ i` for a variable `i`
occurring free in `t`. -/
theorem Tm.HasOp.of_subst_occurs {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {t : Tm S n} → Tm.HasOp P (t.subst σ) → Tm.HasOp P t ∨ ∃ i, Tm.Occurs i t ∧ Tm.HasOp P (σ i)
  | .var i, h => .inr ⟨i, .var, h⟩
  | .op o as, h => by
    cases h with
    | here h => exact .inl (.here h)
    | arg h =>
      rcases Args.HasOp.of_subst_occurs h with h | ⟨i, hi, h⟩
      · exact .inl (.arg h)
      · exact .inr ⟨i, .op hi, h⟩
theorem Args.HasOp.of_subst_occurs {P : S.Op → Prop} {n m : ℕ} {σ : Var n → Tm S m} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.subst σ) →
      Args.HasOp P as ∨ ∃ i, Args.Occurs i as ∧ Tm.HasOp P (σ i)
  | _, .cons (k := k) t as, h => by
    cases h with
    | head h =>
      rcases Tm.HasOp.of_subst_occurs h with h | ⟨x, hx, h⟩
      · exact .inl (.head h)
      · obtain ⟨i, rfl, hi⟩ := Subst.hasOp_upN' k x h
        exact .inr ⟨i, .head hx, hi⟩
    | tail h =>
      rcases Args.HasOp.of_subst_occurs h with h | ⟨i, hi, h⟩
      · exact .inl (.tail h)
      · exact .inr ⟨i, .tail hi, h⟩
end

lemma Args.hasOp_cast {P : S.Op → Prop} {n : ℕ} {ks ks' : List ℕ} (h : ks = ks')
    (as : Args S n ks) : Args.HasOp P (h ▸ as) ↔ Args.HasOp P as := by
  subst h; rfl

mutual
/-- An operator occurring in `t.mapOp f` is the image of an operator occurring in `t`. -/
theorem Tm.HasOp.of_mapOp {S' : Sig} {f : SigHom S S'} {P : S'.Op → Prop} {n : ℕ} :
    {t : Tm S n} → Tm.HasOp P (t.mapOp f) → Tm.HasOp (fun o => P (f.map o)) t
  | .var _, h => by cases h
  | .op o as, h => by
    cases h with
    | here h => exact .here h
    | arg h => exact .arg (Args.HasOp.of_mapOp ((Args.hasOp_cast _ _).1 h))
theorem Args.HasOp.of_mapOp {S' : Sig} {f : SigHom S S'} {P : S'.Op → Prop} {n : ℕ} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P (as.mapOp f) →
      Args.HasOp (fun o => P (f.map o)) as
  | _, .cons t as, h => by
    cases h with
    | head h => exact .head (Tm.HasOp.of_mapOp h)
    | tail h => exact .tail (Args.HasOp.of_mapOp h)
end

mutual
/-- If an operator satisfying `P` occurs, then some operator satisfies `P`. -/
theorem Tm.HasOp.exists_op {P : S.Op → Prop} {n : ℕ} :
    {t : Tm S n} → Tm.HasOp P t → ∃ o, P o
  | .op o _, .here h => ⟨o, h⟩
  | .op _ _, .arg h => Args.HasOp.exists_op h
theorem Args.HasOp.exists_op {P : S.Op → Prop} {n : ℕ} :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P as → ∃ o, P o
  | _, .cons _ _, .head h => Tm.HasOp.exists_op h
  | _, .cons _ _, .tail h => Args.HasOp.exists_op h
end

mutual
/-- If an operator satisfying `P` occurs in `t`, it occurs in every renaming of `t`. -/
theorem Tm.HasOp.ren {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) :
    {t : Tm S n} → Tm.HasOp P t → Tm.HasOp P (t.ren r)
  | .op _ _, .here h => .here h
  | .op _ _, .arg h => .arg (Args.HasOp.ren r h)
theorem Args.HasOp.ren {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) :
    {ks : List ℕ} → {as : Args S n ks} → Args.HasOp P as → Args.HasOp P (as.ren r)
  | _, .cons _ _, .head h => .head (Tm.HasOp.ren _ h)
  | _, .cons _ _, .tail h => .tail (Args.HasOp.ren r h)
end

/-- Renaming does not change which operators occur in a term. -/
@[simp] lemma Tm.hasOp_ren_iff {P : S.Op → Prop} {n m : ℕ} (r : Var n → Var m) (t : Tm S n) :
    Tm.HasOp P (t.ren r) ↔ Tm.HasOp P t :=
  ⟨Tm.HasOp.of_ren, Tm.HasOp.ren r⟩

/-! ### Deciding whether an operator occurs -/

mutual
/-- `Tm.anyOp f t`: some operator `o` of `t` has `f o = true` (a decision procedure for
`Tm.HasOp`). -/
def Tm.anyOp (f : S.Op → Bool) {n : ℕ} : Tm S n → Bool
  | .var _ => false
  | .op o as => f o || as.anyOp f
/-- `Args.anyOp f as`: `Tm.anyOp f` holds for some argument. -/
def Args.anyOp (f : S.Op → Bool) {n : ℕ} {ks : List ℕ} : Args S n ks → Bool
  | .nil => false
  | .cons t as => t.anyOp f || as.anyOp f
end

mutual
theorem Tm.anyOp_iff (f : S.Op → Bool) {n : ℕ} :
    (t : Tm S n) → t.anyOp f = true ↔ Tm.HasOp (fun o => f o = true) t
  | .var _ => by simp [Tm.anyOp]
  | .op o as => by
    rw [Tm.hasOp_op_iff, ← Args.anyOp_iff f as]; simp [Tm.anyOp]
theorem Args.anyOp_iff (f : S.Op → Bool) {n : ℕ} {ks : List ℕ} :
    (as : Args S n ks) → as.anyOp f = true ↔ Args.HasOp (fun o => f o = true) as
  | .nil => by simp [Args.anyOp]
  | .cons t as => by
    rw [Args.hasOp_cons_iff, ← Tm.anyOp_iff f t, ← Args.anyOp_iff f as]; simp [Args.anyOp]
end

instance Tm.decidableHasOp (P : S.Op → Prop) [DecidablePred P] {n : ℕ} (t : Tm S n) :
    Decidable (Tm.HasOp P t) :=
  decidable_of_iff (t.anyOp (fun o => decide (P o))) (by rw [Tm.anyOp_iff]; simp)

end Binding
