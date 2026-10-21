module
public import RequestProject.FOFU.Sec3_CoreCalculus.TypingLemmas

/-!
# §5 — the examples `exampleBorrow`, `exampleReborrow`, `exampleArray`, `exampleClone`,
# `exampleReference`

As in §4, `let x = t₁ in t₂` is read as `(λx. t₂) t₁`, `Colour` is an arbitrary type `C`,
and the semiring is `ℕ` (no grades are used).  The function `observe`, which the paper
only declares (`observe : &p Colour → &p Colour`), is a variable of the context, used
linearly at the permission `1/2` at which the example applies it.  The trailing
`let b = join (x', y) in b` of the paper is simplified to `join x' y`.

Contexts are written with `Ctx.ofList` (variable `#0` first).

`exampleGraded` reads a `Float [4]` out of a reference created with contents of type
`Float [6]` and afterwards uses the reference at type `Ref id (Float [2])`, i.e. `readRef`
splits the grade `6 = 4 + 2`.  The interface printed in §5,
`readRef : &_p (Ref_id (□_r A)) ⊸ A ⊗ &_p (Ref_id (□_r A))`, keeps the type of the reference
unchanged, so the example does not type-check against it.  It is formalised in
`ExampleGraded.lean` with an amended, grade-splitting read primitive `readRefSplit`.
-/

@[expose] public section

namespace FOFU

open Ty

/-- Joining two halves of a permission `f` gives back `f` (rule `join` with `p = q = f/2`). -/
theorem HasType.joinHalves {R : Type} [Grades.PreorderedSemiring R] {k n : ℕ}
    {Γ₁ Γ₂ Γ : Ctx R k n} {t₁ t₂ : Term R n} {A : Ty R k} {f : Frac}
    (h : CtxAdd Γ₁ Γ₂ Γ) (h₁ : HasType Γ₁ t₁ (borrow (.frac f.half) A))
    (h₂ : HasType Γ₂ t₂ (borrow (.frac f.half) A)) :
    HasType Γ (.join t₁ t₂) (borrow (.frac f) A) := by
  have := HasType.join (Frac.half_add_half f) h h₁ h₂
  rwa [Frac.add_half_half] at this

/-- The permission `1/2`. -/
abbrev halfP : Perm := .frac Frac.one.half

/-- `λpersimmon. withBorrow (λb. let (x, y) = split b in let x' = observe x in join x' y)
persimmon`, in the scope of `observe = #0`. -/
def exampleBorrow : Term ℕ 1 :=
  .lam (.withBorrow
    (.lam (.letPair (.split (.var 0))
      (.app (.lam (.join (.var 0) (.var 1))) (.app (.var 4) (.var 1)))))
    (.var 0))

/-- `observe : &_{1/2} C ⊸ &_{1/2} C ⊢ exampleBorrow : *C ⊸ *C`. -/
theorem exampleBorrow_typing {k : ℕ} (C : Ty ℕ k) :
    HasType (Ctx.ofList [some (.lin (lolli (borrow halfP C) (borrow halfP C)))])
      exampleBorrow (lolli (star C) (star C)) := by
  set O : Ty ℕ k := lolli (borrow halfP C) (borrow halfP C)
  refine HasType.abs (HasType.withBorrow
    (Γ₁ := Ctx.ofList [none, some (.lin O)]) (Γ₂ := Ctx.ofList [some (.lin (star C)), none])
    (by ctx_add) ?_ (HasType.var rfl (by zero_rest)))
  -- `b : &₁ C, persimmon : −, observe : O ⊢ ... : &₁ C`
  refine HasType.abs (HasType.tensorE
    (Γ₁ := Ctx.ofList [some (.lin (borrow Perm.one C)), none, none])
    (Γ₂ := Ctx.ofList [none, none, some (.lin O)])
    (by ctx_add) (HasType.split (HasType.var rfl (by zero_rest))) ?_)
  -- `y, x : &_{1/2} C, b : −, persimmon : −, observe : O ⊢ (λx'. join x' y) (observe x)`
  refine HasType.app (A := borrow halfP C)
    (Γ₁ := Ctx.ofList [some (.lin (borrow halfP C)), none, none, none, none])
    (Γ₂ := Ctx.ofList [none, some (.lin (borrow halfP C)), none, none, some (.lin O)])
    (by ctx_add) ?_ ?_
  · exact HasType.abs (HasType.joinHalves
      (Γ₁ := Ctx.ofList [some (.lin (borrow halfP C)), none, none, none, none, none])
      (Γ₂ := Ctx.ofList [none, some (.lin (borrow halfP C)), none, none, none, none])
      (by ctx_add) (HasType.var rfl (by zero_rest)) (HasType.var rfl (by zero_rest)))
  · exact HasType.app (A := borrow halfP C)
      (Γ₁ := Ctx.ofList [none, none, none, none, some (.lin O)])
      (Γ₂ := Ctx.ofList [none, some (.lin (borrow halfP C)), none, none, none])
      (by ctx_add) (HasType.var rfl (by zero_rest)) (HasType.var rfl (by zero_rest))

/-- The permission `1/4`. -/
abbrev quarterP : Perm := .frac Frac.one.half.half

/-- `λamethyst. withBorrow (λb. let (x, y) = split b in let (l, r) = split x in
let x' = join r l in join y x') amethyst`. -/
def exampleReborrow : Term ℕ 0 :=
  .lam (.withBorrow
    (.lam (.letPair (.split (.var 0))
      (.letPair (.split (.var 1))
        (.app (.lam (.join (.var 3) (.var 0))) (.join (.var 0) (.var 1))))))
    (.var 0))

/-- `⊢ exampleReborrow : *C ⊸ *C`: the immutable borrow `x` is reborrowed as `l` and `r`;
all borrows must be joined again before the owner gets the value back. -/
theorem exampleReborrow_typing {k : ℕ} (C : Ty ℕ k) :
    HasType Ctx.empty exampleReborrow (lolli (star C) (star C)) := by
  refine HasType.abs (HasType.withBorrow
    (Γ₁ := Ctx.ofList [none]) (Γ₂ := Ctx.ofList [some (.lin (star C))])
    (by ctx_add) ?_ (HasType.var rfl (by zero_rest)))
  -- `b : &₁ C, amethyst : −`
  refine HasType.abs (HasType.tensorE
    (Γ₁ := Ctx.ofList [some (.lin (borrow Perm.one C)), none])
    (Γ₂ := Ctx.ofList [none, none])
    (by ctx_add) (HasType.split (HasType.var rfl (by zero_rest))) ?_)
  -- `y, x : &_{1/2} C, b, amethyst : −`
  refine HasType.tensorE
    (Γ₁ := Ctx.ofList [none, some (.lin (borrow halfP C)), none, none])
    (Γ₂ := Ctx.ofList [some (.lin (borrow halfP C)), none, none, none])
    (by ctx_add) (HasType.split (HasType.var rfl (by zero_rest))) ?_
  -- `r, l : &_{1/4} C, y : &_{1/2} C, x, b, amethyst : −`
  refine HasType.app (A := borrow halfP C)
    (Γ₁ := Ctx.ofList [none, none, some (.lin (borrow halfP C)), none, none, none])
    (Γ₂ := Ctx.ofList [some (.lin (borrow quarterP C)), some (.lin (borrow quarterP C)),
      none, none, none, none])
    (by ctx_add) ?_ ?_
  · exact HasType.abs (HasType.joinHalves
      (Γ₁ := Ctx.ofList [none, none, none, some (.lin (borrow halfP C)), none, none, none])
      (Γ₂ := Ctx.ofList [some (.lin (borrow halfP C)), none, none, none, none, none, none])
      (by ctx_add) (HasType.var rfl (by zero_rest)) (HasType.var rfl (by zero_rest)))
  · exact HasType.joinHalves
      (Γ₁ := Ctx.ofList [some (.lin (borrow quarterP C)), none, none, none, none, none])
      (Γ₂ := Ctx.ofList [none, some (.lin (borrow quarterP C)), none, none, none, none])
      (by ctx_add) (HasType.var rfl (by zero_rest)) (HasType.var rfl (by zero_rest))

/-- `unpack ⟨id, a⟩ = newArray 3 in let a' = writeArray a 1 4.2 in
let (f, a'') = readArray a' 1 in let () = deleteArray a'' in f`. -/
def exampleArray : Term ℕ 0 :=
  .unpack (.app (.prim .newArray) (.nat 3))
    (.app
      (.lam (.letPair (.app (.app (.prim .readArray) (.var 0)) (.nat 1))
        (.letUnit (.app (.prim .deleteArray) (.var 0)) (.var 1))))
      (.app (.app (.app (.prim .writeArray) (.var 0)) (.nat 1)) (.float 4.2)))

/-- `⊢ exampleArray : 𝔽`. -/
theorem exampleArray_typing : HasType (Ctx.empty : Ctx ℕ 0 0) exampleArray .float := by
  refine HasType.unpack (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) (A := star (array (.bound 0)))
    CtxAdd.empty
    (HasType.app (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) CtxAdd.empty
      (HasType.prim Ctx.IsZero.empty PrimTy.newArray) (HasType.nat 3 Ctx.IsZero.empty)) ?_
  -- in the scope of the new identifier: `a : *(Array_id 𝔽)`
  set A : Ty ℕ 1 := star (array (.bound 0))
  refine HasType.app (A := A) (Γ₁ := Ctx.ofList [none]) (Γ₂ := Ctx.ofList [some (.lin A)])
    (by ctx_add) ?_ ?_
  · -- `a' : A, a : − ⊢ let (f, a'') = readArray a' 1 in ...`
    refine HasType.abs (HasType.tensorE (A := .float) (B := A)
      (Γ₁ := Ctx.ofList [some (.lin A), none]) (Γ₂ := Ctx.ofList [none, none])
      (by ctx_add) ?_ ?_)
    · exact HasType.app (Γ₁ := Ctx.ofList [some (.lin A), none])
        (Γ₂ := Ctx.ofList [none, none]) (by ctx_add)
        (HasType.app (Γ₁ := Ctx.ofList [none, none]) (Γ₂ := Ctx.ofList [some (.lin A), none])
          (by ctx_add) (HasType.prim (by zero_rest) (PrimTy.readArray Perm.star (.bound 0)))
          (HasType.var rfl (by zero_rest)))
        (HasType.nat 1 (by zero_rest))
    · exact HasType.unitE (Γ₁ := Ctx.ofList [some (.lin A), none, none, none])
        (Γ₂ := Ctx.ofList [none, some (.lin .float), none, none]) (by ctx_add)
        (HasType.app (Γ₁ := Ctx.ofList [none, none, none, none])
          (Γ₂ := Ctx.ofList [some (.lin A), none, none, none]) (by ctx_add)
          (HasType.prim (by zero_rest) (PrimTy.deleteArray (.bound 0)))
          (HasType.var rfl (by zero_rest)))
        (HasType.var rfl (by zero_rest))
  · -- `a : A ⊢ writeArray a 1 4.2 : A`
    exact HasType.app (Γ₁ := Ctx.ofList [some (.lin A)]) (Γ₂ := Ctx.ofList [none])
      (by ctx_add)
      (HasType.app (Γ₁ := Ctx.ofList [some (.lin A)]) (Γ₂ := Ctx.ofList [none]) (by ctx_add)
        (HasType.app (Γ₁ := Ctx.ofList [none]) (Γ₂ := Ctx.ofList [some (.lin A)]) (by ctx_add)
          (HasType.prim (by zero_rest)
            (PrimTy.writeArray Perm.star (.bound 0) (Or.inr rfl)))
          (HasType.var rfl (by zero_rest)))
        (HasType.nat 1 (by zero_rest)))
      (HasType.float 4.2 (by zero_rest))

/-- `unpack ⟨id, a⟩ = newArray 3 in clone (share a) as x in unpack ⟨id', a'⟩ = x in
deleteArray a'` (sharing at grade `1`, the one use made by `clone`). -/
def exampleClone : Term ℕ 0 :=
  .unpack (.app (.prim .newArray) (.nat 3))
    (.clone (.share 1 (.var 0)) (.unpack (.var 0) (.app (.prim .deleteArray) (.var 0))))

/-- `⊢ exampleClone : unit`. -/
theorem exampleClone_typing : HasType (Ctx.empty : Ctx ℕ 0 0) exampleClone .unit := by
  refine HasType.unpack (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) (A := star (array (.bound 0)))
    CtxAdd.empty
    (HasType.app (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) CtxAdd.empty
      (HasType.prim Ctx.IsZero.empty PrimTy.newArray) (HasType.nat 3 Ctx.IsZero.empty)) ?_
  -- `a : *(Array_id 𝔽) ⊢ clone (share a) as x in ...`
  refine HasType.clone (A := array (.bound 0)) (A' := array (.bound 0)) (r := 1) (.bound 0)
    (Γ₁ := Ctx.ofList [some (.lin (star (array (.bound 0))))]) (Γ₂ := Ctx.ofList [none])
    (by ctx_add) (HasType.share 1 (HasType.var rfl (by zero_rest))) le_rfl
    (Cloneable.array _) rfl ?_
  -- `x : ∃ id'. *(Array_id' 𝔽), a : − ⊢ unpack ⟨id', a'⟩ = x in deleteArray a'`
  refine HasType.unpack (A := star (array (.bound 0)))
    (Γ₁ := Ctx.ofList [some (.lin (ex (star (array (.bound 0))))), none])
    (Γ₂ := Ctx.ofList [none, none]) (by ctx_add) (HasType.var rfl (by zero_rest)) ?_
  exact HasType.app (Γ₁ := Ctx.ofList [none, none, none])
    (Γ₂ := Ctx.ofList [some (.lin (star (array (.bound 0)))), none, none]) (by ctx_add)
    (HasType.prim (by zero_rest) (PrimTy.deleteArray (.bound 0)))
    (HasType.var rfl (by zero_rest))

/-- `unpack ⟨id, ref⟩ = newRef 0.0 in let (x, ref') = swapRef ref 42.0 in
let y = freezeRef ref' in (x, y)` (with `y` inlined). -/
def exampleReference : Term ℕ 0 :=
  .unpack (.app (.prim .newRef) (.float 0.0))
    (.letPair (.app (.app (.prim .swapRef) (.var 0)) (.float 42.0))
      (.pair (.var 1) (.app (.prim .freezeRef) (.var 0))))

/-- `⊢ exampleReference : 𝔽 ⊗ 𝔽`. -/
theorem exampleReference_typing :
    HasType (Ctx.empty : Ctx ℕ 0 0) exampleReference (tensor .float .float) := by
  refine HasType.unpack (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty)
    (A := star (ref (.bound 0) .float)) CtxAdd.empty
    (HasType.app (Γ₁ := Ctx.empty) (Γ₂ := Ctx.empty) CtxAdd.empty
      (HasType.prim Ctx.IsZero.empty (PrimTy.newRef .float))
      (HasType.float 0.0 Ctx.IsZero.empty)) ?_
  set A : Ty ℕ 1 := star (ref (.bound 0) .float)
  refine HasType.tensorE (A := .float) (B := A)
    (Γ₁ := Ctx.ofList [some (.lin A)]) (Γ₂ := Ctx.ofList [none]) (by ctx_add) ?_ ?_
  · exact HasType.app (Γ₁ := Ctx.ofList [some (.lin A)]) (Γ₂ := Ctx.ofList [none])
      (by ctx_add)
      (HasType.app (Γ₁ := Ctx.ofList [none]) (Γ₂ := Ctx.ofList [some (.lin A)]) (by ctx_add)
        (HasType.prim (by zero_rest) (PrimTy.swapRef Perm.star (.bound 0) .float (Or.inr rfl)))
        (HasType.var rfl (by zero_rest)))
      (HasType.float 42.0 (by zero_rest))
  · exact HasType.tensorI (Γ₁ := Ctx.ofList [none, some (.lin .float), none])
      (Γ₂ := Ctx.ofList [some (.lin A), none, none]) (by ctx_add)
      (HasType.var rfl (by zero_rest))
      (HasType.app (Γ₁ := Ctx.ofList [none, none, none])
        (Γ₂ := Ctx.ofList [some (.lin A), none, none]) (by ctx_add)
        (HasType.prim (by zero_rest) (PrimTy.freezeRef (.bound 0) .float))
        (HasType.var rfl (by zero_rest)))

end FOFU
