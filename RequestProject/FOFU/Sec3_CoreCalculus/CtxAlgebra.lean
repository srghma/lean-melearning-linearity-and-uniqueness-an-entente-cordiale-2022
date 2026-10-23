module
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra.Add
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra.Scale
public import RequestProject.FOFU.Sec3_CoreCalculus.CtxAlgebra.Approx

/-!
# The algebra of contexts

Properties of the partial operations on contexts of `Context.lean`, used by the
substitution lemmas (Lemmas 6.2 and 6.3):

* context addition is commutative and associative (as relations): `CtxAdd.comm`,
  `CtxAdd.assoc`, and the interchange law `CtxAdd.interchange`;
* scalar multiplication distributes over addition: `CtxScale.add_scale`,
  `CtxScale.add_exists`, and composes: `CtxScale.comp`, `CtxScale.one_eq`;
* the pointwise order on grades `CtxLe Γ Γ'` (`Γ'` is `Γ` with some grades approximated
  upwards), which is compatible with addition and scaling.

Since grades form an arbitrary (not necessarily commutative) pre-ordered semiring, the
grade of a sum is `r + s` and scaling multiplies on the left, `r · (x : [A]_s) =
x : [A]_(r * s)`.

(The analogous development for *Linearity and Uniqueness* is
`RequestProject/LCU/Sec3_1_Calculus/CtxAlgebra.lean`; the statements here are
generalised to grades and so are proved separately.)

## Files

* `CtxAlgebra/Add.lean`: addition of assumptions and contexts, zero contexts;
* `CtxAlgebra/Scale.lean`: scaling;
* `CtxAlgebra/Approx.lean`: approximating grades (`AssmLe`, `CtxLe`).
-/
