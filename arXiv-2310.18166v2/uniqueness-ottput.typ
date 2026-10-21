#import "common.typ": *

The first extension we make to the core calculus is to represent _ownership_: values that have a unique owner can mutate the value freely because they are in possession of the only reference that exists. It turns out this matches closely with the idea of _uniqueness_ types; if it is possible to guarantee that a reference to a value is unique (i.e., it is the only reference that exists), then whichever part of the program (e.g., a given thread or process) holds that reference must be the owner.

Uniqueness types were introduced into Granule's core type system in previous work @marshall2022linearity, but we will extend this in two ways: first, we generalise the rules of @marshall2022linearity to allow for a graded necessity modality parameterised by an arbitrary semiring rather than the simple non-linear $!$, and second, we incorporate the identifiers described in @sec:core into the typing, which will become important when multiple references need to be tracked.

As with uniqueness typing, the crucial insight for integrating owned values with linear and graded values is to consider any linear or graded value to have no ownership information attached; these values have their memory managed in other ways, such as explicitly by the programmer or implicitly by a garbage collector. We then introduce a modality, written $ucol(*)$ (akin to Marshall et al.'s uniqueness modality) to type values that are _uniquely owned_, meaning that the type system must ensure only one reference exists at any given time. We extend the syntax of terms and types:

$
  t &::= ldots | bold("share") t | bold("clone") t_1 bold("as") x bold("in") t_2 \
  A, B &::= ldots | ucol(*) A
$

The two constructs for this uniqueness modality $ucol(*)$ provide sharing and cloning, with types:

#v(0.5em)
#grid(
  columns: (1fr, 1.4fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [Share],
      $Gamma ⊢ t : ucol(*) A$,
      $Gamma ⊢ bold("share") t : Box_(lcol(r)) A$
    )
  ),
  prooftree(
    rule(
      name: [Clone],
      $Gamma_1 ⊢ t_1 : Box_(lcol(r)) A$,
      $Gamma_2, x : ucol(*) A ⊢ t_2 : B$,
      $1 sqle r$,
      $sans("cloneable")(A)$,
      $Gamma_1 + Gamma_2 ⊢ bold("clone") t_1 bold("as") x bold("in") t_2 : exists overline(id). B$
    )
  )
)
#v(0.5em)

The #smallcaps[Share] construct allows a guarantee of unique ownership to be discarded, though this means that memory must now once again be managed automatically just as with any other Granule values where ownership is not tracked. Any grade $r$ can be selected here, though the shared value must eventually be either discarded (requiring $0 sqle r$) or fully consumed via pattern matching.

The #smallcaps[Clone] construct makes a _deep copy_ of the value $t_1$, where we take a value that does not have an owner and make a unique copy of it; we take ownership of the copy, binding it in the scope of $t_2$. We can guarantee uniqueness since this is now the only reference that exists to the copied value. We must update any identifiers along the way, however, to ensure that this is understood as a separate value to the original, in case other references still exist. This is mediated by existential types, where all identifiers $overline(id)$ used in typing $t_1$ are bound under an existential quantifier.

Note, however, that cloning requires some additional conditions for soundness. The predicate $sans("cloneable")(A)$ ensures the value is of a resource type---such as a reference---or a product of resources. (The full definition of $sans("cloneable")$ is presented in @sec:fractional, where we discuss said resource types in more depth.) This is necessary to prevent values which do not come with identifiers from being managed via ownership, since once we introduce borrowing in @sec:fractional this would lead to borrows of different values of the same type (such as two floating point numbers) being indistinguishable at the type level and thus interchangeable. The side-condition $1 sqle r$ explains that we must be able to accommodate a usage of the input $t_1$ since $bold("clone")$ consumes the $t_1$ value once in copying it.

Our implementation of these ideas in Granule follows the above typing. We recap the initial ownership example from @sec:key here in our new extension of Granule using a data type `Colour` which acts as an alias for a triple of type `(Int, Int, Int)`.

The following code illustrates that linear types already require us to obey the laws of _move semantics_ for owned values, where we move ownership of `scarlet` to `x` and then to `y`:

#codebox(title: "Granule")[
```haskell
exampleMove : *Colour -> *Colour
exampleMove scarlet =
  let x = scarlet in
  -- ownership "moved" to x
  -- let y = scarlet in ... -- error: non-linear use of 'scarlet'
  let y = x in y           -- but "moving" ownership from x to y is allowed
```
]

We can have multiple variables which all point to the initial value of type `Colour` via the *share* operation; this explicitly exempts the value from being managed by the ownership system. Here, we share at the interval grade `[0..2]`, capturing the idea that the value must be used somewhere between zero and two times (where here it happens to be used twice).

#codebox(title: "Granule")[
```haskell
exampleShare : *Colour -> (Colour, Colour)
exampleShare scarlet =
  let [s] : Colour [0..2] = share scarlet in
  let x = s in
  let y = s in (x, y)
```
]

The $bold("share")$ and $bold("clone")$ operations have the following equations showing their interaction:

$
  bold("clone") (bold("share") v) bold("as") x bold("in") t &equiv t [bold("pack") langle overline(id), v rangle  \/ x] \
  bold("clone") t_1 bold("as") x bold("in") (bold("clone") t_2 bold("as") y bold("in") t_3) &equiv bold("clone") (bold("clone") t_1 bold("as") x bold("in") t_2) bold("as") y bold("in") t_3 quad (x in.not sans("FV")(t_3))
$

The ($beta_*$) axiom states that sharing a value $v$ (term with no further reductions---see @sec:semantics) and cloning it to create a new owned $x$ in the scope of $t$ is equivalent to substituting the original $v$ for $x$ in $t$ (with its identifiers packed in an existential). The ($*sans("assoc")$) axiom is associativity of cloning.

The presence of identifiers necessitates the existential typing. The need for identifiers is shown in the next section once we move to a generalisation of uniqueness with the ability to separate _immutable borrows_ from _mutable borrows_, where existential types will allow for tighter control of the _lifetime_ of borrowed values with identifiers.
