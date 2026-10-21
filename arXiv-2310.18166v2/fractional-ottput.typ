#import "common.typ": *

We now generalise from the above system which incorporates uniqueness into the core calculus to a system that allows for the uniqueness guarantees to be temporarily broken in controlled ways, such that we can continue to ensure memory safety and more closely approximate Rust-like ownership and borrowing rules. We take inspiration from the fractional permissions of @boyland2003checking (which themselves served as partial inspiration for Rust's notion of ownership) and from recent literature on integrating linear types with fractional permissions #cite(<makwana2019numlin>).

Just as grading non-linearity gives a more precise account of resource usage, we introduce borrowing as a graded form of non-_uniqueness_ denoted $withB_p A$, allowing precise control of references:

$
  A, B &::= ldots | withB_p A \
  p, q &::= * | f quad quad (text("where") f in bb(Q), 0 < f <= 1)
$

where $p$ is a new form of grade for tracking borrowing, called a _permission_. Permissions are either rational numbers $f$ between $0$ and $1$ or a special permission $*$ representing unique ownership (described below). A _mutable borrow_ is represented by $withB_1 A$ which allows temporary mutable access to a value while preserving the guarantee that it will be eventually returned to its original owner. Note that $0$ is excluded: the typing rules we provide can never produce a value with permission $0$.

For working with the borrowing graded modality, terms are extended as follows:

$
  t ::= ldots | bold("withBorrow") t_1 t_2 | bold("split") t | bold("join") t_1 t_2
$

The creation of mutable borrows is via $bold("withBorrow")$ with the following typing:

#v(0.5em)
#align(center)[
#prooftree(
  rule(
    name: [withBorrow],
    $Gamma_1 ⊢ t_1 : ucol(*) A$,
    $Gamma_2 ⊢ t_2 : withB_1 A lolli withB_1 B$,
    $Gamma_1 + Gamma_2 ⊢ bold("withBorrow") t_1 t_2 : ucol(*) B$
  )
)
]
#v(0.5em)

Here, we allow for a uniquely owned $ucol(*) A$ value to be borrowed and manipulated in a mutable way by some function $t_2$ which expects a $withB_1 A$ as input, so long as it returns the mutable borrow as a $withB_1 B$ in the output so that the original owner can reclaim this as a unique reference ($ucol(*) B$). By encapsulating the mutable borrow behaviour inside a continuation, we ensure that it is impossible to construct a closed term with a borrowed type, which means borrowed references to values must always eventually return full access to the owner of said value.

*Uniqueness as uniquely borrowed.*

We absorb the development of @sec:uniqueness by the inclusion of $* in p$ and a type identity $ucol(*) A equiv withB_* A$. Thus, the borrowing graded modality captures both (uniquely) owned and borrowed values and hence functions polymorphic in their permission can range over both kinds of ownership. Furthermore, this enables us to later define operations that can work over uniquely owned or mutably borrowed values without needing multiple primitives.

*Immutable borrows.*

We generalise further to _immutable borrows_, wherein multiple references to a value can exist at any given time as long as they are unable to be mutated (as otherwise this would violate memory safety and lead to, e.g., data races). Mutable borrows are already graded with permission $1$, representing full unfettered access to a value, so both reads and writes are permissible (shown later for resources). The $bold("split")$ and $bold("join")$ constructs generalise mutable borrows, with typing:

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [split],
      $Gamma ⊢ t : withB_p A$,
      $Gamma ⊢ bold("split") t : withB_(p / 2) A tensor withB_(p / 2) A$
    )
  ),
  prooftree(
    rule(
      name: [join],
      $Gamma_1 ⊢ t_1 : withB_p A$,
      $Gamma_2 ⊢ t_2 : withB_q A$,
      $Gamma_1 + Gamma_2 ⊢ bold("join") t_1 t_2 : withB_(p + q) A$
    )
  )
)
#v(0.5em)

where $bold("split")$ takes a borrowed reference and splits it into two borrowed references to the same value, each graded by half of the original permission.#footnote[could be generalised to produce a vector with any number $n$ of $withB_(p / n) A$, or even to arbitrary permissions $q$ and $q'$ such that $q + q' = p$, but here we restrict to halving for simplicity.] The dual *join* (re)combines two borrows into one with their permissions added. Due to the interfaces for manipulating resources (shown later), the type $A$ above will always contain a resource identifier, so it is never possible to combine references to two different values. The addition and halving operations are defined only for fractions $f$, not $*$.

These rules do not encompass every detail of Rust's intricate ownership system; they instead aim to represent the _core_ concepts of ownership and borrowing in such a way that they can integrate into an existing graded type system, leaving room for potential extensions. In particular, as was mentioned in @sec:key, we only support _lexical_ lifetimes, meaning that there is a class of programs which are accepted by Rust's compiler but cannot be represented in this calculus. We focus on being able to represent notions of ownership _explicitly_ in the types, rather than using a complex static analysis like Rust's borrow checker to _infer_ which programs are safe.

The following code demonstrates how all of these new primitives can be put together in a simple Granule program:

#codebox(title: "Granule")[
```haskell
observe : forall {p : Fraction} . &p Colour -> &p Colour

exampleBorrow : *Colour -> *Colour
exampleBorrow persimmon =
  withBorrow (\b ->
    let (x, y) = split b in
    let x' = observe x in
    let b = join (x', y) in b) persimmon
```
]

In `exampleBorrow`, we _mutably_ borrow the value as `b`, split this into two _immutable_ borrows `x` and `y`, and apply `observe` to `x` before rejoining the borrows and returning the value.

The unsafe patterns demonstrated in @sec:key are also unrepresentable in Granule. It is impossible for two mutable borrows or for a mutable borrow and an immutable borrow to coexist here, since splitting a borrow must reduce the permission in its type by the nature of the primitive. We can, however, represent _reborrowing_; this simply involves continuing to split immutable borrows further, where recovering the original value now requires collecting all of the borrows once more:

#codebox(title: "Granule")[
```haskell
exampleReborrow : *Colour -> *Colour
exampleReborrow amethyst =
  withBorrow (\b ->
    let (x, y) = split b in
    let (l, r) = split x in
    let x' = join (r, l) in
    let b = join (y, x') in b) amethyst
```
]

*Resources.*

Enforcing which behaviours should be allowed for different permissions on a given resource is mediated by said resource's interface. We give two in-depth examples: mutable arrays of floats, and polymorphic references.

First, we extend our calculus with primitive types of resources:

$
  A &::= ldots | Res_id A | bb(N) | bb(F) \
  Res &::= sans("Array") | sans("Ref")
$

where $bb(N)$ are natural numbers, $bb(F)$ are floating-point numbers, and resources $Res$ are indexed by an identifier. Our interface for mutable arrays provides the following primitives:

$
  0 dot.op Gamma ⊢ bold("newArray") &: bb(N) lolli exists id. ucol(*) (sans("Array")_id bb(F)) \
  0 dot.op Gamma ⊢ bold("readArray") &: withB_p (sans("Array")_id bb(F)) lolli bb(N) lolli bb(F) tensor withB_p (sans("Array")_id bb(F)) \
  0 dot.op Gamma ⊢ bold("writeArray") &: withB_p (sans("Array")_id bb(F)) lolli bb(N) lolli bb(F) lolli withB_p (sans("Array")_id bb(F)) quad (p equiv 1 or p equiv *) \
  0 dot.op Gamma ⊢ bold("deleteArray") &: ucol(*) (sans("Array")_id bb(F)) lolli sans("unit")
$

In Granule, $bold("readArray")$ is polymorphic in the permission:

#codebox(title: "Granule")[
```haskell
readFloatArray : forall {p : Fraction, id : Name} . &p (FloatArray id) -> Int -> (Float, &p (FloatArray id))
```
]

The following example illustrates the application of these primitives:

#codebox(title: "Granule")[
```haskell
exampleArray : Float
exampleArray =
  unpack <id, a> = newFloatArray 3 in
  let a' = writeFloatArray a 1 4.2 in
  let (f, a'') = readFloatArray a' 1 in
  let () = deleteFloatArray a'' in f
```
]

We can also apply $bold("clone")$ to make a deep copy of a unique array:

#codebox(title: "Granule")[
```haskell
exampleClone : ()
exampleClone =
  unpack <id, a> = newFloatArray 3 in
  clone (share a) as x in
  unpack <id', a'> = x in
  deleteFloatArray a'
```
]

The interface for polymorphic references is similar:

$
  0 dot.op Gamma ⊢ bold("newRef") &: A lolli exists id. ucol(*) (sans("Ref")_id A) \
  0 dot.op Gamma ⊢ bold("readRef") &: withB_p (sans("Ref")_id (Box_(lcol(r)) A)) lolli A tensor withB_p (sans("Ref")_id (Box_(lcol(r)) A)) \
  0 dot.op Gamma ⊢ bold("swapRef") &: withB_p (sans("Ref")_id A) lolli A lolli A tensor withB_p (sans("Ref")_id A) quad (p equiv 1 or p equiv *) \
  0 dot.op Gamma ⊢ bold("freezeRef") &: ucol(*) (sans("Ref")_id A) lolli A
$

#codebox(title: "Granule")[
```haskell
exampleReference : (Float, Float)
exampleReference =
  unpack <id, ref> = newRef 0.0 in
  let (x, ref') = swapRef ref 42.0 in
  let y = freezeRef ref' in (x, y)

test : Float [6]
test = [42.0]

exampleGraded : (Float [4], Float [2])
exampleGraded =
  unpack <id, ref> = newRef test in
  let ([x], ref') : (Float [4], *(Ref id (Float [2]))) = readRef ref in
  let [y] : Float [2] = freezeRef ref' in ([x], [y])
```
]

We can now give the inductive definition of the $sans("copyable")$ and $sans("cloneable")$ predicates:

#v(0.5em)
#grid(
  columns: (1fr, 1fr, 1.3fr),
  align: center + horizon,
  prooftree(rule($sans("copyable")(sans("unit"))$)),
  prooftree(rule($sans("copyable")(bb(F))$)),
  prooftree(rule(
    $sans("copyable")(A)$,
    $sans("copyable")(B)$,
    $sans("copyable")(A tensor B)$
  ))
)

#v(0.5em)
#grid(
  columns: (1fr, 1.4fr, 1.3fr),
  align: center + horizon,
  prooftree(rule($sans("cloneable")(sans("Array")_id bb(F))$)),
  prooftree(rule(
    $sans("cloneable")(A) or sans("copyable")(A)$,
    $sans("cloneable")(sans("Ref")_id A)$
  )),
  prooftree(rule(
    $sans("cloneable")(A)$,
    $sans("cloneable")(B)$,
    $sans("cloneable")(A tensor B)$
  ))
)
#v(0.5em)

*Resource allocators.*

Here, the restriction introduced on the promotion rule in @sec:core meaning that 'resource allocators' are forbidden from being promoted becomes crucial for ensuring soundness in the call-by-value setting. Consider:

#codebox(title: "Pseudocode")[
```haskell
let [x] : ((*(Array id Float)) [2]) = [newArray 1] in
let () = deleteArray x in
writeArray x 0 1.0
```
]

The solution we apply here is to syntactically restrict promotion to terms which do not allocate resources, via the predicate $sans("resourceAllocator")(t)$.

== Equational theory
<sec:equational>

The typing suggests a close relationship between $withB_* A$ and $withB_1 A$. By analogy to relative monads, $withB_* A$ acts as a 'relative functor' with regard to $withB_1 A$:

$
  bold("withBorrow") (lambda x. x) t &equiv t \
  bold("withBorrow") (lambda x. f (g x)) t &equiv bold("withBorrow") f (bold("withBorrow") g t)
$

Lastly, *split* and *join* satisfy:

$
  bold("let") (x, y) = bold("split") t bold("in") bold("join") x y &equiv t \
  bold("split") (bold("join") t_1 t_2) &equiv (t_1, t_2)
$

== Divide and conquer: partial views via distributive laws
<sec:distrib>

We introduce two constructs for distributing the borrowing graded modality into and out of products:

#v(0.5em)
#grid(
  columns: (1fr, 1fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [push],
      $Gamma ⊢ t : withB_p (A tensor B)$,
      $Gamma ⊢ bold("push") t : withB_p A tensor withB_p B$
    )
  ),
  prooftree(
    rule(
      name: [pull],
      $Gamma ⊢ t : withB_p A tensor withB_p B$,
      $Gamma ⊢ bold("pull") t : withB_p (A tensor B)$
    )
  )
)
#v(0.5em)

#codebox(title: "Granule")[
```haskell
examplePartial : *Colour -> *Colour
examplePartial indigo =
  let (r, p) = push indigo in
  let r' = withBorrow alter r in
  pull (r', p)
```
]

This notion extends gracefully to structures containing more than two components. For example, to borrow a single element from a unique tuple of three values, leaving the remaining two values available to their original owner, we can use nested products, e.g. $star(A tensor (B tensor C))$, and push and pull to then access just one part, similarly to in `indigo`. We may need to push twice in order to distribute the modality over the entire product depending on which component we are borrowing, but in the same way as above we can use `withBorrow` to extract the desired data (for example, $withB_1 A$) while applying pull to recover the remaining structure (in this case, of type $star(B tensor C)$).

Partial borrowing allows safe mutation of disjoint parts of a single data structure concurrently without risking a data race, e.g., using `par` for concurrent threads @marshall2022replicate:#footnote[One might wonder whether the $Box_r$ modality also distributes in this way; the answer is not in general, though some choices of semiring permit this behaviour. This question has been explored in depth in prior work @hughes2021linear.]

#codebox(title: "Granule")[
```haskell
par : forall {a b : Type} . (() -> a) -> (() -> b) -> (a, b) -- Granule's parallel composition

exampleConcurrent : *Colour -> *Colour
exampleConcurrent indigo =
  let (r, p) = push indigo in
  let (g, b) = push p in
  let (r', b') = par (\() -> withBorrow alter r)
                     (\() -> withBorrow alter b) in
  let p' = pull (g, b') in
  pull (r', p')
```
]

Building on this core concept in the more expressive setting of Granule's full type system could involve notions such as borrowing from any algebraic data type, or borrowing a 'slice' of multiple values. One low-hanging fruit is to extend the `push` and `pull` primitives in order to derive generic operations for arbitrary data structures, following patterns described in prior work @hughes2021deriving. We do not formalise this again here, but the approach allows for writing programs like:

#codebox(title: "Granule")[
```haskell
exampleDeriving : forall {p : Fraction} . &p (Maybe Colour) -> Either () (&p Colour)
exampleDeriving octarine =
  case (push@Maybe octarine) of
    Nothing -> Left ()
    Just x  -> Right x
```
]

Here, the borrow modality is distributed into the `Maybe` data type using a derived push operation. This general pattern for partial borrowing relates closely to McBride's notion of computing the derivative of a data type by finding its type of one-hole contexts @mcbride2001derivative, where the derivative describes the structure that remains after borrowing one element. Under this interpretation, borrowing a slice of multiple values would be akin to taking the derivative of a data type with respect to another type---an idea described elsewhere in recent work @marshall2022take.

*Parallel sum example.* To conclude this section, we present one last example which combines all of the elements we have introduced here in a more practical setting. The result will be a function which splits a unique mutable array of floats into two immutably borrowed halves and computes their sums concurrently, returning the total sum inside a polymorphic reference.

First, in order to implement this function elegantly we will need two additional basic functions for working with arrays and references. Within Granule it is possible to derive a `writeRef` operation which destructively mutates the value inside a reference, as long as the type of said value allows for it to be discarded freely; this makes use of Granule's existing mechanism for deriving a drop operation for this kind of value @hughes2021deriving. Granule also provides an additional primitive for taking the length of an array, which is useful for iteration but was elided from our formal calculus for brevity. The types of both of these operations are given below.

#codebox(title: "Granule")[
```haskell
lengthFloatArray : forall {id : Name, p : Fraction} . &p (FloatArray id) -> (!Int, &p (FloatArray id))
writeRef : forall {id : Name, a : Type} . {Droppable a} => a -> &1 (Ref id a) -> &1 (Ref id a)
```
]

We begin by defining a simple recursive auxiliary function for iterating through an array of floats and summing all values between two given indices.

#codebox(title: "Granule")[
```haskell
sumFromTo : forall {id : Name, p : Fraction} . &p (FloatArray id) -> !Int -> !Int -> (Float, &p (FloatArray id))
sumFromTo array [i] [n] =
  if i == n then (0.0, array)
  else
    let (x, a) = readFloatArray array i in
    let (y, arr) = sumFromTo a [i+1] [n] in
    (x + y, arr)
```
]

Finally, we define the core `parSum` function as described above. Note in particular the usage of `withBorrow` to borrow an initial reference to the mutable array, `split` and `join` to manage the forking dataflow when computing the sums for the two separate halves in parallel, and `push` and `pull` to distribute modalities into and out of products. A more comprehensive version of this example is presented in the appendices, including full definitions for all auxiliary functions and an illustration of how this function could be applied in practice to a freshly created pair of an array (which is generated from a length-indexed vector) and a polymorphic reference.

#codebox(title: "Granule")[
```haskell
parSum : forall {id id' : Name} . *(FloatArray id) -> *(Ref id' Float) -> *(Ref id' Float, FloatArray id)
parSum array ref =
  let ([n], array) : (!Int, *(FloatArray id)) = lengthFloatArray array;
      compIn = pull (ref, array)
  in withBorrow (\compIn ->
       let (ref, array) = push compIn;
           (array1, array2) = split array; -- immutable borrow happens here

           -- Compute in parallel
           ((x, array1), (y, array2)) =
             par (\() -> sumFromTo array1 [0] [div n 2])
                 (\() -> sumFromTo array2 [div n 2] [n]);

           -- Update the reference
           ref' = writeRef ((x : Float) + y) ref;
           compOut = pull (ref', join (array1, array2)) -- end immutable borrow

       in compOut) compIn
```
]
