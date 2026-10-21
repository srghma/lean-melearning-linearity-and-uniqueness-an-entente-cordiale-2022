#import "common.typ": *

We recap Granule's core calculus which incorporates graded modal types into a linear type theory #cite(<orchard2019quantitative>); we later extend this calculus with our functional model of uniqueness and borrowing. This section covers the syntax and static semantics (type system), whilst @sec:semantics gives an operational semantics incorporating the various extensions discussed throughout this work.

The calculus extends the linear $lambda$-calculus with multiplicative products and unit, and a _semiring-graded necessity modality_ $Box_(lcol(r)) A$ where $r$ is an element of a pre-ordered semiring $(lcol(cal(R)), lcol(*), lcol(1), lcol(+), lcol(0), lcol(sqle))$ which includes a requirement that $lcol(*)$ and $lcol(+)$ must be monotonic with respect to the ordering $lcol(sqle)$. This calculus gives a simplified monomorphic subset of Granule @orchard2019quantitative, and closely resembles other graded systems from the literature #cite(label("10.1145/3622843")) @brunel2014core @petricek2014coeffects @gaboardi2016combining @mcbride2016got @atkey2018syntax @abel2020 @choudhury2021graded #cite(<moon2021graded>). Our extensions for ownership and borrowing could be made compatible with such systems, as they do not rely on particular details of the core calculus in question.

Beyond existing work, we add existential types and type variables (restricted to a particular kind) to track identifiers associated with resources (whose dataflow paths may fork and join, due to the borrowing patterns we discuss later). These identifiers explicitly name and identify a resource at the type level such that references to different resources cannot be interchanged or joined as they will have different types, distinguished by the identifier. This will be illustrated in depth in @sec:fractional when we discuss particular examples of resources that can be managed by ownership.

== Syntax
<syntax>

Our syntax consists of the linear $lambda$-calculus with multiplicative products and unit (first line of syntax below), graded modal terms (second line) and existentially quantified identifiers (third line):

$
  t &::= x | lambda x. t | t_1 t_2 | (t_1, t_2) | bold("let") (x, y) = t_1 bold("in") t_2 | () | bold("let") () = t_1 bold("in") t_2 \
    &quad | [t] | bold("let") [x] = t_1 bold("in") t_2 \
    &quad | bold("pack") langle id, t rangle | bold("unpack") langle id, x rangle = t_1 bold("in") t_2
$

Following the syntax of variables, we group terms above into pairs of introduction and elimination forms, for functions, products, units, the graded modality, and existential types respectively. The meaning of these terms is explained in the next subsection with reference to their typing.

== Type system
<type-system>

Typing judgments have the form $Gamma ⊢ t : A$, assigning type $A$ to term $t$ under context $Gamma$. Types are:

$
  A, B ::= A lolli B | A tensor B | sans("unit") | Box_(lcol(r)) A | exists id. A
$

Hence, our type syntax comprises linear function types $A lolli B$, linear multiplicative products $A tensor B$, a linear multiplicative unit $sans("unit")$, the graded modality $Box_(lcol(r)) A$ where $lcol(r) in lcol(cal(R))$, and existentially quantified types where $id : sans("Name")$ for an abstract kind of names $sans("Name")$.

Contexts $Gamma$ contain both linear assumptions $x : A$, graded assumptions $lcol(x : [A]_r)$ which have originated from inside a graded modality, and type variables which we write as $id$ due to their restricted purpose here, omitting the kind which is the abstract type $sans("Name")$:

$
  Gamma ::= emptyset | Gamma, x : A | Gamma, lcol(x : [A]_r) | Gamma, id
$

Typing of the $lambda$-calculus fragment is then by the following rules:

#v(0.5em)
#grid(
  columns: (1fr, 1.2fr, 1.5fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [var],
      $0 dot.op Gamma, x : A ⊢ x : A$
    )
  ),
  prooftree(
    rule(
      name: [abs],
      $Gamma, x : A ⊢ t : B$,
      $Gamma ⊢ lambda x. t : A lolli B$
    )
  ),
  prooftree(
    rule(
      name: [app],
      $Gamma_1 ⊢ t_1 : A lolli B$,
      $Gamma_2 ⊢ t_2 : A$,
      $Gamma_1 + Gamma_2 ⊢ t_1 t_2 : B$
    )
  )
)
#v(0.5em)

The #smallcaps[var], #smallcaps[abs], and #smallcaps[app] rules are the standard rules of the linear $lambda$-calculus, augmented with a notion of _contraction_ captured by the $+$ operation on contexts coming from multiple sub-terms, which is only defined when contexts are disjoint with respect to linear assumptions, and on overlapping graded assumptions we add their grades, e.g. $(Gamma_1, lcol(x : [A]_r)) + (Gamma_2, lcol(x : [A]_s)) = (Gamma_1 + Gamma_2), lcol(x : [A]_(r + s))$. More explicitly, context addition is declaratively specified as follows:

$
  (Gamma, x : A) + Gamma' &= (Gamma + Gamma') , x : A quad &&"iff" x in.not |Gamma'| \
  Gamma + (Gamma', x : A) &= (Gamma + Gamma') , x : A quad &&"iff" x in.not |Gamma| \
  (Gamma, lcol(x : [A]_r)) + (Gamma', lcol(x : [A]_s)) &= (Gamma + Gamma') , lcol(x : [A]_(r + s)) \
  emptyset + Gamma &= Gamma \
  Gamma + emptyset &= Gamma \
  (Gamma, id) + (Gamma', id) &= (Gamma + Gamma'), id
$

In the first two cases, $x$ may be $i d$ with $A = sans("Name")$ implicitly. This is a declarative rather than algorithmic specification of $+$ as graded assumptions of the same variable may appear in different positions within the two contexts. The #smallcaps[var] rule also embeds the notion of _weakening_, allowing a context of variables graded by $0$, using the partial operation of _scalar multiplication of a context_:

$
  r dot.op emptyset &= emptyset \
  r dot.op (Gamma, lcol(x : [A]_s)) &= (r dot.op Gamma), lcol(x : [A]_(r * s)) \
  r dot.op (Gamma, id) &= (r dot.op Gamma), id
$

scaling graded assumptions by $r$, preserving $id$s, but undefined if $Gamma$ contains linear assumptions.

The rules involving graded modalities are then:

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  row-gutter: 1.5em,
  align: center + horizon,
  prooftree(
    rule(
      name: [pr],
      $r dot.op Gamma ⊢ t : A$,
      $Gamma ⊢ [t] : Box_(lcol(r)) A$
    )
  ),
  prooftree(
    rule(
      name: [elim],
      $Gamma_1 ⊢ t_1 : Box_(lcol(r)) A$,
      $Gamma_2, lcol(x : [A]_r) ⊢ t_2 : B$,
      $Gamma_1 + Gamma_2 ⊢ bold("let") [x] = t_1 bold("in") t_2 : B$
    )
  ),
  prooftree(
    rule(
      name: [der],
      $Gamma, x : A ⊢ t : B$,
      $Gamma, lcol(x : [A]_1) ⊢ t : B$
    )
  ),
  prooftree(
    rule(
      name: [approx],
      $Gamma, lcol(x : [A]_r) ⊢ t : B$,
      $s sqle r$,
      $Gamma, lcol(x : [A]_s) ⊢ t : B$
    )
  )
)
#v(0.5em)

The #smallcaps[pr] rule (_promotion_) introduces a graded modality with grade $r$, implying that the result of $t$ can be used in an '$r$-like' way and thus all of the dependencies of $t$ must be scaled by $r$ to propagate usage to the dependencies, none of which are allowed to be linear. Promotion also contains an explicit restriction that the value to be promoted must not be a _resource allocator_, designed to avoid problems that otherwise arise when promoting values with certain behaviours in a call-by-value setting; we will discuss this in detail when we describe our interface for mutable arrays in @sec:fractional.

The #smallcaps[elim] rule eliminates a graded modality, capturing the idea that a requirement for $x$ to be used in an '$r$-like' way in $t_2$ can be matched with the capability of $t_1$ described by its graded modal type. In Granule, this construct is folded into pattern matching: we can 'unbox' (eliminate) a graded modality to provide a graded variable in the body of the function (the analogue to $t_2$ in this rule).

The #smallcaps[der] rule (_dereliction_) connects linear typing to graded typing, stating that a requirement for a linear assumption is satisfied by an assumption graded by $1$. The #smallcaps[approx] rule converts a grade $r$ to $s$ if $s$ _approximates_ $r$ according to the semiring's pre-order $sqle$.

One possible choice of semiring is that of natural numbers $(bb(N), *, +, 0, 1, equiv)$ with _discrete ordering_ $equiv$ such that there is no approximation and we track the exact number of times a term has been used. We could instead use the standard $<=$ ordering on natural numbers which would permit approximation, allowing for an _upper bound_ on a term's usage. Another useful semiring is on _intervals_ of natural numbers. Here, we can use a grade such as $[0..1]$ to represent a value which can be used _either_ zero or one times; this captures the notion of an _affine_ value. Other interesting semirings include lattices for security levels @gaboardi2016combining @abel2020, hardware schedules @ghica2014coeffects, and sets for abstract property tracking.

Finally, we have the rules for introducing and eliminating tensor products and the multiplicative unit, which are standard, though it is important to remember that products are _linear_ and so it is not possible to freely discard either side: both elements must be used when consuming a product.

#v(0.5em)
#grid(
  columns: (1fr, 1fr),
  row-gutter: 1.5em,
  align: center + horizon,
  prooftree(
    rule(
      name: [$tensor_I$],
      $Gamma_1 ⊢ t_1 : A$,
      $Gamma_2 ⊢ t_2 : B$,
      $Gamma_1 + Gamma_2 ⊢ (t_1, t_2) : A tensor B$
    )
  ),
  prooftree(
    rule(
      name: [$tensor_E$],
      $Gamma_1 ⊢ t_1 : A tensor B$,
      $Gamma_2, x : A, y : B ⊢ t_2 : C$,
      $Gamma_1 + Gamma_2 ⊢ bold("let") (x, y) = t_1 bold("in") t_2 : C$
    )
  ),
  prooftree(
    rule(
      name: [$1_I$],
      $0 dot.op Gamma ⊢ () : unitT$
    )
  ),
  prooftree(
    rule(
      name: [$1_E$],
      $Gamma_1 ⊢ t_1 : unitT$,
      $Gamma_2 ⊢ t_2 : A$,
      $Gamma_1 + Gamma_2 ⊢ bold("let") () = t_1 bold("in") t_2 : A$
    )
  )
)
#v(0.5em)

The following gives an example derivation assuming the natural number semiring:

#v(0.5em)
#align(center)[
#prooftree(
  rule(
    name: [app],
    rule(
      name: [abs],
      rule(
        name: [$tensor_I$],
        rule($x : A tensor A ⊢ x : A tensor A$, name: [var]),
        rule($lcol(y : [A]_1) ⊢ y : A$, name: [var$'$]),
        $lcol(y : [A]_1), x : A tensor A ⊢ (x, y) : (A tensor A) tensor A$
      ),
      $lcol(y : [A]_1) ⊢ lambda x. (x, y) : (A tensor A) lolli ((A tensor A) tensor A)$
    ),
    rule(
      name: [$tensor_I$],
      $emptyset ⊢ v : A$,
      rule($lcol(y : [A]_1) ⊢ y : A$, name: [var$'$]),
      $lcol(y : [A]_1) ⊢ (v, y) : A tensor A$
    ),
    $lcol(y : [A]_2) ⊢ (lambda x. (x, y)) (v, y) : ((A tensor A) tensor A)$
  )
)
]
#v(0.5em)

where (var$'$) is a synonym for the (var) rule followed by dereliction (der).

As a first taste of Granule syntax (which resembles Haskell, apart from the presence of the graded modal type constructs), the following captures the same idea as this example:

#codebox(title: "Granule")[
```haskell
exampleNat : forall {a : Type} . a -> a [2] -> ((a, a), a)
exampleNat v yb = let [y] = yb in (\x -> (x, y)) (v, y)
```
]

The type $Box_(lcol(r)) A$ is instead written postfix as `a [r]`, and Granule uses `->` for its linear function types.

Existential types have standard introduction and elimination typing forms, but restricted only to type variables of kind $sans("Name")$ (whose kind is omitted here for simplicity due to this restriction):

#v(0.5em)
#grid(
  columns: (1fr, 1.3fr),
  align: center + horizon,
  prooftree(
    rule(
      name: [pack],
      $Gamma ⊢ t : A$,
      $id in.not sans("dom")(Gamma)$,
      $Gamma ⊢ bold("pack") langle id', t rangle : exists id. A [id \/ id']$
    )
  ),
  prooftree(
    rule(
      name: [unpack],
      $Gamma_1 ⊢ t_1 : exists id. A$,
      $Gamma_2, id, x : A ⊢ t_2 : B$,
      $id in.not sans("fv")(B)$,
      $Gamma_1 + Gamma_2 ⊢ bold("unpack") langle id, x rangle = t_1 bold("in") t_2 : B$
    )
  )
)
#v(0.5em)

*Note on Linear Haskell.* As mentioned at the start of this section, we aim for the extensions we develop throughout this work to be compatible with other graded type systems after some adaptation. One particular system of interest is the calculus underlying the recent extension which introduces linear types to Haskell @bernardy2017linear. This extension uses a graded type system below the surface in order to implement linearity; all function types are given a 'multiplicity' annotation $r$ written `(a %r -> b)` akin to a type $Box_r A lolli B$ here, where the annotation can be either `'One` or `'Many` representing either linear or unrestricted usage respectively. Work on formalising the connection between systems like this where all function types come with a grade (sometimes called 'graded base') and systems such as Granule's where values are linear by default and graded values are wrapped inside a modality (called 'linear base') is ongoing @vollmer2024mixed.

