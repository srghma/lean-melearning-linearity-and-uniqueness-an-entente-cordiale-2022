#import "@preview/curryst:0.6.0": prooftree, rule

// Document setup
#set document(
  title: "Linearity and Uniqueness: An Entente Cordiale",
  author: ("Daniel Marshall", "Michael Vollmer", "Dominic Orchard"),
)

#set page(
  paper: "a4",
  margin: (x: 2.2cm, top: 2.5cm, bottom: 2.5cm),
  header: context {
    if here().page() > 1 {
      smallcaps[Linearity and Uniqueness: An Entente Cordiale]
      h(1fr)
      str(here().page())
    }
  },
)

#set text(font: "Libertinus Serif", size: 10pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")

// Domain-specific math macros
#let lolli = $⊸$
#let tensor = $⊗$
#let unitT = $bold(1)$
#let sqle = $⊑$
#let comprel = $bowtie$
#let circ = $compose$
#let le = $<=$
#let squig = $arrow.zigzag$
#let bang = $!$
#let star = $*$
#let dom = math.op("dom")
#let arrRefs = math.op("arrRefs")
#let copyop = math.op("copy")
#let over(x) = $overline(#x)$

// Code block helper with language/status tag
#let codebox(title: none, body) = {
  block(
    width: 100%,
    stroke: rgb("cbd5e1"),
    radius: 3pt,
    inset: 0.8em,
    fill: rgb("f8fafc"),
    stack(
      if title != none {
        align(right, text(size: 8pt, fill: rgb("64748b"), style: "italic", title))
      },
      v(if title != none { 0.3em } else { 0em }),
      body
    )
  )
}

// Metadata / Header
#align(center)[
  #v(0.5em)
  #text(1.6em, weight: "bold")[Linearity and Uniqueness: An Entente Cordiale]\
  #v(0.8em)
  #text(1.1em)[Daniel Marshall#super[1], Michael Vollmer#super[1], and Dominic Orchard#super[1,2]]\
  #v(0.4em)
  #text(0.9em)[
    #super[1] University of Kent, Canterbury, UK \
    `{dm635,m.vollmer,d.a.orchard}@kent.ac.uk` \
    #super[2] University of Cambridge, UK
  ]\
  #v(1.2em)
]

#block(
  fill: rgb("f1f5f9"),
  stroke: rgb("cbd5e1"),
  inset: 1.2em,
  radius: 4pt,
)[
  #align(center)[*Abstract*]
  #set text(size: 9pt)
  Substructural type systems are growing in popularity because they allow for a resourceful interpretation of data which can be used to rule out various software bugs. Indeed, substructurality is finally taking hold in modern programming; Haskell now has linear types roughly based on Girard’s linear logic but integrated via graded function arrows, Clean has uniqueness types designed to ensure that values have at most a single reference to them, and Rust has an intricate ownership system for guaranteeing memory safety. But despite this broad range of resourceful type systems, there is comparatively little understanding of their relative strengths and weaknesses or whether their underlying frameworks can be unified. There is often confusion about whether linearity and uniqueness are essentially the same, or are instead ‘dual’ to one another, or somewhere in between. This paper formalises the relationship between these two well-studied but rarely contrasted ideas, building on two distinct bodies of literature, showing that it is possible and advantageous to have both linear and unique types in the same type system. We study the guarantees of the resulting system and provide a practical implementation in the graded modal setting of the Granule language, adding a third kind of modality alongside coeffect and effect modalities. We then demonstrate via a benchmark that our implementation benefits from expected efficiency gains enabled by adding uniqueness to a language that already has a linear basis.

  #v(0.5em)
  *Keywords:* linear types $dot$ uniqueness types $dot$ substructural logic
]

#v(1em)

= Introduction
<sec:introduction>

Linear types @ref15 @ref57 and uniqueness types @ref5 @ref47 are two influential and long-standing flavours of substructural type system. As these approaches have developed, it has become clear in the community (both in folklore and the literature) that these are closely related ideas. For example, the chapter on substructurality in _Advanced Topics in Types and Programming Languages_ @ref62 describes uniqueness types as “a variant of linear types”. This framing is supported by various works which, for example, make reference to “a form of linearity (called uniqueness)” @ref33 or other such statements of equality or similarity @ref38.

But reading a different set of papers gives a contrasting impression that linearity and uniqueness are not the same but in some sense dual to one another, and with different behaviour for at least some applications. Recent work on linear types for Haskell @ref7 describes the two concepts as being “at their core, dual” and later having a “weak duality”. The impression that these two approaches behave differently is backed up by much of the theoretical work on uniqueness types, with one paper stating that “although both linear logic and uniqueness typing are substructural logics, there are important differences” @ref56, closely followed by a tantalising mention of the fact that “some systems based on linear logic are much closer to uniqueness typing than to linear logic”.

It is clear, at least, that both linear types and uniqueness types are substructural type systems: they both restrict structural rules (in particular, contraction and weakening) of type systems that are the Curry-Howard counterparts to regular intuitionistic logic. This captures the well-known maxim that “not all things in life are free” @ref61; many kinds of data behave resourcefully, and are subject to constraints on their usage. Sensitive data should not be infinitely duplicated and passed around freely, file handles should not be arbitrarily discarded without being properly closed, and communication channels should not be used without adherence to a fixed protocol, to name a few!

Thanks to these clear benefits, notions of substructurality are slowly but surely making their way into the programming ecosystem, with languages such as Haskell @ref7, Idris @ref9, Clean @ref47, Rust @ref24, ATS @ref65, and Granule @ref36 all having type systems that behave substructurally in some way. What is not clear, however, is what exactly the relationship is between these varying systems; for instance, it is not obvious how to relate linearity and uniqueness. Linear types, though they themselves come in various forms, are most often based on the linear logic of Girard @ref15, and in the strictest sense they treat values as resources which must be used exactly once and never again. On the other hand, uniqueness types are named as such because they aim to ensure that values are guaranteed to have at most one reference to them @ref40 @ref45 @ref47 @ref48 @ref55 @ref56, with a view towards allowing them to be safely updated in-place. Do these two requirements always coincide, or are there cases where they diverge?

In this paper, we resolve this long-standing confusion, building on two distinct bodies of literature to develop an accurate understanding of the contexts in which linear and uniqueness types behave the same or behave differently, and their relative strengths and weaknesses. Our primary contributions are as follows:
- In Section 2, we discuss the contrasting understandings of the relationship between linearity and uniqueness, and draw together aspects of these viewpoints to intuitively describe the link between these concepts.
- In Section 3, we formalise these notions by developing a unified calculus and type system that incorporates linear, unique, and Cartesian (unrestricted or non-unique/non-linear) types all at once, building on the linear $lambda$-calculus. We give an operational model via a heap semantics which allows us to prove various key operational guarantees for both linearity and uniqueness.
- In Section 4, as a proof of concept, we implement uniqueness types into the language Granule which already has a linear basis, introducing a third flavour of modality alongside the graded comonadic (coeffectful) and graded monadic (effectful) modalities already present in the language. The implementation enables the classic primary use of uniqueness: access to safe in-place update in a functional language without working inside a monad.
- In Section 4.2, we confirm the performance benefits of uniqueness types by benchmarking the performance of arrays which allow for in-place update. We generate impure Haskell code from our Granule implementation in order to demonstrate that further efficiency can be gained via adding uniqueness types even when your language is already linear at its core.

Section 5 and Section 6 provide related work and discussion, including relation to ideas in Rust. Various additional details are collected in the appendix @ref28, including proofs and collected reduction rules for the operational semantics. We also provide an artifact @ref29, so that the interested reader can experiment with code examples in Granule and reproduce our benchmarks for themselves.

= Key Ideas
<sec:key-ideas>

It is clear that linear and uniqueness types both involve restricting the substructural rules of intuitionistic logic, but what remains unclear is the exact relationship between the two concepts. This section discusses two widespread understandings of their relationship, both of which are accurate in some respects but fail to capture some key similarities and differences. We then combine aspects of both viewpoints to systematically relate linearity and uniqueness.

== Are linearity and uniqueness (essentially) the same?
<sec:same>

Perhaps the most well-known substructural types are _linear types_, which have been studied for decades in the literature @ref57 @ref62 as the Curry-Howard counterpart of linear logic @ref15. Several languages have implemented linear type systems over the years, including ATS @ref65, Alms @ref52 and Quill @ref32, and they are steadily making their way into the mainstream via extensions to languages like Haskell @ref7. Examples of linearity in this paper will focus on the functional language Granule @ref36 (whose syntax resembles Haskell), since values in Granule are linear by default making the examples less complex, and also because Granule will later be the foundation upon which we build our unified calculus.

Strictly, linear types treat values as resources which must be used once and then never again. For instance, we can type the identity function, since it binds a single variable and then uses it, but the K combinator (which discards one of its arguments) is not linearly typed. Thus linearity is a claim about the _consumption_ of a resource: a linear type is a contract, which says that we must consume a value that we are given exactly once. Consider the following classic example (rendered in Granule) of a function which cannot be represented using linear types, assuming an interface where `eat : Cake -> Happy` and `have : Cake -> Cake`:

#codebox(title: "Ill-typed Granule")[
```haskell
impossible : Cake -> (Happy, Cake)
impossible cake = (eat cake, have cake)
```
]

Note that Granule’s function type `->` is the type of linear functions, more traditionally written $lolli$. The above function is ill-typed and the Granule compiler will brand it with a linearity error; this is because the value of type `Cake` passed into the function is a linear resource, and the body of the function requires us to duplicate it (via contraction), which is forbidden. Thus, linear types remind us of the familiar aphorism: _you can't have your cake and eat it too_.

Uniqueness types, on the other hand, are primarily aimed at ensuring that values have only a single reference to them, which is a useful property for ensuring the safety of updating data in-place. But is this uniqueness restriction really so different from the constraints of linearity?

One of the most familiar languages featuring uniqueness types is Clean @ref47, which uses uniqueness for mutable state and input/output, in contrast to languages such as Haskell which use monads for similar purposes. We shall use Clean for our uniqueness examples for the moment, before we introduce our own implementation of uniqueness in Section 4. Consider the following in Clean:

#codebox(title: "Ill-typed Clean")[
```clean
impossible :: *Coffee -> (*Awake, *Coffee)
impossible coffee = (drink coffee, keep coffee)
```
]

We use coffee instead of cake to distinguish unique values from the linear values of the Granule example, but notice this function has exactly the same structure as the previous example. The operator `*` denotes a unique type, since unrestricted values are the default in Clean. Similarly to Granule, when presented with this function Clean gives a uniqueness error; the argument of type `*Coffee` is duplicated, and so we can no longer guarantee there is only one reference to it upon exiting the function. Think of a `*Coffee` as having been freshly poured; we cannot continue acting as though it is fresh once some of it has been drunk!

So far, it seems that the concepts of linearity and uniqueness are very similar after all, as is often claimed. However, neither of these examples uses _unrestricted_ values; we only see values that are linearly typed or uniquely typed. In fact, in a setting where all values must be linear, we can also guarantee that every value is unique, and vice versa! Intuitively, if it is never possible to duplicate a value, then it will never be possible for said value to have multiple references. It is when we also have the ability for unrestricted use (non-linear/non-unique) that differences between linearity and uniqueness begin to arise, as we will soon see.

Much of the classic literature on linear types makes mention of the idea that linearity can be used for tracking whether a value has only one reference, though we know by now that this more accurately describes uniqueness; indeed, one of the oldest such papers by Wadler, which has been (rightly) hugely influential, states that “values of linear type have exactly one reference to them, and so require no garbage collection” @ref57[p. 2]. However, systems akin to the one discussed by Wadler @ref4 @ref18 @ref46 crucially separate values into two completely distinct and (mostly) disconnected linear and non-linear worlds. In this context, a linear value can never have been duplicated previously and thus must also obey the conditions required for uniqueness. Therefore, it is correct to say that a value of linear type has exactly one reference in such a system.

This issue is further discussed in a later article by Wadler @ref58, though uniqueness types had yet to be invented and so the concept is never referred to by this name. Linear types based on linear logic are defined in Section 3 of said article, for which linearity behaves as we understand it: a value having linear type guarantees that it will not be duplicated or discarded, but the notion of _dereliction_ allows a non-linear variable to be used linearly going forwards @ref15. As Wadler states, “dereliction means we cannot guarantee a priori that a variable of linear type has exactly one pointer to it” @ref58[p. 7], and so we cannot guarantee uniqueness of reference in a system based upon linear logic. In Section 7, Wadler goes on to define _steadfast types_, where dereliction and promotion are again restricted to recover the uniqueness guarantee in addition to the linearity restriction.#footnote\[The concept of steadfastness coincides with the notion of “necessarily unique” used in languages such as Clean, where a necessarily unique value is one that is unique and also can never be made non-unique @ref47\.\]

However, never being able to duplicate or discard any value is an overly restrictive view of data, preventing many valid uses of various kinds of information, and so modern languages with linear types therefore generally do provide a mechanism for non-linearity rather than working in the ‘steadfast’ style. Linear logic provides the $!$ modality (also called the _exponential modality_), which allows the representation of non-linear (unrestricted) values. In Granule, we can use this modality to rewrite the previous example into one that is now well-typed:

#codebox(title: "Granule")[
```haskell
possible : !Cake -> (Happy, Cake)
possible lots = let !cake = lots in (eat cake, have cake)
```
]

We can think of `!Cake` values as representing an infinite amount of cake, which is made available once we eliminate the modality (via the `let`) to get an unrestricted (non-linear) variable `cake`. The functions `eat` and `have` are linear functions, so each application in isolation views `cake` linearly, by an implicit use of dereliction in the type system. Crucially, from an unrestricted value we can produce a linear value, so we can impose the restriction of linearity whenever we like. However it is not possible to produce an unrestricted value from a linear one. This restriction means that linear types are useful for representing resources such as file handles, as in the following example:

#codebox(title: "Granule")[
```haskell
twoChars : (Char, Char) <IO>
twoChars = let -- do-notation like syntax
  h       <- openHandle ReadMode "someFile";
  (h, c1) <- readChar h;
  (h, c2) <- readChar h;
  ()      <- closeHandle h
in pure (c1, c2)
```
]

Here, we open a file handle, read two characters from it, and then close it. The linearity of the handle ensures that once we have created it, we must close it properly, and also that we cannot duplicate it along the way. But linearity is less useful in other circumstances. As an example, consider the case of mutable arrays. Discarding an array will not cause any problems,#footnote[One may worry that discarding an array could cause space leaks, but this can be tempered via garbage collection. If a non-linear value will no longer be used we know statically that it can be garbage collected, and thus it is harmless to reuse the space occupied by this value going forwards. This will allow us to update unique objects such as arrays destructively without being concerned about referential transparency.] so a linear array would be too restrictive and not allow for some valid use cases; _affine types_ allow discarding behaviour by adding back in weakening @ref52. But in order to be able to mutate an array we need to be able to guarantee that no other references to it exist, and in this sense linearity is not strong enough; any linear value could have previously been a non-linear one that was duplicated any number of times before being specialised (via dereliction) to a linear type. For representing mutable arrays, we are better served by considering uniqueness types.

Uniqueness behaves differently to linearity in the context of a system with the ability to describe unrestricted values. If we have an unrestricted value, we certainly cannot produce a unique one from it which would violate the guarantee of uniqueness; we cannot claim that a value has only one reference to it when it could have been duplicated and manipulated elsewhere. But conversely, if we have a unique value, there is no harm in dropping this guarantee and producing an unrestricted value; a non-unique value does not need to make any promises about how many references may exist. Thus, in Clean we can write:

#codebox(title: "Clean")[
```clean
possible :: *Coffee -> (Awake, Coffee)
possible coffee = (drink coffee, keep coffee)
```
]

Here, we require that the input is unique (it has type `*Coffee`), so for the function to be well-typed we can no longer claim this value is unique once it reaches the output, as it has been duplicated along the way (and it now must have type `Coffee`). The information here is flowing in the opposite direction than for linearity; the `possible` function in Clean would be ill-typed if we replaced unique values with linear ones, and vice versa for the earlier Granule example. This directionality allows us to represent mutable arrays much more easily with uniqueness. For example, the following destructively fills a real-valued array:

#codebox(title: "Clean")[
```clean
fill :: *{Real} Int -> *{Real}
fill a1 0 = a1
fill a1 i
  # f  = toReal i
  # a2 = {a1 & [i - 1] = f} // write f to index i-1 in a1
  = fill a2 (i - 1)          // recurse with unique array a2
```
]

Here, we take in a unique array of floating point numbers and some unrestricted integer value, and fill the first cells of the array with the numbers up to that value. Here we know that it is safe to write to the array because it is unique, so no other references to it can exist elsewhere; once we are finished with the array later on, however, it is fine to discard it, as with an array in most other functional programming languages, which would not be possible if our array was linearly typed. This however does mean that uniqueness types are not appropriate for the earlier example of file handles—we cannot ensure that a unique file handle is closed, as it can be discarded at any time.

In summary, linearity and uniqueness provide the same guarantees up until a system also has a notion of unrestricted value (non-linear or non-unique). The complementary but distinct use cases shown above make it clear that it would be valuable to have both linear and unique values together in a single language, but this has previously not been possible. Our main contribution is a core calculus that allows linearity and uniqueness to coexist and interact, demonstrated also via an implementation in the Granule language. Next we consider the question of duality, and how to formally describe how linearity and uniqueness differ.

== Are linearity and uniqueness dual?
<sec:dual>

It is common in folklore and in the literature to describe linearity and uniqueness as somehow dual to one another (see e.g., @ref32 @ref52) but rigorous versions of this statement are more rarely found. The earliest formalisation of uniqueness is from Harrington’s ‘uniqueness logic’ @ref20, which we use as a foundation for much of the following. Harrington constructs a logic which is on the surface much like linear logic, but instead of the $!$ modality for non-linearity it includes a $circ$ modality for non-uniqueness which differs from non-linearity in its introduction rule.

In linear logic, the $!$ modality acts as a comonad, such that the introduction of $!$ on the right of a sequent means that all formulae on the left of a sequent must also have $!$ applied, whilst introduction of $!$ on the left is unrestricted:

#align(center)[
  #grid(
    columns: (1fr, 1fr),
    align: center,
    prooftree(rule(name: [$!R$], [$!Gamma tack P$], [$!Gamma tack !P$])),
    prooftree(rule(name: [$!L$], [$Gamma, P tack Q$], [$Gamma, !P tack Q$]))
  )
]

(also known as _storage_ and _dereliction_ respectively @ref16). In contrast, the non-uniqueness modality $circ$ of Harrington acts as a monad, meaning that introduction of $circ$ on the right is unrestricted but introduction of $circ$ on the left of a sequent means that all formulae on the right of the sequent must also have $circ$ applied:

#align(center)[
  #grid(
    columns: (1fr, 1fr),
    align: center,
    prooftree(rule(name: [$circ R$], [$Gamma tack P$], [$Gamma tack P^circ$])),
    prooftree(rule(name: [$circ L$], [$Gamma, P tack Q^circ$], [$Gamma, P^circ tack Q^circ$]))
  )
]

The non-uniqueness modality $circ$ then has the following structural rules for contraction and weakening, which are conspicuously identical to those for the $!$ modality representing non-linearity:

#align(center)[
  #grid(
    columns: (1fr, 1fr, 1fr, 1fr),
    align: center,
    prooftree(rule(name: [$circ C$], [$Gamma, P^circ, P^circ tack R$], [$Gamma, P^circ tack R$])),
    prooftree(rule(name: [$circ W$], [$Gamma tack R$], [$Gamma, P^circ tack R$])),
    prooftree(rule(name: [$!C$], [$Gamma, !P, !P tack R$], [$Gamma, !P tack R$])),
    prooftree(rule(name: [$!W$], [$Gamma tack R$], [$Gamma, !P tack R$]))
  )
]

One might be tempted to think that because the introduction rules for $circ$ behave dually to those of $!$, the modalities are simply dual to one another, and thus non-uniqueness is equivalent to linear logic’s $?$. But since the contraction and weakening rules for $circ$ are the same as those for $!$, this is not quite the case; $circ$ behaves dually to $!$ in some ways but not in others. Formally, $circ$ is a monad while $!$ is a comonad, but both are comonoidal, whereas $?$ is monoidal.

Linear logic allows us to derive $!P tack P$ (from dereliction), which agrees with our notion of linearity where non-linear values can be restricted to behave linearly going forwards but if we have a linear value it must remain linear; uniqueness logic conversely allows us to derive $P tack P^circ$, formalising our concept of uniqueness where we can forget the uniqueness guarantee and turn a unique value into a non-unique one, but if we have a non-unique value we cannot go back.

We can now make more precise the intuitive notion we have developed, which suggests that linear types provide a restriction on what can be done with a value ‘in the future’ whilst uniqueness types provide a guarantee about what has been done with a value ‘in the past’. The distinction becomes clearer when we consider substitutions, which are generated by $beta$-reductions.

Substitutions are the same whether we are working with linear logic or uniqueness logic, as the rules for functions are identical, but the difference arises when thinking about what it is possible to know about a value in one logic compared to the other. Given a linear value, we know that substituting this value into an expression will preserve linearity, as there is no way to transform a linear value into a non-linear one. Conversely, given a unique expression then we know that any values substituted in will not affect the uniqueness guarantee, as there is no way to transform a non-unique value into a unique one. Thus ‘future’ refers to outgoing substitutions, while ‘past’ refers to incoming substitutions.

So if linearity and uniqueness do in fact behave the same in some ways but not all, and they do in fact behave dually in some ways but not all, then what is the overall takeaway? What statement can we make about the relationship between their behaviour that reconciles these two viewpoints?

#v(0.4em)
#block(
  fill: rgb("eff6ff"),
  stroke: rgb("bfdbfe"),
  inset: 0.9em,
  radius: 3pt,
)[
  *Takeaway.* _Linearity and uniqueness behave dually with respect to composition, but identically with respect to structural rules, i.e., their internal plumbing._
]
#v(0.4em)

In other words, internally the non-linear and non-unique modalities are both comonoidal, so they allow for the same behaviour of contraction and weakening for values that are wrapped inside them.

But the duality arises upon considering how we can map into and out of these modalities; we can map out of the non-linear modality and retrieve a linear value, but we can never map into it, giving the modality its familiar comonadic structure. Conversely, we can map a unique value into the non-unique modality to allow for contraction and weakening, but we can never map back out of it, which explains the dual monadic behaviour of this modality.

It is this understanding of the similarities and differences between linearity and uniqueness that will allow us to unify them, and have values of both flavours present in a single type system, which will be our goal for the next section.

= The Linear-Cartesian-Unique Calculus
<sec:calculus>

We now consider how to represent both linearity and uniqueness in the same system. The first choice to make is whether our base values will be linear or unique#footnote[We choose a substructural basis over an unrestricted one since this more closely maps to both linear and uniqueness logic, where values have substructural behaviour by default unless they are wrapped in a modality.], as this will influence the directionality of the modalities we need to include in the calculus. Here we present a system where linearity is the base and uniqueness is a modality, as opposed to one where uniqueness is the base and linearity is a modality, for two reasons:
- The first reason is pragmatic; we later implement our approach in Granule, which already has linear values as the default. Therefore, including uniqueness as an additional modality in the system will require far fewer changes to the language, since a unique base would most likely require a redesign. Moreover, languages with uniqueness types like Clean generally have non-unique values as their default, with uniqueness having to be specifically annotated; a system with a uniqueness modality will also map more closely onto these languages than one where uniqueness is the basis.
- The second reason is that developing a sound calculus with a unique base is more complex. Consider such a hypothetical calculus with a modality $circ$ representing unrestricted values and a modality $bullet$ representing linear values. If we construct a product of linear values $(a^bullet, b^bullet)$, then this product is unique (rather than linear), so we can promote to an unrestricted product $(a^bullet, b^bullet)^circ$ and freely duplicate the product, though the values contained within are linear. A linear base avoids this problem (among others) as products being linear by default means that their usage is maximally restricted, so there is no circumventing either a uniqueness guarantee via their construction or a linearity restriction via their duplication.#footnote[A similar problem arises from the application of unique functions, and this has been a thorn in the side of developers of uniqueness type systems for some time. The solution applied in Clean is that any function with unique elements in its closure is “necessarily unique”, meaning it cannot be subtyped into a non-unique function and applied multiple times. Handily, this coincides with the notion of a linear function, which is why our calculus having a linear base also avoids this problem.]

Given a linear basis, we formalise the idea that we can map from unique to non-unique and from non-linear to linear. The key insight is that _we treat non-linearity and non-uniqueness as the same state as both these states are unrestricted_; we can do anything we like with, and have no guarantees for, an unrestricted value. We write $*P$ for a $P$ with a uniqueness guarantee, similar to the syntax of Clean and to avoid confusion with Harrington’s $circ$ modality for non-uniqueness. The resulting calculus, which we call the Linear-Cartesian-Unique calculus (or LCU for short), builds on (intuitionistic multiplicative exponential) linear logic with additional rules for uniqueness.

*Syntax* LCU’s syntax is that of the linear $lambda$-calculus with multiplicative products and unit (first line of syntax below) with terms for introducing and eliminating the $!$ modality and working with the uniqueness modality (second line):

$
  t &::= x | lambda x. t | t_1 space t_2 | (t_1, t_2) | "let" (x, y) = t_1 "in" t_2 | "unit" | "let unit" = t_1 "in" t_2 \
    &quad | !t | "let!" x = t_1 "in" t_2 | &t | "copy" t_1 "as" x "in" t_2 | *t quad (upright("terms"))
$

The meaning is explained in the next section with reference to typing.

== Typing
<sec:typing>

Typing judgments are of the form $Gamma tack t : A$, with types $A$ defined:
$
  A, B ::= A lolli B | A tensor B | unitT | !A | *A quad (upright("types"))
$
Thus our type syntax comprises linear function types $A lolli B$, linear multiplicative products $A tensor B$, a linear multiplicative unit $unitT$, the non-linearity modality $!A$ and the uniqueness modality $*A$.

Typing contexts are defined as follows:
$
  Gamma ::= emptyset | Gamma, x : A | Gamma, x : [A] quad (upright("contexts"))
$
which are either empty, or contexts extended with a linear assignment $x : A$ or contexts extended with a non-linear assignment denoted $x : [A]$. This marking of assumptions in a context as linear or non-linear (see Terui @ref50) is one way to guarantee substitution is admissible (avoiding, for example, issues pointed out by Wadler where substitution is not well-typed if care is not taken @ref59 @ref60, an issue noted also by Prawitz in 1965 in the context of S4 modal logic @ref42).

Throughout, the comma operator $,$, concatenates disjoint contexts.

We introduce the key typing rules inline. Figure 1 collects the full set of rules. The linear $lambda$-calculus core is typed by the following three rules:

#align(center)[
  #grid(
    columns: (1fr, 1.2fr, 1.3fr),
    align: center,
    prooftree(rule(name: [var], $[Gamma], x : A tack x : A$)),
    prooftree(rule(name: [abs], [$Gamma, x : A tack t : B$], [$Gamma tack lambda x. t : A lolli B$])),
    prooftree(rule(name: [app], [$Gamma_1 tack t_1 : A lolli B$], [$Gamma_2 tack t_2 : A$], [$Gamma_1 + Gamma_2 tack t_1 space t_2 : B$]))
  )
]

In the case of var, a linear variable is used but the rest of the context must be marked as non-linear, denoted by $[Gamma]$ which marks all assumptions as non-linear.

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Definition 1 (All non-linear assumptions).* _A context $Gamma$ is denoted as containing only non-linear assumptions by writing $[Gamma]$ in the typing rules, where $[emptyset]$ and $[Gamma] ==> [Gamma], x : [A]$._
]

In the case of app, the two subterms are typed in different contexts which are then combined via context addition.

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Definition 2 (Context addition).* _The partial operation $+$ on contexts is the union of two contexts as long as they are disjoint in their linear assumptions and any variables occurring in both contexts are both non-linear assumptions, i.e._
  $
    Gamma_1 + Gamma_2 = Gamma_1 union Gamma_2 "iff" forall x in dom(Gamma_1) inter dom(Gamma_2) ==> exists A. Gamma_1(x) = Gamma_2(x) = [A]
  $
]

The non-linear modality $!$ has the following introduction and elimination rules and related dereliction rule:

#align(center)[
  #grid(
    columns: (1fr, 1.6fr, 1.1fr),
    align: center,
    prooftree(rule(name: [$!$I], [$[Gamma] tack t : A$], [$[Gamma] tack !t : !A$])),
    prooftree(rule(name: [$!$E], [$Gamma_1 tack t_1 : !A$], [$Gamma_2, x : [A] tack t_2 : B$], [$Gamma_1 + Gamma_2 tack "let!" x = t_1 "in" t_2 : B$])),
    prooftree(rule(name: [der], [$Gamma, x : A tack t : B$], [$Gamma, x : [A] tack t : B$]))
  )
]

The left-most rule captures the idea that a computation $t$ of value $A$ can be used non-linearly, by ‘promoting’ it to $!A$ as long as all its inputs are also non-linear, denoted by $[Gamma]$ in the context. The middle rule eliminates a non-linear modality (a capability to use an $A$ value non-linearly) by composing it with a variable $x$ which is non-linear in $t_2$. These rules are accompanied by the ‘dereliction’ rule that says non-linear variables can be treated as linear variables.

So far everything is standard from other linear type systems. We now move to our uniqueness modality which has two syntactic constructs: _borrow_ and _copy_:

#align(center)[
  #grid(
    columns: (1.1fr, 1.9fr),
    align: center,
    prooftree(rule(name: [borrow], [$Gamma tack t : *A$], [$Gamma tack &t : !A$])),
    prooftree(rule(name: [copy], [$Gamma_1 tack t_1 : !A$], [$Gamma_2, x : *A tack t_2 : !B$], [$Gamma_1 + Gamma_2 tack "copy" t_1 "as" x "in" t_2 : !B$]))
  )
]

The borrow rule maps a unique value to a non-linear value, allowing a uniqueness guarantee to be forgotten. In terms of the operational semantics (see Section 3.4), this causes evaluation of $t$ before the borrow. Next, the copy rule says that a non-linear value of type $A$ can be copied to produce a unique $A$ which is used by $t_2$; the input is required to be non-linear so that we cannot circumvent a linearity restriction by copying a linear value, and the output is required to be non-unique so that we cannot leverage the copy to smuggle out a value which pretends to be truly unique. These rules in turn are accompanied by the ‘necessitation’ rule that says values can be assumed unique as long as they have no dependencies:

#align(center)[
  #prooftree(rule(name: [nec], [$emptyset tack t : A$], [$[Gamma] tack *t : *A$]))
]

The borrow and copy rules in this logic suggest a monad-like relationship between the $!$ and $*$ modalities, with the borrow rule representing the ‘return’ of the monad and the copy rule likewise acting as the ‘bind’. The $*$ modality is not in itself a monad (or indeed, a comonad like $!$); rather, it acts as a functor over which the $!$ modality becomes a _relative monad_ @ref3. A relative monad comprises a functor $J$ and an object mapping $T$, along with an operation $eta : J X -> T X$ and a mapping from $J X -> T Y$ arrows to $T X -> T Y$ with axioms analogous to the monad axioms. Thus, here $J$ is the uniqueness modality $*$ and $T$ the non-linearity modality $!$. If one imagines the dual version of this logic where the basis is unique, the hypothetical linearity modality would act as a functor making the non-uniqueness modality into a relative comonad @ref1 @ref37 in much the same way.

#v(0.5em)
#figure(
  block(
    width: 100%,
    stroke: rgb("000000"),
    inset: 0.9em,
    stack(
      spacing: 1.1em,
      grid(
        columns: (1fr, 1.2fr, 1.4fr),
        align: center + horizon,
        prooftree(rule(name: [var], $[Gamma], x : A tack x : A$)),
        prooftree(rule(name: [abs], [$Gamma, x : A tack t : B$], [$Gamma tack lambda x. t : A lolli B$])),
        prooftree(rule(name: [app], [$Gamma_1 tack t_1 : A lolli B$], [$Gamma_2 tack t_2 : A$], [$Gamma_1 + Gamma_2 tack t_1 space t_2 : B$]))
      ),
      grid(
        columns: (1fr, 1.4fr),
        align: center + horizon,
        prooftree(rule(name: [$tensor$I], [$Gamma_1 tack t_1 : A$], [$Gamma_2 tack t_2 : B$], [$Gamma_1 + Gamma_2 tack (t_1, t_2) : A tensor B$])),
        prooftree(rule(name: [$tensor$E], [$Gamma_1 tack t_1 : A tensor B$], [$Gamma_2, x : A, y : B tack t_2 : C$], [$Gamma_1 + Gamma_2 tack "let" (x, y) = t_1 "in" t_2 : C$]))
      ),
      grid(
        columns: (1fr, 1.4fr),
        align: center + horizon,
        prooftree(rule(name: [$1$I], $[Gamma] tack "unit" : unitT$)),
        prooftree(rule(name: [$1$E], [$Gamma_1 tack t_1 : unitT$], [$Gamma_2 tack t_2 : B$], [$Gamma_1 + Gamma_2 tack "let unit" = t_1 "in" t_2 : B$]))
      ),
      grid(
        columns: (1fr, 1.2fr, 1.7fr),
        align: center + horizon,
        prooftree(rule(name: [der], [$Gamma, x : A tack t : B$], [$Gamma, x : [A] tack t : B$])),
        prooftree(rule(name: [$!$I], [$[Gamma] tack t : A$], [$[Gamma] tack !t : !A$])),
        prooftree(rule(name: [$!$E], [$Gamma_1 tack t_1 : !A$], [$Gamma_2, x : [A] tack t_2 : B$], [$Gamma_1 + Gamma_2 tack "let!" x = t_1 "in" t_2 : B$]))
      ),
      grid(
        columns: (1fr, 1.6fr, 1fr),
        align: center + horizon,
        prooftree(rule(name: [borrow], [$Gamma tack t : *A$], [$Gamma tack &t : !A$])),
        prooftree(rule(name: [copy], [$Gamma_1 tack t_1 : !A$], [$Gamma_2, x : *A tack t_2 : !B$], [$Gamma_1 + Gamma_2 tack "copy" t_1 "as" x "in" t_2 : !B$])),
        prooftree(rule(name: [nec], [$emptyset tack t : A$], [$[Gamma] tack *t : *A$]))
      )
    )
  ),
  caption: [Collected typing rules for LCU calculus],
)
<fig:collected-rules>

== Equational theory
<sec:equational-theory>

One way of understanding the meaning of the LCU calculus is to see its equational theory (which we later prove sound against its operational model). The calculus has the standard $beta eta$-equalities for the multiplicative linear $lambda$-calculus fragment, which includes the following $beta eta$ rules for $!$:
$
  "let!" x = !t "in" t' &equiv [t / x]t' &quad &(beta!) \
  "let!" x = t "in" !x &equiv t &quad &(eta!)
$
along with the following equalities on the uniqueness fragment:
$
  "copy" t "as" x "in" &x &equiv t &quad &("unitR") \
  "copy" &v "as" x "in" t' &equiv [v / x]t' &quad &("unitL") \
  "copy" t_1 "as" x "in" ("copy" t_2 "as" y "in" t_3) &equiv "copy" ("copy" t_1 "as" x "in" t_2) "as" y "in" t_3 &quad &("assoc")
$
The first axiom states that copying a non-linear $t$ into a unique value $x$ and immediately borrowing it to be non-linear is equivalent to just $t$. The second axiom states that borrowing a unique value $v$ and copying it to a unique $x$ in the scope of $t'$ is the same as just substituting in that $v$ for $x$. The last axiom gives associativity of copying under the side condition that $x$ is free in $t_3$. These equations are exactly the relative monad axioms @ref3, though we specialise (unitL) slightly by restricting to values to account for the reduction semantics.

The typability of these axioms relies on the admissibility of linear and non-linear substitution shown in Section 3.5 on the metatheory of the calculus.

== Exploiting uniqueness for mutation
<sec:exploiting-uniqueness>

A key use for ensuring uniqueness of a reference is that this allows mutation to be used safely—the original pun behind Wadler’s “Linear Types can Change the World” @ref57. To illustrate this idea, and consider its soundness in the next section, we extend the LCU calculus with a primitive type of arrays:
$
  A ::= dots.c | "Array" A | bb(N) | bb(F)
$
where $bb(N)$ are natural numbers used for sizes and indices and $bb(F)$ floating-point values. The calculus is also extended with operations for floating-point arrays, typed by axiomatic rules (with built-in weakening):
$
  [Gamma] &tack "newArray" &&: bb(N) lolli *( "Array" bb(F) ) \
  [Gamma] &tack "readArray" &&: *( "Array" bb(F) ) lolli bb(N) lolli bb(F) tensor *( "Array" bb(F) ) \
  [Gamma] &tack "writeArray" &&: *( "Array" bb(F) ) lolli bb(N) lolli bb(F) lolli *( "Array" bb(F) ) \
  [Gamma] &tack "deleteArray" &&: *( "Array" bb(F) ) lolli unitT
$
These operations provide the interface for exploiting unique array references, where `writeArray` performs mutation as the type system guarantees that uniquely typed values have not been duplicated in the past (Section 3.5). We ignore out-of-bounds exceptions as this is an orthogonal issue, which could be solved using indexed types. We elide rules for typing numerical terms here.

Our implementation in Section 4 replays these ideas in a practical setting. The next section gives the operational heap model for the calculus, where the semantics of mutation is made concrete.

== Operational heap model
<sec:heap-model>

We define an operational model for the LCU calculus to make the meaning of uniqueness and linearity more concrete, and to prove that our type system enforces the desired properties. The semantics is call-by-name and resembles a small-step operational semantics but instead uses a notion of _heaps_, both to capture the idea of a memory reference to arrays as well as to give a way to track resource usage on program variables. We adapt the model of Choudhury et al. @ref11, which was used to track resource usage in a pure language with graded types. Our model applies this idea to a non-graded setting, extended to include reference counting for uniqueness. To prove that linearity and uniqueness are respected (soundness), the heap semantics incorporates some typing information in order to ease the theorem statements and proofs as shown in Section 3.5.

Single-step reductions in the operational model are of the form:
$
  H tack t squig H' tack t' | Gamma | Delta quad (upright("single-step judgment form"))
$
where $H$ is the incoming heap which provides bindings to variables that appear in $t$ and array allocations. The result of the reduction is a new term $t'$ with an updated heap $H'$, as well as two additional pieces of information: $Gamma$ gives us a ‘binding context’ recording the typing of any binders that were encountered (or ‘opened’) during reduction, and $Delta$ gives us a ‘usage context’ containing an account of how variables were used. Usage contexts are defined as:
$
  Delta ::= emptyset | Delta, x : r quad (upright("usage contexts")) \
  r ::= 1 | omega quad (upright("usage/reference counter"))
$
where $r$ is a usage marker that says a variable was used either once (denoted $1$) or used more than once (denoted $omega$). Usage has a preorder $le$ where $1 le omega$.

We extend the syntax of terms with a value form $a$ representing runtime array references to the heap. In order to account for their type, the syntax of contexts is extended to include assumptions $a : "Array" A$ which are treated as a different syntactic category of variables. Additional runtime typing rules for array reference terms $a$ are provided akin to a variable rule (see appendix @ref28).

Heaps are defined as follows akin to a context but containing two kinds of ‘allocations’ for variables $x$ and for array references $a$:
$
  H ::= emptyset | H, x |->_r (Gamma tack t : A) | H, a |->_r "arr" quad (upright("heaps"))
$
In the case of extending the heap with a variable allocation for $x$, the heap records that $x$ can be used according to $r$ and that it maps to a term $t$, along with its typing which is only present to aid the metatheory. For brevity, we sometimes write $x |->_r t$ instead of $x |->_r (Gamma tack t : A)$ when the typing is not important. In the case of an array reference $a$, the heap records the number of references currently held to it, where $r$ is again used (representing either one reference $1$ or many $omega$), and describes the heap-only array representation term `arr` pointed to by that reference (whose syntax we introduce later along with the relevant rules).

Multiple reductions are composed from zero or more single-step reductions, with judgments of the form $H tack t arrow.double H' tack t' | Gamma | Delta$ given by two rules capturing empty reduction sequences and extending a sequence at its head:

#align(center)[
  #grid(
    columns: (1fr, 1.4fr),
    align: center,
    prooftree(rule(
      name: [refl],
      [$H tack t arrow.double H tack t | emptyset | emptyset$]
    )),
    prooftree(rule(
      name: [ext],
      [$H tack t_1 squig H' tack t_2 | Gamma_1 | Delta_1$],
      [$H' tack t_2 arrow.double H'' tack t_3 | Gamma_2 | Delta_2$],
      [$H tack t_1 arrow.double H'' tack t_3 | Gamma_1, Gamma_2 | Delta_1 + Delta_2$]
    ))
  )
]

In the case of ext the binding contexts are disjoint (since we treat binders as unique in a standard way) but the usage contexts are added as follows:
$
  Delta_1 + emptyset = Delta_1 \
  Delta_1 + (Delta_2, x : r) = cases(
    (Delta_1 + Delta_2), x : r & quad x in.not dom(Delta_1),
    (Delta_1' + Delta_2), x : omega & quad Delta_1 = Delta_1', x : r'
  )
$
i.e., if a variable $x$ appears in both usage contexts then in the resulting context $x : omega$ since for the purposes of our counting we are interested in counting $0$ uses (via absence in $Delta$) or $1$ use or many uses ($omega$).

*Heap model* The reduction rules are collected in the appendix @ref28, but we explain the core rules for the single-step reduction relation here. Unlike a normal small-step semantics, variables have a reduction, with two possibilities:

#align(center)[
  #grid(
    columns: (1fr, 1.2fr),
    align: center,
    prooftree(rule(name: [$upright("var")_1$], $H, x |->_1 t tack x squig H tack t | emptyset | x : 1$)),
    prooftree(rule(name: [$upright("var")_omega$], $H, x |->_omega t tack x squig H, x |->_omega t tack t | emptyset | x : 1$))
  )
]

Both reduce a variable $x$ to the term $t$ which is assigned to $x$ in the heap. In the left rule, we started out with a heap capability of $1$ (linear) so after the reduction we remove $x$ from the heap. In the right rule, we have a heap capability of $omega$ (non-linear) so we preserve the assignment to $x$ in the outgoing heap.

$beta$-reduction is then given as follows:

#align(center)[
  #prooftree(rule(
    name: [$beta$],
    [$Gamma tack t' : A$],
    [$H tack (lambda x. t) space t' squig H, x |->_1 (Gamma tack t' : A) tack t | x : A | emptyset$]
  ))
]

Rather than using a substitution, the body term is the result under a heap extended with $x$ assigned to the (typed) argument term $t'$. This heap binding is given a resource capability of $1$ since functions are linear. In the output, we remember that a linear binding has been opened up in the scope of the term.

An inductive rule allows an application to reduce on the left:

#align(center)[
  #prooftree(rule(
    name: [app],
    [$H tack t_1 squig H' tack t_1' | Gamma | Delta$],
    [$H tack t_1 space t_2 squig H' tack t_1' space t_2 | Gamma | Delta$]
  ))
]

We elide the rules for products and unit which follow much the same scheme; one congruence to evaluate the reduction of an elimination form and one to enact a $beta$ reduction. For the $!$ modality, this scheme gives us the $!beta$ rule which creates a non-linear binding of $x$ to the term $t_1$:

#align(center)[
  #prooftree(rule(
    name: [$!beta$],
    [$[Gamma] tack t_1 : A$],
    [$H tack "let!" x = !t_1 "in" t_2 squig H, x |->_omega ([Gamma] tack t_1 : A) tack t_2 | x : [A] | emptyset$]
  ))
]

The more interesting rules are for the uniqueness aspects of the language. Borrowing $\&$ (which maps a unique value type $*A$ to a non-linear value $!A$) has a congruence rule and a reduction to enact a borrow:

#align(center)[
  #grid(
    columns: (1fr, 1.4fr),
    align: center,
    prooftree(rule(
      name: [$\&$],
      [$H tack t squig H' tack t' | Gamma | Delta$],
      [$H tack &t squig H' tack &t' | Gamma | Delta$]
    )),
    prooftree(rule(
      name: [$\&beta$],
      [$dom(H) equiv arrRefs(v)$],
      [$H, H' tack &(*v) squig ([H]_omega), H' tack !v | emptyset | emptyset$]
    ))
  )
]

The action is in the right-hand rule here, where the incoming heap is split into two parts, where $H$ is such that it provides the allocations for all array references in $v$ (enforced by the premise here). The unique value $*v$ is wrapped to be non-linear in the result $!v$ and thus all of its array references are now marked as ‘many’ via $[H]_omega$ which replaces all reference counts with $omega$, e.g.:
$
  H', a |->_1 "arr" tack &(*a) squig H', a |->_omega "arr" tack !a | emptyset | emptyset
$
Thus, borrowing enacts the idea that a reference is no longer unique and may be used many times (and hence now is a non-linear value). Copying then has three reductions; a congruence (elided), a reduction which forces evaluation under the non-linear modality, and a $beta$-reduction to enact copying to a unique value:

#align(center)[
  #stack(
    spacing: 1em,
    prooftree(rule(
      name: [$"copy"_!$],
      [$H tack t squig H' tack t' | Gamma | Delta$],
      [$H tack "copy" !t "as" x "in" t_2 squig H' tack "copy" !t' "as" x "in" t_2 | Gamma | Delta$]
    )),
    prooftree(rule(
      name: [$"copy"_beta$],
      [$Gamma tack v : A$],
      [$dom(H') equiv arrRefs(v)$],
      [$(H'', theta) equiv copyop(H')$],
      [$H, H' tack "copy" !v "as" x "in" t squig H, H', H'', x |->_1 (Gamma tack *theta(v) : *A) tack t | x : *A | emptyset$]
    ))
  )
]

The $"copy"_!$ rule evaluates under $!$ so that the first term can be reduced to a value $v$ to be copied in the next rule. The $"copy"_beta$ rule enacts copying where $dom(H') equiv arrRefs(v)$ marks the part of the heap with array references coming from $v$. Then $copyop(H')$ copies the arrays in this part of the heap, creating a heap fragment $H''$ and a renaming $theta$ which maps from the old array references to the references of the new copies. This renaming is applied to $v$ in the newly bound unique variable $x$. Thus the value $theta(v)$ refers to any freshly copied arrays.

Lastly, the semantics of the array primitives uses an array representation on the heap, where `arr` is some array object and $"arr"[i] = v$ indicates that the $i^text("th")$ element is bound to the value $v$, and we write $a \# H$ for an array reference $a$ which is fresh for heap $H$:

#align(center)[
  #stack(
    spacing: 1em,
    prooftree(rule(
      [$a \# H$],
      [$H tack "newArray" space n squig H, a |->_1 "arr" tack *a | emptyset | emptyset$]
    )),
    prooftree(rule(
      $H, a |->_r ("arr"[i] = v) tack "readArray" space (*a) space i squig H, a |->_r ("arr"[i] = v) tack (v, *a) | emptyset | emptyset$
    )),
    prooftree(rule(
      $H, a |->_r "arr" tack "writeArray" space (*a) space i space v squig H, a |->_r ("arr"[i] = v) tack *a | emptyset | emptyset$
    )),
    prooftree(rule(
      $H, a |->_r "arr" tack "deleteArray" space (*a) squig H tack "unit" | emptyset | emptyset$
    ))
  )
]

Thus `newArray` creates a fresh array reference $a$ and allocates a new array on the heap with a single reference count. The `readArray` and `writeArray` primitives work as expected to read and destructively update the array referenced by $a$, whose reference count is arbitrary but unchanged by the reduction. Lastly `deleteArray` deallocates the array. Noticeably, the rules do not enforce uniqueness; but as we see in the next section, well-typed programs preserve uniqueness of references.

== Metatheory
<sec:metatheory>

Proofs of all the statements that follow are provided in the appendix @ref28. We first establish some key results showing the admissibility of substitution and weakening, which are leveraged in later proofs:

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Lemma 1 (Linear substitution).* _If $Gamma' tack t' : A$ and $Gamma, x : A tack t : B$ then $Gamma' + Gamma tack [t' / x]t : B$._
]

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Lemma 2 (Non-linear substitution).* _If $[Gamma'] tack t' : A$ and $Gamma, x : [A] tack t : B$ then $[Gamma'] + Gamma tack [t' / x]t : B$._
]

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Lemma 3 (Weakening is admissible).* _If $Gamma tack t : A$ then $Gamma, [Gamma'] tack t : A$._
]

Next, the heap model allows us to establish the key properties of well-typed programs respecting linearity and uniqueness restrictions. We first define when a heap is compatible with a typing context:

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Definition 3 (Heap-context compatibility).* _A heap $H$ is compatible with a typing context $Gamma$ if $H$ contains assignments for every variable in the context and the typing contexts of the terms in the heap are also compatible with the heap. The relation is defined inductively as:_

  #align(center)[
    #grid(
      columns: (1fr, 1.4fr),
      align: center,
      prooftree(rule(
        name: [Ref],
        [$H comprel Gamma$],
        [$H, a |->_r "arr" comprel Gamma, a : "Array" A$]
      )),
      prooftree(rule(
        name: [Lin],
        [$H comprel (Gamma_1 + Gamma_2)$],
        [$Gamma_2 tack t : A$],
        [$x in.not dom(H)$],
        [$(H, x |->_r (Gamma_2 tack t : A)) comprel (Gamma_1, x : A)$]
      ))
    )
  ]
  #align(center)[
    #grid(
      columns: (0.7fr, 1.5fr),
      align: center,
      prooftree(rule(name: [Empty], $emptyset comprel emptyset$)),
      prooftree(rule(
        name: [$omega$],
        [$H comprel (Gamma_1 + [Gamma_2])$],
        [$[Gamma_2] tack t : A$],
        [$x in.not dom(H)$],
        [$(H, x |->_omega ([Gamma_2] tack t : A)) comprel (Gamma_1, x : [A])$]
      ))
    )
  ]
]

Thus, a heap compatible with $Gamma_1, x : A$ contains an assignment for $x$ marked with a usage annotation $r$ which can be either $1$ for linear or $omega$ for non-linear use. Note that non-linear values can be used linearly, as captured by dereliction (the der typing rule). However, a non-linear assumption must have a heap assignment marked with $omega$ (rule $omega$), where the dependencies of the assigned term $t$ must all be non-linear in the remaining compatibility judgment on the rest of the heap.

From a heap (and likewise from a typing context) we can also extract usage information. This is useful for focusing on resource usage as follows:

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Definition 4 (Usage context extraction).* _For a context $Gamma$ or heap $H$ we can extract usage information denoted $over(Gamma)$ or $over(H)$ defined as:_
  $
    over(emptyset) &= emptyset &quad over((Gamma, x : [A])) &= over(Gamma), x : omega &quad over((Gamma, a : A)) &= over(Gamma) &quad over((Gamma, x : A)) &= over(Gamma), x : 1 \
    over(emptyset) &= emptyset &quad over((H, x |->_r (Gamma tack t : A))) &= over(H), x : r &quad over((H, a |->_r t)) &= over(H)
  $
]

We now give the two main theorems about our calculus which give us the properties that linearity is respected (called _conservation_, Theorem 4) and that uniqueness is respected (Theorem 5).

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Theorem 4 (Conservation).* _For a well-typed term $Gamma tack t : A$ and all $Gamma_0$ and $H$ such that $H comprel (Gamma_0 + Gamma)$ and a reduction $H tack t squig H' tack t' | Gamma_1 | Delta$ we have:_
  $
    exists Gamma'. quad Gamma' tack t' : A quad and quad H' comprel (Gamma_0 + Gamma') quad and quad (over(H') + Delta) sqle (over(H), over(Gamma_1))
  $
]

The first conjunct is regular type preservation, linked with heap compatibility in the second conjunct. The last conjunct expresses the core of conservation: that resource usage accrued in this reduction, given by $Delta$, plus remaining resources given in the heap $H'$ are approximated (via $sqle$, the pointwise lifting of $le$) by the original resources given in the heap $H$ plus the specification of the resources from any variable bindings $Gamma_1$ encountered along the way. The context $Gamma_0$ accounts for bindings not described by $Gamma$, and is key to the inductive proof of this result.

We then establish that all heap references have only one reference to them at the end of execution.

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Theorem 5 (Uniqueness).* _For a well-typed term $Gamma tack t : *A$ and all $Gamma_0$ and $H$ such that $H comprel (Gamma_0 + Gamma)$ and given a multi-reduction to a value $H tack t arrow.double H' tack *v | Gamma' | Delta$, for all $a in arrRefs(v)$ (array references in $v$) we have:_
  $
    a |->_1 t' in H ==> exists t''. a |->_1 t'' in H' quad and quad a in.not dom(H) ==> exists t''. a |->_1 t'' in H'
  $
  _i.e., any array references contributing to the final term that are unique in the incoming heap stay unique in the resulting term, and any new array references contributing to the final term are also unique._
]

Notice that there is a certain duality between the conservation theorem and the uniqueness theorem which mirrors the weak duality between linearity and uniqueness. The statement of conservation is a generalised way to say that if a variable is linear then it will always be used in a linear way, or in other words that linearity restrictions will always be upheld; conversely, the uniqueness theorem tells us that if a variable is unique then it must always have been used in a unique way, or in other words that it does not have multiple references.

One important point to notice is that the additional rules (borrow and copy) that we include for unique types are in fact trivial cases when it comes to the uniqueness theorem since they can never output a value with a unique type. This makes sense as the idea behind these additional rules is to mediate the interaction between uniqueness and non-uniqueness, and this interaction can only ever go in the direction of producing values that are non-unique.

A sub-result of conservation is type preservation which is complemented by a separate progress result in Theorem 6 to give syntactic type safety:

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Theorem 6 (Progress).* _Values of the heap model $v$ are given by:_
  $
    v ::= (t_1, t_2) | "unit" | *t | !t | lambda x. t | i | a | p quad (upright("value terms sub-grammar"))
  $
  _where $p$ are partially-applied primitives, e.g., `newArray`, `readArray`, `readArray (*a)`._
  _Given $Gamma tack t : A$, then $t$ is either a value, or if $H comprel Gamma_0 + Gamma$ there exists a heap $H'$, term $t'$, usage context $Delta$, and context $Gamma'$ such that $H tack t squig H' tack t' | Gamma' | Delta$._
]

Finally, we see that the operational semantics, extended to full $beta$-reduction (i.e., all congruences), supports the equational theory:

#block(stroke: (left: 2pt + rgb("94a3b8")), inset: (left: 0.8em))[
  *Theorem 7 (Soundness with respect to the equational theory).* _For all $t_1, t_2$ such that $Gamma tack t_1 : A$ and $Gamma tack t_2 : A$ and $t_1 equiv t_2$ and given $H$ such that $H comprel Gamma$, there exists a value (irreducible term) $v$ and $Gamma_1, Gamma_2, Delta_1, Delta_2$ such that there are full $beta$-reductions to the same value_
  $
    H tack t_1 arrow.double_beta H' tack v | Gamma_1 | Delta_1 quad and quad H tack t_2 arrow.double_beta H' tack v | Gamma_2 | Delta_2
  $
]

= Implementation
<sec:implementation>

== Frontend
<sec:frontend>

The implementation of uniqueness types in Granule follows much the same pattern as the logic defined earlier. Granule already possesses a semiring graded necessity modality, where for a pre-ordered semiring $(R, *, 1, +, 0, sqle)$, there is a family of types $\{square_r A\}_{r in R}$. We represent the $!$ from linear logic (and our calculus) via the pre-ordered semiring $\{0, 1, omega\}$ (none-one-tons @ref30) with $!A = square_omega A$.#footnote[It may not seem obvious that such a graded modality does exactly represent the behaviour of linear logic’s $!$, and in fact capturing the precise behaviour of $!$ does require some additional semiring structure which is present in Granule @ref22.]
The semiring is defined with $r + s = r$ if $s = 0$, $r + s = s$ if $r = 0$ and otherwise $omega$, and $r * 0 = 0 * r = 0$, $r * omega = omega * r = omega$ (for $r eq.not 0$), and $r * 1 = 1 * r = r$ with ordering $0 sqle omega$ and $1 sqle omega$. This semiring allows us to represent both linear and non-linear use: variables graded with $1$ must be used linearly, with $0$ must be discarded, and a grade of $omega$ permits unconstrained use à la linear logic’s $!$.

(In Granule, $square_omega A$ can be written as the type `A [Many]`, but we syntactically alias this to `!A` for simplicity and ease of understanding.)

As in LCU, uniqueness is represented by a new modality, which we call $*$ to match the calculus (and so that the syntax of programs involving uniqueness will be familiar to Clean users). The uniqueness modality wraps a value that behaves ‘linearly’ (and so cannot be duplicated or discarded), with the key difference being that we provide primitive functions which allow $!$ to act as a relative monad over unique values. The primitives have the following type signatures:

#codebox(title: "Granule")[
```haskell
uniqueReturn : ∀ {a : Type} . *a -> !a         -- borrow
uniqueBind   : ∀ {a b : Type} . (*a -> !b) -> !a -> !b -- copy
```
]

The `uniqueReturn` function here implements the BORROW rule from the calculus (acting as the ‘return’ of the relative monad), and similarly the `uniqueBind` function implements the COPY rule (acting as the ‘bind’).

We provide syntactic sugar for both of these primitives for convenience, with syntax designed to evoke the rules from the LCU calculus; `&x` is equivalent to writing `uniqueReturn x`, while `clone t1 as x in t2` is equivalent to writing `uniqueBind (\x -> t2) t1`.#footnote[In the implementation we use ‘clone’ rather than ‘copy’, as the name ‘copy’ is often used elsewhere in Granule, e.g. for the non-linear function which duplicates its input.] A simple example of uniqueness types in action is given below, to demonstrate the idea.

#codebox(title: "Granule")[
```haskell
sip : *Coffee -> (Coffee, Awake)
sip fresh = let !coffee = &fresh in (keep coffee, drink coffee)
```
]

Here, borrowing (`&`) converts the unique `Coffee` value into an unrestricted one, so that it can be duplicated and used twice for the two separate functions. Note however that the uniqueness guarantee is lost in the process, so both of the output values are non-unique (linear, in this case).

Figure 2 illustrates the relationship between uniqueness, linearity and other common forms of substructural typing in the resulting system.

#figure(
  block(
    width: 100%,
    stroke: rgb("94a3b8"),
    inset: 1.2em,
    radius: 4pt,
    fill: rgb("fafafa"),
    align(center)[
      #grid(
        columns: (1.2fr, 2.2fr, 1.8fr, 1.8fr, 1fr),
        align: center + horizon,
        gutter: 0.5em,
        [
          #block(stroke: 0.5pt, inset: 6pt, radius: 2pt, fill: white)[
            *Unique*\
            #text(size: 8pt)[$*a$]
          ]
        ],
        [
          $limits(-->)^("forget guarantee")_("of no contraction")$
        ],
        [
          #block(stroke: 0.5pt, inset: 6pt, radius: 2pt, fill: white)[
            *Unrestricted*\
            #text(size: 8pt)[(non-linear)\ (non-unique)\ $a [0..infinity]$\ $a ["Many"]$\ $!a$]
          ]
        ],
        [
          #stack(
            spacing: 1.2em,
            [
              $limits(arrow.tr)^("restrict")_("contraction")$
              #block(stroke: 0.5pt, inset: 4pt, radius: 2pt, fill: white)[
                *Affine*\
                #text(size: 8pt)[$a [0..1]$]
              ]
              $limits(arrow.br)^("restrict")_("weakening")$
            ],
            [
              $limits(arrow.br)^("restrict")_("weakening")$
              #block(stroke: 0.5pt, inset: 4pt, radius: 2pt, fill: white)[
                *Relevant*\
                #text(size: 8pt)[$a [1..infinity]$]
              ]
              $limits(arrow.tr)^("restrict")_("contraction")$
            ]
          )
        ],
        [
          #block(stroke: 0.5pt, inset: 6pt, radius: 2pt, fill: white)[
            *Linear*\
            #text(size: 8pt)[$a [1]$\ $a$]
          ]
        ]
      )
    ]
  ),
  caption: [Relationship between various flavours of substructural types demonstrating how they can all be represented using Granule’s expressive modalities.],
)
<fig:substructural-relationships>

We implemented a built-in library for primitive floating point arrays in Granule, matching the interface for arrays of floats that was introduced as an extension to the LCU calculus in Section 3.3, with operations typed as follows:

#codebox(title: "Granule")[
```haskell
newFloatArray    : Int -> *FloatArray
readFloatArray   : *FloatArray -> Int -> (Float, *FloatArray)
writeFloatArray  : *FloatArray -> Int -> Float -> *FloatArray
deleteFloatArray : *FloatArray -> ()
```
]

The `writeFloatArray` primitive updates an array destructively in place since we have a guarantee that no other references exist to the array which has been passed in. In the next section, we use this set of primitives to evaluate the performance of our implementation, by measuring the performance gains from allowing for in-place updates in this fashion. We have another set of immutable primitives akin to the above (but written with a suffix `I`) which work with non-unique arrays, e.g. `readFloatArrayI : FloatArray -> Int -> (Float, FloatArray)`, and thus do not perform mutation.

The following shows an example of `clone`, where a new array is borrowed and a copy of this borrowed `FloatArray` on line 3 is deleted, leaving the original (now immutable) instance of the array unaffected on line 4:

#codebox(title: "Granule")[
```haskell
let x = newFloatArray 10 in
let [y] = &x in
let [()] = clone [y] as y' in (let () = deleteFloatArray y' in [()])
in readFloatArrayI y 10
```
]

== Compilation and Evaluation
<sec:evaluation>

As part of our implementation of uniqueness types in Granule, as described in Section 4.1, we also implemented a simple compiler that translates programs into Haskell. This compiler preserves the value types, but erases all of Granule’s substructural types (linear, unique, graded, etc.). As a result, we can take advantage of both Granule’s flexible type system and Haskell’s libraries and optimizing compiler. For this paper, all performance results were measured by compiling Granule programs to Haskell, and compiling the resulting Haskell with GHC 9.0.1. The measurements were collected on an ordinary MacBook with a 2 GHz quad-core Intel i5 processor and 16 GB of RAM.

As mentioned in Section 1, one motivation for using uniqueness types is to do the kind of in-place mutation necessary for efficient programming with arrays. To check that our implementation is reasonable, we carried out an evaluation using an array processing benchmark. The benchmark recursively allocates and sums up lists of arrays of various sizes, with the goal of demonstrating the benefits of uniqueness types for arrays in functional programming. Each iteration of the benchmark allocates a list of a thousand arrays, populates the arrays with values, then traverses the list to sum them up. We prepared two versions of this benchmark: one with functional in-place updates and manual (safe) deletion of unique arrays, and one with non-unique, immutable, garbage collected arrays and updates via copying. The overall performance of these two benchmarks is shown in Figure 3, with lower bars/numbers representing better performance.

#figure(
  block(
    width: 100%,
    stroke: rgb("cbd5e1"),
    inset: 1.2em,
    radius: 4pt,
    fill: rgb("f8fafc"),
    stack(
      spacing: 1em,
      grid(
        columns: (1fr, 1fr),
        gutter: 2em,
        align: center,
        [
          *Overall runtime*\
          #v(0.5em)
          #table(
            columns: (auto, auto, auto),
            inset: 5pt,
            align: (left, right, right),
            stroke: 0.5pt + rgb("cbd5e1"),
            [Iterations], [Unique (ms)], [Non-unique (ms)],
            [100], [~20], [~120],
            [200], [~40], [~250],
            [300], [~60], [~390],
            [400], [~80], [~530],
            [500], [~105], [~680]
          )
        ],
        [
          *GC overhead*\
          #v(0.5em)
          #table(
            columns: (auto, auto, auto),
            inset: 5pt,
            align: (left, right, right),
            stroke: 0.5pt + rgb("cbd5e1"),
            [Iterations], [Unique (ms)], [Non-unique (ms)],
            [100], [< 5], [~30],
            [200], [< 8], [~70],
            [300], [< 12], [~115],
            [400], [< 18], [~155],
            [500], [< 24], [~200]
          )
        ]
      ),
      text(size: 8pt, fill: rgb("64748b"))[Benchmark summary measurements from Figure 3 of the original paper.]
    )
  ),
  caption: [Performance of mutable vs. immutable arrays in Granule. Lower is better.],
)
<fig:benchmarks>

The results, while not surprising, do confirm that array-handling is generally more efficient when in-place mutation is allowed. Additionally, in Figure 3, we compared the time spent in garbage collection between the two versions of the benchmark. Because our implementation allocates unique data outside of GHC’s heap, and uniqueness types allow programmers to directly de-allocate objects in memory, the unique version of the benchmark spends significantly less time in garbage collection. For this benchmark, the unique arrays are outside of the garbage collected heap and directly de-allocated, while other incidental objects (closures, lists, and so on) are still handled by the garbage collector.

Of course, this is a somewhat contrived benchmark. Real-world Haskell libraries, for example, typically provide functional high-level interfaces for array manipulation while using unsafe code to mutate arrays internally. The popular vector library#footnote[#link("https://hackage.haskell.org/package/vector")] is one example, and repa @ref25 is another. Additionally, there is significant prior work on improving the efficiency of functional programs operating on arrays (for example, using combinators like map and fold along with aggressive fusion @ref13 @ref25 @ref27), which we will not dwell on. The main point is that, at some stage, arrays must be mutated. Rather than having this happen through unsafe code, or via external C or Fortran, uniqueness types give us a way to do that mutation directly in our functional language, efficiently and safely.

Crucially, in these comparisons, all versions of the programs are implemented in the same language: Granule. With our extensions, the language is expressive enough to encompass a variety of programming approaches. Functional programmers may freely mix and match from a variety of options for data management and manipulation. Object lifetimes may be either manually or automatically managed, and object contents may allow in-place mutation or be immutable.

= Related Work
<sec:related-work>

Uniqueness types are most well known for their appearance in the Clean language @ref40 @ref47, where they are used in lieu of monadic computation and for the efficiency gains offered by in-place update. In Clean, computation is based on graph rewriting and reduction; constants such as numbers are graphs, and functions are graph rewriting formulas. This gives the type system a rather different feel to those offered by more recent functional programming languages, and makes it more difficult to capture the benefits of Clean-style uniqueness in a modern setting, hence the value in our pursuit of this goal.

Some theoretical groundwork for Clean’s uniqueness types has certainly been developed over the years, particularly in works by de Vries among others @ref55 @ref56; these papers aim to clarify the distinction between Clean’s type system and systems based on the $lambda$-calculus. Further work makes headway on the problem of distinguishing uniqueness from other substructural systems @ref53 @ref54. This follows a similar theoretical approach to the one demonstrated in our paper; such ideas for limited settings inspired the groundwork for our system, which is more general and has a practical implementation.

Other languages (old and new) featuring uniqueness types include Single-Assignment C @ref45, Mercury @ref48 and Cogent @ref35.

Ownership was first developed as a framework for understanding aliasing in object-oriented languages @ref34, and is intended to give a high-level structural view of objects and references in much the same way that powerful type systems give a high-level structural view of data. Ownership is now most familiar due to being pervasive in the Rust programming language, for which multiple formalisations have been attempted; RustBelt @ref24 gives a lower-level encoding of Rust intended for formal verification while Oxide @ref64 is a higher-level encoding designed for more theoretical work, among others @ref39. Extending these ideas to other languages is an active area of research; RefinedC @ref44 is one example.

Regions have been used over the years in the context of effect systems @ref23 @ref26. One of the primary motivations of research into region types was their application in _region-based memory management_ @ref51, which aimed to bring some of the benefits of traditional stack-based memory management to higher-order functional languages. Regions divide values based on their lifetimes, so a system with region types can safely allocate and de-allocate memory for values based on region type information, eliminating the need for garbage collection.

Early on, regions were restricted to have LIFO (last-in, first-out) lifetimes which followed the block structure of a language, but later work relaxed this constraint using uniqueness (see: static capabilities @ref63 and Cyclone @ref21); a unique reference to a region ensures there are no aliases to the region, and that it can therefore be promptly de-allocated. Additionally, regions themselves act as a way to control aliasing, and can be thought of as equivalence classes for a “may alias” relation—in other words, values which do not share a region may not alias with one another, and so if a value does not share a region with anything else then it may be safely mutated in place.

Work on Cyclone @ref14 demonstrated the relationship between regions and unique pointers, observing that “unique pointers are essentially lightweight, dynamic regions that hold exactly one object.” Beyond that, Rust’s lifetimes are heavily based on regions, and there exists an extension of ML called Affe @ref43 which aims to support both linearity and borrowing using regions.

Capabilities are tokens that a function must possess in order to be able to access a particular location in memory. Capabilities are linear, and cannot be duplicated or discarded, in order to prevent them from being forged @ref17. Implementations exist for various object-oriented languages such as Java @ref2 and Scala @ref19; more functional languages taking inspiration from the idea of capabilities also exist @ref33 @ref41. Recent work on linear constraints for Haskell @ref49, which hopes to allow for something similar to borrowing within the framework of linear Haskell, also descends from work on capabilities. Ambient capabilities can also be internalised as a comonad to capture purity within an impure language @ref12.

= Future Work
<sec:future-work>

*Ownership via fractional permissions* Though Granule can now represent values with both linear and unique types, the language allows for much more fine-grained analysis of resourceful data via grading. For instance, we can replay our earlier non-linearity example but with some extra information in the types:

#codebox(title: "Granule")[
```haskell
accurate : Cake [2] -> (Happy, Cake)
accurate [cake] = let extra = have cake in (eat cake, extra)
```
]

Instead of an infinite amount of cake we specify that we have exactly two cakes; the cake on the right-hand side must be linear as we only have one usage remaining. If we used the input three times we would receive a type error.

Given that we can move beyond the simple binary view of linear and non-linear, one might suspect that we could track the quantity of existing references to a value more accurately than just unique or non-unique. We propose taking inspiration here from Boyland’s notion of fractional permissions @ref8.

The purpose of fractional permissions is to allow multiple readers to access the same resource without losing the ability to later gain unique write access. A “permission” can be split up, allowing read-only access to multiple consumers, and then later recombined (while ensuring no other permissions still exist).

To relate these with our calculus, let us hypothesise that $*_1 P$ is a ‘complete’ unique value that we can read from or write to, and that we can split up arbitrarily into ‘fractionally’ unique values $*_n P$ where $0 < n le 1$, as follows:
$
  *_n P tensor *_m P <---> *_(n+m) P
$
As with fractional permissions, fractional values must only be used for behaviour that does not involve mutation, because whilst a value is only fractionally unique we cannot guarantee that other references do not exist. We should only regain this ability if we recombine the guarantees into a complete $*_1 P$.

This model closely resembles ownership as in Rust @ref24 – we can think of a value of type $*_n P$ for $n < 1$ as being equivalent to a Rust-style `&P` which is a borrowed value that we cannot mutate.#footnote[Rust also includes mutable borrows, which allow the borrower to both read from and write to their borrowed reference. These are a much closer analogue to our current non-fractional calculus, since mutable borrows must be unique.] When a value has been borrowed the original value cannot be written to until we are finished with the borrows, much like we would need to collect all the fractionally unique values back together to get back to our original unique $*_1 P$. Being able to more closely model Rust’s powerful ownership system would make this a fruitful avenue for future research.

*Linear Haskell* Granule’s linear basis and assortment of modalities allows for a particularly natural embedding of the LCU calculus, but this does not preclude the theory of this paper from being applied in other contexts. One particularly valuable setting to consider would be Haskell, which as of GHC 9 already has linear types based on an underlying graded system called $lambda_arrow.r^q$.

Haskell’s graded representation of linearity involves function types `(a %r -> b)` which have a multiplicity annotation `r`; at present, this can be either `'One` (linear) or `'Many` (unrestricted). But $lambda_arrow.r^q$ is designed to be extensible, and the possibility of introducing additional multiplicities is welcomed @ref7 @ref49.

The original paper on linear Haskell @ref7 mentions that “linear types are conceptually simpler than uniqueness type systems, giving a clearer path to implementation in GHC”, and also that “functional languages have more use for fusion than in-place update”. Our clarification of the relationship between linearity and uniqueness demonstrates that not only are uniqueness types no more complex conceptually than linear ones, they can comfortably sit alongside one another in a single calculus; our evaluation demonstrates that while linearity is certainly useful, there are still further practical benefits to be gained from introducing uniqueness into a language with linear types. Perhaps these contributions will begin to forge a path towards a future for Haskell where linear types and uniqueness types can both be leveraged for their respective strengths.

*Adjoint models* Benton’s linear/non-linear (LNL) logic @ref6 consists of two fragments: intuitionistic (non-linear) logic $Phi tack_I X$ and a mixed fragment of intuitionistic linear logic with non-linear hypotheses $Phi, Gamma tack_L A$. These two fragments are connected by a pair of modalities $"Lin"(X)$ and $"Mny"(A)$, which form an adjunction; the $!$ modality can then be recovered by $!A = "Lin"("Mny"(A))$.

Breaking the $!$ modality into two and allowing linear logic to be mixed with non-linear logic has been a valuable endeavour, and so a natural question is whether it is possible to build an LNL-style adjoint model for our unified LCU calculus. It seems plausible that building an adjoint model for just uniqueness logic would not be too difficult; this would be very similar to the LNL model but with the adjunction moving in the opposite direction, and the monadic modality $circ$ from uniqueness logic could be represented in much the same way that the comonadic $!$ can be recovered in LNL.

An adjoint model for the full LCU calculus would be more interesting. This would most likely involve three fragments, two of which would be symmetric monoidal categories (for unique and linear values) and one of which would be a Cartesian closed category (for unrestricted values), with two adjunctions allowing values to flow from unique to unrestricted to linear as we might hope.

*Ordered and dependent types* As expressive as Granule’s type system may be, there are opportunities for enforcing stronger properties on programs elsewhere in the landscape of type theories. One possibility is that in addition to restricting contraction and weakening, it is also possible to restrict _exchange_, giving ordered type theories which correspond to noncommutative logic.

Such systems can be used to model stack-based memory allocation (as opposed to heap-based), since without exchange an object may only be used when it is at the top of the stack @ref10 @ref62. But much like linearity, these systems restrict the use of exchange in the _future_; is there an equivalent of uniqueness for ordered types which guarantees that exchange has never been applied in the _past_, and could this be useful for tracking references on the stack?

Another possibility is to bring uniqueness into the realm of dependent types. Recent work on graded modal dependent type theory (GrTT) @ref31 allows for capturing requirements on variable usage at both the type and computation levels; grades come in pairs, where the first component is the computation-level grading and the second component is the type-level grading. Strictly linear usage in types is rare – is there value in being able to represent uniqueness here?

= Conclusion
<sec:conclusion>

Linearity and uniqueness are both well-studied concepts with similar substructural foundations, but differing benefits; linearity enables the careful management of resourceful data, while uniqueness offers the possibility of safe in-place updates. By formalising the relationship between these two ideas, building on two distinct bodies of literature, we have shown that there is value in having both linear and unique types in the same type system. This could be a first step on the road towards properly understanding the relationships between more advanced substructural type systems, such as the fine-grained resource tracking of Granule and Idris and the complex memory management provided by Rust.

Moreover, we implemented this system in the graded modal setting of the Granule language and provided benchmarks to demonstrate the efficiency gains that can be accessed via adding uniqueness to a language that already has a linear basis. The opportunities to incorporate uniqueness types into languages outside of Granule are apparent, and this paper offers both a theoretical underpinning for uniqueness as it relates to linearity as well as clear validation of the performance benefits that a system which unifies linearity and uniqueness can offer.

*Acknowledgments* This work was supported by an EPSRC Doctoral Training Award (Marshall) and EPSRC grant EP/T013516/1 (_Verifying Resource-like Data Use in Programs via Types_).

#v(1em)

#bibliography("paper.bib", title: "References", style: "lncs-alpha.csl")
