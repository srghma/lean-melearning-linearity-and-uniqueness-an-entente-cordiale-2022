#import "common.typ": *

In order to develop a type system which integrates ownership and borrowing concepts with the linear and graded types already present in Granule, we will first need to understand the ideas in question. This section presents six key patterns which we capture in our system in the rest of this paper, along with simple Rust code examples to demonstrate the patterns in action. Each of these examples relies on a single base value of type `Colour(u32, u32, u32)` - a struct containing three unsigned integers, representing a colour with red, green and blue components.

== Ownership
<ownership>

The first crucial concept is _owned_ values, where a value is 'owned' by a particular _identifier_. Below, the value `Colour(220, 20, 60)` is owned by the identifier `scarlet`. Each value can only be owned by a single identifier at any given time. Rust enforces this via _move semantics_: on the second line, ownership of the value is _moved_ to the identifier `x`. Now the identifier `scarlet` no longer owns the value, so attempting to use it again on the third line gives an error.

#codebox(title: text(fill: rgb("dc2626"))[Rust ✗])[
```rust
let scarlet = Colour(220, 20, 60);
let x = scarlet;
let y = scarlet; // error: use of moved value: `scarlet`
```
]

It is fairly clear that the idea here in some way relates to linearity, since linear values can only be used once which restricts them to being passed around sequentially; indeed, much of the literature on Rust makes mention of linear (or affine) types. We demonstrate through our unified type system in @sec:uniqueness that in fact ownership can be better understood as an extension of _uniqueness_ types, since each value having a single owner implies that the owner holds the unique reference to said value. These are similar to linear types in some ways but with important differences.

== Immutable borrowing
<immutable-borrowing>

Borrowing generalises the concept of ownership, permitting multiple references to point to a single value simultaneously. Rust's _borrow checker_ manages all borrows that exist at a given time, ensuring that memory safety properties are maintained until values are eventually returned to their owners. _Immutable_ borrows are one flavour of reference; any number of these can exist at a given time, but mutation of a value is disallowed through an immutable borrow, since this could result in data races. Below, two immutable borrows (`x` and `y`) both reference the original `persimmon` value.

#codebox(title: text(fill: rgb("16a34a"))[Rust ✓])[
```rust
let persimmon = Colour(252, 118, 5);
let x = &persimmon; // & denotes a borrow of `persimmon`
let y = &persimmon; // ok!
```
]

== Mutable borrowing
<mutable-borrowing>

It is also possible to borrow values and retain the capacity to mutate them, but this comes at a price: as mentioned above, allowing mutation through multiple references simultaneously is harmful to memory safety, so in order to prevent this only a single mutable borrow is permitted at a time. Much like owned values, mutably borrowing a value guarantees the sole capability for destructive access to the underlying data. This is demonstrated below, where attempting to create two _mutable_ borrows following the pattern of the above example is disallowed.

#codebox(title: text(fill: rgb("dc2626"))[Rust ✗])[
```rust
let mut viridian = Colour(52, 161, 128);
let x = &mut viridian; // error: cannot borrow `viridian` as mutable
let y = &mut viridian; //                   more than once at a time
```
]

Note, however, that the above example copied verbatim into a Rust file will in fact compile successfully unless additional code is introduced that makes use of the variables `x` and `y`; this is due to a feature called _non-lexical lifetimes_, through which the Rust compiler is able to _infer_ that allowing two mutable borrows is safe as long as one of them is never used. We do not linger on this, since we will not capture this behaviour in our type system; our goal is to embed some essential ownership and borrowing patterns _explicitly_. However, we will mention the possibility for extending our system with more advanced ideas in @sec:conclusion.

== Mixing mutable and immutable borrows
<mixing-mutable-and-immutable-borrows>

Rust also disallows immutable borrows of values that are already borrowed mutably, since this invites similar problems: e.g., a value could be updated through the mutable borrow whilst being read through the immutable borrow. Hence, the following example wherein the second reference is borrowed immutably rather than mutably is also forbidden by the borrow checker. In @sec:fractional, we demonstrate that both notions can be represented through a graded generalisation of uniqueness typing to represent a borrower's level of access.

#codebox(title: text(fill: rgb("dc2626"))[Rust ✗])[
```rust
let mut cerulean = Colour(3, 109, 230);
let x = &mut cerulean; // error: cannot borrow `cerulean` as immutable
let y = &cerulean;     //       because it is also borrowed as mutable
```
]

== Partial borrowing
<partial-borrowing>

A useful pattern for working with larger data structures is to borrow only _part_ of the structure while the original owner retains access to what remains. This is valuable for allowing one part of a program to work with a particular piece of data without restricting access to the entire structure, enabling tasks to be carried out in parallel more easily. In the below example, the red and green components of the `indigo` value are simultaneously borrowed mutably. The Rust compiler allows this since the references point to disjoint parts of the original struct:

#codebox(title: text(fill: rgb("16a34a"))[Rust ✓])[
```rust
let mut indigo = Colour(32, 36, 209);
let r = &mut indigo.0;
let g = &mut indigo.1; // ok!
```
]

In @sec:distrib, we take advantage of Granule's functional nature to present a cohesive way of managing this kind of partial borrow at the type level, including the possibility for working with disjoint components of the original structure concurrently.

== Reborrowing
<reborrowing>

The final pattern we aim to capture in our system, also essential for practical programming, is the notion of _reborrowing_, through which it is possible to create a borrow of an identifier that itself references another value. We will show in @sec:fractional that this behaviour falls out of our generalisation of uniqueness naturally, without a need for additional constructs. To illustrate the general idea, consider the following example; here, the red component of the `amethyst` value is borrowed mutably as `r`, then another immutable borrow `x` is created pointing to `r`. The value can now only be read through `x`---both `r` and `amethyst` are inaccessible until the borrow is complete.

#codebox(title: text(fill: rgb("16a34a"))[Rust ✓])[
```rust
let mut amethyst = Colour(98, 1, 170);
let r = &mut amethyst.0;
let x = & *r; // ok!
```
]
