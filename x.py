import os, re, subprocess

base_dir = "arXiv-2310.18166v2"

# 1. Update core-ottput.typ: append "Note on Linear Haskell"
core_path = f"{base_dir}/core-ottput.typ"
with open(core_path, "r", encoding="utf-8") as f:
    core_text = f.read()

note_linear_haskell = """
*Note on Linear Haskell.* As mentioned at the start of this section, we aim for the extensions we develop throughout this work to be compatible with other graded type systems after some adaptation. One particular system of interest is the calculus underlying the recent extension which introduces linear types to Haskell @bernardy2017linear. This extension uses a graded type system below the surface in order to implement linearity; all function types are given a 'multiplicity' annotation $r$ written `(a %r -> b)` akin to a type $Box_r A lolli B$ here, where the annotation can be either `'One` or `'Many` representing either linear or unrestricted usage respectively. Work on formalising the connection between systems like this where all function types come with a grade (sometimes called 'graded base') and systems such as Granule's where values are linear by default and graded values are wrapped inside a modality (called 'linear base') is ongoing @vollmer2024mixed.
"""

if "Note on Linear Haskell" not in core_text:
    core_text = core_text.rstrip() + "\n" + note_linear_haskell + "\n"
    with open(core_path, "w", encoding="utf-8") as f:
        f.write(core_text)
    print("Added 'Note on Linear Haskell' to core-ottput.typ.")

# 2. Update fractional-ottput.typ
frac_path = f"{base_dir}/fractional-ottput.typ"
with open(frac_path, "r", encoding="utf-8") as f:
    frac_text = f.read()

# Replace premature == headings with run-ins
frac_text = re.sub(r'==\s+Uniqueness as uniquely borrowed\s*(?:<[^>]+>)?', '*Uniqueness as uniquely borrowed.*', frac_text)
frac_text = re.sub(r'==\s+Immutable borrows\s*(?:<[^>]+>)?', '*Immutable borrows.*', frac_text)
frac_text = re.sub(r'==\s+Resources\s*(?:<[^>]+>)?', '*Resources.*', frac_text)
frac_text = re.sub(r'==\s+Resource allocators\s*(?:<[^>]+>)?', '*Resource allocators.*', frac_text)

# Find end of examplePartial and replace/append missing content
pos_partial = frac_text.find("examplePartial indigo =")
if pos_partial != -1:
    pos_end_box = frac_text.find("```\n]", pos_partial)
    if pos_end_box != -1:
        prefix = frac_text[:pos_end_box + 5]
        missing_section_tail = """
This notion extends gracefully to structures containing more than two components. For example, to borrow a single element from a unique tuple of three values, leaving the remaining two values available to their original owner, we can use nested products, e.g. $star(A tensor (B tensor C))$, and push and pull to then access just one part, similarly to in `indigo`. We may need to push twice in order to distribute the modality over the entire product depending on which component we are borrowing, but in the same way as above we can use `withBorrow` to extract the desired data (for example, $withB_1 A$) while applying pull to recover the remaining structure (in this case, of type $star(B tensor C)$).

Partial borrowing allows safe mutation of disjoint parts of a single data structure concurrently without risking a data race, e.g., using `par` for concurrent threads @marshall2022replicate:#footnote[One might wonder whether the $Box_r$ modality also distributes in this way; the answer is not in general, though some choices of semiring permit this behaviour. This question has been explored in depth in prior work @hughes2021linear.]

#codebox(title: "Granule")[
```haskell
par : forall {a b : Type} . (() -> a) -> (() -> b) -> (a, b) -- Granule's parallel composition

exampleConcurrent : *Colour -> *Colour
exampleConcurrent indigo =
  let (r, p) = push indigo in
  let (g, b) = push p in
  let (r', b') = par (\\() -> withBorrow alter r)
                     (\\() -> withBorrow alter b) in
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
  in withBorrow (\\compIn ->
       let (ref, array) = push compIn;
           (array1, array2) = split array; -- immutable borrow happens here

           -- Compute in parallel
           ((x, array1), (y, array2)) =
             par (\\() -> sumFromTo array1 [0] [div n 2])
                 (\\() -> sumFromTo array2 [div n 2] [n]);

           -- Update the reference
           ref' = writeRef ((x : Float) + y) ref;
           compOut = pull (ref', join (array1, array2)) -- end immutable borrow

       in compOut) compIn
```
]
"""
        frac_text = prefix + "\n" + missing_section_tail
        with open(frac_path, "w", encoding="utf-8") as f:
            f.write(frac_text)
        print("Updated fractional-ottput.typ with all missing subsections and parSum example.")

# 3. Update intro.typ bullet points to match 5.1 and 5.2
intro_path = f"{base_dir}/intro.typ"
with open(intro_path, "r", encoding="utf-8") as f:
    intro_text = f.read()

intro_text = re.sub(r'Section\s*5\.5', 'Section 5.1', intro_text)
intro_text = re.sub(r'Section\s*5\.6', 'Section 5.2', intro_text)
with open(intro_path, "w", encoding="utf-8") as f:
    f.write(intro_text)

# 4. Update theorem titles and numbering to match arXiv
thm_updates = {
    "theorem-linear-substitution-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Linear substitution is admissible, extending @orchard2019quantitative", kind: "Lemma 6.2")'
    ),
    "theorem-graded-substitution-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Graded substitution is admissible, extending @orchard2019quantitative", kind: "Lemma 6.3")'
    ),
    "theorem-progress-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Progress", kind: "Theorem 6.6")'
    ),
    "theorem-type-preservation-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Type Preservation", kind: "Theorem 6.7")'
    ),
    "theorem-borrow-safety-single-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Borrow safety", kind: "Lemma 6.8")'
    ),
    "theorem-borrow-safety-multi-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Multi-reduction borrow safety", kind: "Theorem 6.9")'
    ),
    "theorem-uniqueness-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Uniqueness", kind: "Corollary 6.10")'
    ),
    "theorem-soundness-eq-theory-ottput.typ": (
        r'#thm\("[^"]*",\s*kind:\s*"[^"]*"\)',
        '#thm("Soundness with respect to the equational theory", kind: "Theorem 6.11")'
    ),
}

for fname, (pattern, replacement) in thm_updates.items():
    fpath = f"{base_dir}/{fname}"
    with open(fpath, "r", encoding="utf-8") as f:
        content = f.read()
    content = re.sub(pattern, replacement, content, count=1)
    with open(fpath, "w", encoding="utf-8") as f:
        f.write(content)
print("Updated theorem numberings.")

# 5. Switch paper.typ bibliography style to chicago-author-date
paper_path = f"{base_dir}/paper.typ"
with open(paper_path, "r", encoding="utf-8") as f:
    pt = f.read()

pt = re.sub(r'#bibliography\("references\.bib"[^\)]*\)', '#bibliography("references.bib", title: "References", style: "chicago-author-date")', pt)
with open(paper_path, "w", encoding="utf-8") as f:
    f.write(pt)
print("Set bibliography style to chicago-author-date.")

# 6. Recompile
res = subprocess.run(
    ["nix", "run", "--extra-experimental-features", "nix-command flakes", "nixpkgs#typst", "--", "compile", paper_path, "/tmp/full_paper.pdf"],
    capture_output=True, text=True
)

print(f"\nTypst Compile Returncode: {res.returncode}")
if res.stderr:
    print("Typst Stderr:\n" + res.stderr)
else:
    pdf_size = os.path.getsize("/tmp/full_paper.pdf") / (1024 * 1024)
    print(f"SUCCESS: Compiled /tmp/full_paper.pdf ({pdf_size:.2f} MB, 0 errors, 0 warnings)!")
