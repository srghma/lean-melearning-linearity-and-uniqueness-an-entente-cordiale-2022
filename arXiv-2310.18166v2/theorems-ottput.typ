#import "common.typ": *

We now consider the relationship between typing and the operational semantics. First, we must build a foundation via checking some preliminary results and noting some crucial definitions.

Two useful results, which extend those found elsewhere in the literature, are that substitution is admissible for our calculus, coming in both linear and graded variants:

#include "theorem-linear-substitution-ottput.typ"
#include "theorem-graded-substitution-ottput.typ"

*Type safety.* Key to ensuring type safety is the notion of heap compatibility with a typing context.

#block(
  width: 100%,
  stroke: (left: 2.5pt + rgb("0750d0")),
  inset: (left: 0.8em, y: 0.4em),
  above: 0.8em,
  below: 0.8em,
)[
  #text(weight: "bold")[Definition 6.4 (Heap compatibility).] A heap $H$ is compatible with free variable context $Gamma$, denoted $H comprel Gamma$, if the grades in the heap match those of the context, and any values stored in the heap have their resources accounted for in the rest of the heap. The relation is defined inductively over the syntax of heaps and contexts:

  #v(0.5em)
  #grid(
    columns: (1fr, 1.8fr, 1.2fr),
    row-gutter: 1.5em,
    align: center + horizon,
    prooftree(
      rule(
        name: [empty],
        $emptyset comprel emptyset$
      )
    ),
    prooftree(
      rule(
        name: [extRes],
        $H, id mapsto v_r comprel Gamma + gamma$,
        $gamma ⊢ v_r : Res_id A$,
        $H, ref mapsto_(ucol(p)) id, id mapsto v_r comprel (Gamma, ref : Res_id A)$
      )
    ),
    prooftree(
      rule(
        name: [GCArr],
        $H comprel emptyset$,
        $H, ref mapsto_(ucol(p)) id comprel emptyset$
      )
    ),
    grid.cell(
      colspan: 3,
      align: center,
      grid(
        columns: (1.5fr, 1.5fr),
        align: center + horizon,
        prooftree(
          rule(
            name: [ext],
            $H comprel Gamma + s dot.op Gamma'$,
            $x in.not sans("dom")(H)$,
            $Gamma' ⊢ v : A$,
            $exists r'. med s + r' equiv r$,
            $(H, x mapsto_(lcol(r)) v) comprel (Gamma, lcol(x : [A]_s))$
          )
        ),
        prooftree(
          rule(
            name: [extLin],
            $H comprel Gamma + Gamma'$,
            $x in.not sans("dom")(H)$,
            $Gamma' ⊢ v : A$,
            $exists r'. med 1 + r' equiv r$,
            $(H, x mapsto_(lcol(r)) v) comprel (Gamma, x : A)$
          )
        )
      )
    )
  )
  #v(0.5em)
]

Thus, a context extended with a runtime type of a resource reference (extRes) is compatible with a heap which contains that resource reference, pointing to some resource term with the corresponding identifier that the resource points to. In the premise of (extRes), the resource term with its identifier is preserved in the heap since there may be other references pointing to it (e.g., generated from a split). The (GCArr) rule then allows heap compatibility to 'garbage collect' any remaining resources.

The (ext) rule says that a context with graded assumption $lcol(x : [A]_s)$ is compatible with a heap as long as the heap contains a binding for $x$ to some value $v$ and heap grade $r$ that can accommodate the usage of $s$ (via the constraint $exists r'. med s + r' equiv r$) and as long as the free variables $Gamma'$ of $v$ are also compatible with the heap (scaled by $s$ to reflect the usage of $x$). The (extLin) rule is similar to (ext), but _effectively_ where $s = 1$; the variable $x$ is used in a linear fashion.

#block(
  width: 100%,
  stroke: (left: 2.5pt + rgb("0750d0")),
  inset: (left: 0.8em, y: 0.4em),
  above: 0.8em,
  below: 0.8em,
)[
  #text(weight: "bold")[Example 6.5.] As an illustrative example, the context $lcol(x : [A]_1), lcol(y : [B]_2)$ is compatible with the heap $x mapsto_(lcol(7)) v_1, y mapsto_(lcol(2)) v_2$ assuming the typing $lcol(x : [A]_3) ⊢ v_2 : B$, with heap compatibility derivation:

  #v(0.5em)
  #align(center)[
  #prooftree(
    rule(
      name: [ext],
      rule(
        name: [ext],
        rule($emptyset comprel emptyset$, name: [empty]),
        $emptyset, x mapsto_(lcol(7)) v comprel lcol(x : [A]_7)$
      ),
      $lcol(x : [A]_3) ⊢ v_2 : B$,
      $(emptyset, x mapsto_(lcol(7)) v_1, y mapsto_(lcol(2)) v_2) comprel (lcol(x : [A]_1), lcol(y : [B]_2))$
    )
  )
  ]
  #v(0.5em)
]

Heap compatibility allows us to establish key properties for our calculus in conjunction with the operational semantics. We begin with syntactic type safety, by verifying progress and preservation. These are largely standard, though preservation links with heap compatibility in its second conjunct.

In addition to preservation, @marshall2022linearity also proved a _conservation_ property, ensuring that resource usage is respected. Their semantics was call-by-name, which is more natural for conservation; checking that a modified form of conservation still holds in our setting is future work, though various other graded type systems with similar properties are also call-by-value @orchard2019quantitative .

We now move on to establishing the properties related to the safety of ownership and borrowing and how these notions relate to the references present in the heap:

#include "theorem-progress-ottput.typ"
#include "theorem-type-preservation-ottput.typ"
#include "theorem-borrow-safety-single-ottput.typ"
#include "theorem-borrow-safety-multi-ottput.typ"
#include "theorem-uniqueness-ottput.typ"

The uniqueness theorem presented by @marshall2022linearity now follows as a direct corollary of the multi-step borrow safety theorem we described above.

Finally, we see that the operational semantics we have defined (extended to full $beta$-reduction) supports the equational theory we have gradually developed in this work:

#include "theorem-soundness-eq-theory-ottput.typ"

Full proofs for the above theorems may be found in the appendices for this paper, provided as supplementary material, along with collected typing and reduction rules.
