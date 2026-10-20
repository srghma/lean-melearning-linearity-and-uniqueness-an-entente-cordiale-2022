# Summary of changes for run c97d04f3-a3b0-4e76-a25f-be874e7a9d1a
I added four results to the formalisation, in five new files under `RequestProject/LCU/`. The whole project builds with no `sorry`, and the only axioms used are `propext`, `Classical.choice` and `Quot.sound`. Terms still use de Bruijn indices, with `Term 0` for closed terms.

**1. Evaluation terminates (`CbnNormalization.lean`).** This applies to the call-by-name semantics from the previous run, for terms without array primitives. The paper doesn't state this result.
- `cbn_normalization`: every closed term that has a type reduces to a value.
- `cbn_eval`: that value has the same type, given non-linear array references in the context.
- `cbn_value_unique`: the value is unique.

**2. The examples from Section 2 (`KeyIdeas.lean`).** `Cake`, `Coffee` and the other types are arbitrary, and `eat`, `have`, `drink` and `keep` are free non-linear variables.
- `not_hasType_lam_pair_dup`: `λx. (t₁, t₂)` has no type if `x` occurs in both parts. So `λc. (eat c, have c)` (`impossible_cake`) and `λc. (drink c, keep c)` (`impossible_coffee`) are ill-typed at every type.
- These have the expected types:
  - `possible_cake`: `λlots. let! cake = lots in (eat cake, have cake) : !Cake ⊸ Happy ⊗ Cake`;
  - `sip_hasType`: `λfresh. let! coffee = &fresh in (keep coffee, drink coffee) : *Coffee ⊸ Coffee ⊗ Awake`;
  - dereliction `!A ⊸ A`, `*A ⊸ A`, and contraction and weakening for `!`;
  - Granule's `uniqueReturn : *A ⊸ !A` and `uniqueBind : (*A ⊸ !B) ⊸ !A ⊸ !B`.

**3. Type safety with mutable arrays (`ArraySemantics.lean`, `RefShift.lean`).** I added a semantics `AStep` with a store of float arrays, following the paper's array rules:
- `newArray` allocates a fresh array, `readArray` reads it, and `writeArray` updates it in place;
- `copy` copies every array the copied value refers to, giving the copies fresh references;
- primitive arguments are evaluated, including under `*`.

Results:
- `AStep.preserves`: each step keeps the type (the typing context may gain fresh arrays).
- `astep_progress`: a term with a type is a value or can step. This now includes the array primitives.
- `array_type_safety`: a closed program that has a type, run from the empty store, never gets stuck.

**4. An example run (`ArrayExamples.lean`).** For any float `x`, `readArray (writeArray (newArray 3) 0 x) 0` has a type and evaluates to `(x, *a)`, so the read sees the write.

**Limitations.**
- In the array semantics, `deleteArray` does not free memory. Freeing safely needs the uniqueness guarantee (Theorem 5), which I did not prove. Array references are treated as non-linear throughout.
- These are repaired semantics I designed, not the paper's heap model. The literal Theorems 4–7 remain disproved, as in the previous run.

`README.md` describes the new files. The new definition and theorems are in the Properties table, and the theorems are marked proved. `ARISTOTLE_SUMMARY.md` is unchanged.