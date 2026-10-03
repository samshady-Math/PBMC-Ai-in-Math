# Hall’s marriage theorem in Lean 4

This project contains a complete, annotated finite induction proof, adapted
from the mathlib proof by Alena Gusakov, Bhavik Mehta, and Kyle Miller.
It is not claimed as an original proof. The source is distributed under
Apache 2.0; see LICENSE and the attribution at the top of HallMarriage.lean.

## The mathematical statement

Let L and R be the two sides of a finite bipartite graph. For S ⊆ L, let
N(S) be the vertices in R adjacent to at least one vertex of S. Then

    (for every S ⊆ L, |S| ≤ |N(S)|)
        if and only if
    there is an injective f : L → R with l adjacent to f(l) for every l.

An injective adjacent assignment is exactly a matching covering the left
side. It need not cover the right side. The theorem includes empty sides.

The main family-of-sets formulation, HallProof.hall_marriage, is slightly
more general: L is finite, R need not be finite, and each individual neighbor
set must be finite. HallProof.hall_bipartite specializes it to finite R.

## Read the proof

The file includes every Hall-specific induction lemma. It does not import
Mathlib.Combinatorics.Hall or assume Hall’s theorem.

1. `hall_after_deleting_pair`: in the strict-inequality case, deleting a
   chosen right vertex leaves enough neighbors for the remaining left side.
2. `match_when_all_proper_subsets_have_slack`: choose one edge, apply the
   induction hypothesis after deleting its endpoints, and extend the matching.
3. `hall_on_subset`: Hall’s condition passes to a subfamily.
4. `hall_outside_tight_subset`: deleting a tight subset and all its neighbors
   leaves another instance of Hall’s condition.
5. `match_using_tight_subset`: build the two smaller matchings and combine
   them, using disjointness of their images.
6. `construct_matching`: strong induction on the number of left vertices,
   with the empty case and the two cases above.
7. `hall_marriage`: adds the necessary direction using injective image counts.
8. `hall_bipartite`: states the familiar graph version using an adjacency relation.

The underlying counting argument for step 4 is the key:

    |S| + |U| ≤ |N(S ∪ U)| = |N(S)| + |N(U) ∖ N(S)|.

When |S| = |N(S)|, cancellation proves |U| ≤ |N(U) ∖ N(S)|.
Both S and its complement have fewer left vertices, so induction applies.

## Lean notation

- `Finset L`: a finite subset of L.
- `s.card`, also written `#s`: cardinality of s.
- `s.biUnion t`: the union of the sets t(i) as i ranges over s.
- `Function.Injective f`: distinct inputs have distinct outputs.
- `∃ f, ...`: there exists a function with the stated properties.
- `↔`: both implications are proved.
- `Fintype`: an enumeration of a finite type.
- `Finite`: a proposition asserting finiteness, without an explicit enumeration.
- `DecidableRel adj`: adjacency can be decided; classical logic can supply this.

## Reproduce the check

Install Lean’s elan toolchain manager, then open a terminal in this directory:

```sh
lake update
lake exe cache get Mathlib/Data/Fintype/Basic.lean Mathlib/Data/Fintype/Powerset.lean Mathlib/Data/Set/Finite/Basic.lean
lake env lean HallMarriage.lean
```

The toolchain is pinned to Lean 4.19.0 and the mathlib dependency is pinned
to commit c44e0c8ee63ca166450922a373c7409c5d26b00b (mathlib v4.19.0).
The final command checks the source and prints the axiom dependencies.

## Attribution

Original file:
https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Combinatorics/Hall/Finite.lean

Changes in this version: renamed the namespace and proof lemmas, added a
proof guide and explanatory comments, restated the final equivalence, and
added the finite bipartite-relation formulation.

## Verification result

Lean 4.19.0 checked HallMarriage.lean successfully (exit code 0), with no
errors or warnings. Both public theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`, the standard classical foundations used
by Lean/mathlib. There is no `sorryAx` dependency and no added axiom.
See verification.txt for the compiler output and source SHA-256.

The source was compiled in the pinned mathlib checkout. The small Lake
project configuration is provided to reproduce that check in a new folder.
