/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Alena Gusakov, Bhavik Mehta, Kyle Miller

Adapted and annotated for Sam Shady, September 28, 2026.
Source: mathlib4, Mathlib/Combinatorics/Hall/Finite.lean
Commit: c44e0c8ee63ca166450922a373c7409c5d26b00b (v4.19.0)

Changes: renamed the proof namespace and lemmas, added an explanatory guide,
restated the final equivalence, and added a bipartite-relation formulation.
The inductive core is adapted from the credited mathlib proof, not claimed
as an independently discovered proof.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic

/-!
# Hall's marriage theorem, with the full finite induction

## Statement
For a finite left vertex type `ι`, let `t i` be the finite set of neighbors
of vertex `i`. A matching covering the left side is an injective function
`f : ι → α` such that `f i ∈ t i` for every `i`.

Hall's condition says that for every subset `s` of the left side,
  `s.card ≤ (s.biUnion t).card`.
Here `s.biUnion t` is the union of the neighbor sets of vertices in `s`.
The notation `#s` is shorthand for `s.card`.

## Proof map
We use strong induction on the number of left vertices.
* Empty side: the empty function is a matching.
* Slack case: every nonempty proper subset has strictly more neighbors
  than vertices. Choose an edge x--y, delete x and y, and apply induction.
  Deleting y decreases any neighbor count by at most one, so Hall survives.
  Add x--y to the smaller matching.
* Tight case: some nonempty proper subset s has exactly |s| neighbors.
  Apply induction inside s. For the remaining vertices, delete all neighbors
  of s. For every subset u of those remaining vertices, Hall on s ∪ u gives
      |s| + |u| ≤ |N(s) ∪ N(u)| = |N(s)| + |N(u) \ N(s)|.
  Since |s| = |N(s)|, the reduced problem satisfies Hall too. Apply induction
  there and join the two matchings; their images are disjoint.
* Necessity: the image of any subset under an injective matching has the
  same cardinality as the subset and lies inside its neighborhood.

## Trust boundary
No Hall theorem is imported. All Hall-specific induction lemmas are below.
The imports supply ordinary finite-set, cardinality, and subtype machinery.
The final commands print the axioms of both public theorem statements.
-/

open Finset

universe u v

namespace HallProof

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

/-- In the slack case, removing one right vertex leaves Hall's inequality
on the left vertices other than x. This is the key counting lemma for case A. -/
theorem hall_after_deleting_pair {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  haveI := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, exists_prop, SetCoe.exists, exists_and_right,
        exists_eq_right, Subtype.coe_mk]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_not_mem hb]
      exact Nat.le_of_lt ha'
  · rw [nonempty_iff_ne_empty, not_not] at he
    subst s'
    simp

/-- First case of the inductive step: assuming that
`∀ (s : Finset ι), s.Nonempty → s ≠ univ → #s < #(s.biUnion t)`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem match_when_all_proper_subsets_have_slack {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  haveI := Classical.decEq ι
  -- Choose an arbitrary element `x : ι` and `y : t x`.
  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]

  choose y hy using tx_ne
  -- Restrict to everything except `x` and `y`.
  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]

  rcases ih t' card_ι'.le (hall_after_deleting_pair y ha) with ⟨f', hfinj, hfr⟩
  -- Extend the resulting function.
  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only [ne_eq, Set.mem_setOf_eq]
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

/-- A subfamily inherits Hall's condition by viewing its index subsets
as subsets of the original index type. -/
theorem hall_on_subset {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

/-- If s is tight, removing s and all of its neighbors preserves Hall.
The proof applies Hall to s union a subset of its complement, then subtracts
|s| = |N(s)| from the cardinality inequality. -/
theorem hall_outside_tight_subset {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  haveI := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, exists_prop, SetCoe.exists, exists_and_right,
      exists_eq_right, Subtype.coe_mk]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff]
  · refine (card_le_card ?_).trans le_rfl
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union, exists_and_right,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

/-- Second case of the inductive step: assuming that
there is a nonempty proper subset `s` with `#s = #(s.biUnion t)`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem match_using_tight_subset {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI := Classical.decEq ι
  -- Restrict to `s`
  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_on_subset ht) with ⟨f', hf', hsf'⟩
  -- Restrict to `sᶜ` in the domain and `(s.biUnion t)ᶜ` in the codomain.
  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_outside_tight_subset hus ht) with ⟨f'', hf'', hsf''⟩
  -- Put them together
  have f'_mem_biUnion : ∀ (x') (hx' : x' ∈ s), f' ⟨x', hx'⟩ ∈ s.biUnion t := by
    intro x' hx'
    rw [mem_biUnion]
    exact ⟨x', hx', hsf' _⟩
  have f''_not_mem_biUnion : ∀ (x'') (hx'' : ¬x'' ∈ s), ¬f'' ⟨x'', hx''⟩ ∈ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : ¬x'' ∈ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    intro x x' hx' hx'' h
    apply f''_not_mem_biUnion x' hx''
    rw [← h]
    apply f'_mem_biUnion x
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only [of_eq_true]
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

/-- Here we combine the two inductive steps into a full strong induction proof,
completing the proof the harder direction of **Hall's Marriage Theorem**.
-/
theorem construct_matching (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine match_when_all_proper_subsets_have_slack hn ht (@fun ι' => ih' ι') h
    · push_neg at h
      rcases h with ⟨s, sne, snu, sle⟩
      exact match_using_tight_subset hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallProof


namespace HallProof

/-- Hall's marriage theorem for a finite family of finite neighbor sets. -/
theorem hall_marriage {ι α : Type*} [Finite ι] [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i := by
  constructor
  · -- Sufficiency: the strong induction proved above constructs the matching.
    exact construct_matching
  · -- Necessity: f(s) is a subset of N(s), and injectivity gives |f(s)| = |s|.
    rintro ⟨f, hf, hneighbor⟩ s
    rw [← card_image_of_injective s hf]
    apply card_le_card
    intro y hy
    rcases mem_image.mp hy with ⟨i, hi, rfl⟩
    exact mem_biUnion.mpr ⟨i, hi, hneighbor i⟩

/-- The neighborhood N(S) in a finite bipartite graph described by `adj`.
The two vertex types L and R encode the two sides of the graph. -/
def neighbors {L R : Type*} [Fintype R] [DecidableEq R]
    (adj : L → R → Prop) [DecidableRel adj] (S : Finset L) : Finset R :=
  S.biUnion (fun l => Finset.univ.filter (adj l))

/-- Bipartite-graph form: Hall's inequalities hold exactly when there is
an injective assignment of an adjacent right vertex to each left vertex. -/
theorem hall_bipartite {L R : Type*} [Finite L] [Fintype R] [DecidableEq R]
    (adj : L → R → Prop) [DecidableRel adj] :
    (∀ S : Finset L, S.card ≤ (neighbors adj S).card) ↔
      ∃ f : L → R, Function.Injective f ∧ ∀ l, adj l (f l) := by
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using
    (hall_marriage (fun l => Finset.univ.filter (adj l)))

end HallProof

-- Audit: these should list only standard Lean foundations, never sorryAx.
#print axioms HallProof.hall_marriage
#print axioms HallProof.hall_bipartite
