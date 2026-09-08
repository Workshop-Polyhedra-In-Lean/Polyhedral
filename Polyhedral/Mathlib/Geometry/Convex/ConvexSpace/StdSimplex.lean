/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Tactic.Linarith

/-! # Peeling a point off a standard-simplex combination

Two elementary facts about `StdSimplex`, needed (in `Set/Face/Vertex.lean`) to break a convex
combination into "one named point" plus "the rest". Both are pure `ConvexSpace`/`StdSimplex`
facts — no `ConvexSet` or face machinery is involved, so they belong here rather than next to the
face-theoretic material that uses them.

* `StdSimplex.sConvexComb_eq_of_weights_eq_one`: if a single point carries all the weight of a
  combination, the combination evaluates to that point.
* `StdSimplex.exists_sConvexComb_lineMap`: otherwise, the combination can be re-expressed as an
  affine combination of that point and a combination supported away from it. -/

namespace Convexity

namespace StdSimplex

section Field

variable {k V A : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup V] [Module k V] [AddTorsor V A] [DecidableEq A]

attribute [local instance] AddTorsor.toConvexSpace

variable {w : StdSimplex k A} {v : A}

omit [DecidableEq A] in
theorem weights_le_one (w : StdSimplex k A) (v : A) : w.weights v ≤ 1 := by
  classical
  rw [← w.total]
  by_cases hv : v ∈ w.weights.support
  · exact Finset.single_le_sum (fun i _ => w.nonneg i) hv
  · rw [Finsupp.notMem_support_iff.mp hv]
    exact Finsupp.sum_nonneg (fun i _ => w.nonneg i)

omit [DecidableEq A] in
/-- If a point carries all the weight of a combination, the combination evaluates to that
point. The support of `w.weights` is forced down to `{v}` — since the weights are nonnegative,
sum to `1`, and `v` already accounts for all of that sum, everything else must sum to `0`
(`Finset.sum_eq_zero_iff_of_nonneg`), hence vanish termwise — after which
`support_weights_eq_singleton` (Mathlib's `StdSimplex` API) identifies `w` with the point mass at
`v`. -/
theorem sConvexComb_eq_of_weights_eq_one (h : w.weights v = 1) : w.sConvexComb = v := by
  classical
  have hvmem : v ∈ w.weights.support := by simp [Finsupp.mem_support_iff, h]
  have hsupp : w.weights.support = {v} := by
    have hsum1 : ∑ x ∈ w.weights.support, w.weights x = 1 := by
      have := w.total; rwa [Finsupp.sum] at this
    have htot : (∑ x ∈ w.weights.support.erase v, w.weights x) + w.weights v =
        ∑ x ∈ w.weights.support, w.weights x := Finset.sum_erase_add _ _ hvmem
    rw [h, hsum1] at htot
    have hsum0 : ∑ x ∈ w.weights.support.erase v, w.weights x = 0 := by linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => w.nonneg i)).mp hsum0
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hvmem, ?_⟩
    intro x hx
    by_contra hxv
    exact (Finsupp.mem_support_iff.mp hx) (hzero x (Finset.mem_erase.mpr ⟨hxv, hx⟩))
  rw [support_weights_eq_singleton.mp hsupp]
  exact AddTorsor.convexCombination_single v

/-- If a point does *not* carry all the weight of a combination, the combination can be
re-expressed as an affine combination of that point and a combination supported away from it. -/
theorem exists_sConvexComb_lineMap (hv1 : w.weights v ≠ 1) :
    ∃ w' : StdSimplex k A, w'.weights.support = w.weights.support \ {v} ∧
      AffineMap.lineMap w'.sConvexComb v (w.weights v) = w.sConvexComb := by
  classical
  by_cases hv0 : w.weights v = 0
  · refine ⟨w, ?_, by simp [hv0]⟩
    have hvns : v ∉ w.weights.support := by simp [Finsupp.mem_support_iff, hv0]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨fun hx => ⟨hx, fun he => hvns (he ▸ hx)⟩, fun hx => hx.1⟩
  · have hs : ∃ x ∈ ({v} : Set A), w.weights x ≠ 0 := ⟨v, rfl, hv0⟩
    have hsupp : w.weights.support ⊆ {v} → w.weights v = 1 := by
      intro hsupp
      rcases Finset.subset_singleton_iff.mp hsupp with heq | heq
      · exfalso
        have htot := w.total
        rw [Finsupp.sum, heq] at htot
        simp at htot
      · have htot := w.total
        rw [Finsupp.sum, heq] at htot
        simpa using htot
    have hs' : ∃ x ∈ ({v} : Set A)ᶜ, w.weights x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv1 (hsupp fun x hx => ?_)
      by_contra hxv
      exact (Finsupp.mem_support_iff.mp hx) (hcon x (by simpa using hxv))
    refine ⟨w.restrict {v}ᶜ hs', ?_, ?_⟩
    · rw [support_weights_restrict]
      ext x
      simp only [Finset.mem_filter, Set.mem_compl_iff, Set.mem_singleton_iff,
        Finset.mem_sdiff, Finset.mem_singleton]
    have hkey := StdSimplex.convexCombPair_restrict_restrict_compl w {v} hs hs'
    have hthis := congrArg sConvexComb hkey
    rw [sConvexComb_convexCombPair, restrict_singleton, sConvexComb_single,
      AddTorsor.convexCombPair_eq_lineMap] at hthis
    have hv : (w.weights.filter (· ∈ ({v} : Set A))).sum (fun _ k => k) = w.weights v := by
      classical
      rw [Finsupp.sum, Finsupp.support_filter]
      rw [Finset.sum_congr rfl (fun a ha => by
        rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp ha).2])]
      by_cases hvs : v ∈ w.weights.support
      · have heq : {x ∈ w.weights.support | x ∈ ({v} : Set A)} = {v} := by
          ext x
          simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨hvs, rfl⟩
        rw [heq]; simp
      · have heq : {x ∈ w.weights.support | x ∈ ({v} : Set A)} = ∅ := by
          ext x
          simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.notMem_empty, iff_false,
            not_and]
          rintro hx rfl
          exact hvs hx
        rw [heq]
        simp [Finsupp.notMem_support_iff.mp hvs]
    rwa [hv] at hthis

end Field

end StdSimplex

end Convexity
