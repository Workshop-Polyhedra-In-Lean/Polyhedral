/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/
module

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.StdSimplex

/-!
# Vertices of a convex hull

This file proves the elementary fact underlying the (non-homogenization) Krein-Milman theorem
for polytopes: a point of a finite set `T` that is *not* a convex combination of the rest of `T`
is automatically a vertex (extreme point) of `convexHull k T`, and conversely. This is proved
directly from the definition of `ConvexSet.IsFaceOf`, with no separation theorem needed.
-/

public section

namespace Convexity

variable {k V A : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup V] [Module k V] [AddTorsor V A] [DecidableEq A]

attribute [local instance] AddTorsor.toConvexSpace

open StdSimplex

/-- If `x = w.sConvexComb` for a combination `w` of points of `C`, and `x` lies in a face `F` of
`C`, then every point in the support of `w` lies in `F` too. This generalizes
`ConvexSet.IsFaceOf.left_mem_of_mem_openSegment` from binary chords to arbitrary finite convex
combinations, exactly mirroring `PointedCone.IsFaceOf.mem_of_sum_smul_mem` for cones: peel one
point `s` of the support off at a time via `exists_sConvexComb_lineMap`, exhibiting `w.sConvexComb`
as a chord point between `s` and the combination of the rest, and read off `s ∈ F` directly. -/
theorem ConvexSet.IsFaceOf.mem_of_sConvexComb_mem {F C : ConvexSet k A} (hF : F.IsFaceOf C)
    {w : StdSimplex k A} (hw : ↑w.weights.support ⊆ (C : Set A)) (hmem : w.sConvexComb ∈ F) :
    ∀ s ∈ w.weights.support, s ∈ F := by
  classical
  intro s hs
  by_cases hcase : w.weights s = 1
  · rwa [sConvexComb_eq_of_weights_eq_one hcase] at hmem
  · obtain ⟨w', hw'supp, hw'lm⟩ := exists_sConvexComb_lineMap hcase
    have hsC : s ∈ (C : Set A) := hw (Finset.mem_coe.mpr hs)
    have hw'C : ↑w'.weights.support ⊆ (C : Set A) := by
      rw [hw'supp]
      exact (Finset.coe_subset.mpr Finset.sdiff_subset).trans hw
    have hw'Cmem : w'.sConvexComb ∈ (C : Set A) := C.isConvexSet.sConvexComb_mem hw'C
    have hs0 : 0 < w.weights s :=
      lt_of_le_of_ne (w.nonneg s) (Ne.symm (Finsupp.mem_support_iff.mp hs))
    have hs1 : w.weights s < 1 := lt_of_le_of_ne (weights_le_one w s) hcase
    have hpt : AffineMap.lineMap w'.sConvexComb s (w.weights s) ∈ F := by rw [hw'lm]; exact hmem
    have hseg : AffineMap.lineMap w'.sConvexComb s (w.weights s) ∈
        openSegment k s w'.sConvexComb := by
      refine ⟨w.weights s, 1 - w.weights s, hs0, by linarith, by ring, ?_⟩
      rw [AddTorsor.convexCombPair_eq_lineMap]
    exact hF.left_mem_of_mem_openSegment hsC hw'Cmem hpt hseg

/-- **The core lemma.** A point `v` of a finite set `T` that is not a convex combination of
`T \ {v}` is automatically a vertex (extreme point) of `convexHull k T`, and conversely.

This is what makes the finite Krein-Milman theorem elementary: no separating hyperplane is
needed, just splitting a combination that witnesses `v` as non-essential (or splitting the
witnessing chord) using `left_mem_of_mem_openSegment` directly. -/
theorem essential_iff_singleton_isFaceOf {T : Finset A} {v : A} (hv : v ∈ T) :
    v ∉ convexHull k (T.erase v : Set A) ↔
      ({v} : ConvexSet k A).IsFaceOf (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) := by
  classical
  constructor
  · intro hess
    refine ⟨?_, ?_⟩
    · rintro y rfl
      exact subset_convexHull_self hv
    · intro a ha b hb z hz hzab
      simp only [ConvexSet.mem_mk] at ha hb
      have hz' : v = z := hz.symm
      subst hz'
      by_contra hav
      obtain ⟨wa, hwa, rfla⟩ := mem_convexHull_iff_exists_sConvexComb.mp ha
      obtain ⟨wb, hwb, rflb⟩ := mem_convexHull_iff_exists_sConvexComb.mp hb
      obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hzab
      rw [AddTorsor.convexCombPair_eq_lineMap] at hcomb
      subst rfla; subst rflb
      set wc : StdSimplex k A := convexCombPair p q hp.le hq.le hpq wa wb with hwcdef
      have hwcsupp : ↑wc.weights.support ⊆ (T : Set A) := by
        rw [hwcdef, weights_convexCombPair]
        intro y hy
        rw [Finset.mem_coe] at hy
        rcases Finset.mem_union.mp (Finsupp.support_add hy) with hy' | hy'
        · exact hwa (Finset.mem_coe.mpr (Finsupp.support_smul hy'))
        · exact hwb (Finset.mem_coe.mpr (Finsupp.support_smul hy'))
      have hwcv : (wc.sConvexComb : A) = v := by
        rw [hwcdef, sConvexComb_convexCombPair, AddTorsor.convexCombPair_eq_lineMap, ← hcomb]
      -- `wc.weights v = 1` would force `wa.weights v = 1`, i.e. `a = v`, contradicting `hav`.
      have hcase : wc.weights v ≠ 1 := by
        intro hcase1
        apply hav
        have hle : wa.weights v ≤ 1 := weights_le_one wa v
        have hle' : wb.weights v ≤ 1 := weights_le_one wb v
        have heq : p * wa.weights v + q * wb.weights v = 1 := by
          rwa [hwcdef, weights_convexCombPair, Finsupp.add_apply, Finsupp.smul_apply,
            Finsupp.smul_apply, smul_eq_mul, smul_eq_mul] at hcase1
        rw [sConvexComb_eq_of_weights_eq_one (show wa.weights v = 1 by nlinarith)]
        rfl
      apply hess
      obtain ⟨w', hw', hw'lm⟩ := exists_sConvexComb_lineMap hcase
      rw [hwcv] at hw'lm
      have hsolve : w'.sConvexComb = v := by
        have hlm := (AffineMap.lineMap_eq_right_iff (k := k)).mp hw'lm
        exact hlm.resolve_right hcase
      have hmem' : w'.sConvexComb ∈ convexHull k (T.erase v : Set A) := by
        apply mem_convexHull_iff_exists_sConvexComb.mpr
        refine ⟨w', ?_, rfl⟩
        refine (Finset.coe_subset.mpr hw'.le).trans (Finset.coe_subset.mpr ?_)
        intro y hy
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hy
        exact Finset.mem_erase.mpr ⟨hy.2, Finset.mem_coe.mp (hwcsupp (Finset.mem_coe.mpr hy.1))⟩
      rwa [hsolve] at hmem'
  · intro hface hmem
    obtain ⟨w, hwsupp, hwv⟩ := mem_convexHull_iff_exists_sConvexComb.mp hmem
    have hvnotsupp : v ∉ w.weights.support := fun hvs =>
      Finset.notMem_erase v T (Finset.mem_coe.mp (hwsupp (Finset.mem_coe.mpr hvs)))
    obtain ⟨v₀, hv₀⟩ := w.support_weights_nonempty
    have hv₀v : v₀ ≠ v := fun h => hvnotsupp (h ▸ hv₀)
    have hr₀pos : 0 < w.weights v₀ :=
      lt_of_le_of_ne (w.nonneg v₀) (Ne.symm (Finsupp.mem_support_iff.mp hv₀))
    have hlt1 : w.weights v₀ ≠ 1 := by
      intro heq
      exact hv₀v ((sConvexComb_eq_of_weights_eq_one heq).symm.trans hwv)
    obtain ⟨w', hw'supp, hw'lm⟩ := exists_sConvexComb_lineMap hlt1
    rw [hwv] at hw'lm
    have hseg : v ∈ openSegment k v₀ w'.sConvexComb := by
      refine ⟨w.weights v₀, 1 - w.weights v₀, hr₀pos,
        by linarith [lt_of_le_of_ne (weights_le_one w v₀) hlt1], by ring, ?_⟩
      rw [AddTorsor.convexCombPair_eq_lineMap]
      exact hw'lm
    have hv₀mem : v₀ ∈ (⟨convexHull k (T : Set A), IsConvexSet.convexHull⟩ : ConvexSet k A) :=
      subset_convexHull_self
        (Finset.mem_of_mem_erase (Finset.mem_coe.mp (hwsupp (Finset.mem_coe.mpr hv₀))))
    have hw'mem :
        w'.sConvexComb ∈ (⟨convexHull k (T : Set A), IsConvexSet.convexHull⟩ : ConvexSet k A) := by
      apply mem_convexHull_iff_exists_sConvexComb.mpr
      refine ⟨w', ?_, rfl⟩
      refine (Finset.coe_subset.mpr hw'supp.le).trans (Finset.coe_subset.mpr ?_)
      intro y hy
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hy
      exact Finset.mem_of_mem_erase (Finset.mem_coe.mp (hwsupp (Finset.mem_coe.mpr hy.1)))
    exact hv₀v (hface.2 hv₀mem hw'mem (z := v) rfl hseg)

end Convexity
