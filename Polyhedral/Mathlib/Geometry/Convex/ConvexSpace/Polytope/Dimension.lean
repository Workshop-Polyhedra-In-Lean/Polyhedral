/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Dimension
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-!

A 1-dimensional polytope is a segment: the convex hull of two distinct points.

-/

noncomputable section

namespace Convexity

variable (k : Type*) {V P : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup V] [Module k V] [AddTorsor V P]

attribute [local instance] AddTorsor.toConvexSpace

variable (P) in
/-- A segment is the convex hull of two distinct points. -/
def IsSegment (s : Set P) : Prop := ∃ x y : P, x ≠ y ∧ s = convexHull k {x, y}

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- The line through two points is the range of the line map between them. -/
theorem affineSpan_pair_eq_range_lineMap (x y : P) :
    (affineSpan k {x, y} : Set P) = Set.range (AffineMap.lineMap x y : k → P) :=
  Set.ext fun _ ↦ mem_affineSpan_pair_iff_exists_lineMap_eq

/-- A 1-dimensional polytope is a segment. -/
theorem IsPolytope.isSegment_of_cardinalDim_eq_one {s : Set P} (hs : IsPolytope k s)
    (h1 : cardinalDim k s = 1) : IsSegment k P s := by
  obtain ⟨t, rfl⟩ := hs
  -- The affine span of the generating finset already carries the whole hull's affine span.
  have hcd : cardinalDim k (t : Set P) = 1 := by
    change (affineSpan k (t : Set P)).cardinalDim = 1
    rwa [← affineSpan_convexHull_eq k (t : Set P)]
  -- so, being 1-dimensional, it is the line through two distinct points.
  obtain ⟨x, y, hxy, hspan⟩ :=
    (AffineSubspace.cardinalDim_eq_one_iff k P (affineSpan k (t : Set P))).mp hcd
  -- Parametrize that line by `k` via the (injective) line map through `x` and `y`.
  have hli : Function.Injective (AffineMap.lineMap x y : k → P) := AffineMap.lineMap_injective k hxy
  have hsub : (t : Set P) ⊆ Set.range (AffineMap.lineMap x y : k → P) := by
    rw [← affineSpan_pair_eq_range_lineMap k x y, ← hspan]
    exact subset_affineSpan k (t : Set P)
  -- Pull the (finite) generating set back along the line map.
  set t' : Finset k := t.preimage (AffineMap.lineMap x y) hli.injOn with ht'def
  have himg : AffineMap.lineMap x y '' (t' : Set k) = (t : Set P) := by
    rw [ht'def, Finset.coe_preimage]
    exact Set.image_preimage_eq_of_subset hsub
  have ht'card : 1 < t'.card := by
    rw [Finset.one_lt_card]
    by_contra hc
    push Not at hc
    refine not_subsingleton_of_cardinalDim_eq_one k hcd (s := (t : Set P)) ?_
    rw [← himg]
    exact Set.Subsingleton.image (fun a ha b hb ↦ hc a ha b hb) (AffineMap.lineMap x y)
  -- The extremes of the pulled-back parameter set give the endpoints of the segment.
  have ht'ne2 : t'.Nonempty := Finset.card_pos.mp (by omega)
  have hlt : t'.min' ht'ne2 < t'.max' ht'ne2 := t'.min'_lt_max'_of_card ht'card
  set rmin := t'.min' ht'ne2 with hrmindef
  set rmax := t'.max' ht'ne2 with hrmaxdef
  set p := AffineMap.lineMap x y rmin with hpdef
  set q := AffineMap.lineMap x y rmax with hqdef
  have hpq : p ≠ q := fun he ↦ hlt.ne (hli he)
  have hrsub : (rmax - rmin) ≠ 0 := sub_ne_zero_of_ne hlt.ne'
  refine ⟨p, q, hpq, le_antisymm ?_ ?_⟩
  · -- `t ⊆ convexHull k {p, q}`: every point is a `convexCombPair` of `p` and `q`.
    refine convexHull_min (fun z hz ↦ ?_) IsConvexSet.convexHull
    obtain ⟨r, hr, rfl⟩ := himg ▸ hz
    have hr1 : rmin ≤ r := Finset.min'_le t' r hr
    have hr2 : r ≤ rmax := Finset.le_max' t' r hr
    set c := (r - rmin) / (rmax - rmin) with hcdef
    have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
    have hc1 : c ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hceq : AffineMap.lineMap rmin rmax c = r := by
      rw [AffineMap.lineMap_apply]
      simp only [smul_eq_mul, vadd_eq_add, vsub_eq_sub, hcdef]
      field_simp
      ring
    have hz : AffineMap.lineMap x y r = AffineMap.lineMap p q c := by
      rw [← hceq, AffineMap.apply_lineMap]
    rw [hz, ← AddTorsor.convexCombPair_eq_lineMap c (1 - c) hc0 (by linarith) (by ring) q p]
    exact IsConvexSet.convexHull.convexCombPair_mem (subset_convexHull_self (by simp))
      (subset_convexHull_self (by simp)) hc0 (by linarith) (by ring)
  · -- `{p, q} ⊆ convexHull k t`, hence so is its hull, by convexity.
    refine convexHull_min ?_ IsConvexSet.convexHull
    rintro z (rfl | rfl)
    · exact subset_convexHull_self
        (himg ▸ Set.mem_image_of_mem (AffineMap.lineMap x y) (Finset.min'_mem t' _))
    · exact subset_convexHull_self
        (himg ▸ Set.mem_image_of_mem (AffineMap.lineMap x y) (Finset.max'_mem t' _))

end Convexity
