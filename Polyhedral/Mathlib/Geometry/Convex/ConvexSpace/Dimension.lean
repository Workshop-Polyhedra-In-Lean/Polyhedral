/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- TODO: #min_imports later
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Dimension
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

/-!

TODO

-/

namespace Convexity

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (s : Set P)

section Ring

variable [Ring k] [Module k V]

noncomputable def cardinalDim : WithBot Cardinal :=
  (affineSpan k s).cardinalDim
noncomputable def finDim : WithBot Nat :=
  WithBot.map Cardinal.toNat (cardinalDim k s)
noncomputable def efinDim : WithBot ENat :=
  WithBot.map Cardinal.toENat (cardinalDim k s)

@[simp]
theorem cardinalDim_eq_bot_iff : cardinalDim k s = ⊥ ↔ s = ∅ := by
  simp [cardinalDim]

@[simp]
theorem efinDim_eq_bot_iff : efinDim k s = ⊥ ↔ s = ∅ := by
  simp [efinDim]

@[simp]
theorem eq_singleton_of_affineSpan_eq (k : Type*) {V : Type*} {P : Type*}
    [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] (s : Set P) (x : P)
    (hx : ↑(affineSpan k s) = {x}) : s = {x} := by
  have h : s ⊆ {x} := by
    have h' := (affineSpan_le.mp hx.le)
    apply h'.trans
    rfl
  have hs : s.Nonempty := by
    apply (affineSpan_nonempty k).mp
    rw [hx]
    simp
  exact ((Set.Nonempty.subset_singleton_iff hs).mp h)

@[simp]
theorem eq_affineSpan_singleton (k : Type*) {V : Type*} {P : Type*}
    [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] (x : P) :
      affineSpan k {x} = {x} := by
  ext y
  simp only [AffineSubspace.mem_affineSpan_singleton, SetLike.mem_singleton_iff]

theorem cardinalDim_eq_zero_iff : cardinalDim k s = 0 ↔ ∃ x : P, s = {x} := by
  simp only [cardinalDim]
  rw [AffineSubspace.cardinalDim_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    use x
    exact eq_singleton_of_affineSpan_eq _ _ x hx
  · rintro ⟨x, hx⟩
    use x
    rw [hx]
    simp

theorem efinDim_eq_zero_iff : efinDim k s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

end Ring

section Field

variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

attribute [local instance] AddTorsor.toConvexSpace

/-- Every affine subspace is convex: it already absorbs segments by definition
(`AffineSubspace.smul_vsub_vadd_mem`), and over a field that's enough to check convexity, without
unwinding general finite convex combinations. -/
theorem isConvexSet_affineSubspace (t : AffineSubspace k P) : IsConvexSet k (t : Set P) :=
  IsConvexSet.of_convexCombPair_mem fun a b ha hb hab x hx y hy ↦ by
    rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply]
    exact t.smul_vsub_vadd_mem a hx hy hy

/-- An affine span is convex: a special case of `isConvexSet_affineSubspace`. -/
theorem isConvexSet_affineSpan : IsConvexSet k (affineSpan k s : Set P) :=
  isConvexSet_affineSubspace k (affineSpan k s)

/-- The convex hull of a set and the set itself have the same affine span: `convexHull k s`
already sits inside the (convex) `affineSpan k s` by minimality of the hull, and conversely
`affineSpan` is monotone along `s ⊆ convexHull k s`. -/
theorem affineSpan_convexHull_eq : affineSpan k (convexHull k s : Set P) = affineSpan k s := by
  refine le_antisymm ?_ (affineSpan_mono k subset_convexHull_self)
  have h1 : convexHull k s ⊆ (affineSpan k s : Set P) :=
    convexHull_min (subset_affineSpan k s) (isConvexSet_affineSpan k s)
  calc affineSpan k (convexHull k s : Set P)
      ≤ affineSpan k (affineSpan k s : Set P) := affineSpan_mono k h1
    _ = affineSpan k s := AffineSubspace.affineSpan_coe _

end Field

section DivisionRing

variable [DivisionRing k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

/-- A set spanning a line (`cardinalDim = 1`) has at least two points: a subsingleton spans at
most a point, whose `vectorSpan` is `⊥`, i.e. has rank `0 ≠ 1`. -/
theorem not_subsingleton_of_cardinalDim_eq_one {s : Set P} (h : cardinalDim k s = 1) :
    ¬ s.Subsingleton := by
  -- TODO: Easier way to do this using the earlier lemmas?
  intro hsub
  rcases hsub.eq_empty_or_singleton with rfl | ⟨a, rfl⟩
  · simp [cardinalDim, AffineSubspace.cardinalDim] at h
  · have hne : (affineSpan k ({a} : Set P)).carrier ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp ⟨a, mem_affineSpan k rfl⟩
    have h0 : cardinalDim k ({a} : Set P) = (0 : Cardinal) := by
      change (affineSpan k ({a} : Set P)).cardinalDim = _
      rw [AffineSubspace.cardinalDim, if_neg hne, direction_affineSpan, vectorSpan_singleton]
      simp
    rw [h0] at h
    exact absurd (WithBot.coe_eq_coe.mp h) zero_ne_one

theorem subset_affineSpan_pair_of_cardinalDim_eq_one
    (h : cardinalDim k s = 1) :
    ∃ x y : P, x ≠ y ∧ s ⊆ affineSpan k {x, y} := by
  simp only [cardinalDim] at h
  obtain ⟨x, y, h₁, h₂⟩ := AffineSubspace.cardinalDim_eq_one_iff .. |>.mp h
  exact ⟨x, y, h₁, h₂ ▸ subset_affineSpan ..⟩

-- TODO: other direction?

theorem efinDim_eq_one_iff :
    efinDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  -- TODO adapt to above
  sorry

end DivisionRing

end Convexity
