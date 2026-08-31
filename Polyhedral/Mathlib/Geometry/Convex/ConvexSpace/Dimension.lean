/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- TODO: #min_imports later
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.LinearAlgebra.AffineSpace.Independent

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
theorem cardinalDim_empty : cardinalDim k (∅ : Set P) = ⊥ := by
  simp [cardinalDim]

@[simp]
theorem finDim_empty : finDim k (∅ : Set P) = ⊥ := by
  simp [finDim]

@[simp]
theorem efinDim_empty : efinDim k (∅ : Set P) = ⊥ := by
  simp [efinDim]

@[simp]
theorem cardinalDim_eq_bot_iff : cardinalDim k s = ⊥ ↔ s = ∅ := by
  sorry

@[simp]
theorem finDim_eq_bot_iff : finDim k s = ⊥ ↔ s = ∅ := by
  simp [finDim]

@[simp]
theorem efinDim_eq_bot_iff : efinDim k s = ⊥ ↔ s = ∅ := by
  simp [efinDim]

--@[simp]
theorem eq_singleton_of_affineSpan_eq {x : P} (hx : ↑(affineSpan k s) = {x}) : s = {x} := by
  refine (Set.Nonempty.subset_singleton_iff ?_).mp ?_
  · exact (affineSpan_nonempty k).mp (by simp [hx])
  · simpa using affineSpan_le.mp hx.le

@[simp]
theorem eq_affineSpan_singleton (x : P) : affineSpan k {x} = {x} := by
  simp [AffineSubspace.ext_iff]

theorem cardinalDim_eq_zero_iff : cardinalDim k s = 0 ↔ ∃ x : P, s = {x} := by
  simp only [cardinalDim, AffineSubspace.cardinalDim_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, eq_singleton_of_affineSpan_eq _ _ hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simp [hx]⟩

theorem efinDim_eq_zero_iff : efinDim k s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

theorem cardinalDim_eq_rank {s : Set P} (hs : s.Nonempty) :
    cardinalDim k s = Module.rank k (affineSpan k s).direction :=
  AffineSubspace.cardinalDim_eq_rank_of_nonempty _ (Set.Nonempty.affineSpan k hs)

theorem finDim_eq_finrank {s : Set P} (hs : s.Nonempty) :
    finDim k s = Module.finrank k (affineSpan k s).direction := by
  refine WithBot.unbot_inj ?_ (by simp) |>.mp ?_
  · simpa [Set.nonempty_iff_ne_empty] using hs
  congr 1
  simp [finDim, cardinalDim_eq_rank _ hs]
  norm_cast

end Ring

section Field

variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

-- TODO: read and consider the doc comment, should this be stated for a
-- [ConvexSpace k P] type class instead?
attribute [local instance] AddTorsor.toConvexSpace

theorem _root_.AffineSubspace.isConvexSet (t : AffineSubspace k P) : IsConvexSet k (t : Set P) :=
  IsConvexSet.of_convexCombPair_mem fun a b ha hb hab x hx y hy ↦ by
    rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply]
    exact t.smul_vsub_vadd_mem a hx hy hy

@[simp]
theorem _root_.AffineSubspace.convexHull_eq (t : AffineSubspace k P) :
    convexHull k t = (t : Set P) :=
  convexHull_eq_self.mpr (AffineSubspace.isConvexSet ..)

@[simp]
theorem _root_.affineSpan_convexHull_eq : affineSpan k (convexHull k s : Set P) = affineSpan k s := by
  refine le_antisymm ?_ (affineSpan_mono k subset_convexHull_self)
  have := convexHull_min (subset_affineSpan k s) (AffineSubspace.isConvexSet _ _)
  grw [affineSpan_mono k this, affineSpan_le_of_subset_coe le_rfl]

end Field

section DivisionRing

variable [DivisionRing k] [Module k V]

theorem cardinalDim_lt_aleph0 (s : Set P) (hs : s.Nonempty) [FiniteDimensional k V] :
    cardinalDim k s < Cardinal.aleph0 := by
  refine (WithBot.unbot_lt_iff ?_).mp ?_
  · simpa [Set.nonempty_iff_ne_empty] using hs
  simp [cardinalDim_eq_rank _ hs, Module.rank_lt_aleph0]

theorem cardinalDim_eq_finDim_unbot (s : Set P) (hs : s.Nonempty) [Module.Finite k V] :
    cardinalDim k s = (finDim k s).unbot (by simpa [Set.nonempty_iff_ne_empty] using hs) := by
  simp_rw [cardinalDim_eq_rank _ hs, finDim_eq_finrank _ hs, ← Module.finrank_eq_rank]
  norm_cast

-- TODO: Replace exists_affineIndependent?
theorem exists_affineIndependent''' (s : Set P) [FiniteDimensional k V] :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t → P) ∧
      t.ncard = (finDim k s).succ := by
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_affineIndependent k V s
  refine ⟨t, ht1, ht2, ht3, ?_⟩
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp_all
  rw [finDim_eq_finrank _ hs, ← ht2, direction_affineSpan, WithBot.succ_natCast]
  have : t.Finite := finite_set_of_fin_dim_affineIndependent k ht3
  have : Fintype { x // x ∈ t } := Set.Finite.fintype this
  have : t.ncard ≠ 0 := by
    grind [Set.ncard_eq_zero, affineSpan_eq_bot, Set.not_nonempty_empty]
  have := ht3.finrank_vectorSpan (n := t.ncard - 1) (by simp [Nat.sub_one_add_one this])
  rw [Subtype.range_coe] at this
  lia

-- TODO: Get rid of [FiniteDimensional k V] and only assume that the affine
-- subspace is finite, e.g. [Module.Finite k (affineSpace k s).direction]


/-!
TODO
- split the ↔ in finDim_eq_iff and delete it (✓)
- get review by Vlad
- make corollaries of finDim_eq_iff for dim 1 (✓), 2
- (later) refactor proofs about affine spaces to go into AffineSpace/Dimension.lean
-/

-- TODO: Should this be stated in the AffineSubspace dimension file instead and this is a corollary?
theorem finDim_n_then_affineSpan_spanned_by_np1_points{n : ℕ} [FiniteDimensional k V]
  (h : finDim k s = n) :
    ∃ t ⊆ s, s ⊆ affineSpan k t ∧ AffineIndependent k ((↑) : t → P) ∧ t.ncard = n + 1 := by
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := exists_affineIndependent''' k s
  rw [h] at ht4
  exact ⟨t, ht1, ht2 ▸ subset_affineSpan .., ht3, ht4⟩

theorem finDim_n_if_affineSpan_has_np1_points{n : ℕ} [FiniteDimensional k V]
  (h : ∃ t ⊆ s, s ⊆ affineSpan k t ∧ AffineIndependent k ((↑) : t → P) ∧ t.ncard = n + 1) :
  finDim k s = n := by
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := h
  have : Fintype t := Set.Finite.fintype <| by grind [Set.finite_of_ncard_ne_zero]
  have := le_antisymm (affineSpan_le_of_subset_coe ht2) (affineSpan_mono k ht1)
  rw [finDim_eq_finrank, this, direction_affineSpan,
    ← ht3.finrank_vectorSpan (n := n) (by simpa), Subtype.range_coe]
  by_contra! hh
  simp_all

-- Corollary of the above
theorem finDim_1_then_affineSpan_spanned_by_2_points [FiniteDimensional k V]
  (h : finDim k s = 1) :
    ∃ x y : s, x ≠ y ∧ s ⊆ affineSpan k {x.1, y.1} := by
  have := finDim_n_then_affineSpan_spanned_by_np1_points _ _ h
  obtain ⟨t, ⟨inSpan, tAffInd, _, card2⟩⟩ := this
  norm_num at card2
  obtain ⟨x, y, xneqy, t_is_xy⟩ := Set.ncard_eq_two.mp card2
  clear card2
  have hx : x ∈ t := by simp [t_is_xy]
  have hy : y ∈ t := by simp [t_is_xy]
  have := Set.mem_of_mem_of_subset hx inSpan
  have := Set.mem_of_mem_of_subset hy inSpan
  have : s ⊆ ↑line[k, ↑x, ↑y] := by
    simp_all
  refine ⟨⟨x,inSpan hx⟩,⟨y,inSpan hy⟩,?_⟩
  constructor
  · simp_all
  · assumption

end DivisionRing

end Convexity
