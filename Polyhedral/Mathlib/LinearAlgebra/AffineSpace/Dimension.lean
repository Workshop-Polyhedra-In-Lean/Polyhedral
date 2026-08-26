/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- TODO #min_imports at the end
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

/-!

TODO

-/


namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V]
variable (s : AffineSubspace k P)
-- Ring k
-- VectorSpace / Module V
-- Affine subspace s

noncomputable def cardinalDim : WithBot Cardinal :=
  if s.carrier = ∅ then ⊥
  else Module.rank k s.direction

--noncomputable def finDim : WithBot Nat :=
--  WithBot.map Cardinal.toNat (cardinalDim s)

noncomputable def efinDim : WithBot ENat :=
  WithBot.map Cardinal.toENat (cardinalDim s)

-- nice API
@[simp]
theorem cardinalDim_eq_bot_iff : cardinalDim s = ⊥ ↔ s.carrier = ∅ := by
  simp [cardinalDim]

@[simp]
theorem efinDim_eq_bot_iff : efinDim s = ⊥ ↔ s.carrier = ∅ := by
  simp [efinDim]

@[simp]
theorem cardinalDim_eq_zero_iff :
    cardinalDim s = 0 ↔ ∃ x : P, s = {x} := by
  dsimp [cardinalDim]
  constructor
  · intro h
    sorry
  · rintro ⟨x, hx⟩
    sorry

@[simp]
theorem efinDim_eq_zero_iff :
    efinDim s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

end Ring

section DivisionRing

-- TODO: Investigate weaker hypotheses.
variable [DivisionRing k] [Module k V]

/-- Two distinct points span a line: their `vectorSpan` has rank exactly `1`. -/
theorem finrank_vectorSpan_pair {x y : P} (h : x ≠ y) :
    Module.finrank k (vectorSpan k ({x, y} : Set P)) = 1 := by
  have hi : AffineIndependent k ![x, y] := affineIndependent_of_ne k h
  have := hi.finrank_vectorSpan (n := 1) (by simp)
  rwa [Matrix.range_cons_cons_empty] at this

variable [LinearOrder k] [IsStrictOrderedRing k]
variable (s : AffineSubspace k P)

theorem cardinalDim_eq_one_iff :
    cardinalDim s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- TODO general lemma for this
    dsimp [cardinalDim] at h
    split_ifs at h with h'
    · simp_all
    obtain ⟨⟨x, hx⟩, h₁, h₂⟩ := rank_eq_one_iff.mp (WithBot.coe_eq_one.mp h)
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr h'
    have hne : y ≠ x +ᵥ y := fun heq ↦ by
      simp [eq_vadd_iff_vsub_eq] at heq
      simp [heq] at h₁
    refine ⟨y, x +ᵥ y, hne, ?_⟩
    have hxy := vadd_mem_of_mem_direction hx hy
    refine eq_iff_direction_eq_of_mem hxy (right_mem_affineSpan_pair ..) |>.mpr ?_
    have hle : affineSpan k {y, x +ᵥ y} ≤ s := affineSpan_le.mpr (Set.pair_subset hy hxy)
    let := FiniteDimensional.of_rank_eq_one (WithBot.coe_eq_one.mp h)
    refine Submodule.eq_of_le_of_finrank_eq (direction_le hle) ?_ |>.symm
    rw [direction_affineSpan, finrank_vectorSpan_pair  hne,
      Module.rank_eq_one_iff_finrank_eq_one.mp (by simpa using h)]
  · rintro ⟨x, y, h₁, h₂⟩
    -- TODO: lemma that s ≠ ∅ → cardinalDim = Module.rank
    dsimp [cardinalDim]
    split_ifs with h'
    · grind [coe_eq_bot_iff, affineSpan_eq_bot]
    simp at h'
    rw [WithBot.coe_eq_one]
    rw [Module.rank_eq_one_iff_finrank_eq_one]
    rw [h₂, direction_affineSpan]
    exact finrank_vectorSpan_pair k P h₁

end DivisionRing

end AffineSubspace
