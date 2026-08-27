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

theorem cardinalDim_eq_rank_of_nonempty (h : s.carrier.Nonempty) :
    cardinalDim s = Module.rank k s.direction := by
  contrapose! h
  simp_all [cardinalDim]

theorem nonempty_of_cardinalDim_ne_bot (h : cardinalDim s ≠ ⊥) :
    s.carrier.Nonempty := by
  simp_all [cardinalDim, nonempty_iff_ne_bot]

-- nice API
@[simp]
theorem cardinalDim_eq_bot_iff : cardinalDim s = ⊥ ↔ s.carrier = ∅ := by
  simp [cardinalDim]

@[simp]
theorem efinDim_eq_bot_iff : efinDim s = ⊥ ↔ s.carrier = ∅ := by
  simp [efinDim]

end Ring

section DivisionRing

-- TODO: Investigate weaker hypotheses.
variable [DivisionRing k] [Module k V]
variable (s : AffineSubspace k P)

@[simp]
theorem cardinalDim_eq_zero_iff :
    cardinalDim s = 0 ↔ ∃ x : P, s = {x} := by
  dsimp [cardinalDim]
  constructor
  · intro h
    split_ifs at h with h'
    · simp_all
    · simp only [WithBot.coe_eq_zero, Submodule.rank_eq_zero] at h
      have sub_singleton: s.carrier.Subsingleton := by
        intro x x_mem y y_mem
        simpa [h] using vsub_mem_direction x_mem y_mem
      have := Set.nonempty_iff_ne_empty.mpr h'
      obtain ⟨x,hx⟩ := Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨this, sub_singleton⟩
      exact ⟨x, (AffineSubspace.ext_iff _ _).mpr hx⟩
  · rintro ⟨x, rfl⟩
    simp
    simp [AffineSubspace.direction]

@[simp]
theorem efinDim_eq_zero_iff :
    efinDim s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

-- TODO: Necessary? Many Module.finrank + vectorSpan lemmas are stated over Set.range, do we want
-- helpers in a different form?
theorem finrank_vectorSpan_pair {x y : P} (h : x ≠ y) :
    Module.finrank k (vectorSpan k ({x, y} : Set P)) = 1 := by
  have := (affineIndependent_of_ne k h).finrank_vectorSpan (n := 1) (by simp)
  rwa [Matrix.range_cons_cons_empty] at this

variable [LinearOrder k] [IsStrictOrderedRing k]
variable (s : AffineSubspace k P)

theorem cardinalDim_eq_one_iff :
    cardinalDim s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h' := nonempty_of_cardinalDim_ne_bot s (by simp [h])
    rw [cardinalDim_eq_rank_of_nonempty _ h'] at h
    obtain ⟨⟨x, hx⟩, h₁, h₂⟩ := rank_eq_one_iff.mp (WithBot.coe_eq_one.mp h)
    obtain ⟨y, hy⟩ := h'
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
    rw [cardinalDim_eq_rank_of_nonempty _ (by simp [h₂, affineSpan_nonempty])]
    rw [WithBot.coe_eq_one, Module.rank_eq_one_iff_finrank_eq_one, h₂, direction_affineSpan]
    exact finrank_vectorSpan_pair h₁

end DivisionRing

end AffineSubspace
