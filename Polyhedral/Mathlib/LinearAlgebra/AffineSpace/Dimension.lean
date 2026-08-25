/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- TODO #min_imports at the end
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

/-!

TODO

-/


namespace AffineSubspace

section dimension

variable (k : Type*) {V : Type*} (P : Type*) [Ring k]
variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (s : AffineSubspace k P)

noncomputable def cardinalDim : WithBot Cardinal :=
  if s.carrier = ∅ then ⊥
  else Module.rank k s.direction

--noncomputable def finDim : WithBot Nat :=
--  WithBot.map Cardinal.toNat (cardinalDim _ _ s)

noncomputable def efinDim : WithBot ENat :=
  WithBot.map Cardinal.toENat (cardinalDim _ _ s)

-- nice API
@[simp]
theorem cardinalDim_eq_bot_iff : cardinalDim _ _ s = ⊥ ↔ s.carrier = ∅ := by
  simp [cardinalDim]

@[simp]
theorem efinDim_eq_bot_iff : efinDim _ _ s = ⊥ ↔ s.carrier = ∅ := by
  simp [efinDim]

@[simp]
theorem cardinalDim_eq_zero_iff :
    cardinalDim _ _ s = 0 ↔ ∃ x : P, s = {x} := by
  dsimp [cardinalDim]
  constructor
  · intro h
    sorry
  · rintro ⟨x, hx⟩
    sorry

@[simp]
theorem efinDim_eq_zero_iff :
    efinDim _ _ s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

end dimension

-- TODO: Investigate weaker hypotheses
variable (k : Type*) {V : Type*} (P : Type*) [DivisionRing k]
variable [AddCommGroup V] [Module k V] [AddTorsor V P]
variable [StrongRankCondition k] [LinearOrder k] [IsStrictOrderedRing k]

variable (s : AffineSubspace k P)

@[simp]
theorem cardinalDim_eq_one_iff :
    cardinalDim _ _ s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · dsimp [cardinalDim] at h
    split_ifs at h with h'
    · simp_all
    obtain ⟨⟨x, hx⟩, h₁, h₂⟩ := rank_eq_one_iff.mp (WithBot.coe_eq_one.mp h)
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr h'
    refine ⟨y, x +ᵥ y, fun heq ↦ ?_, ?_⟩
    · simp [eq_vadd_iff_vsub_eq] at heq
      simp [heq] at h₁
    · ext z
      rw [mem_affineSpan_iff_exists]
      refine ⟨fun h ↦ ?_, ?_⟩
      · refine ⟨y, by simp, z -ᵥ y, ?_, by simp⟩
        simpa [mem_vectorSpan_pair_rev] using h₂ ⟨z -ᵥ y, vsub_mem_direction h hy⟩
      · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mem_vectorSpan_pair_rev,
          vadd_vsub] at hp₁ hp₂
        obtain ⟨r, hr⟩ := hp₂
        rw [← hr]
        rcases hp₁ with rfl | rfl
        · refine (vadd_mem_iff_mem_of_mem_direction ?_).mpr hy
          exact Submodule.smul_mem s.direction r hx
        · refine (vadd_mem_iff_mem_of_mem_direction ?_).mpr ?_
          · exact Submodule.smul_mem s.direction r hx
          exact (vadd_mem_iff_mem_of_mem_direction hx).mpr hy
  · rintro ⟨x, y, h₁, h₂⟩
    dsimp [cardinalDim]
    split_ifs with h'
    · grind [coe_eq_bot_iff, affineSpan_eq_bot]
    simp at h'
    rw [WithBot.coe_eq_one]
    rw [Module.rank_eq_one_iff_finrank_eq_one]
    sorry
    /-
    --apply?
    --
    have : s.direction = Submodule.span k {x -ᵥ y} := by
      ext z
      --rw [AffineSubspace.mem_direction_iff_eq_vsub_left (P := P)]
      rw [AffineSubspace.direction_eq_vectorSpan]
      rw [h₂]
      --rw?
      rw [coe_affineSpan]
      --rw?
      --rw [vectorSpan_def]
      ext z
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · simp [affineSpan, spanPoints] at h₂
        simp [h₂] at h
        have := mem_affineSpan_iff_exists k |>.mp ⟨x, sorry, z, h, by simp⟩
        rw? at h₂
        intro A hA
        simp at hA

        sorry
      · sorry
      simp
      --rw [mem_affineSpan_iff_exists] at h₂
      sorry
    rw [AffineSubspace.direction_eq_vectorSpan]
    --rw [Module.rank_eq_one_iff_finrank_eq_one]
    rw [vectorSpan_def]
    /-
    have : Fintype ((s : Set P) -ᵥ s) := sorry
    rw [finrank_span_set_eq_card]
    · simp
    · simp
    -/
    have WANT : ∃ y, Submodule.span k ((s : Set P) -ᵥ s) = Submodule.span k {y} := sorry
    obtain ⟨y, hy⟩ := WANT
    rw [hy]
    exact?
    simp

--    have := Fintype.ofFinite s
    rw [finrank_span_set_eq_card]
    · simp [hy]
    · simp [hy]
      have := IsStrictOrderedRing.isDomain (R := k)
      have : Module.IsTorsionFree k V := sorry
      exact LinearIndepOn.singleton (by sorry)
      -/

end AffineSubspace
