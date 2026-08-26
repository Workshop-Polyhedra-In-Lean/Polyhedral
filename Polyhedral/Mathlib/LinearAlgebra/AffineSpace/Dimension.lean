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

variable (k : Type*) {V : Type*} (P : Type*) [AddCommGroup V] [AddTorsor V P]

section Ring

variable [Ring k] [Module k V]
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
    cardinalDim _ _ s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · dsimp [cardinalDim] at h
    split_ifs at h with h'
    · simp_all
    -- TODO: Clean-up
    -- a rank-1 direction has a nonzero spanning vector `v`
    obtain ⟨⟨v, hv⟩, hv₁, -⟩ := rank_eq_one_iff.mp (WithBot.coe_eq_one.mp h)
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr h'
    set q := v +ᵥ p with hq_def
    have hq : q ∈ s := vadd_mem_of_mem_direction hv hp
    have hvvsub : q -ᵥ p = v := by rw [hq_def, vadd_vsub]
    have hpq : p ≠ q := fun he ↦ hv₁ <| Subtype.ext <| by
      rw [he, vsub_self] at hvvsub
      exact hvvsub.symm
    -- `{p, q}` already spans a line inside `s`, and by rank it must be all of `s`.
    refine ⟨p, q, hpq, ?_⟩
    have hle : affineSpan k ({p, q} : Set P) ≤ s :=
      affineSpan_le.mpr (Set.insert_subset hp (Set.singleton_subset_iff.mpr hq))
    have hdir : s.direction = (affineSpan k ({p, q} : Set P)).direction := by
      have hfr : FiniteDimensional k s.direction :=
        FiniteDimensional.of_rank_eq_one (WithBot.coe_eq_one.mp h)
      have h1 : Module.finrank k s.direction = 1 :=
        Module.rank_eq_one_iff_finrank_eq_one.mp (WithBot.coe_eq_one.mp h)
      have h2 : Module.finrank k (affineSpan k ({p, q} : Set P)).direction = 1 := by
        rw [direction_affineSpan]; exact finrank_vectorSpan_pair k P hpq
      exact (Submodule.eq_of_le_of_finrank_eq (direction_le hle) (h2.trans h1.symm)).symm
    exact (eq_iff_direction_eq_of_mem hp (subset_affineSpan k _ (Set.mem_insert p _))).mpr hdir
      /- TODO: Decide if we want anything from here
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
      -/
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
