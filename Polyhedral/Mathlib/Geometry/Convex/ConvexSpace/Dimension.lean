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
    (hx : ↑(affineSpan k s) = {x}) : s = {x} :=
  sorry

theorem cardinalDim_eq_zero_iff : cardinalDim k s = 0 ↔ ∃ x : P, s = {x} := by
  simp only [cardinalDim]
  rw [AffineSubspace.cardinalDim_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    use x
    exact eq_singleton_of_affineSpan_eq _ _ x hx
  · rintro ⟨x, hx⟩
    use x
    simp [hx]
    sorry -- TODO fix

theorem efinDim_eq_zero_iff : efinDim k s = 0 ↔ ∃ x : P, s = {x} := by
  sorry

end Ring

section DivisionRing

variable [DivisionRing k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

-- TODO: If this is `cardinalDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ affineSpan k s = affineSpan k {x, y}`
-- it closes at rw
theorem cardinalDim_eq_one_iff :
    cardinalDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  simp only [cardinalDim]
  rw [AffineSubspace.cardinalDim_eq_one_iff k P]
  constructor
  · rintro ⟨x, y, h₁, h₂⟩
    refine ⟨x, y, h₁, ?_⟩
    simp [← h₂]
    sorry
  · rintro ⟨x, y, h₁, h₂⟩
    refine ⟨x, y, h₁, ?_⟩
    simp [h₂]

theorem efinDim_eq_one_iff :
    efinDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  simp [efinDim, WithBot.map_eq_one_iff, cardinalDim_eq_one_iff]

end DivisionRing

end Convexity
