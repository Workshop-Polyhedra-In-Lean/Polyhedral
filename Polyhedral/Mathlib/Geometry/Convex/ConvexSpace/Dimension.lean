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

variable {R M X : Type*}

variable (k : Type*) {V P : Type*} [Ring k]
variable [AddCommGroup V] [Module k V] [AddTorsor V P]
variable (s : Set P)

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

theorem cardinalDim_eq_one_iff :
    cardinalDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  sorry

theorem efinDim_eq_one_iff :
    efinDim k s = 1 ↔ ∃ x y : P, x ≠ y ∧ s = affineSpan k {x, y} := by
  sorry

end Convexity
