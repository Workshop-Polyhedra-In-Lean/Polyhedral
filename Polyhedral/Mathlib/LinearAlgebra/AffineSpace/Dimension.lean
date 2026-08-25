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

end AffineSubspace
