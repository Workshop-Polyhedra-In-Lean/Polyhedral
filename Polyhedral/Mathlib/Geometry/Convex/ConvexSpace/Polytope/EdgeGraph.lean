/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Dimension

/-!
## The edge graph of a polytope

TODO

-/

namespace Convexity

open ConvexSet

variable {R M X Y V A : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

-- Should this be a Coe instance? Look at Polyhedron.toConvexSet impl, add @[coe]
def Polytope.toConvexSet (p : Polytope R X) : ConvexSet R X := ⟨p.carrier, p.isPolytope.isConvexSet⟩

lemma isConvexSet {P : Set X} (hP : IsPolytope R P) : IsConvexSet R P := by
  obtain ⟨_, rfl⟩ := hP
  exact IsConvexSet.convexHull

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
variable [AddCommGroup M] [Module R M] [AddTorsor R X]

def Polytope.vertices (p : Polytope R X) : Set (Face p.toConvexSet) :=
  { v : Face p.toConvexSet | IsAtom v}

def Polytope.edges (p : Polytope R X) : Set (Face p.toConvexSet) :=
  { f : Face p.toConvexSet | ∃ v w : p.vertices , f = v.1 ⊔ w.1 }

def Polytope.edgeGraph (p : Polytope R X) : SimpleGraph p.vertices where
  Adj x y := x.1 ≠ y.1 ∧ (x.1 ⊔ y.1) ∈ p.edges
  symm.symm := by grind
  loopless.irrefl := by
    simp +contextual [Polytope.edges]

lemma graphEdge_exists_polytopeEdge (p : Polytope R X) (e : p.edges) : ∃ x y : p.vertices,
  p.edgeGraph.Adj x y ∧ (x.1 ⊔ y.1) ∈ p.edges := by
  sorry

lemma polytopeEdge_exits_graphEdge (p : Polytope R X) (x : p.vertices) (y : p.vertices)
  (hxy : p.edgeGraph.Adj x y) :  ∃ e : p.edges, e = x.1 ⊔ y.1  := by
  sorry

end Ring

end Convexity
