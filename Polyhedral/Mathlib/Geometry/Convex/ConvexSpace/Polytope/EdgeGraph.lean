/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Dimension

/-!
## The edge graph of a polytope

This file defines the edge graph (or 1-skeleton) of a polytope purely in terms of its face
lattice: the vertices are the atoms of the lattice, the edges are the faces covering two distinct
atoms, and two vertices are adjacent when their join is such an edge. Working through the lattice
rather than through the underlying point set means the definition is automatically invariant under
combinatorial equivalence of polytopes.

## Main definitions

* `Convexity.Polytope.toConvexSet`: a polytope viewed as a bundled convex set, so that its face
  lattice `Face p.toConvexSet` is available.
* `Convexity.Polytope.vertices`: the vertices of `p`, namely the atoms of its face lattice.
* `Convexity.Polytope.edges`: the edges of `p`, namely the faces covering two distinct vertices.
* `Convexity.Polytope.edgeGraph`: the resulting simple graph on `p.vertices`.

## TODO

* Show Balinski: the edge graph is is **`d`**-connected for a `d`-dimensional polytope.
* Relate `Polytope.vertices` to `Convexity.Vertices` from `Polytope/KreinMilman.lean`.
-/

public section

namespace Convexity

open ConvexSet

variable {R M X Y V A : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

-- Should this be a Coe instance? Look at Polyhedron.toConvexSet impl, add @[coe]
def Polytope.toConvexSet (p : Polytope R X) : ConvexSet R X := ⟨p.carrier, p.isPolytope.isConvexSet⟩


end Semiring

section AffineConvex

variable [DivisionRing R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

variable [AddCommGroup M] [Module R M] [AddTorsor M X] [IsAffineConvexSpace R M X]

-- def IsPolytope (s : Set X) : Prop := ∃ t : Finset X, s = convexHull R t

-- **The affine span of a polytope is finite dimensional**
instance (p : Polytope R X) :
    FiniteDimensional R (affineSpan R p.carrier).direction := by
  obtain ⟨t, ht⟩ := p.isPolytope
  rw [ht, affineSpan_convexHull_eq]
  exact finiteDimensional_direction_affineSpan_of_finite _ t.finite_toSet

-- **Definition of the edge graph (or 1-skeleton) of a polytope**

-- the vertices of the edge graph are the atoms (i.e. singletons of a vertices) of the face lattice
def Polytope.vertices (p : Polytope R X) : Set (Face p.toConvexSet) :=
  { v : Face p.toConvexSet | IsAtom v }

-- the edges of the edge graph are the two element sets produced by
def Polytope.edges (p : Polytope R X) : Set (Face p.toConvexSet) :=
  { f : Face p.toConvexSet | ∃ v w : p.vertices, v.1 ≠ w.1 ∧ v.1 ⋖ f ∧ w.1 ⋖ f }

-- this is indeed a simple undirected graph
def Polytope.edgeGraph (p : Polytope R X) : SimpleGraph p.vertices where
  -- …it has a well defined adjacency relation: it is symmetric and irreflexive
  Adj x y := x.1 ≠ y.1 ∧ (x.1 ⊔ y.1) ∈ p.edges
  symm.symm := by grind
  loopless.irrefl := by
    simp +contextual [Polytope.edges]

-- Useful lemmas for edge graphs:

theorem foo (p : Polytope R X) (v w : p.vertices) (f : Face p.toConvexSet)
    (hne : v.1 ≠ w.1) (h1 : v.1 ⋖ f) (h2 : w.1 ⋖ f) :
    f = v.1 ⊔ w.1 := by
  apply le_antisymm
  · -- `f ≤ v ⊔ w`: `v ⊔ w` sits between `v` and `f`, so `v ⋖ f` forces it to be one of them,
    -- and it cannot be `v`, since that would make `w ≤ v` and hence `v = w`.
    rcases h1.eq_or_eq le_sup_left (sup_le h1.le h2.le) with h | h
    · exact absurd (h2.eq_or_eq (h ▸ le_sup_right) h1.le) (by simp [hne, h1.ne])
    · exact h.ge
  · -- `v ⊔ w ≤ f`: both `v` and `w` are below `f`.
    exact sup_le h1.le h2.le


-- for any edge, there exist two adjacent vertices who have it as their supremum
example (p : Polytope R X) (e v w : Face p.toConvexSet)
    (hv : v ⋖ e) (hw : w ⋖ e) (hne : v ≠ w) : v ⊔ w = e := by
  rcases hv.eq_or_eq (le_sup_left) (sup_le hv.le hw.le) with h | h
  · exact absurd (hw.eq_or_eq (h ▸ le_sup_right) hv.le) (by simp [hne, hv.ne])
  · exact h

-- for any two adjacent vertices, there is an edge which is their supremum
lemma polytopeEdge_exits_graphEdge (p : Polytope R X)
    (x : p.vertices) (y : p.vertices) (hxy : p.edgeGraph.Adj x y) :
    ∃ e : p.edges, e = x.1 ⊔ y.1 := ⟨⟨_, hxy.2⟩, rfl⟩

end AffineConvex

end Convexity
