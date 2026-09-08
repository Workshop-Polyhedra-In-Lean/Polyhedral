/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Polyhedral.Mathlib.Combinatorics.SimpleGraph.Connectivity.Ranking
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.NormalCone
import Polyhedral.Mathlib.Order.KrullDimension

/-! # The edge graph of a polytope is connected

`edgeGraph K` is the graph on the rank-`1` faces of the face lattice of a (bundled) polytope `K`
— its atoms, `PolytopeVertex.isAtom` — with an edge between two distinct such `a`, `b` exactly
when their join `a ⊔ b` has rank `2`, i.e. covers both of them: the lattice-theoretic definition
of an edge, matching the classical 1-skeleton of a polytope.
`IsPolytope.height_sup_singleton_eq_two` is the geometric fact backing this, proved separately:
whenever the segment between two vertex points is itself a face, the join of their atoms has rank
exactly `2`.

`edgeGraph_connected` shows this graph is always connected, via
`SimpleGraph.connected_of_greedy_ascent`: fix a vertex `x` and a linear form `φ` maximized over
`K` *only* at `x.point` (`IsPolytope.exists_maximized_exactly_at_vertex`); then every other vertex
`a` has an *adjacent* vertex `b` with `φ` strictly larger at `b.point`
(`IsPolytope.exists_vertex_edge_of_not_mem_normalCone_singleton`, since `φ` is not maximized at
`a.point ≠ x.point`). -/

noncomputable section

namespace Convexity

namespace ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P]

local instance instConvexSpaceOfAddTorsorEdgeGraph : ConvexSpace R P := AddTorsor.toConvexSpace

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

variable {K : Polytope R P}

/-! ## The geometry of an edge: a join of rank two is the segment between its two vertices

The results below need no reference to `PolytopeVertex`/`edgeGraph` themselves: they isolate
exactly the geometric content behind an "edge" of a polytope, in terms of the two named points. -/

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **A face `convexHull R {x, y}` (`x`, `y` vertices of `K`) has exactly `x` and `y` as its own
vertices.** `⊆` is `IsPolytope.vertices_subset` (vertices are always among the generators); `⊇` is
immediate since `{x}` and `{y}`, already faces of `K`, restrict to faces of the sub-face
`convexHull R {x, y}` (`IsFaceOf.isFaceOf_iff`). -/
theorem IsPolytope.vertices_eq_pair {x y : P}
    (hx : ({x} : ConvexSet R P).IsFaceOf (K : ConvexSet R P))
    (hy : ({y} : ConvexSet R P).IsFaceOf (K : ConvexSet R P))
    (hf : (convexHull R ({x, y} : Set P) : ConvexSet R P).IsFaceOf (K : ConvexSet R P)) :
    Vertices R (convexHull R ({x, y} : Set P) : ConvexSet R P) = {x, y} := by
  classical
  apply le_antisymm
  · have hset : ({x, y} : Set P) = (({x, y} : Finset P) : Set P) := by simp
    have heq : (convexHull R ({x, y} : Set P) : ConvexSet R P) =
        (⟨convexHull R (({x, y} : Finset P) : Set P), IsConvexSet.convexHull⟩ : ConvexSet R P) := by
      apply SetLike.coe_injective
      exact congrArg (Convexity.convexHull R) hset
    rw [heq, hset]
    exact IsPolytope.vertices_subset
  · rintro z (rfl | rfl)
    · exact (IsFaceOf.isFaceOf_iff _ hf).mpr
        ⟨Set.singleton_subset_iff.mpr (subset_convexHull_self (Set.mem_insert _ _)), hx⟩
    · exact (IsFaceOf.isFaceOf_iff _ hf).mpr
        ⟨Set.singleton_subset_iff.mpr (subset_convexHull_self (Set.mem_insert_of_mem _ rfl)), hy⟩

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **The join of the singleton faces of two distinct points has rank `2`, whenever the segment
between them is itself a face.** The join is exactly the segment-face `f := convexHull R {x, y}`
(it is an upper bound of both singletons since `x, y ∈ f`; it is the *least* upper bound since any
upper bound is a convex set containing `x` and `y`, hence containing the whole segment). `f` has
rank `2`: at least `2` since it strictly contains the rank-`1` atom `{x}`
(`Order.height_add_one_le`); at most `2` since every face strictly below `f` has vertex set
`⊆ {x, y}` (`Order.height_le_coe_iff` reduces this to a case split on
`IsPolytope.vertices_eq_pair`, giving `∅`, `{x}`, or `{y}` — the fourth case, `{x, y}`, would force
equality with `f`, contradicting strictness). -/
theorem IsPolytope.height_sup_singleton_eq_two {x y : P}
    (hx : ({x} : ConvexSet R P).IsFaceOf (K : ConvexSet R P))
    (hy : ({y} : ConvexSet R P).IsFaceOf (K : ConvexSet R P)) (hxy : x ≠ y)
    (hface : (convexHull R ({x, y} : Set P) : ConvexSet R P).IsFaceOf (K : ConvexSet R P)) :
    Order.height ((⟨({x} : ConvexSet R P), hx⟩ : Face (K : ConvexSet R P)) ⊔
      (⟨({y} : ConvexSet R P), hy⟩ : Face (K : ConvexSet R P))) = 2 := by
  classical
  set f : Face (K : ConvexSet R P) :=
    ⟨(convexHull R ({x, y} : Set P) : ConvexSet R P), hface⟩ with hf_def
  set ax : Face (K : ConvexSet R P) := ⟨({x} : ConvexSet R P), hx⟩ with hax_def
  set ay : Face (K : ConvexSet R P) := ⟨({y} : ConvexSet R P), hy⟩ with hay_def
  have hxf : x ∈ (f : ConvexSet R P) := subset_convexHull_self (Set.mem_insert _ _)
  have hyf : y ∈ (f : ConvexSet R P) := subset_convexHull_self (Set.mem_insert_of_mem _ rfl)
  have haxf : ax ≤ f := by
    intro z hz
    have hz' : z = x := hz
    rw [hz']; exact hxf
  have hayf : ay ≤ f := by
    intro z hz
    have hz' : z = y := hz
    rw [hz']; exact hyf
  have hsup : ax ⊔ ay = f := by
    apply le_antisymm (sup_le haxf hayf)
    intro z hz
    have hz' : z ∈ (convexHull R ({x, y} : Set P) : Set P) := hz
    have hxmem : x ∈ ((ax ⊔ ay : Face (K : ConvexSet R P)) : Set P) :=
      SetLike.coe_subset_coe.mpr le_sup_left (rfl : x ∈ ax)
    have hymem : y ∈ ((ax ⊔ ay : Face (K : ConvexSet R P)) : Set P) :=
      SetLike.coe_subset_coe.mpr le_sup_right (rfl : y ∈ ay)
    exact (ax ⊔ ay).toConvexSet.isConvexSet.convexHull_subset_iff.mpr
      (by rintro w (rfl | rfl); exacts [hxmem, hymem]) hz'
  rw [hsup]
  have hVf : Vertices R (f : ConvexSet R P) = ({x, y} : Set P) :=
    IsPolytope.vertices_eq_pair hx hy hface
  have haxatom : IsAtom ax := IsPolytope.isAtom_singletonFace hx
  have hayatom : IsAtom ay := IsPolytope.isAtom_singletonFace hy
  have hheight_ax : Order.height ax = 1 := Order.isAtom_iff_height_eq_one.mp haxatom
  have hheight_ay : Order.height ay = 1 := Order.isAtom_iff_height_eq_one.mp hayatom
  have haxlt : ax < f := by
    refine lt_of_le_of_ne haxf (fun heq => hxy ?_)
    have : y ∈ (ax : ConvexSet R P) := heq ▸ hyf
    exact this.symm
  have hge : (2 : ℕ∞) ≤ Order.height f := by
    have hstep := Order.height_add_one_le haxlt
    rw [hheight_ax] at hstep
    have h11 : (1 : ℕ∞) + 1 = 2 := by decide
    rwa [h11] at hstep
  have hle : Order.height f ≤ 2 := by
    rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) by simp, Order.height_le_coe_iff]
    intro G hGlt
    have hGfaceF : (G : ConvexSet R P).IsFaceOf (f : ConvexSet R P) :=
      (IsFaceOf.isFaceOf_iff _ f.isFaceOf).mpr ⟨hGlt.le, G.isFaceOf⟩
    have hVGsub : Vertices R (G : ConvexSet R P) ⊆ ({x, y} : Set P) :=
      hVf ▸ Vertices.mono_of_isFaceOf hGfaceF
    have hGeq : (G : Set P) = Convexity.convexHull R (Vertices R (G : ConvexSet R P)) :=
      IsPolytope.face_eq_convexHull_vertices K.isPolytope G.isFaceOf
    rcases Set.subset_pair_iff_eq.mp hVGsub with hV | hV | hV | hV
    · have hGbot : G = ⊥ := by
        apply SetLike.coe_injective
        rw [hGeq, hV, convexHull_empty]; rfl
      rw [hGbot, Order.height_bot]
      simp
    · have hGeqax : G = ax := by
        apply SetLike.coe_injective
        rw [hGeq, hV, convexHull_singleton]; rfl
      rw [hGeqax, hheight_ax]
      simp
    · have hGeqay : G = ay := by
        apply SetLike.coe_injective
        rw [hGeq, hV, convexHull_singleton]; rfl
      rw [hGeqay, hheight_ay]
      simp
    · exact absurd (SetLike.coe_injective (show (G : Set P) = (f : Set P) by
        rw [hGeq, hV]; rfl)) hGlt.ne
  exact le_antisymm hle hge

/-! ## The atomistic edge graph -/

/-- The vertices of `K`, bundled as the rank-`1` faces of its face lattice. -/
abbrev PolytopeVertex (K : Polytope R P) := {a : Face (K : ConvexSet R P) // Order.height a = 1}

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **The rank-`1` faces are exactly the atoms of the face lattice** — the general order fact
`Order.isAtom_iff_height_eq_one`, specialized to `PolytopeVertex`. -/
theorem PolytopeVertex.isAtom (a : PolytopeVertex K) : IsAtom a.1 :=
  Order.isAtom_iff_height_eq_one.mpr a.2

instance : Finite (PolytopeVertex K) := Subtype.finite

/-- **The edge graph of a polytope**: two distinct rank-`1` faces are adjacent iff their join has
rank `2`. -/
def edgeGraph (K : Polytope R P) : SimpleGraph (PolytopeVertex K) where
  Adj a b := a ≠ b ∧ Order.height (a.1 ⊔ b.1) = 2
  symm := ⟨by rintro a b ⟨hne, heq⟩; rw [sup_comm] at heq; exact ⟨hne.symm, heq⟩⟩
  loopless := ⟨fun a ⟨hne, _⟩ => hne rfl⟩

/-- The point named by a vertex-atom of `K`. -/
noncomputable def PolytopeVertex.point (a : PolytopeVertex K) : P :=
  ((IsPolytope.isAtom_iff_exists_eq_singleton K.isPolytope).mp a.isAtom).choose

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
theorem PolytopeVertex.isFaceOf_point (a : PolytopeVertex K) :
    ({a.point} : ConvexSet R P).IsFaceOf (K : ConvexSet R P) :=
  ((IsPolytope.isAtom_iff_exists_eq_singleton K.isPolytope).mp a.isAtom).choose_spec.1

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
theorem PolytopeVertex.coe_eq_point (a : PolytopeVertex K) :
    (a.1 : Set P) = {a.point} :=
  ((IsPolytope.isAtom_iff_exists_eq_singleton K.isPolytope).mp a.isAtom).choose_spec.2

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
theorem PolytopeVertex.eq_mk_point (a : PolytopeVertex K) :
    a.1 = (⟨({a.point} : ConvexSet R P), a.isFaceOf_point⟩ : Face (K : ConvexSet R P)) := by
  apply SetLike.coe_injective
  exact a.coe_eq_point

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
theorem PolytopeVertex.point_injective :
    Function.Injective (fun a : PolytopeVertex K => a.point) := by
  intro a b hab
  apply Subtype.ext
  have hab' : a.point = b.point := hab
  apply SetLike.coe_injective
  rw [a.coe_eq_point, b.coe_eq_point, hab']

/-- **At a vertex where `φ` is not maximized, there is an adjacent vertex with `φ` strictly
larger.** Combines `IsPolytope.exists_vertex_edge_of_not_mem_normalCone_singleton` (a point `z`
with `φ (z -ᵥ a.point) > 0` and `{a.point, z}` a face) with
`IsPolytope.height_sup_singleton_eq_two` (the atom named by `z` is then adjacent to `a` in
`edgeGraph K`). -/
theorem IsPolytope.exists_adjacent_gt {a : PolytopeVertex K} {φ : Module.Dual R M}
    (hφ : φ ∉ normalCone (K : ConvexSet R P) ({a.point} : ConvexSet R P)) :
    ∃ b : PolytopeVertex K, (edgeGraph K).Adj a b ∧
      φ (a.point -ᵥ a.point) < φ (b.point -ᵥ a.point) := by
  obtain ⟨z, hz1, hz2, hz3⟩ :=
    IsPolytope.exists_vertex_edge_of_not_mem_normalCone_singleton K.isPolytope
      a.isFaceOf_point hφ
  have haz : a.point ≠ z := fun h => by
    rw [h, vsub_self, map_zero] at hz2; exact lt_irrefl 0 hz2
  have hzatom : IsAtom (⟨({z} : ConvexSet R P), hz1⟩ : Face (K : ConvexSet R P)) :=
    (IsPolytope.isAtom_iff_exists_eq_singleton K.isPolytope).mpr ⟨z, hz1, rfl⟩
  have hheight2 : Order.height ((⟨({a.point} : ConvexSet R P), a.isFaceOf_point⟩ :
      Face (K : ConvexSet R P)) ⊔ (⟨({z} : ConvexSet R P), hz1⟩ : Face (K : ConvexSet R P))) = 2 :=
    IsPolytope.height_sup_singleton_eq_two a.isFaceOf_point hz1 haz hz3
  set b : PolytopeVertex K :=
    ⟨⟨({z} : ConvexSet R P), hz1⟩, Order.isAtom_iff_height_eq_one.mp hzatom⟩ with hb_def
  have hbz : b.point = z := by
    have h1 : (b.1 : Set P) = {z} := rfl
    have h2 : (b.1 : Set P) = {b.point} := b.coe_eq_point
    exact (Set.singleton_eq_singleton_iff.mp (h1.symm.trans h2)).symm
  have hab_ne : a ≠ b := fun h => haz (by rw [← hbz, ← h])
  have ha_eq : a.1 = (⟨({a.point} : ConvexSet R P), a.isFaceOf_point⟩ : Face (K : ConvexSet R P)) :=
    a.eq_mk_point
  have hb_eq : b.1 = (⟨({z} : ConvexSet R P), hz1⟩ : Face (K : ConvexSet R P)) := rfl
  refine ⟨b, ⟨hab_ne, by rw [ha_eq, hb_eq]; exact hheight2⟩, ?_⟩
  rw [vsub_self, map_zero, hbz]
  exact hz2

/-- **The edge graph of a polytope is connected.** Fix a vertex `x` and a linear form `φ`
maximized over `K` *only* at `x.point` (`IsPolytope.exists_maximized_exactly_at_vertex`). Every
other vertex `a` has an adjacent vertex `b` on which the ranking function
`w ↦ φ (w.point -ᵥ x.point)` is strictly larger (`IsPolytope.exists_adjacent_gt`, applied after
showing `φ` is not maximized at `a.point ≠ x.point`).
`SimpleGraph.connected_of_greedy_ascent` turns this into connectivity. -/
theorem edgeGraph_connected (K : Polytope R P) [Nonempty (PolytopeVertex K)] :
    (edgeGraph K).Connected := by
  obtain ⟨x⟩ := ‹Nonempty (PolytopeVertex K)›
  obtain ⟨φ, hφx⟩ := IsPolytope.exists_maximized_exactly_at_vertex K.isPolytope x.isFaceOf_point
  apply SimpleGraph.connected_of_greedy_ascent
    (fun a : PolytopeVertex K => φ (a.point -ᵥ x.point)) x
  intro a hax
  have hane : a.point ≠ x.point := fun h => hax (PolytopeVertex.point_injective h)
  have hnotmax : φ ∉ normalCone (K : ConvexSet R P) ({a.point} : ConvexSet R P) := by
    rw [ConvexSet.not_mem_normalCone_iff a.isFaceOf_point.le (Set.singleton_nonempty _)]
    refine ⟨a.point, rfl, x.point, x.isFaceOf_point.le rfl, ?_⟩
    have hlt : φ (a.point -ᵥ x.point) < 0 := hφx a.point (a.isFaceOf_point.le rfl) hane
    have heq : x.point -ᵥ a.point = -(a.point -ᵥ x.point) := (neg_vsub_eq_vsub_rev _ _).symm
    rw [heq, map_neg]
    linarith
  obtain ⟨b, hadj, hgt⟩ := IsPolytope.exists_adjacent_gt hnotmax
  refine ⟨b, hadj, ?_⟩
  rw [(vsub_add_vsub_cancel b.point a.point _).symm , map_add]
  rw [vsub_self, map_zero] at hgt
  linarith

end Field

end ConvexSet

end Convexity
