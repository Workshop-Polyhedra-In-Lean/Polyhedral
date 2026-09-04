/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/
module

public import Mathlib.Order.Atoms
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Vertex

/-! # Krein-Milman for polytopes, proved directly (no homogenization)

This file proves that every polytope is the convex hull of its vertices, and more generally
that every face of a polytope is the convex hull of a subset of the ambient polytope's own
vertices, without ever homogenizing. The core fact making this possible,
`essential_iff_singleton_isFaceOf` (in `Set/Face/Vertex.lean`), needs no separating-hyperplane
theorem: a point of a finite generating set that is not a combination of the rest of the set is
automatically a vertex, by an elementary splitting argument on `ConvexSet.IsFaceOf`'s own
definition.

Along the way, `IsPolytope.face_isPolytope` reproves "a face of a polytope is a polytope"
directly (this shadows, but does not call, the homogenization-based `IsPolytope.face_isPolytope`
in `Polytope/Face.lean`, which lives outside the `Convexity` namespace).

The public API mirrors the rest of `Polytope/`: `IsPolytope k (X : Set A)` is the hypothesis, not
a fixed generating `Finset`. The `Finset`-indexed versions of the key facts (needed for the
induction) stay as `private` auxiliary lemmas. -/

public section

namespace Convexity

variable {k V A : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup V] [Module k V] [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace

variable (k) in
/-- `x` is a vertex of `X`: `{x}` is a face of `X`. See `Set/Face/Vertex.lean` for the
equivalence with the "minimal containing face" characterization of the relative interior of a
chord. -/
def Vertices (X : ConvexSet k A) : Set A := {x | ({x} : ConvexSet k A).IsFaceOf X}

/-- A vertex of a face is a vertex of the ambient set: `IsFaceOf` is transitive, so once `F` is a
face of `X`, any singleton that is a face of `F` is already a face of `X`. -/
theorem Vertices.mono_of_isFaceOf {F X : ConvexSet k A} (hF : F.IsFaceOf X) :
    Vertices k F ⊆ Vertices k X :=
  fun _ hv => hv.trans hF

/-- If `x` is a vertex of `convexHull k T`, then `x ∈ T`: vertices are always among the
generators. Proved via `ConvexSet.IsFaceOf.mem_of_sConvexComb_mem`: `x` has *some*
representation as a combination over `T`, and every point of that combination's support must
land in the face `{x}`, forcing the whole (nonempty) support to be `{x}` itself. -/
private theorem mem_of_mem_vertices_convexHull {T : Finset A} {x : A}
    (hx : x ∈ Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A)) : x ∈ T := by
  classical
  have hxmem : x ∈ convexHull k (T : Set A) := hx.le (rfl : x ∈ ({x} : ConvexSet k A))
  obtain ⟨w, hwsupp, hwx⟩ := mem_convexHull_iff_exists_sConvexComb.mp hxmem
  have hw' : ↑w.weights.support ⊆
      ((⟨convexHull k (T : Set A), IsConvexSet.convexHull⟩ : ConvexSet k A) : Set A) :=
    hwsupp.trans subset_convexHull_self
  have hmem : w.sConvexComb ∈ ({x} : ConvexSet k A) := by rw [hwx]; rfl
  have hall := hx.mem_of_sConvexComb_mem hw' hmem
  obtain ⟨s₀, hs₀⟩ := w.support_weights_nonempty
  have hs₀x : s₀ = x := hall s₀ hs₀
  exact hs₀x ▸ Finset.mem_coe.mp (hwsupp (Finset.mem_coe.mpr hs₀))

/-- The vertices of `convexHull k T` are a subset of the generators `T`. -/
theorem IsPolytope.vertices_subset {T : Finset A} :
    Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) ⊆ (T : Set A) :=
  fun _ hx => mem_of_mem_vertices_convexHull hx

/-- **No induction needed.** Every polytope is the convex hull of its own vertices, among any
finite generating set `T`: `convexHull k T` is already the convex hull of the essential points
of `T`, i.e. its vertices.

Among the (finitely many, hence nonempty-minimum-having) subsets `S ⊆ T` with
`convexHull k S = convexHull k T`, take one `S` of minimum cardinality. Every point of `S` is
essential *in `S`* — otherwise dropping it would give a smaller subset with the same hull,
contradicting minimality — so `essential_iff_singleton_isFaceOf` makes every point of `S` a
vertex of `convexHull k T`. Sandwiching `convexHull k T = convexHull k S` between
`convexHull k S ⊆ convexHull k (Vertices k (convexHull k T))` (since `S` is all vertices) and
`convexHull k (Vertices k (convexHull k T)) ⊆ convexHull k T` (since vertices are always among
the generators `T`, `IsPolytope.vertices_subset`) finishes it. -/
private theorem eq_convexHull_vertices_aux (T : Finset A) :
    convexHull k (T : Set A) = convexHull k
      (Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A)) := by
  classical
  obtain ⟨S, hS, hSmin⟩ := (T.powerset.filter
      (fun S : Finset A => convexHull k (S : Set A) = convexHull k (T : Set A))).exists_min_image
      Finset.card ⟨T, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hST, hSeq⟩ := hS
  have hess : ∀ v ∈ S, v ∉ convexHull k ((S.erase v : Finset A) : Set A) := by
    intro v hv hcon
    have herase_eq : convexHull k ((S.erase v : Finset A) : Set A) = convexHull k (S : Set A) := by
      conv_rhs => rw [← Finset.insert_erase hv]
      rw [Finset.coe_insert, ← Set.singleton_union, ← convexHull_union_convexHull,
        Set.union_eq_self_of_subset_left (Set.singleton_subset_iff.mpr hcon),
        IsConvexSet.convexHull_eq_self IsConvexSet.convexHull]
    have hmem𝒮 : S.erase v ∈ T.powerset.filter
        (fun S : Finset A => convexHull k (S : Set A) = convexHull k (T : Set A)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(Finset.erase_subset v S).trans hST, herase_eq.trans hSeq⟩
    have := hSmin _ hmem𝒮
    have hcard := Finset.card_erase_lt_of_mem hv
    omega
  have hXeq : (⟨convexHull k (S : Set A), IsConvexSet.convexHull⟩ : ConvexSet k A) =
      ⟨convexHull k (T : Set A), IsConvexSet.convexHull⟩ := SetLike.coe_injective hSeq
  have hall : (S : Set A) ⊆
      Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) := fun v hv =>
    hXeq ▸ (essential_iff_singleton_isFaceOf hv).mp (hess v hv)
  exact le_antisymm (hSeq.symm.subset.trans (convexHull_mono hall))
    (convexHull_mono IsPolytope.vertices_subset)

variable (k) in
/-- **Krein-Milman for polytopes.** Every polytope is the convex hull of its own vertices. -/
theorem IsPolytope.eq_convexHull_vertices {X : Set A} (hX : IsPolytope k X) :
    X = convexHull k (Vertices k (⟨X, hX.isConvexSet⟩ : ConvexSet k A)) := by
  obtain ⟨T, rfl⟩ := hX
  exact eq_convexHull_vertices_aux T

/-- **A face of a polytope is the convex hull of the generators that lie in it**, proved
directly (no homogenization). Combined with `ConvexSet.IsFaceOf.mem_of_sConvexComb_mem`: any
`x ∈ F` has some representation over `T`, and every point of that representation's support must
land in `F` too, so `x` is already a combination of `T`-points that lie in `F`. -/
private theorem face_eq_convexHull_inter_aux {T : Finset A} {F : ConvexSet k A}
    (hF : F.IsFaceOf (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A)) :
    (F : Set A) = convexHull k {x ∈ (T : Set A) | x ∈ F} := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hxF
    have hxX : x ∈ convexHull k (T : Set A) := hF.le hxF
    obtain ⟨w, hwsupp, hwx⟩ := mem_convexHull_iff_exists_sConvexComb.mp hxX
    have hw' : ↑w.weights.support ⊆
        ((⟨convexHull k (T : Set A), IsConvexSet.convexHull⟩ : ConvexSet k A) : Set A) :=
      hwsupp.trans subset_convexHull_self
    have hmem : w.sConvexComb ∈ F := by rw [hwx]; exact hxF
    have hall := hF.mem_of_sConvexComb_mem hw' hmem
    have hsub : ↑w.weights.support ⊆ {x ∈ (T : Set A) | x ∈ F} := by
      intro y hy
      exact ⟨hwsupp hy, hall y (Finset.mem_coe.mp hy)⟩
    rw [← hwx]
    exact mem_convexHull_iff_exists_sConvexComb.mpr ⟨w, hsub, rfl⟩
  · exact IsConvexSet.convexHull_subset_iff F.isConvexSet |>.mpr fun x hx => hx.2

/-- **A face of a polytope is a polytope**, proved directly (no homogenization). This shadows,
but does not call, the homogenization-based `IsPolytope.face_isPolytope` in `Polytope/Face.lean`
(which lives outside the `Convexity` namespace, so there is no name clash). -/
theorem IsPolytope.face_isPolytope {X F : ConvexSet k A} (hX : IsPolytope k (X : Set A))
    (hF : F.IsFaceOf X) : IsPolytope k (F : Set A) := by
  classical
  obtain ⟨T, hT⟩ := hX
  have hXeq : X = (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) :=
    SetLike.coe_injective hT
  refine ⟨T.filter (· ∈ F), ?_⟩
  rw [face_eq_convexHull_inter_aux (hXeq ▸ hF)]
  congr 1
  ext x
  simp

/-- A face of a polytope is the convex hull of its own vertices. Combines
`IsPolytope.face_isPolytope` (a face is itself a polytope, so has vertices at all) with
`IsPolytope.eq_convexHull_vertices` (a polytope is the hull of its vertices) applied to the face;
neither step uses homogenization. This is a stepping stone to
`IsPolytope.face_eq_convexHull_subset_vertices` below, which upgrades "its own vertices" to "a
subset of `X`'s vertices" via `Vertices.mono_of_isFaceOf`. -/
theorem IsPolytope.face_eq_convexHull_vertices {X F : ConvexSet k A}
    (hX : IsPolytope k (X : Set A)) (hF : F.IsFaceOf X) :
    (F : Set A) = convexHull k (Vertices k F) :=
  IsPolytope.eq_convexHull_vertices k (IsPolytope.face_isPolytope hX hF)

/-- **Krein-Milman for faces of polytopes**, the statement requested: every face `F` of a
polytope `X` is the convex hull of a subset of `X`'s own vertices — namely, `F`'s own vertices,
which are vertices of `X` by `Vertices.mono_of_isFaceOf`. -/
theorem IsPolytope.face_eq_convexHull_subset_vertices {X F : ConvexSet k A}
    (hX : IsPolytope k (X : Set A)) (hF : F.IsFaceOf X) :
    ∃ S ⊆ Vertices k X, (F : Set A) = convexHull k S :=
  ⟨Vertices k F, Vertices.mono_of_isFaceOf hF, IsPolytope.face_eq_convexHull_vertices hX hF⟩

/-! ## Convex independence

The generators of a polytope need not be its vertices (some may be redundant, i.e. combinations
of the rest). `IsConvexIndep` is the predicate singling out generating sets that already *are*
their own vertex sets, usable as a hypothesis; `IsPolytope.existsConvexIndep` says every polytope
has such a generating set (its vertex set itself, which is finite since it is a subset of any
given generating `Finset`). -/

variable [DecidableEq A]

variable (k) in
/-- A finite set of points is convex independent if none of them is a convex combination of the
rest, i.e. every point of `T` is already a vertex of `convexHull k T`. See
`isConvexIndep_iff_coe_eq_vertices` for this equivalence. -/
def IsConvexIndep (T : Finset A) : Prop := ∀ v ∈ T, v ∉ convexHull k (T.erase v : Set A)

theorem isConvexIndep_iff_coe_eq_vertices {T : Finset A} :
    IsConvexIndep k T ↔
      (T : Set A) = Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) := by
  constructor
  · intro h
    ext x
    exact ⟨fun hx => (essential_iff_singleton_isFaceOf hx).mp (h x hx),
      fun hx => mem_of_mem_vertices_convexHull hx⟩
  · intro h v hv
    have hv' : v ∈ Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) := h ▸ hv
    exact (essential_iff_singleton_isFaceOf hv).mpr hv'

variable (k) in
/-- **Every polytope is generated by a convex independent subset of any given generating set** —
namely its own vertex set, which is finite (`IsPolytope.vertices_subset`) and already convex
independent. -/
theorem IsPolytope.existsConvexIndep {X : Set A} (hX : IsPolytope k X) :
    ∃ T : Finset A, IsConvexIndep k T ∧ X = convexHull k (T : Set A) := by
  classical
  obtain ⟨T, rfl⟩ := hX
  have hScoe : (T.filter (· ∈ Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A))
      : Set A) = Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A) := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨mem_of_mem_vertices_convexHull hx, hx⟩⟩
  have hconv : convexHull k
      (T.filter (· ∈ Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A))
        : Set A) = convexHull k (T : Set A) := by
    rw [hScoe]; exact (eq_convexHull_vertices_aux T).symm
  refine ⟨T.filter (· ∈ Vertices k (⟨convexHull k (T : Set A), .convexHull⟩ : ConvexSet k A)),
    ?_, hconv.symm⟩
  rw [isConvexIndep_iff_coe_eq_vertices]
  exact hScoe.trans (congrArg (Vertices k) (SetLike.coe_injective hconv)).symm

/-! ## The face lattice of a polytope is atomistic

Every element of the face lattice is the join of the atoms below it, i.e. of the vertices it
contains — this is `Krein-Milman` restated in lattice-theoretic language via `IsAtomistic`. -/

open ConvexSet in
omit [DecidableEq A] in
/-- **The face lattice of a polytope is atomistic**: every face is the join of the vertex-faces
(atoms) it contains. The atoms of `Face P` are exactly the singleton-vertex faces `⟨{v}, _⟩`, and
the join of the atoms below `F` is `F` itself because `F` is convex and equals the convex hull of
its own vertices (`IsPolytope.face_eq_convexHull_vertices`). -/
theorem IsPolytope.face_isAtomistic {P : ConvexSet k A} (hP : IsPolytope k (P : Set A)) :
    IsAtomistic (Face P) := by
  classical
  refine ⟨fun F => ⟨{G : Face P | ∃ v ∈ Vertices k (F : ConvexSet k A), (G : Set A) = {v}},
    ⟨?_, ?_⟩, ?_⟩⟩
  · rintro G ⟨v, hv, hGv⟩
    apply SetLike.coe_subset_coe.mp
    rw [hGv]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hv.le (rfl : x ∈ ({x} : ConvexSet k A))
  · intro c hc
    have hFeq : (F.toConvexSet : Set A) = convexHull k (Vertices k F.toConvexSet) :=
      IsPolytope.face_eq_convexHull_vertices hP F.isFaceOf
    have hsub : (F.toConvexSet : Set A) ⊆ (c : Set A) := by
      rw [hFeq]
      apply c.isConvexSet.convexHull_subset_iff.mpr
      intro v hv
      have hface : (⟨({v} : ConvexSet k A), hv.trans F.isFaceOf⟩ : Face P) ∈
          {G : Face P | ∃ v ∈ Vertices k (F : ConvexSet k A), (G : Set A) = {v}} := ⟨v, hv, rfl⟩
      exact SetLike.coe_subset_coe.mpr (hc hface) (rfl : v ∈ ({v} : ConvexSet k A))
    exact SetLike.coe_subset_coe.mp hsub
  · rintro a ⟨v, hv, ha⟩
    refine ⟨fun hbot => ?_, fun b hba => ?_⟩
    · have hbotEmpty : (a : Set A) = ∅ := by rw [hbot]; simp [Bot.bot]
      rw [hbotEmpty] at ha
      exact Set.singleton_ne_empty v ha.symm
    · have hbsub : (b : Set A) ⊆ ({v} : Set A) := ha ▸ SetLike.coe_subset_coe.mpr hba.le
      rcases Set.subset_singleton_iff_eq.mp hbsub with hemp | hsing
      · exact SetLike.coe_injective (hemp.trans (rfl : (∅ : Set A) = ((⊥ : Face P) : Set A)))
      · exact absurd (SetLike.coe_injective (hsing.trans ha.symm)) hba.ne

open ConvexSet in
/-- As an instance: the face lattice of a (bundled) polytope is always atomistic, found
automatically by typeclass search whenever `Face (P : ConvexSet k A)` is written for an actual
`P : Polytope k A` (mirroring the `CoeOut (Face (P : ConvexSet R A)) (Polytope R A)` instance in
`Polytope/Face.lean`, which uses the same indexing trick). This can't be a bare
`∀ P : ConvexSet k A, IsAtomistic (Face P)` instance since not every `ConvexSet` is a polytope —
`IsPolytope` is a `Prop`, not something typeclass search can discharge on its own. -/
instance {P : Polytope k A} : IsAtomistic (Face (P : ConvexSet k A)) :=
  IsPolytope.face_isAtomistic P.isPolytope

end Convexity
