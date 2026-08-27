/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.TangentCone
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.TangentCone
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.KreinMilman
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.KreinMilman
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Faces
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed

/-! This file specializes the tangent cone of `Affine.TangentCone` to polytopes, and proves
  basic structural facts:

  - there is an order isomorphism between the tangent cone face lattice at a vertex and the upper
    ideal over the vertex in the polytope face lattice (this is combinatorial)
  - the faces of the tangent cone are cones over faces of the polytope (this is
    geometric and what is needed in optimization arguments)

 -/

namespace Affine

open Convexity PointedCone Module

section Polytope

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable {s : Set P} (x : s)
variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

attribute [local instance] AddTorsor.toConvexSpace
attribute [local instance] Convexity.ConvexSpace.ofModule
local instance : Convexity.IsModuleConvexSpace k V := .ofModule

/-- The tangent cone of a polytope at any of its points is finitely generated. -/
theorem IsPolytope.tangentCone_fg (hs : IsPolytope k s) :
    (tangentCone k s x).FG := by
  obtain ⟨t, rfl⟩ := hs
  rw [tangentCone_eq_hull_image, (isAffineMap_vsub_right k (x : P)).image_convexHull,
    PointedCone.hull_convexHull]
  exact Submodule.fg_span (t.finite_toSet.image _)

/-- The tangent cone at a vertex (extreme point) of a polytope is salient. -/
theorem IsPolytope.tangentCone_salient (hs : IsPolytope k s)
    (hx : IsExtremePoint k s (x : P)) : (tangentCone k s x).Salient :=
  Salient.tangentCone_of_isExtremePoint k s x hs.isConvexSet hx

/-- The tangent cone at a vertex of a polytope is the cone hull of a finite set of
  representatives of its rays. -/
theorem IsPolytope.tangentCone_eq_hull_rays (hs : IsPolytope k s)
    (hx : IsExtremePoint k s (x : P)) :
    ∃ r : Finset V, PointedCone.hull k (r : Set V) = tangentCone k s x ∧
      ∀ v ∈ r, (k ∙₊ v).IsFaceOf (tangentCone k s x) :=
  FG.krein_milman (IsPolytope.tangentCone_fg k x hs) (IsPolytope.tangentCone_salient k x hs hx)

/-- The point `x`, viewed as a member of the exposed face of `s` cut out by `φ`. -/
private def sepMem {φ : Dual k V} (hφx : φ ((x : P) -ᵥ (x : P)) = 0) :
    ↥{y ∈ s | φ (y -ᵥ (x : P)) = 0} :=
  ⟨(x : P), x.2, hφx⟩

/-- The set of points of `s` whose chordal direction from `x` lies in a given subcone `F` of the
tangent cone. This is `s`, "cut" by `F`.

LST comment: The point of this is that we need a formal way to say that a linear form supporting a
face of the tangent cone also supports a face of the polytope.  This doesn't quite make
sense, even informally, because of what spaces things are in.  sepSet is the way to
transport the contact locus of a linear form back into the polytope.
-/
def sepSet (F : PointedCone k V) : Set P := {y ∈ s | y -ᵥ (x : P) ∈ F}

/-- `sepSet` is convex

LST comment: the main point is that `y ↦ y -ᵥ x` is an affine map since everything in
sight is convex. -/
theorem isConvexSet_sepSet (hsc : IsConvexSet k s) (F : PointedCone k V) :
    IsConvexSet k (sepSet k x F) :=
  hsc.inter (IsConvexSet.preimage (isAffineMap_vsub_right k (x : P)) F.isConvexSet)

/-- If `F` is a face of the tangent cone at `x`, then `sepSet F` (`s` cut by `F`) is a face of
`s`.

LST comment: the proof is to take a z in the relint of the segment [z,w] in sepSet F;
the convex combination lifts to a linear combination of z - x and w - x which forces
these directions in F and then z,w in sepSet F.
 -/
theorem isFaceOf_sepSet (hsc : IsConvexSet k s) {F : PointedCone k V}
    (hF : F.IsFaceOf (tangentCone k s x)) :
    Convexity.ConvexSet.IsFaceOf
      (⟨sepSet k x F, isConvexSet_sepSet k x hsc F⟩ : Convexity.ConvexSet k P) ⟨s, hsc⟩ where
  le := fun _ hy => hy.1
  left_mem_of_mem_openSegment := by
    intro a ha b hb w hw hwseg
    obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hwseg
    rw [AddTorsor.convexCombPair_eq_lineMap] at hcomb
    have hrw : AffineMap.lineMap b a p -ᵥ (x : P)
        = (1 - p) • (b -ᵥ (x : P)) + p • (a -ᵥ (x : P)) := by
      simp only [AffineMap.lineMap_apply, vadd_vsub_assoc]
      rw [show a -ᵥ b = (a -ᵥ (x : P)) - (b -ᵥ (x : P)) from
        (vsub_sub_vsub_cancel_right a b (x : P)).symm, smul_sub]
      module
    have hwmem : (1 - p) • (b -ᵥ (x : P)) + p • (a -ᵥ (x : P)) ∈ F := by
      rw [← hrw, hcomb]; exact hw.2
    have haC : a -ᵥ (x : P) ∈ tangentCone k s x := vsub_mem_tangentCone k s x ha
    have hbC : b -ᵥ (x : P) ∈ tangentCone k s x := vsub_mem_tangentCone k s x hb
    exact ⟨ha, hF.mem_of_smul_add_smul_mem_right hbC haC (by linarith) hp hwmem⟩

/-- The set `{y ∈ s | φ (y -ᵥ x) = 0}` cut out by `φ` is convex: it is `sepSet k x φ.ker`.

LST comment: this is the usual application of sepSet: expose a face of the cone with a
form and then look at the sepSet of the kernel.
-/
private theorem isConvexSet_sep (hsc : IsConvexSet k s) (φ : Dual k V) :
    IsConvexSet k {y ∈ s | φ (y -ᵥ (x : P)) = 0} := by
  have hset : {y ∈ s | φ (y -ᵥ (x : P)) = 0} = sepSet k x (φ.ker : PointedCone k V) := by
    simp [sepSet]
  rw [hset]; exact isConvexSet_sepSet k x hsc _

/-- The set cut out by `φ` is `sepSet k x` of the exposed intersection
`tangentCone k s x ⊓φ.ker`.

LST comment: used in both directions

AI proof

 -/
private theorem sepSet_inf_ker_eq_sep (φ : Dual k V) :
    sepSet k x (tangentCone k s x ⊓ (φ.ker : PointedCone k V)) =
      {y ∈ s | φ (y -ᵥ (x : P)) = 0} := by
  ext y
  simp only [sepSet, Set.mem_ofPred_eq, Submodule.mem_inf, and_congr_right_iff]
  exact fun hys => ⟨fun h => h.2, fun h => ⟨vsub_mem_tangentCone k s x hys, h⟩⟩

/-- If `φ` exposes a face of the tangent cone of polytope `s` at a vertex
`x` , then `{y ∈ s | φ (y -ᵥ x) = 0}` is a face of s.

AI proof
 -/
theorem isFaceOf_sep (hsc : IsConvexSet k s) (φ : Dual k V)
    (hφ : tangentCone k s x ≤ φ.nonneg) :
    Convexity.ConvexSet.IsFaceOf
      (⟨{y ∈ s | φ (y -ᵥ (x : P)) = 0}, isConvexSet_sep k x hsc φ⟩ : Convexity.ConvexSet k P)
      ⟨s, hsc⟩ := by
  have hface : (tangentCone k s x ⊓ (φ.ker : PointedCone k V)).IsFaceOf (tangentCone k s x) :=
    PointedCone.IsExposedFaceOf.isFaceOf ⟨φ, hφ, rfl⟩
  simpa only [sepSet_inf_ker_eq_sep] using isFaceOf_sepSet k x hsc hface

/--  If `φ` exposes a face `f` of a the cone hull of s, then the cone hull of
`s ∩ ker φ` is equal to `hull s ∩ ker φ`.

TODO move this someplace else, since it's a general cone fact.

TODO usually in this file `s` is a polytope but here it a set generating a cone.

LST comment: possibly this proof can use existing facts for `⊆` but the
direct proof is a simple optimization argument.
-/
private lemma hull_inf_ker_eq_hull_inter {W : Type*} [AddCommGroup W] [Module k W]
    {s : Set W} {φ : Dual k W} (hφ : PointedCone.hull k s ≤ φ.nonneg) :
    PointedCone.hull k s ⊓ (φ.ker : PointedCone k W) =
      PointedCone.hull k (s ∩ (φ.ker : Set W)) := by
  refine le_antisymm ?_ (le_inf (PointedCone.hull_mono Set.inter_subset_left)
    (Submodule.span_le.mpr fun v hv => hv.2))
  rintro a ⟨ha, ha0⟩
  obtain ⟨c, hcs, hc0, rfl⟩ := PointedCone.mem_hull_set.mp ha
  have ha0' : φ (c.sum fun m r => r • m) = 0 := ha0
  rw [Finsupp.sum, map_sum] at ha0'
  simp only [map_smul, smul_eq_mul] at ha0'
  have hnn : ∀ m ∈ c.support, 0 ≤ c m * φ m :=
    fun m hm => mul_nonneg (hc0 m) (hφ (PointedCone.subset_hull (hcs hm)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp ha0'
  refine PointedCone.mem_hull_set.mpr ⟨c, fun m hm => ⟨hcs hm, ?_⟩, hc0, rfl⟩
  rcases mul_eq_zero.mp (hz m hm) with h | h
  · exact absurd h (Finsupp.mem_support_iff.mp hm)
  · exact h

/-- Taking tangent cones commutes with exposing faces.  If `t` is the tangent cone of
`s` at `x`, and `φ` exposes a face `f` of `t`, then `f` is the tangent cone at `x`
of the corresponding face of `s`.

This is a saturated version of `isFaceOf_sepSet`.

LST comment: This is the main technical step, but its primal-dual nature
probably means we should either build more technique on one side or
think it through more carefully.
 -/
theorem tangentCone_inf_ker_eq_tangentCone_sep (φ : Dual k V)
    (hφ : tangentCone k s x ≤ φ.nonneg) :
    tangentCone k s x ⊓ (φ.ker : PointedCone k V) =
      tangentCone k {y ∈ s | φ (y -ᵥ (x : P)) = 0} (sepMem k x (by simp)) := by
  simp only [tangentCone_eq_hull_image, sepMem] at hφ ⊢
  rw [hull_inf_ker_eq_hull_inter k hφ]
  congr 1
  ext v
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq, SetLike.mem_coe,
    LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨y, hys, rfl⟩, hφv⟩
    exact ⟨y, ⟨hys, hφv⟩, rfl⟩
  · rintro ⟨y, ⟨hys, hφy⟩, rfl⟩
    exact ⟨⟨y, hys, rfl⟩, hφy⟩

/-- If `G` is a face of the polytope `s` containing `x`, there is a linear functional `φ` on `V`
that exposes the corresponding face of the tangent cone:
`φ` is nonnegative on the whole tangent cone at `x`, and its
zero set within `s` recovers `G` exactly.

The functional is built by homogenizing.

AI proof
 -/
theorem IsPolytope.exists_expose_of_isFaceOf (hs : IsPolytope k s)
    {G : Convexity.ConvexSet k P} (hG : G.IsFaceOf ⟨s, hs.isConvexSet⟩) (hxG : (x : P) ∈ G) :
    ∃ φ : Dual k V, tangentCone k s x ≤ φ.nonneg ∧
      {y ∈ s | φ (y -ᵥ (x : P)) = 0} = (G : Set P) := by
  classical
  let W := CanonicalHomogenization k P
  let := IsModuleConvexSpace.ofAddTorsor (R := k) (V := W)
  let hom : Affine.IsHomogenization k P W := inferInstance
  set Ss : Convexity.ConvexSet k P := ⟨s, hs.isConvexSet⟩ with hSsdef
  have hCPfg : (Convexity.ConvexSet.homogenize W Ss).FG := IsPolytope.homogenize_fg (W := W) hs
  have hCPpoly := hCPfg.isPolyhedral
  obtain ⟨ψ, hψnn, hψeq⟩ := PointedCone.IsFaceOf.isExposed_of_polyhedral hCPpoly
    (Affine.IsHomogenization.homogenize_isFaceOf (W := W) hG)
  set φ : Dual k V := ψ.comp hom.ofVector with hφdef
  have hφkey : ∀ y : P, φ (y -ᵥ (x : P)) = ψ (hom.ofPoint y) - ψ (hom.ofPoint (x : P)) := by
    intro y
    have h1 : hom.ofVector (y -ᵥ (x : P)) = hom.ofPoint y -ᵥ hom.ofPoint (x : P) :=
      AffineMap.linearMap_vsub hom.ofPoint y (x : P)
    simp only [hφdef, LinearMap.comp_apply, h1, vsub_eq_sub, map_sub]
  have hchar : ∀ y : P, y ∈ (G : Set P) ↔ y ∈ s ∧ ψ (hom.ofPoint y) = 0 := by
    intro y
    constructor
    · intro hy
      have h1 : hom.ofPoint y ∈ Convexity.ConvexSet.homogenize W G :=
        (Convexity.ConvexSet.ofPoint_mem_homogenize_iff_mem W y G).mpr hy
      rw [hψeq] at h1
      obtain ⟨h1s, h1k⟩ := h1
      exact ⟨(Convexity.ConvexSet.ofPoint_mem_homogenize_iff_mem W y Ss).mp h1s,
        by simpa [LinearMap.mem_ker] using h1k⟩
    · rintro ⟨hys, hψy⟩
      refine (Convexity.ConvexSet.ofPoint_mem_homogenize_iff_mem W y G).mp ?_
      rw [hψeq]
      exact ⟨(Convexity.ConvexSet.ofPoint_mem_homogenize_iff_mem W y Ss).mpr hys,
        by simpa [LinearMap.mem_ker] using hψy⟩
  have hx0 : ψ (hom.ofPoint (x : P)) = 0 := ((hchar (x : P)).mp hxG).2
  have hφkey' : ∀ y : P, φ (y -ᵥ (x : P)) = ψ (hom.ofPoint y) := by
    intro y; rw [hφkey, hx0, sub_zero]
  refine ⟨φ, ?_, ?_⟩
  · rw [tangentCone_eq_hull_image]
    apply Submodule.span_le.mpr
    rintro v ⟨y, hys, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_nonneg, hφkey' y]
    exact hψnn (subset_hull ⟨y, hys, rfl⟩)
  · ext y
    rw [Set.mem_sep_iff, hφkey' y, hchar y]

/-- `x` always lies in `sepSet k x F`, since `0 ∈ F`. -/
private theorem mem_sepSet_self (F : PointedCone k V) : (x : P) ∈ sepSet k x F :=
  ⟨x.2, by simp⟩

/-- The tangent cone construction is monotone in its underlying set, at a common basepoint. -/
private theorem tangentCone_mono {T₁ T₂ : Set P} (h : T₁ ⊆ T₂) {p : P} (hp : p ∈ T₁) :
    tangentCone k T₁ ⟨p, hp⟩ ≤ tangentCone k T₂ ⟨p, h hp⟩ := by
  rw [tangentCone_eq_hull_image, tangentCone_eq_hull_image]
  exact PointedCone.hull_mono (Set.image_mono h)

/-- The tangent cone construction only depends on its underlying set (not on the specific
membership proof of the basepoint): transporting the basepoint's membership proof along a set
equality is safe. Needed since directly `rw`-ing a set equality under a `tangentCone` whose
basepoint's *type* depends on that set hits a "motive is not type correct" error.

AI lemma and proof
-/
private theorem tangentCone_congr {T₁ T₂ : Set P} (h : T₁ = T₂) (p : P) (hp : p ∈ T₁) :
    tangentCone k T₁ ⟨p, hp⟩ = tangentCone k T₂ ⟨p, h ▸ hp⟩ := by
  subst h; rfl

/-- General saturation: for *any* face `F` of the tangent cone at `x` (using that the tangent
cone is polyhedral, hence every face is exposed by `exists_expose_of_isFaceOf`'s underlying
machinery), the tangent cone of `sepSet k x F` at `x` recovers `F` exactly. This completes the
converse of `isFaceOf_sepSet`.

Ai proof
-/
theorem tangentCone_sepSet_eq_self (hs : IsPolytope k s) {F : PointedCone k V}
    (hF : F.IsFaceOf (tangentCone k s x)) :
    tangentCone k (sepSet k x F) ⟨(x : P), mem_sepSet_self k x F⟩ = F := by
  obtain ⟨φ, hφnn, hφeq⟩ :=
    PointedCone.IsFaceOf.isExposed_of_polyhedral (IsPolytope.tangentCone_fg k x hs).isPolyhedral hF
  have hsub : sepSet k x F = {y ∈ s | φ (y -ᵥ (x : P)) = 0} := by
    rw [hφeq]; exact sepSet_inf_ker_eq_sep k x φ
  have h1 := tangentCone_congr k hsub (x : P) (mem_sepSet_self k x F)
  rw [h1]
  change tangentCone k {y ∈ s | φ (y -ᵥ (x : P)) = 0} (sepMem k x (by simp)) = F
  rw [← tangentCone_inf_ker_eq_tangentCone_sep k x φ hφnn, ← hφeq]

/-- If the tangent cone of a set `T` at one of its points is a ray, `T` lies on the line through
that point in the ray's direction.

TODO: this belongs in a more general file once one exists for
facts relating `tangentCone` to affine dimension (see `ConvexSpace/Dimension.lean`).

AI proof
 -/
private theorem subset_affineSpan_pair_of_tangentCone_eq_ray {T : Set P} (x' : T) {v : V}
    (hT : tangentCone k T x' = k ∙₊ v) :
    T ⊆ affineSpan k ({(x' : P), v +ᵥ (x' : P)} : Set P) := by
  intro z hz
  have hmem : z -ᵥ (x' : P) ∈ tangentCone k T x' := vsub_mem_tangentCone k T x' hz
  rw [hT] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
  have hc' : (↑c : k) • v = z -ᵥ (x' : P) := by exact_mod_cast hc
  rw [AffineMap.lineMap_apply, vadd_vsub, hc', vsub_vadd]

/-- A finite set of points, all lying on a common line and all extreme in a common ambient
convex set, has at most two elements.

TODO: this belongs in a more general file about convexity on a line once one exists
(see `ConvexSpace/Dimension.lean`).

AI proof
-/
private theorem card_le_two_of_forall_isFaceOf_of_subset_affineSpan_pair
    {a b : P} {C : Convexity.ConvexSet k P} {E : Finset P}
    (hEC : (E : Set P) ⊆ C) (hEspan : (E : Set P) ⊆ affineSpan k ({a, b} : Set P))
    (hext : ∀ z ∈ E, ({z} : Convexity.ConvexSet k P).IsFaceOf C) : E.card ≤ 2 := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hEne
  · simp
  set v : V := b -ᵥ a with hvdef
  have htex : ∀ z ∈ E, ∃ t : k, z -ᵥ a = t • v := by
    intro z hz
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hEspan hz)
    exact ⟨t, by rw [← ht, AffineMap.lineMap_apply, vadd_vsub, hvdef]⟩
  let tOf : P → k := fun z => if hz : z ∈ E then (htex z hz).choose else 0
  have hteq : ∀ z ∈ E, z -ᵥ a = tOf z • v := by
    intro z hz; simp only [tOf, dif_pos hz]; exact (htex z hz).choose_spec
  have htinj : ∀ p ∈ E, ∀ q ∈ E, tOf p = tOf q → p = q := by
    intro p hp q hq he
    have hpq : p -ᵥ a = q -ᵥ a := by rw [hteq p hp, hteq q hq, he]
    have h1 := congrArg (· +ᵥ a) hpq
    simpa using h1
  obtain ⟨tmin, htminE, htminle⟩ := Finset.exists_min_image E tOf hEne
  obtain ⟨tmax, htmaxE, htmaxle⟩ := Finset.exists_max_image E tOf hEne
  have hmid : ∀ z ∈ E, z = tmin ∨ z = tmax := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    obtain ⟨hzne_min, hzne_max⟩ := hcon
    have h1 : tOf tmin ≤ tOf z := htminle z hz
    have h2 : tOf z ≤ tOf tmax := htmaxle z hz
    have h1' : tOf tmin < tOf z :=
      lt_of_le_of_ne h1 (fun he => hzne_min (htinj tmin htminE z hz he).symm)
    have h2' : tOf z < tOf tmax :=
      lt_of_le_of_ne h2 (fun he => hzne_max (htinj z hz tmax htmaxE he))
    have hden : 0 < tOf tmax - tOf tmin := by linarith
    set t : k := (tOf z - tOf tmin) / (tOf tmax - tOf tmin) with htdef
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    have hkey : AffineMap.lineMap tmin tmax t = z := by
      have hrw : AffineMap.lineMap tmin tmax t -ᵥ a
          = (1 - t) • (tmin -ᵥ a) + t • (tmax -ᵥ a) := by
        simp only [AffineMap.lineMap_apply, vadd_vsub_assoc]
        rw [show tmax -ᵥ tmin = (tmax -ᵥ a) - (tmin -ᵥ a) from
          (vsub_sub_vsub_cancel_right tmax tmin a).symm, smul_sub]
        module
      rw [hteq tmin htminE, hteq tmax htmaxE] at hrw
      have hcoef : (1 - t) • tOf tmin • v + t • tOf tmax • v = tOf z • v := by
        have hte : (1 - t) * tOf tmin + t * tOf tmax = tOf z := by rw [htdef]; field_simp; ring
        rw [smul_smul, smul_smul, ← add_smul, hte]
      rw [hcoef, ← hteq z hz] at hrw
      have h1 := congrArg (· +ᵥ a) hrw
      simpa using h1
    have hface_z : ({z} : Convexity.ConvexSet k P).IsFaceOf C := hext z hz
    have hseg : z ∈ Convexity.openSegment k tmax tmin := by
      refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
      rw [AddTorsor.convexCombPair_eq_lineMap]
      exact hkey
    have hzz : z ∈ ({z} : Convexity.ConvexSet k P) := rfl
    have hres := hface_z.left_mem_of_mem_openSegment (hEC htmaxE) (hEC htminE) hzz hseg
    exact hzne_max (id hres : tmax = z).symm
  have hss : E ⊆ ({tmin, tmax} : Finset P) := by
    intro z hz; rcases hmid z hz with h | h <;> simp [h]
  exact (Finset.card_le_card hss).trans
    ((Finset.card_insert_le _ _).trans (by simp))

open Convexity.ConvexSet in
/-- Extreme rays of the tangent cone at x correspond to edge directions
emanating from x.

LST comment: This is the main techical theorem.  The underlying machinery
doesn't seem to have any problem generalizing to higher
dimensions.

AI proof
 -/
theorem IsPolytope.exists_edge_of_ray_isFaceOf (hs : IsPolytope k s)
    (hx : IsExtremePoint k s (x : P)) {v : V} (hv0 : v ≠ 0)
    (hface : (k ∙₊ v).IsFaceOf (tangentCone k s x)) :
    ∃ y ∈ s, ({y} : Convexity.ConvexSet k P).IsFaceOf ⟨s, hs.isConvexSet⟩ ∧
      ∃ c : k, 0 < c ∧ y -ᵥ (x : P) = c • v ∧
        (Convexity.ConvexSet.convexHull k ({(x : P), y} : Set P)).IsFaceOf
          ⟨s, hs.isConvexSet⟩ := by
  classical
  have hpoly : (tangentCone k s x).IsPolyhedral := (IsPolytope.tangentCone_fg k x hs).isPolyhedral
  obtain ⟨φ, hφ, hφeq⟩ := PointedCone.IsFaceOf.isExposed_of_polyhedral hpoly hface
  set F : Set P := {y ∈ s | φ (y -ᵥ (x : P)) = 0}
  have hFconv : IsConvexSet k F := isConvexSet_sep k x hs.isConvexSet φ
  set Fs : Convexity.ConvexSet k P := ⟨F, hFconv⟩
  have hx'mem : φ ((x : P) -ᵥ (x : P)) = 0 := by simp
  set x' : ↥F := sepMem k x hx'mem
  have hFface : Fs.IsFaceOf ⟨s, hs.isConvexSet⟩ := isFaceOf_sep k x hs.isConvexSet φ hφ
  have hcone_eq : (k ∙₊ v : PointedCone k V) = tangentCone k F x' := by
    rw [hφeq]; exact tangentCone_inf_ker_eq_tangentCone_sep k x φ hφ
  have hFpoly : IsPolytope k F := IsPolytope.face_isPolytope hs hFface
  let W := CanonicalHomogenization k P
  let := IsModuleConvexSpace.ofAddTorsor (R := k) (V := W)
  obtain ⟨E_F, hE_Fsub, hE_Feq, hE_Fext⟩ :=
    IsPolytope.eq_convexHull_extremePoints W hFpoly
  have hxF : (x : P) ∈ F := x'.2
  have hxExtS : ({(x : P)} : Convexity.ConvexSet k P).IsFaceOf ⟨s, hs.isConvexSet⟩ :=
    ConvexSet.isFaceOf_of_isExtremePoint k s x hs.isConvexSet hx
  have hxExtF : ({(x : P)} : Convexity.ConvexSet k P).IsFaceOf Fs :=
    (Convexity.ConvexSet.IsFaceOf.iff_le_of_isFaceOf hxExtS hFface).mpr
      (Set.singleton_subset_iff.mpr hxF)
  set G : Finset P := insert (x : P) E_F with hGdef
  have hGsub : (G : Set P) ⊆ F := by
    rw [hGdef, Finset.coe_insert]
    exact Set.insert_subset hxF hE_Fsub
  have hGeq : F = Convexity.convexHull k (G : Set P) := by
    have hxmemhull : (x : P) ∈ Convexity.convexHull k (E_F : Set P) := hE_Feq ▸ hxF
    have habs : ({(x : P)} : Set P) ∪ Convexity.convexHull k (E_F : Set P) =
        Convexity.convexHull k (E_F : Set P) :=
      Set.union_eq_self_of_subset_left (Set.singleton_subset_iff.mpr hxmemhull)
    have h1 : Convexity.convexHull k (({(x : P)} : Set P) ∪ (E_F : Set P)) =
        Convexity.convexHull k (E_F : Set P) := by
      rw [← Convexity.convexHull_union_convexHull, habs]
      exact Convexity.IsConvexSet.convexHull_eq_self Convexity.IsConvexSet.convexHull
    rw [hGdef, Finset.coe_insert, ← Set.singleton_union, h1, hE_Feq]
  have hGext : ∀ z ∈ G, ({z} : Convexity.ConvexSet k P).IsFaceOf Fs := by
    intro z hz
    rw [hGdef, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hxExtF
    · exact hE_Fext z hz
  -- `F` lies on the line through `x` in direction `v` (Lemma B), so its extreme points colinear
  -- with `x` along that line number at most two (Lemma C).
  have hFspan : F ⊆ affineSpan k ({(x : P), v +ᵥ (x : P)} : Set P) :=
    subset_affineSpan_pair_of_tangentCone_eq_ray k x' hcone_eq.symm
  have hGcard : G.card ≤ 2 :=
    card_le_two_of_forall_isFaceOf_of_subset_affineSpan_pair k hGsub (hGsub.trans hFspan) hGext
  have hxG : (x : P) ∈ G := Finset.mem_insert_self _ _
  -- `G` cannot be just `{x}`: that would force the tangent cone of `F` at `x` to be trivial,
  -- contradicting `v ≠ 0`.
  have hGne1 : G.card ≠ 1 := by
    intro hcard1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    have hax : a = (x : P) := by rw [ha, Finset.mem_singleton] at hxG; exact hxG.symm
    have hFsingle : F = {(x : P)} := by rw [hGeq, ha, hax]; simp
    have hTeq : tangentCone k F x' = ⊥ := by
      have heq : tangentCone k F x' = PointedCone.hull k ((· -ᵥ (x : P)) '' F) :=
        tangentCone_eq_hull_image k F x'
      rw [heq, hFsingle]; simp
    exact hv0 (by
      have hvmem : (v : V) ∈ (k ∙₊ v : PointedCone k V) := PointedCone.subset_hull rfl
      rw [hcone_eq, hTeq] at hvmem
      exact hvmem)
  have hGcard2 : G.card = 2 := by
    have h1 : 1 ≤ G.card := Finset.one_le_card.mpr ⟨_, hxG⟩
    omega
  have hexists_ne : ∃ z ∈ G, z ≠ (x : P) := by
    by_contra hcon
    push_neg at hcon
    have hsub : G ⊆ {(x : P)} := fun z hz => Finset.mem_singleton.mpr (hcon z hz)
    have : G.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    omega
  obtain ⟨zmax, hzmaxG, hzmaxne⟩ := hexists_ne
  have hxzsub : ({(x : P), zmax} : Finset P) ⊆ G := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    exacts [hxG, hzmaxG]
  have hxzcard : ({(x : P), zmax} : Finset P).card = 2 := Finset.card_pair hzmaxne.symm
  have hGeq2 : G = ({(x : P), zmax} : Finset P) :=
    (Finset.eq_of_subset_of_card_le hxzsub (by rw [hGcard2, hxzcard])).symm
  have hzmaxF : zmax ∈ F := hGsub hzmaxG
  have hzmaxmem : zmax -ᵥ (x : P) ∈ (k ∙₊ v : PointedCone k V) :=
    hcone_eq ▸ vsub_mem_tangentCone k F x' hzmaxF
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzmaxmem
  have hc0 : 0 < (c : k) := by
    rcases lt_or_eq_of_le c.2 with h | h
    · exact h
    · exfalso
      apply hzmaxne
      have hcz : c • v = (0 : V) := by
        rw [show c = (0 : {c : k // 0 ≤ c}) from Subtype.ext h.symm]; simp
      rw [hcz] at hc
      have h1 := congrArg (· +ᵥ (x : P)) hc.symm
      simpa using h1
  refine ⟨zmax, hzmaxF.1, ?_, (c : k), hc0, hc.symm, ?_⟩
  · have hzmax_mem_EF : zmax ∈ E_F := by
      have hzmax_mem_G : zmax ∈ G := hzmaxG
      rw [hGdef, Finset.mem_insert] at hzmax_mem_G
      exact hzmax_mem_G.resolve_left hzmaxne
    exact (hE_Fext zmax hzmax_mem_EF).trans hFface
  · have hFeq2 : F = Convexity.convexHull k ({(x : P), zmax} : Set P) := by
      rw [hGeq, hGeq2]; simp
    change (Convexity.ConvexSet.convexHull k ({(x : P), zmax} : Set P)).IsFaceOf _
    have hFseq : (Convexity.ConvexSet.convexHull k ({(x : P), zmax} : Set P)) = Fs := by
      apply SetLike.coe_injective
      change Convexity.convexHull k ({(x : P), zmax} : Set P) = F
      exact hFeq2.symm
    rw [hFseq]
    exact hFface

/-- The tangent cone at a vertex of a polytope is generated by finitely many
edge vectors.

LST comment: this could be improved to say that it's generated exactly
by the edge vectors.
-/
theorem IsPolytope.tangentCone_eq_hull_edgeVectors (hs : IsPolytope k s)
    (hx : IsExtremePoint k s (x : P)) :
    ∃ r : Finset V, PointedCone.hull k (r : Set V) = tangentCone k s x ∧
      ∀ v ∈ r, v ≠ 0 → ∃ y ∈ s, ({y} : Convexity.ConvexSet k P).IsFaceOf ⟨s, hs.isConvexSet⟩ ∧
        ∃ c : k, 0 < c ∧ y -ᵥ (x : P) = c • v ∧
          (Convexity.ConvexSet.convexHull k ({(x : P), y} : Set P)).IsFaceOf
            ⟨s, hs.isConvexSet⟩ := by
  obtain ⟨r, hr, hface⟩ := IsPolytope.tangentCone_eq_hull_rays k x hs hx
  exact ⟨r, hr, fun v hv hv0 =>
    IsPolytope.exists_edge_of_ray_isFaceOf k x hs hx hv0 (hface v hv)⟩

/-- `x` viewed as the bottom face `{x}` of the polytope's face lattice: the base point of the
interval that `IsPolytope.tangentConeFace_orderIso` identifies with the tangent cone's face
lattice. -/
private def xFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P)) :
    Convexity.ConvexSet.Face (⟨s, hs.isConvexSet⟩ : Convexity.ConvexSet k P) :=
  ⟨⟨{(x : P)}, IsConvexSet.singleton (x := (x : P))⟩,
    ConvexSet.isFaceOf_of_isExtremePoint k s x hs.isConvexSet hx⟩

/-- The face of `s` corresponding to a face `F` of the tangent cone: `sepSet k x F`, packaged as
a `Convexity.ConvexSet.Face`. -/
private def sepFace (hs : IsPolytope k s) (F : PointedCone.Face (tangentCone k s x)) :
    Convexity.ConvexSet.Face (⟨s, hs.isConvexSet⟩ : Convexity.ConvexSet k P) :=
  ⟨⟨sepSet k x F, isConvexSet_sepSet k x hs.isConvexSet F⟩,
    isFaceOf_sepSet k x hs.isConvexSet F.isFaceOf⟩

@[simp] private theorem coe_sepFace (hs : IsPolytope k s)
    (F : PointedCone.Face (tangentCone k s x)) : (sepFace k x hs F : Set P) = sepSet k x F := rfl

private theorem xFace_le_sepFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (F : PointedCone.Face (tangentCone k s x)) : xFace k x hs hx ≤ sepFace k x hs F := by
  change (xFace k x hs hx : Set P) ⊆ (sepFace k x hs F : Set P)
  rw [coe_sepFace]
  exact Set.singleton_subset_iff.mpr (mem_sepSet_self k x F)

/-- `sepFace`, packaged as an element of `Set.Ici (xFace k x hs hx)`. Named (rather than an
inline anonymous constructor) so it elaborates once and is referenced consistently. -/
private def sepFaceIci (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (F : PointedCone.Face (tangentCone k s x)) : Set.Ici (xFace k x hs hx) :=
  ⟨sepFace k x hs F, xFace_le_sepFace k x hs hx F⟩

/-- The face of the tangent cone corresponding to a face `G` of `s` containing `x`:
`tangentCone k G x`, packaged as a `PointedCone.Face`. It is indeed a face because `G` arises as
the zero set of a functional exposing `tangentCone k s x ⊓ φ.ker`
(`IsPolytope.exists_expose_of_isFaceOf`), so `tangentCone k G x` *is* that exposed
intersection. -/
private def coneFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (G : Set.Ici (xFace k x hs hx)) : PointedCone.Face (tangentCone k s x) :=
  ⟨tangentCone k (G.1 : Set P) ⟨(x : P), G.2 rfl⟩, by
    obtain ⟨φ, hφnn, hφeq⟩ := IsPolytope.exists_expose_of_isFaceOf k x hs G.1.isFaceOf (G.2 rfl)
    have hexp : (tangentCone k s x ⊓ (φ.ker : PointedCone k V)).IsFaceOf (tangentCone k s x) :=
      PointedCone.IsExposedFaceOf.isFaceOf ⟨φ, hφnn, rfl⟩
    have heq2 : tangentCone k {y ∈ s | φ (y -ᵥ (x : P)) = 0} (sepMem k x (by simp))
        = tangentCone k (G.1 : Set P) ⟨(x : P), G.2 rfl⟩ :=
      tangentCone_congr k hφeq (x : P) (sepMem k x (by simp)).2
    rwa [tangentCone_inf_ker_eq_tangentCone_sep k x φ hφnn, heq2] at hexp⟩

@[simp] private theorem coe_coneFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (G : Set.Ici (xFace k x hs hx)) :
    (coneFace k x hs hx G : PointedCone k V) = tangentCone k (G.1 : Set P) ⟨(x : P), G.2 rfl⟩ :=
  rfl

private theorem sepFace_coneFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (G : Set.Ici (xFace k x hs hx)) : sepFace k x hs (coneFace k x hs hx G) = G.1 := by
  apply Convexity.ConvexSet.Face.ext
  intro y
  obtain ⟨φ, hφnn, hφeq⟩ := IsPolytope.exists_expose_of_isFaceOf k x hs G.1.isFaceOf (G.2 rfl)
  have heq2 : tangentCone k {y ∈ s | φ (y -ᵥ (x : P)) = 0} (sepMem k x (by simp))
      = tangentCone k (G.1 : Set P) ⟨(x : P), G.2 rfl⟩ :=
    tangentCone_congr k hφeq (x : P) (sepMem k x (by simp)).2
  have heq3 : tangentCone k s x ⊓ (φ.ker : PointedCone k V)
      = tangentCone k (G.1 : Set P) ⟨(x : P), G.2 rfl⟩ :=
    (tangentCone_inf_ker_eq_tangentCone_sep k x φ hφnn).trans heq2
  change y ∈ sepSet k x (coneFace k x hs hx G : PointedCone k V) ↔ y ∈ (G.1 : Set P)
  rw [coe_coneFace, ← heq3, sepSet_inf_ker_eq_sep, hφeq]
  exact Iff.rfl

private theorem coneFace_sepFace (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P))
    (F : PointedCone.Face (tangentCone k s x)) :
    coneFace k x hs hx (sepFaceIci k x hs hx F) = F := by
  rw [← PointedCone.Face.toPointedCone_eq_iff]
  show (coneFace k x hs hx (sepFaceIci k x hs hx F) : PointedCone k V) = (F : PointedCone k V)
  rw [coe_coneFace]
  exact (tangentCone_congr k (coe_sepFace k x hs F) (x : P)
    ((sepFaceIci k x hs hx F).2 rfl)).trans (tangentCone_sepSet_eq_self k x hs F.isFaceOf)

/-- The face lattice of the tangent cone at a vertex `x` of a polytope `s` is isomorphic to the
interval `[{x}, ⊤]` in the face lattice of `s`.

A face `F` of the tangent cone corresponds to `sepSet k x F` (`sepFace`), a face of `s`
containing `x` (`isFaceOf_sepSet`). Conversely, a face `G` of `s` containing `x` corresponds to
`tangentCone k G x` (`coneFace`), a face of the tangent cone. The two maps are mutually inverse
by the saturation identity `tangentCone_sepSet_eq_self` and the analogous computation for `G`
(`sepFace_coneFace`, `coneFace_sepFace`). -/
def IsPolytope.tangentConeFace_orderIso (hs : IsPolytope k s) (hx : IsExtremePoint k s (x : P)) :
    PointedCone.Face (tangentCone k s x) ≃o Set.Ici (xFace k x hs hx) where
  toFun F := sepFaceIci k x hs hx F
  invFun G := coneFace k x hs hx G
  left_inv F := coneFace_sepFace k x hs hx F
  right_inv G := Subtype.ext (sepFace_coneFace k x hs hx G)
  map_rel_iff' := by
    intro F₁ F₂
    constructor
    · intro h
      have h1 : sepSet k x F₁ ⊆ sepSet k x F₂ := h
      have h2 := tangentCone_mono k h1 (mem_sepSet_self k x F₁)
      change tangentCone k (sepSet k x F₁) ⟨(x : P), mem_sepSet_self k x F₁⟩ ≤
        tangentCone k (sepSet k x F₂) ⟨(x : P), mem_sepSet_self k x F₂⟩ at h2
      rwa [tangentCone_sepSet_eq_self k x hs F₁.isFaceOf,
        tangentCone_sepSet_eq_self k x hs F₂.isFaceOf] at h2
    · intro h y hy
      exact ⟨hy.1, h hy.2⟩

end Polytope

end Affine
