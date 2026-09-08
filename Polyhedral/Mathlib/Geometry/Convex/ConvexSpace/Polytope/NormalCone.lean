/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.KreinMilman
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.TangentCone
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.NormalCone

/-! # The normal cone of a face of a polytope

For a polytope `K` and a face `F₀`, `K.tangentCone F₀` is finitely generated
(`IsPolytope.tangentCone_fg`). This sharpens `ConvexSet.not_mem_normalCone_iff`: instead of
quantifying over all `y ∈ K`, failure to be maximized is witnessed by *some element of a fixed
finite generating set* of the tangent cone. -/

noncomputable section

namespace Convexity

namespace ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P]

local instance instConvexSpaceOfAddTorsorPolytopeNormalCone : ConvexSpace R P :=
  AddTorsor.toConvexSpace

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

variable {K F₀ : ConvexSet R P}

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **A linear functional's ascent set on a finitely generated cone is witnessed by a generating
finset.** If `C = hull R s`, then `φ` is positive somewhere on `C` iff it is positive somewhere on
`s`: `s ⊆ C` gives the easy direction; conversely if `φ ≤ 0` on all of `s`, then `s ⊆ (-φ).nonneg`
(a pointed cone), so `hull R s ≤ (-φ).nonneg` too, by minimality of the hull. -/
theorem _root_.PointedCone.exists_mem_pos_iff_exists_mem_finset_pos {s : Finset M}
    {φ : Module.Dual R M} :
    (∃ v ∈ PointedCone.hull R (s : Set M), 0 < φ v) ↔ ∃ v ∈ s, 0 < φ v := by
  constructor
  · rintro ⟨v, hv, hφv⟩
    by_contra! h
    have hsub : (s : Set M) ⊆ ((-φ).nonneg : Set M) := by
      intro x hx
      change 0 ≤ (-φ) x
      rw [LinearMap.neg_apply, neg_nonneg]
      exact h x hx
    have hle : PointedCone.hull R (s : Set M) ≤ (-φ).nonneg := Submodule.span_le.mpr hsub
    have hmem := hle hv
    change 0 ≤ (-φ) v at hmem
    rw [LinearMap.neg_apply, neg_nonneg] at hmem
    linarith
  · rintro ⟨v, hv, hφv⟩
    exact ⟨v, PointedCone.subset_hull hv, hφv⟩

/-- **Polytope version of `not_mem_normalCone_iff`.** For `K` a polytope, a linear form `φ` fails
to be maximized over `K` on the face `F₀` iff some element of a *finite* generating set `s` of the
tangent cone `K.tangentCone F₀` (whose existence is `IsPolytope.tangentCone_fg`) is an ascent
direction — not "some `y ∈ K`", but a check against a fixed finite list of directions.
Combines `ConvexSet.not_mem_normalCone_iff` (ascent iff some tangent-cone generator `y -ᵥ x` has
`φ (y -ᵥ x) > 0`) with `PointedCone.exists_mem_pos_iff_exists_mem_finset_pos` (ascent on the cone
iff ascent on any of its finite generating sets). -/
theorem IsPolytope.not_mem_normalCone_iff (hF₀K : F₀ ≤ K) (hF₀ne : (F₀ : Set P).Nonempty)
    {s : Finset M} (hs : PointedCone.hull R (s : Set M) = K.tangentCone F₀)
    {φ : Module.Dual R M} :
    φ ∉ normalCone K F₀ ↔ ∃ v ∈ s, 0 < φ v := by
  rw [ConvexSet.not_mem_normalCone_iff hF₀K hF₀ne,
    ← PointedCone.exists_mem_pos_iff_exists_mem_finset_pos, hs]
  constructor
  · rintro ⟨x, hx, y, hy, hφ⟩
    exact ⟨y -ᵥ x, PointedCone.subset_hull ⟨y, hy, x, hx, rfl⟩, hφ⟩
  · rintro ⟨v, hv, hφv⟩
    obtain ⟨r, hr, y, hy, x, hx, hveq⟩ := (mem_tangentCone_iff K F₀ hF₀K hF₀ne v).mp hv
    refine ⟨x, hx, y, hy, ?_⟩
    rw [← hveq, map_smul, smul_eq_mul] at hφv
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · rw [← hr0] at hφv; simp at hφv
    · exact (mul_pos_iff_of_pos_left hr0).mp hφv

/-- **At a vertex, failure to be maximized is an ascent along an edge — tightly.** Unlike a naive
specialization of `IsPolytope.not_mem_normalCone_iff` (which would quantify over an arbitrary,
possibly redundant generating set of `K`), this quantifies only over directions `v` that are
*genuinely extreme*: `(PointedCone.hull R {v}).IsFaceOf (K.tangentCone {x₀})`, i.e. `v` spans an
actual 1-dimensional face of the tangent cone, the tangent direction of an honest edge of `K`
covering the vertex `{x₀}`. The witnessing finite set of such directions is produced by cone-level
Krein–Milman (`PointedCone.FG.krein_milman`) applied to `K.tangentCone {x₀}`, which is finitely
generated (`IsPolytope.tangentCone_singleton_fg`) and salient
(`tangentCone_salient_iff_subsingleton`, since `{x₀}` is a subsingleton) — exactly because `{x₀}`
is a face of `K` (a genuine vertex), not merely a point of `K`. -/
theorem IsPolytope.not_mem_normalCone_singleton_iff (hK : IsPolytope R (K : Set P)) {x₀ : P}
    (hx₀ : ({x₀} : ConvexSet R P).IsFaceOf K) {φ : Module.Dual R M} :
    φ ∉ normalCone K ({x₀} : ConvexSet R P) ↔
      ∃ v : M, (PointedCone.hull R {v}).IsFaceOf (K.tangentCone {x₀}) ∧
        0 < φ v := by
  rw [ConvexSet.not_mem_normalCone_iff_exists_mem_tangentCone]
  have hFG : (K.tangentCone ({x₀} : ConvexSet R P)).FG :=
    IsPolytope.tangentCone_singleton_fg hK x₀
  have hSal : (K.tangentCone ({x₀} : ConvexSet R P)).Salient :=
    (tangentCone_salient_iff_subsingleton hx₀ (Set.singleton_nonempty x₀)).mpr
      Set.subsingleton_singleton
  obtain ⟨t, ht, htray⟩ := PointedCone.FG.krein_milman hFG hSal
  constructor
  · rintro ⟨v, hv, hφv⟩
    have hvt : v ∈ PointedCone.hull R (t : Set M) := by rw [ht]; exact hv
    obtain ⟨w, hw, hφw⟩ := PointedCone.exists_mem_pos_iff_exists_mem_finset_pos.mp ⟨v, hvt, hφv⟩
    exact ⟨w, htray w hw, hφw⟩
  · rintro ⟨v, hFace, hφv⟩
    exact ⟨v, hFace.le (PointedCone.subset_hull rfl), hφv⟩

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **A subcone of a ray is trivial or the whole ray.** If `H ≤ hull R {v}` (`v ≠ 0`), then either
`H = ⊥` or `H = hull R {v}`: any nonzero `z ∈ H` is `z = c • v` for some `c > 0` (since
`z ∈ hull R {v}` and `z ≠ 0`), so `v = c⁻¹ • z ∈ H`, forcing `hull R {v} ≤ H` too. -/
private theorem _root_.PointedCone.eq_bot_or_eq_hull_singleton_of_le {v : M} (hv : v ≠ 0)
    {H : PointedCone R M} (hH : H ≤ PointedCone.hull R ({v} : Set M)) :
    H = ⊥ ∨ H = PointedCone.hull R ({v} : Set M) := by
  by_cases hHbot : H = ⊥
  · exact Or.inl hHbot
  · refine Or.inr (le_antisymm hH ?_)
    obtain ⟨z, hzH, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hHbot
    have hzray := hH hzH
    simp only [Submodule.mem_span_singleton, Subtype.exists, Nonneg.mk_smul,
      exists_prop] at hzray
    obtain ⟨c, hc, hcv⟩ := hzray
    have hc0 : 0 < c := lt_of_le_of_ne hc (fun h => hz0 (by simp [← hcv, ← h]))
    have hvH : v ∈ H := by
      have hveq : v = c⁻¹ • z := by rw [← hcv, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
      rw [hveq]
      exact H.smul_mem (inv_nonneg.mpr hc0.le) hzH
    exact Submodule.span_le.mpr (by rintro _ rfl; exact hvH)

/-- **At a vertex where `φ` is not maximized, there is an adjacent vertex `y` with `φ (y -ᵥ x) >
0`, and `{x, y}` is an edge of `K`.** From `not_mem_normalCone_singleton_iff`, get an ascent
direction `v` spanning a genuine face of `K.tangentCone {x}`; `G := Face.vadd_inf` of that face is
then a face of `K` with `G.tangentCone {x} = hull R {v}` (`tangentCone_vadd_inf`), hence (by
`span_tangentCone_eq_direction`) affine dimension exactly `1`. Since `{x}` has dimension `0`,
`G ≠ {x}`, so (`G` being a polytope, `= convexHull` of its vertices) `G` has some vertex `y ≠ x`;
`y -ᵥ x`, being a nonzero element of the ray `G.tangentCone {x} = hull R {v}`, is a positive
multiple of `v`, giving `0 < φ (y -ᵥ x)`. Any *other* vertex `w` of `G` is forced to equal `x` or
`y`: comparing its ratio along the ray to `y`'s, extremality of `w` (or of `y`) rules out `w`
lying strictly between `x` and `y`, or `y` lying strictly between `x` and `w`. So `G`'s vertex set
is exactly `{x, y}`, giving `G = convexHull R {x, y}`. -/
theorem IsPolytope.exists_vertex_edge_of_not_mem_normalCone_singleton
    (hK : IsPolytope R (K : Set P)) {x : P} (hx : ({x} : ConvexSet R P).IsFaceOf K)
    {φ : Module.Dual R M} (hφ : φ ∉ normalCone K ({x} : ConvexSet R P)) :
    ∃ y : P, ({y} : ConvexSet R P).IsFaceOf K ∧ 0 < φ (y -ᵥ x) ∧
      (convexHull R ({x, y} : Set P) : ConvexSet R P).IsFaceOf K := by
  classical
  obtain ⟨v, hFace, hφv⟩ := (IsPolytope.not_mem_normalCone_singleton_iff hK hx).mp hφ
  have hv0 : v ≠ 0 := fun h => by simp [h] at hφv
  have hxne : ({x} : Set P).Nonempty := Set.singleton_nonempty x
  set F' : PointedCone.Face (K.tangentCone ({x} : ConvexSet R P)) :=
    ⟨PointedCone.hull R ({v} : Set M), hFace⟩ with hF'_def
  set G : Face K := Face.vadd_inf F' with hG_def
  have hGtc : (G : ConvexSet R P).tangentCone ({x} : ConvexSet R P) =
      PointedCone.hull R ({v} : Set M) := tangentCone_vadd_inf hx hxne F'
  have hxleG : ({x} : ConvexSet R P) ≤ (G : ConvexSet R P) := fun z hz => by
    have hz' : z = x := hz
    rw [hz']
    exact (mem_Face_vadd_inf F').mpr
      ⟨hx.le rfl, x, rfl, by rw [vsub_self]; exact F'.toPointedCone.zero_mem⟩
  have hGpoly : IsPolytope R ((G : ConvexSet R P) : Set P) :=
    IsPolytope.face_isPolytope hK G.isFaceOf
  -- `G` has affine dimension exactly 1.
  have hspan : Submodule.span R ((G : ConvexSet R P).tangentCone ({x} : ConvexSet R P) :
      Set M) = (affineSpan R ((G : ConvexSet R P) : Set P)).direction :=
    span_tangentCone_eq_direction hxleG hxne
  have hspaneq : Submodule.span R (PointedCone.hull R ({v} : Set M) : Set M) =
      Submodule.span R ({v} : Set M) := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (PointedCone.hull_le_submodule_span _)
    · exact Submodule.span_mono PointedCone.subset_hull
  have hGfinrank : (G : ConvexSet R P).finrank = 1 := by
    change Module.finrank R (affineSpan R ((G : ConvexSet R P) : Set P)).direction = 1
    rw [← hspan, hGtc, hspaneq, finrank_span_singleton hv0]
  have hxfinrank : ({x} : ConvexSet R P).finrank = 0 := by
    change Module.finrank R (affineSpan R (({x} : ConvexSet R P) : Set P)).direction = 0
    have hbot : (affineSpan R (({x} : ConvexSet R P) : Set P)).direction = ⊥ := by
      rw [direction_affineSpan, vectorSpan_def]
      apply Submodule.span_eq_bot.mpr
      rintro w ⟨p, hp, q, hq, rfl⟩
      have hp' : p = x := hp
      have hq' : q = x := hq
      simp [hp', hq']
    rw [hbot]
    simp
  have hGnex : (G : ConvexSet R P) ≠ ({x} : ConvexSet R P) := fun h => by
    rw [h, hxfinrank] at hGfinrank; norm_num at hGfinrank
  -- `G` has a vertex `y ≠ x`.
  have hVney : ∃ y ∈ Vertices R (G : ConvexSet R P), y ≠ x := by
    by_contra hall
    push Not at hall
    apply hGnex
    apply le_antisymm _ hxleG
    have heq := IsPolytope.eq_convexHull_vertices R hGpoly
    have hGeq : (⟨((G : ConvexSet R P) : Set P), hGpoly.isConvexSet⟩ : ConvexSet R P) =
        (G : ConvexSet R P) := SetLike.coe_injective rfl
    rw [hGeq] at heq
    intro z hz
    have hz' : z ∈ (Convexity.convexHull R (Vertices R (G : ConvexSet R P)) : Set P) := heq ▸ hz
    have hzsub : Convexity.convexHull R (Vertices R (G : ConvexSet R P)) ⊆ ({x} : Set P) :=
      Convexity.convexHull_min (fun w hw => hall w hw) IsConvexSet.singleton
    exact hzsub hz'
  obtain ⟨y, hyV, hyne⟩ := hVney
  -- Every point of `G` other than `x` is `x +ᵥ c • (v)` along the ray, for a unique `c > 0`.
  have hratio : ∀ z : P, z ∈ (G : ConvexSet R P) → z ≠ x → ∃ c : R, 0 < c ∧ z -ᵥ x = c • v := by
    intro z hzG hzne
    have hzt : z -ᵥ x ∈ (G : ConvexSet R P).tangentCone ({x} : ConvexSet R P) :=
      PointedCone.subset_hull ⟨z, hzG, x, rfl, rfl⟩
    rw [hGtc] at hzt
    simp only [Submodule.mem_span_singleton, Subtype.exists, Nonneg.mk_smul, exists_prop] at hzt
    obtain ⟨c, hc, hcv⟩ := hzt
    refine ⟨c, lt_of_le_of_ne hc (fun h => hzne ?_), hcv.symm⟩
    have hz0 : z -ᵥ x = 0 := by rw [← hcv, ← h, zero_smul]
    rwa [vsub_eq_zero_iff_eq] at hz0
  have hyG : y ∈ (G : ConvexSet R P) := hyV.le rfl
  have hxG : x ∈ (G : ConvexSet R P) := hxleG rfl
  obtain ⟨c, hc0, hceq⟩ := hratio y hyG hyne
  have hφyx : 0 < φ (y -ᵥ x) := by
    rw [hceq, map_smul, smul_eq_mul]
    exact mul_pos hc0 hφv
  refine ⟨y, hyV.trans G.isFaceOf, hφyx, ?_⟩
  -- Every vertex of `G` other than `x` is `y`, so `G = convexHull R {x, y}`.
  have hVsub : Vertices R (G : ConvexSet R P) ⊆ ({x, y} : Set P) := by
    intro w hwV
    by_cases hwx : w = x
    · exact Or.inl hwx
    · refine Or.inr ?_
      have hwG : w ∈ (G : ConvexSet R P) := hwV.le rfl
      obtain ⟨cw, hcw0, hcweq⟩ := hratio w hwG hwx
      rcases lt_trichotomy cw c with hlt | heqc | hgt
      · exfalso
        have hweq : w = (cw / c) • (y -ᵥ x) +ᵥ x := by
          rw [← vsub_vadd w x, hcweq, hceq, smul_smul]
          congr 2
          field_simp
        have ha0 : (0 : R) < 1 - cw / c := by
          have : cw / c < 1 := (div_lt_one hc0).mpr hlt
          linarith
        have hb0 : (0 : R) < cw / c := by positivity
        have hab : (1 - cw / c) + cw / c = 1 := by ring
        have hwseg : w ∈ openSegment R y x :=
          ⟨cw / c, 1 - cw / c, hb0, ha0, by ring, by
            rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply]; exact hweq.symm⟩
        have hwseg' : w ∈ openSegment R x y := by rw [openSegment_symm]; exact hwseg
        have hxw : x = w := hwV.left_mem_of_mem_openSegment hxG hyG rfl hwseg'
        exact hwx hxw.symm
      · have hwyeq : w -ᵥ x = y -ᵥ x := by rw [hcweq, hceq, heqc]
        have : w = y := by rw [← vsub_vadd w x, hwyeq, vsub_vadd]
        rw [this]
        rfl
      · exfalso
        have hyeq : y = (c / cw) • (w -ᵥ x) +ᵥ x := by
          rw [← vsub_vadd y x, hceq, hcweq, smul_smul]
          congr 2
          field_simp
        have ha0 : (0 : R) < 1 - c / cw := by
          have : c / cw < 1 := (div_lt_one hcw0).mpr hgt
          linarith
        have hb0 : (0 : R) < c / cw := by positivity
        have hyseg : y ∈ openSegment R w x :=
          ⟨c / cw, 1 - c / cw, hb0, ha0, by ring, by
            rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply]; exact hyeq.symm⟩
        have hyseg' : y ∈ openSegment R x w := by rw [openSegment_symm]; exact hyseg
        have hxy : x = y := hyV.left_mem_of_mem_openSegment hxG hwG rfl hyseg'
        exact hyne hxy.symm
  have hGeqconv : (G : ConvexSet R P) = (convexHull R ({x, y} : Set P) : ConvexSet R P) := by
    apply le_antisymm
    · have heq := IsPolytope.eq_convexHull_vertices R hGpoly
      have hGeq : (⟨((G : ConvexSet R P) : Set P), hGpoly.isConvexSet⟩ : ConvexSet R P) =
          (G : ConvexSet R P) := SetLike.coe_injective rfl
      rw [hGeq] at heq
      intro z hz
      have hz' : z ∈ (Convexity.convexHull R (Vertices R (G : ConvexSet R P)) : Set P) :=
        heq ▸ hz
      exact Convexity.convexHull_mono hVsub hz'
    · apply Convexity.convexHull_min _ (G : ConvexSet R P).isConvexSet
      rintro z (rfl | rfl)
      · exact hxG
      · exact hyG
  rw [← hGeqconv]
  exact G.isFaceOf

/-- **Every vertex of a polytope is the exact (strict) maximizer of some linear form.** Since
`{x}` is a face, `K.tangentCone {x}` is finitely generated (`tangentCone_singleton_fg`) and
salient (`tangentCone_salient_iff_subsingleton`, as `{x}` is a subsingleton), so
`PointedCone.exists_pos_of_salient_fg` gives `φ'` strictly positive on
`K.tangentCone {x} \ {0}`. Negating, `φ := -φ'` is strictly negative on every nonzero
`y -ᵥ x` (`y ∈ K`, `y ≠ x`), i.e. `φ` attains its maximum over `K` *only* at `x`. -/
theorem IsPolytope.exists_maximized_exactly_at_vertex (hK : IsPolytope R (K : Set P)) {x : P}
    (hx : ({x} : ConvexSet R P).IsFaceOf K) :
    ∃ φ : Module.Dual R M, ∀ y ∈ K, y ≠ x → φ (y -ᵥ x) < 0 := by
  have hFG : (K.tangentCone ({x} : ConvexSet R P)).FG := IsPolytope.tangentCone_singleton_fg hK x
  have hSal : (K.tangentCone ({x} : ConvexSet R P)).Salient :=
    (tangentCone_salient_iff_subsingleton hx (Set.singleton_nonempty x)).mpr
      Set.subsingleton_singleton
  obtain ⟨φ', hφ'⟩ := PointedCone.exists_pos_of_salient_fg hFG hSal
  refine ⟨-φ', fun y hy hyne => ?_⟩
  have hv : y -ᵥ x ∈ K.tangentCone ({x} : ConvexSet R P) :=
    PointedCone.subset_hull ⟨y, hy, x, rfl, rfl⟩
  have hvne : y -ᵥ x ≠ 0 := vsub_ne_zero.mpr hyne
  have hpos : 0 < φ' (y -ᵥ x) := hφ' hv hvne
  simp only [LinearMap.neg_apply]
  linarith

end Field

end ConvexSet

end Convexity
