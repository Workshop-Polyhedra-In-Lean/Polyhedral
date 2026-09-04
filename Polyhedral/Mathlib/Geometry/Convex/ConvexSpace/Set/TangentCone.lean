/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Pointwise

/-! # The tangent cone of a convex set at a face

This file is about general convex sets; the polytope-specific finite-generation statements are in
`Polytope/TangentCone.lean`. -/

noncomputable section

namespace Convexity

open Pointwise

namespace ConvexSet

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P] --[ConvexSpace R P] [IsAffineConvexSpace R M P]

local instance : ConvexSpace R P := AddTorsor.toConvexSpace

variable {K : ConvexSet R P} {C : PointedCone R M}

/-- The tangent cone of `K` at `F`: the cone of directions from points of `F` towards points of
`K`. The interesting case is when `F.IsFaceOf K` ("the tangent cone over the face `F`"), but the
definition itself makes sense for any `F`. `F` is deliberately a bare `ConvexSet R P`, not a
bundled `Face K`, so that the *same* `F` can be compared across different ambient convex sets
(e.g. in `tangentCone_mono`, `IsFaceOf.tangentCone`) without running into the fact that
`ConvexSet.Face` is a type depending on its ambient set. -/
def tangentCone (K F : ConvexSet R P) : PointedCone R M :=
  PointedCone.hull R {y -ᵥ x | (y ∈ K) (x ∈ F)}

end Ring

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P] -- [ConvexSpace R P] [IsAffineConvexSpace R M P]

local instance : ConvexSpace R P := AddTorsor.toConvexSpace

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

variable {K : ConvexSet R P} {C : PointedCone R M}

section Relint

-- TODO: move

/-- The algebraic relative interior, defined as the non-extreme points. -/
def relint (K : ConvexSet R P) : ConvexSet R P where
  carrier := {x | x ∈ K ∧ ∀ F : Face K, x ∈ F → F = ⊤}
  isConvexSet := by
    apply IsConvexSet.of_convexCombPair_mem
    rintro a b ha hb hab p hp q hq
    refine ⟨K.isConvexSet.convexCombPair_mem hp.1 hq.1 ha hb hab, ?_⟩
    intro F hF
    by_cases ha' : 0 < a
    · by_cases hb' : 0 < b
      · exact hp.2 F <| F.isFaceOf.left_mem_of_mem_openSegment hp.1 hq.1 hF
          ⟨a, b, ha', hb', hab, rfl⟩
      · have hb0 : b = 0 := le_antisymm (le_of_not_gt hb') hb
        subst b
        have ha1 : a = 1 := by simpa using hab
        subst a
        exact hp.2 F (by simpa using hF)
    · have ha0 : a = 0 := le_antisymm (le_of_not_gt ha') ha
      subst a
      have hb1 : b = 1 := by simpa using hab
      subst b
      exact hq.2 F (by simpa using hF)

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
lemma relint_le : K.relint ≤ K := fun _ hx ↦ hx.1

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
lemma Face.le_of_mem_relint {F G : Face K} {x : P} (hxF : x ∈ relint (F : ConvexSet R P))
    (hxG : x ∈ G) : F ≤ G := by
  let H : Face (F : ConvexSet R P) :=
    ⟨(G : ConvexSet R P) ⊓ F,
      (IsFaceOf.isFaceOf_iff _ F.isFaceOf).2 ⟨inf_le_right, G.isFaceOf.inf_left F.isFaceOf⟩⟩
  have hH : H = ⊤ := hxF.2 H ⟨hxG, hxF.1⟩
  intro y hy
  have hyH : y ∈ H := by
    rw [hH]
    exact hy
  exact hyH.1

end Relint

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
private lemma convexCombPair_vsub (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (p q x : P) :
    convexCombPair a b ha hb hab p q -ᵥ x = a • (p -ᵥ x) + b • (q -ᵥ x) := by
  rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply, vadd_vsub_assoc]
  rw [← vsub_add_vsub_cancel p q x]
  have hb' : b = 1 - a := by linarith
  rw [hb']
  module

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- The "double" version of `convexCombPair_vsub`, combining two *different* base points `x`, `y`
along with `p`, `q` (using the same weights `a, b` throughout). Needed to show the two-point
difference set `{y -ᵥ x | y ∈ H, x ∈ F}` (the underlying set of `tangentCone`) is convex, since
elements of `H` and of `F` now vary independently. -/
private lemma convexCombPair_vsub_convexCombPair (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (p q x y : P) :
    convexCombPair a b ha hb hab p q -ᵥ convexCombPair a b ha hb hab x y =
      a • (p -ᵥ x) + b • (q -ᵥ y) := by
  have h1 := convexCombPair_vsub a b ha hb hab p q x
  have h2 := convexCombPair_vsub a b ha hb hab x y x
  rw [vsub_self, smul_zero, zero_add] at h2
  rw [← vsub_sub_vsub_cancel_right (convexCombPair a b ha hb hab p q)
    (convexCombPair a b ha hb hab x y) x, h1, h2]
  rw [show q -ᵥ x = (q -ᵥ y) + (y -ᵥ x) from (vsub_add_vsub_cancel q y x).symm]
  module

/-- The difference set underlying `tangentCone` is convex: `H` and `F` vary independently, but a
convex combination of two differences is again a single difference, of the combined points
(`convexCombPair_vsub_convexCombPair`). -/
private lemma vsub_set_isConvex (H F : ConvexSet R P) :
    IsConvexSet R {y -ᵥ x | (y ∈ H) (x ∈ F)} := by
  apply IsConvexSet.of_convexCombPair_mem
  rintro a b ha hb hab _ ⟨p, hp, x, hx, rfl⟩ _ ⟨q, hq, y, hy, rfl⟩
  refine ⟨convexCombPair a b ha hb hab p q, H.isConvexSet.convexCombPair_mem hp hq ha hb hab,
    convexCombPair a b ha hb hab x y, F.isConvexSet.convexCombPair_mem hx hy ha hb hab, ?_⟩
  rw [show convexCombPair a b ha hb hab (p -ᵥ x) (q -ᵥ y) =
    a • (p -ᵥ x) + b • (q -ᵥ y) from convexCombPair_eq_sum ..]
  exact convexCombPair_vsub_convexCombPair a b ha hb hab p q x y

/-- **Explicit representatives for `tangentCone`.** Since `{y -ᵥ x | y ∈ H, x ∈ F}` is convex
(`vsub_set_isConvex`), its hull is just its positive scalings: a single `r • (y -ᵥ x)` already
describes every element, no finite sums needed. -/
theorem mem_tangentCone_iff (H F : ConvexSet R P) (hFH : F ≤ H)
    (hFne : (F : Set P).Nonempty) (v : M) :
    v ∈ H.tangentCone F ↔ ∃ r : R, 0 ≤ r ∧ ∃ y ∈ H, ∃ x ∈ F, r • (y -ᵥ x) = v := by
  rw [tangentCone]
  obtain ⟨x₀, hx₀⟩ := hFne
  have hs : {v : M | ∃ y ∈ H, ∃ x ∈ F, y -ᵥ x = v}.Nonempty :=
    ⟨0, x₀, hFH hx₀, x₀, hx₀, vsub_self x₀⟩
  have hc : IsConvexSet R {v : M | ∃ y ∈ H, ∃ x ∈ F, y -ᵥ x = v} := vsub_set_isConvex H F
  have heq : v ∈ PointedCone.hull R {v : M | ∃ y ∈ H, ∃ x ∈ F, y -ᵥ x = v} ↔
      v ∈ Set.Ici (0 : R) • {v : M | ∃ y ∈ H, ∃ x ∈ F, y -ᵥ x = v} :=
    Set.ext_iff.mp (PointedCone.hull_eq_smul hs hc) v
  constructor
  · intro hv
    obtain ⟨r, hr, d, ⟨y, hy, x, hx, rfl⟩, hd⟩ := heq.mp hv
    exact ⟨r, hr, y, hy, x, hx, hd⟩
  · rintro ⟨r, hr, y, hy, x, hx, hd⟩
    apply heq.mpr
    exact ⟨r, hr, y -ᵥ x, ⟨y, hy, x, hx, rfl⟩, hd⟩

/-- **The lineality space of `K.tangentCone F₀` is the direction of `F₀`'s affine span** — this
confirms the geometric picture: when `F₀` is a vertex, `K.tangentCone F₀` is salient (pointed);
once `F₀` has positive dimension, every direction *within* `F₀` is reversible in the tangent cone
(`x' -ᵥ x` and its negative are both attainable, using `x, x' ∈ F₀` as the two base points), and
those are exactly the lineal directions. The `⊆` direction uses `F₀.IsFaceOf K`: if `v` and `-v`
are both `r • (y -ᵥ x)`/`s • (y' -ᵥ x')` for `y, y' ∈ K`, `x, x' ∈ F₀`, then a weighted average of
`y, y'` coincides with a weighted average of `x, x' ∈ F₀`, exhibiting that common point as both an
element of `F₀` and an interior point of the segment `[y, y']` — the face property then forces
`y ∈ F₀` too, so `y -ᵥ x` (and hence `v`) already lies in the direction of `F₀`. -/
theorem tangentCone_lineal {F₀ : ConvexSet R P} (hF₀K : F₀.IsFaceOf K)
    (hF₀ne : (F₀ : Set P).Nonempty) :
    (K.tangentCone F₀).lineal = (affineSpan R (F₀ : Set P)).direction := by
  rw [direction_affineSpan, vectorSpan_def]
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hv1, hv2⟩ := PointedCone.mem_lineal.mp hv
    obtain ⟨r, hr, y, hy, x, hx, hrxy⟩ := (mem_tangentCone_iff K F₀ hF₀K.le hF₀ne v).mp hv1
    obtain ⟨s, hs, y', hy', x', hx', hsxy⟩ :=
      (mem_tangentCone_iff K F₀ hF₀K.le hF₀ne (-v)).mp hv2
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · rw [← hr0, zero_smul] at hrxy
      rw [← hrxy]; exact Submodule.zero_mem _
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · have hv0 : v = 0 := by
        rw [← hs0, zero_smul] at hsxy
        exact neg_eq_zero.mp hsxy.symm
      rw [hv0]; exact Submodule.zero_mem _
    have hrs : 0 < r + s := by positivity
    have hkey : r • (y -ᵥ x) + s • (y' -ᵥ x') = 0 := by rw [hrxy, hsxy]; abel
    have ha0 : (0 : R) ≤ r / (r + s) := by positivity
    have hb0 : (0 : R) ≤ s / (r + s) := by positivity
    have hab : r / (r + s) + s / (r + s) = 1 := by field_simp
    have hpeq : convexCombPair (r / (r + s)) (s / (r + s)) ha0 hb0 hab y y' =
        convexCombPair (r / (r + s)) (s / (r + s)) ha0 hb0 hab x x' := by
      rw [← vsub_eq_zero_iff_eq, convexCombPair_vsub_convexCombPair]
      have hscale : (r / (r + s)) • (y -ᵥ x) + (s / (r + s)) • (y' -ᵥ x') =
          (r + s)⁻¹ • (r • (y -ᵥ x) + s • (y' -ᵥ x')) := by
        rw [smul_add, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul]
      rw [hscale, hkey, smul_zero]
    have hpF₀ : convexCombPair (r / (r + s)) (s / (r + s)) ha0 hb0 hab x x' ∈ F₀ :=
      F₀.isConvexSet.convexCombPair_mem hx hx' ha0 hb0 hab
    have hpopen : convexCombPair (r / (r + s)) (s / (r + s)) ha0 hb0 hab y y' ∈
        openSegment R y y' :=
      ⟨r / (r + s), s / (r + s), div_pos hr0 hrs, div_pos hs0 hrs, hab, rfl⟩
    have hyF₀ : y ∈ F₀ := hF₀K.left_mem_of_mem_openSegment hy hy' (hpeq ▸ hpF₀) hpopen
    have hspan : y -ᵥ x ∈ Submodule.span R ((F₀ : Set P) -ᵥ (F₀ : Set P)) :=
      Submodule.subset_span ⟨y, hyF₀, x, hx, rfl⟩
    rw [← hrxy]
    exact Submodule.smul_mem _ r hspan
  · exact Submodule.span_le.mpr (by
      rintro v ⟨x', hx', x, hx, rfl⟩
      rw [SetLike.mem_coe, PointedCone.mem_lineal]
      refine ⟨PointedCone.subset_hull ⟨x', hF₀K.le hx', x, hx, rfl⟩, ?_⟩
      have hmem : x -ᵥ x' ∈ K.tangentCone F₀ :=
        PointedCone.subset_hull ⟨x, hF₀K.le hx, x', hx', rfl⟩
      simpa [neg_vsub_eq_vsub_rev] using hmem)

/-- **Confirms the geometric picture directly**: the tangent cone over a face is salient
(pointed) exactly when that face is a single point — matching the classical fact that tangent
cones are pointed at vertices, and necessarily have a nontrivial lineality space over any
higher-dimensional face. -/
theorem tangentCone_salient_iff_subsingleton {F₀ : ConvexSet R P} (hF₀K : F₀.IsFaceOf K)
    (hF₀ne : (F₀ : Set P).Nonempty) :
    (K.tangentCone F₀).Salient ↔ (F₀ : Set P).Subsingleton := by
  rw [PointedCone.salient_iff_lineal_bot, tangentCone_lineal hF₀K hF₀ne, direction_affineSpan,
    vectorSpan_eq_bot_iff_subsingleton]

/-- If `F'` is a face of `K`'s tangent cone at `F₀`, translating `F'` by `F₀` and intersecting
with `K` gives a face of `K` (the face "generated by moving from `F₀` in directions `F'`"). -/
lemma IsFaceOf.vadd_inf {F₀ : ConvexSet R P} {F' : PointedCone R M}
    (hF' : F'.IsFaceOf (K.tangentCone F₀)) :
    IsFaceOf ((F'.toConvexSet +ᵥ F₀) ⊓ K) K := by
  refine ⟨inf_le_right, ?_⟩
  intro p hp q hq z hz hzo
  rcases hzo with ⟨a, b, ha, hb, hab, hcomb⟩
  have hz' : z ∈ ((F'.toConvexSet : Set M) +ᵥ (F₀ : Set P)) := hz.1
  obtain ⟨v, hv, x, hx, hzeq⟩ := hz'
  have hpT : p -ᵥ x ∈ K.tangentCone F₀ := PointedCone.subset_hull ⟨p, hp, x, hx, rfl⟩
  have hqT : q -ᵥ x ∈ K.tangentCone F₀ := PointedCone.subset_hull ⟨q, hq, x, hx, rfl⟩
  have hzF : z -ᵥ x ∈ F' := by rw [← hzeq, vadd_vsub]; exact hv
  have hsum : a • (p -ᵥ x) + b • (q -ᵥ x) ∈ F' := by
    rw [← convexCombPair_vsub a b ha.le hb.le hab p q x, hcomb]
    exact hzF
  have hpF' := hF'.mem_of_smul_add_smul_mem_left hpT hqT ha hb hsum
  refine ⟨?_, hp⟩
  change p ∈ ((F'.toConvexSet : Set M) +ᵥ (F₀ : Set P))
  exact ⟨p -ᵥ x, hpF', x, hx, vsub_vadd p x⟩

def Face.vadd_inf {F₀ : ConvexSet R P} (F' : PointedCone.Face (K.tangentCone F₀)) : Face K :=
  ⟨_, IsFaceOf.vadd_inf F'.isFaceOf⟩

@[simp] lemma mem_Face_vadd_inf {F₀ : ConvexSet R P} {y : P}
    (F' : PointedCone.Face (K.tangentCone F₀)) :
    y ∈ Face.vadd_inf F' ↔ y ∈ K ∧ ∃ x ∈ F₀, y -ᵥ x ∈ F' := by
  constructor
  · rintro ⟨hy, hyK⟩
    obtain ⟨v, hv, x, hx, rfl⟩ := hy
    exact ⟨hyK, x, hx, by simpa⟩
  · rintro ⟨hyK, x, hx, hy⟩
    exact ⟨⟨y -ᵥ x, hy, x, hx, vsub_vadd y x⟩, hyK⟩

/-!
### `IsFaceOf.tangentCone`

For a *single* base point `x` (i.e. `F₀ = {x}`), the classical Carathéodory-style argument shows
that a face `F` of `K` at `x` gives a face `F.tangentCone {x}` of `K.tangentCone {x}`: every
tangent vector used in the argument (`u`, `v`, and the witness for `a • u + v`) is measured
relative to the *same* point `x`, so `convexCombPair_vsub` (single base point) suffices to make
the algebra close.

Once `F₀` is allowed to be a genuine multi-point face, `u ∈ K.tangentCone F₀`, `v ∈ K.tangentCone
F₀`, and the witness for `u + v ∈ F.tangentCone F₀` each come with their *own*, generally
different, base points `xp, xq, xz ∈ F₀` (`mem_tangentCone_iff` only gives one existential witness
per element, it does not let you pick a common one). Two things make this tractable despite that:

1. Mathlib's `PointedCone.IsFaceOf.of_mem_of_add_mem_left` shows that, over a division ring, the
   face condition only needs checking for a *sum* `u + v ∈ F.tangentCone F₀` (coefficient `1` on
   both), not a general positive combination `a • u + v` — one fewer parameter to carry around.
2. The three base points don't need to be reconciled pairwise; instead, `F₀`'s own convexity lets
   *all three* be folded into a single point `X := combo(xp, xq)` and, together with `p, q`, a
   single point `W` — and a direct barycentric identity (see the proof) shows `W` coincides with
   `Z := combo(z, X)`, which is visibly in `F` since `z ∈ F` and `X ∈ F₀ ⊆ F`. The face property
   of `F` in `K`, applied to `W ∈ openSegment R p Q` (`Q := combo(q, xz)`), then gives `p ∈ F`
   directly. -/

/-- **The face relation lifts to tangent cones over the same `F₀`.** Uses Mathlib's
`PointedCone.IsFaceOf.of_mem_of_add_mem_left`: over a division ring, it suffices to check that
`u + v ∈ F.tangentCone F₀` (for `u, v ∈ K.tangentCone F₀`) forces `u ∈ F.tangentCone F₀` — no
scalar coefficient to juggle. Writing `u = r•(p -ᵥ xp)`, `v = s•(q -ᵥ xq)`,
`u + v = t•(z -ᵥ xz)` (`p, q ∈ K`, `z ∈ F`, `xp, xq, xz ∈ F₀`), the identity
`r•(xp -ᵥ xz) + s•(xq -ᵥ xz) + [r•(p -ᵥ xp) + s•(q -ᵥ xq)] = r•(p -ᵥ xz) + s•(q -ᵥ xz)`
combined with `r•(p -ᵥ xp) + s•(q -ᵥ xq) = t•(z -ᵥ xz)` shows that a single weighted average `W`
of `p` and `Q := combo(q, xz)` coincides with a weighted average `Z` of `z` and
`X := combo(xp, xq)` — the latter manifestly in `F` (`z ∈ F`, `X ∈ F₀ ⊆ F`, `F` convex), the
former manifestly in the open segment `(p, Q)`. The face property of `F` in `K` then forces
`p ∈ F` directly: no need to reconcile `xp`, `xq`, `xz` against each other individually, only to
translate them (via `F₀`'s own convexity) into the single point `X`. -/
lemma IsFaceOf.tangentCone {F F₀ : ConvexSet R P} (hF : F.IsFaceOf K) (hF₀F : F₀ ≤ F)
    (hF₀ne : (F₀ : Set P).Nonempty) :
    (F.tangentCone F₀).IsFaceOf (K.tangentCone F₀) := by
  have hF₀K : F₀ ≤ K := hF₀F.trans hF.le
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · apply PointedCone.hull_mono
    rintro _ ⟨y, hy, x, hx, rfl⟩
    exact ⟨y, hF.le hy, x, hx, rfl⟩
  · intro u v hu hv huv
    obtain ⟨r, hr, p, hp, xp, hxp, hup⟩ := (mem_tangentCone_iff K F₀ hF₀K hF₀ne u).mp hu
    obtain ⟨s, hs, q, hq, xq, hxq, hvq⟩ := (mem_tangentCone_iff K F₀ hF₀K hF₀ne v).mp hv
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · rw [← hup, ← hr0, zero_smul]
      exact (F.tangentCone F₀).zero_mem
    obtain ⟨t, ht, z, hz, xz, hxz, hzw⟩ :=
      (mem_tangentCone_iff F F₀ hF₀F hF₀ne (u + v)).mp huv
    have hkey : r • (p -ᵥ xp) + s • (q -ᵥ xq) = t • (z -ᵥ xz) := by rw [hup, hvq, hzw]
    rcases eq_or_lt_of_le (add_nonneg hs ht) with hst0 | hst0
    · obtain ⟨hs0, ht0⟩ := (add_eq_zero_iff_of_nonneg hs ht).mp hst0.symm
      have hv0 : v = 0 := by rw [← hvq, hs0, zero_smul]
      have hu0 : u = 0 := by
        have huv0 : u + v = 0 := by rw [← hzw, ht0, zero_smul]
        rwa [hv0, add_zero] at huv0
      rw [hu0]
      exact (F.tangentCone F₀).zero_mem
    · have hD : (0 : R) < r + s + t := by positivity
      have hDne : (r + s + t : R) ≠ 0 := ne_of_gt hD
      have hst : (0 : R) < s + t := hst0
      have hrs : (0 : R) < r + s := by positivity
      have hSt : (0 : R) ≤ s / (s + t) := by positivity
      have hTt : (0 : R) ≤ t / (s + t) := by positivity
      have hSTt : s / (s + t) + t / (s + t) = 1 := by field_simp
      have hrD : (0 : R) ≤ r / (r + s + t) := by positivity
      have hstD : (0 : R) ≤ (s + t) / (r + s + t) := by positivity
      have hrstD : r / (r + s + t) + (s + t) / (r + s + t) = 1 := by field_simp; ring
      have hRS : (0 : R) ≤ r / (r + s) := by positivity
      have hSrs : (0 : R) ≤ s / (r + s) := by positivity
      have hRSrs : r / (r + s) + s / (r + s) = 1 := by field_simp
      have htD : (0 : R) ≤ t / (r + s + t) := by positivity
      have hrsD : (0 : R) ≤ (r + s) / (r + s + t) := by positivity
      have htrsD : t / (r + s + t) + (r + s) / (r + s + t) = 1 := by field_simp; ring
      set Q := convexCombPair (s / (s + t)) (t / (s + t)) hSt hTt hSTt q xz with hQ_def
      have hQK : Q ∈ K := K.isConvexSet.convexCombPair_mem hq (hF₀K hxz) hSt hTt hSTt
      set W := convexCombPair (r / (r + s + t)) ((s + t) / (r + s + t)) hrD hstD hrstD p Q
        with hW_def
      have hWK : W ∈ K := K.isConvexSet.convexCombPair_mem hp hQK hrD hstD hrstD
      set X := convexCombPair (r / (r + s)) (s / (r + s)) hRS hSrs hRSrs xp xq with hX_def
      have hXF₀ : X ∈ F₀ := F₀.isConvexSet.convexCombPair_mem hxp hxq hRS hSrs hRSrs
      set Z := convexCombPair (t / (r + s + t)) ((r + s) / (r + s + t)) htD hrsD htrsD z X
        with hZ_def
      have hZF : Z ∈ F := F.isConvexSet.convexCombPair_mem hz (hF₀F hXF₀) htD hrsD htrsD
      have hWZ : W = Z := by
        have hQx : Q -ᵥ xz = (s / (s + t)) • (q -ᵥ xz) := by
          rw [hQ_def, convexCombPair_vsub _ _ hSt hTt hSTt q xz xz, vsub_self, smul_zero,
            add_zero]
        have hWx : W -ᵥ xz = (r / (r + s + t)) • (p -ᵥ xz) + (s / (r + s + t)) • (q -ᵥ xz) := by
          rw [hW_def, convexCombPair_vsub _ _ hrD hstD hrstD p Q xz, hQx, smul_smul]
          congr 2
          field_simp
        have hXx : X -ᵥ xz =
            (r / (r + s)) • (xp -ᵥ xz) + (s / (r + s)) • (xq -ᵥ xz) := by
          rw [hX_def, convexCombPair_vsub _ _ hRS hSrs hRSrs xp xq xz]
        have hZx : Z -ᵥ xz = (t / (r + s + t)) • (z -ᵥ xz) + (r / (r + s + t)) • (xp -ᵥ xz) +
            (s / (r + s + t)) • (xq -ᵥ xz) := by
          rw [hZ_def, convexCombPair_vsub _ _ htD hrsD htrsD z X xz, hXx, smul_add, smul_smul,
            smul_smul,
            show (r + s) / (r + s + t) * (r / (r + s)) = r / (r + s + t) from by field_simp,
            show (r + s) / (r + s + t) * (s / (r + s)) = s / (r + s + t) from by field_simp]
          abel
        have hscale : (r / (r + s + t)) • (p -ᵥ xp) + (s / (r + s + t)) • (q -ᵥ xq) =
            (t / (r + s + t)) • (z -ᵥ xz) := by
          have h2 := congrArg ((r + s + t : R)⁻¹ • ·) hkey
          simp only [smul_add, smul_smul] at h2
          simp only [div_eq_mul_inv]
          rwa [mul_comm r, mul_comm s, mul_comm t]
        have heq : W -ᵥ xz = Z -ᵥ xz := by
          rw [hWx, hZx,
            show p -ᵥ xz = (p -ᵥ xp) + (xp -ᵥ xz) from (vsub_add_vsub_cancel p xp xz).symm,
            show q -ᵥ xz = (q -ᵥ xq) + (xq -ᵥ xz) from (vsub_add_vsub_cancel q xq xz).symm,
            smul_add, smul_add]
          rw [show (r / (r + s + t)) • (p -ᵥ xp) + (r / (r + s + t)) • (xp -ᵥ xz) +
              ((s / (r + s + t)) • (q -ᵥ xq) + (s / (r + s + t)) • (xq -ᵥ xz)) =
              ((r / (r + s + t)) • (p -ᵥ xp) + (s / (r + s + t)) • (q -ᵥ xq)) +
                (r / (r + s + t)) • (xp -ᵥ xz) + (s / (r + s + t)) • (xq -ᵥ xz)
            from by abel, hscale]
        calc W = (W -ᵥ xz) +ᵥ xz := (vsub_vadd W xz).symm
          _ = (Z -ᵥ xz) +ᵥ xz := by rw [heq]
          _ = Z := vsub_vadd Z xz
      have hWseg : W ∈ openSegment R p Q :=
        ⟨r / (r + s + t), (s + t) / (r + s + t), by positivity, by positivity, hrstD, rfl⟩
      have hpF : p ∈ F := hF.left_mem_of_mem_openSegment hp hQK (hWZ ▸ hZF) hWseg
      rw [← hup]
      exact (F.tangentCone F₀).smul_mem hr (PointedCone.subset_hull ⟨p, hpF, xp, hxp, rfl⟩)

def Face.tangentCone {F : Face K} {F₀ : ConvexSet R P} (h : F₀ ≤ (F : ConvexSet R P))
    (hF₀ne : (F₀ : Set P).Nonempty) :
    PointedCone.Face (K.tangentCone F₀) :=
  ⟨_, F.isFaceOf.tangentCone h hF₀ne⟩

theorem convexHull_tangentCone_eq_hull_vsub (s : Set P) (F₀ : ConvexSet R P) :
    (convexHull R s).tangentCone F₀ = PointedCone.hull R {v -ᵥ x | (v ∈ s) (x ∈ F₀)} := by
  let T : ConvexSet R M := convexHull R {v -ᵥ x | (v ∈ s) (x ∈ F₀)}
  have hvsub : {v -ᵥ x | (v ∈ (convexHull R s : ConvexSet R P)) (x ∈ F₀)} = (T : Set M) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, x, hx, rfl⟩
      have hsU : s ⊆ ((T +ᵥ ({x} : ConvexSet R P)) : Set P) := by
        intro z hz
        change z ∈ ((T : Set M) +ᵥ ({x} : Set P))
        exact ⟨z -ᵥ x, Convexity.subset_convexHull_self ⟨z, hz, x, hx, rfl⟩, x, rfl, vsub_vadd z x⟩
      have hyU : y ∈ T +ᵥ ({x} : ConvexSet R P) :=
        Convexity.convexHull_min hsU (T +ᵥ ({x} : ConvexSet R P)).isConvexSet hy
      have hyU' : y ∈ ((T : Set M) +ᵥ ({x} : Set P)) := hyU
      obtain ⟨v, hv, x', rfl, rfl⟩ := hyU'
      simpa using hv
    · apply Convexity.convexHull_min
      · rintro _ ⟨y, hy, x, hx, rfl⟩
        exact ⟨y, Convexity.subset_convexHull_self hy, x, hx, rfl⟩
      · exact vsub_set_isConvex (convexHull R s) F₀
  rw [tangentCone, hvsub]
  exact PointedCone.hull_convexHull _

/-- **Recovering a face of the tangent cone from its `vadd_inf`.** Uses `tangentCone_lineal` +
Mathlib's `PointedCone.IsFaceOf.lineal_le` (every face of a cone contains the cone's lineality
space): the mismatch between two different base points `x, x₀ ∈ F₀` used to witness membership is
always a difference of `F₀`-points, i.e. a lineal direction of `K.tangentCone F₀` — and since `G`
(any face of that cone) already contains the whole lineality space, this mismatch is absorbed by
`G` directly, with no need to reconcile the base points via convex combinations. -/
@[simp]
lemma tangentCone_vadd_inf {F₀ : ConvexSet R P} (hF₀K : F₀.IsFaceOf K)
    (hF₀ne : (F₀ : Set P).Nonempty) (G : PointedCone.Face (K.tangentCone F₀)) :
    (Face.vadd_inf G : ConvexSet R P).tangentCone F₀ = G := by
  have hlin : (K.tangentCone F₀).lineal ≤ (G : PointedCone R M) := G.isFaceOf.lineal_le
  have hF₀sub : F₀ ≤ (Face.vadd_inf G : ConvexSet R P) := fun x hx =>
    (mem_Face_vadd_inf G).mpr ⟨hF₀K.le hx, x, hx, by rw [vsub_self]; exact G.toPointedCone.zero_mem⟩
  ext v
  rw [mem_tangentCone_iff (Face.vadd_inf G : ConvexSet R P) F₀ hF₀sub hF₀ne]
  constructor
  · rintro ⟨r, hr, y, hy, x, hx, rfl⟩
    obtain ⟨hyK, x₀, hx₀, hyx₀⟩ := (mem_Face_vadd_inf G).mp hy
    have hxx₀ : x -ᵥ x₀ ∈ (K.tangentCone F₀).lineal := by
      rw [tangentCone_lineal hF₀K hF₀ne, direction_affineSpan, vectorSpan_def]
      exact Submodule.subset_span ⟨x, hx, x₀, hx₀, rfl⟩
    have hx₀x : x₀ -ᵥ x ∈ (K.tangentCone F₀).lineal := by
      rw [← neg_vsub_eq_vsub_rev x x₀]
      exact Submodule.neg_mem _ hxx₀
    have hsplit : y -ᵥ x = (y -ᵥ x₀) + (x₀ -ᵥ x) := (vsub_add_vsub_cancel y x₀ x).symm
    rw [hsplit, smul_add]
    exact G.toPointedCone.add_mem (G.toPointedCone.smul_mem hr hyx₀)
      (G.toPointedCone.smul_mem hr (hlin hx₀x))
  · intro hvG
    have hvK : v ∈ K.tangentCone F₀ := G.isFaceOf.le hvG
    obtain ⟨r, hr, y, hy, x, hx, hrxy⟩ := (mem_tangentCone_iff K F₀ hF₀K.le hF₀ne v).mp hvK
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · have hv0 : v = 0 := by rw [← hrxy, ← hr0, zero_smul]
      obtain ⟨x₀, hx₀⟩ := hF₀ne
      exact ⟨0, le_refl 0, x₀, hF₀sub hx₀, x₀, hx₀, by rw [hv0, zero_smul]⟩
    · refine ⟨r, hr0.le, y, ?_, x, hx, hrxy⟩
      have hyx : y -ᵥ x ∈ (G : PointedCone R M) := by
        have hmem := G.toPointedCone.smul_mem (inv_nonneg.mpr hr0.le) hvG
        rwa [← hrxy, smul_smul, inv_mul_cancel₀ (ne_of_gt hr0), one_smul] at hmem
      exact (mem_Face_vadd_inf G).mpr ⟨hy, x, hx, hyx⟩

/-- **Recovering a face `H` of `K` from its own tangent cone at `F₀`.** No lineality-space
bookkeeping is needed here (unlike `IsFaceOf.tangentCone`): given `y -ᵥ x ∈ H.tangentCone F₀`
(witnessed by `r`, `z ∈ H`, `x' ∈ F₀`), the weights `r/(r+1)` and `1/(r+1)` exhibit a *single*
common point as both `combo(z, x, ·)` (visibly in `H`, since `x ∈ F₀ ⊆ H`) and `combo(y, x', ·)`
(visibly in the open segment `(y, x')`, since both weights are positive) — the face property of
`H` in `K` then forces `y ∈ H` directly, with no need to reconcile `x` against a second,
independently-chosen witness point `x'`. Stated at the level of set membership (rather than
through `Face.tangentCone`) since it's used by `tangentCone_ici_orderIso.right_inv` before
`Face.tangentCone`'s own bundling is convenient there. -/
theorem mem_iff_mem_tangentCone (H : Face K) {F₀ : ConvexSet R P}
    (hF₀ : F₀ ≤ (H : ConvexSet R P)) (hF₀ne : (F₀ : Set P).Nonempty) {y : P} :
    y ∈ H ↔ y ∈ K ∧ ∃ x ∈ F₀, y -ᵥ x ∈ (H : ConvexSet R P).tangentCone F₀ := by
  constructor
  · intro hyH
    obtain ⟨x₀, hx₀⟩ := hF₀ne
    exact ⟨H.isFaceOf.le hyH, x₀, hx₀, PointedCone.subset_hull ⟨y, hyH, x₀, hx₀, rfl⟩⟩
  · rintro ⟨hyK, x, hx, hyT⟩
    obtain ⟨r, hr, z, hz, x', hx', hrxy⟩ :=
      (mem_tangentCone_iff (H : ConvexSet R P) F₀ hF₀ hF₀ne (y -ᵥ x)).mp hyT
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · have hyx : y = x := by rw [← vsub_eq_zero_iff_eq, ← hrxy, ← hr0, zero_smul]
      rw [hyx]; exact hF₀ hx
    have hr1 : (0 : R) < r + 1 := by positivity
    have ha0 : (0 : R) < r / (r + 1) := by positivity
    have hb0 : (0 : R) < 1 / (r + 1) := by positivity
    have hab : r / (r + 1) + 1 / (r + 1) = 1 := by field_simp
    have hab' : 1 / (r + 1) + r / (r + 1) = 1 := by field_simp; ring
    have h1 : convexCombPair (r / (r + 1)) (1 / (r + 1)) ha0.le hb0.le hab z x -ᵥ x =
        (r / (r + 1)) • (z -ᵥ x) := by
      rw [convexCombPair_vsub _ _ ha0.le hb0.le hab z x x, vsub_self, smul_zero, add_zero]
    have h2 : convexCombPair (1 / (r + 1)) (r / (r + 1)) hb0.le ha0.le hab' y x' -ᵥ x =
        (1 / (r + 1)) • (y -ᵥ x) + (r / (r + 1)) • (x' -ᵥ x) :=
      convexCombPair_vsub _ _ hb0.le ha0.le hab' y x' x
    have h3 : (r / (r + 1)) • (z -ᵥ x) =
        (1 / (r + 1)) • (y -ᵥ x) + (r / (r + 1)) • (x' -ᵥ x) := by
      rw [← hrxy, show z -ᵥ x = (z -ᵥ x') + (x' -ᵥ x) from (vsub_add_vsub_cancel z x' x).symm]
      module
    have hcombeq : convexCombPair (r / (r + 1)) (1 / (r + 1)) ha0.le hb0.le hab z x =
        convexCombPair (1 / (r + 1)) (r / (r + 1)) hb0.le ha0.le hab' y x' := by
      calc convexCombPair (r / (r + 1)) (1 / (r + 1)) ha0.le hb0.le hab z x
          = (r / (r + 1)) • (z -ᵥ x) +ᵥ x := by rw [← h1, vsub_vadd]
        _ = ((1 / (r + 1)) • (y -ᵥ x) + (r / (r + 1)) • (x' -ᵥ x)) +ᵥ x := by rw [h3]
        _ = convexCombPair (1 / (r + 1)) (r / (r + 1)) hb0.le ha0.le hab' y x' := by
            rw [← h2, vsub_vadd]
    have hpH : convexCombPair (r / (r + 1)) (1 / (r + 1)) ha0.le hb0.le hab z x ∈ H :=
      H.toConvexSet.isConvexSet.convexCombPair_mem hz (hF₀ hx) ha0.le hb0.le hab
    have hx'K : x' ∈ K := H.isFaceOf.le (hF₀ hx')
    have hpseg : convexCombPair (1 / (r + 1)) (r / (r + 1)) hb0.le ha0.le hab' y x' ∈
        openSegment R y x' :=
      ⟨1 / (r + 1), r / (r + 1), hb0, ha0, hab', rfl⟩
    exact H.isFaceOf.left_mem_of_mem_openSegment hyK hx'K (hcombeq ▸ hpH) hpseg

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
theorem tangentCone_mono {A B : ConvexSet R P} (hAB : A ≤ B) (F₀ : ConvexSet R P) :
    A.tangentCone F₀ ≤ B.tangentCone F₀ := by
  apply PointedCone.hull_mono
  rintro _ ⟨y, hy, x, hx, rfl⟩
  exact ⟨y, hAB hy, x, hx, rfl⟩

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- `tangentCone` is also monotone in its second (`F`) argument: more points to move away from
only ever adds more difference vectors, hence a bigger hull. -/
theorem tangentCone_mono_right {A B : ConvexSet R P} (hAB : A ≤ B) (K : ConvexSet R P) :
    K.tangentCone A ≤ K.tangentCone B := by
  apply PointedCone.hull_mono
  rintro _ ⟨y, hy, x, hx, rfl⟩
  exact ⟨y, hy, x, hAB hx, rfl⟩

/-- **The tangent cone over a face is the tangent cone at any one of its points, plus the
lineality space.** This is the "cone over a vertex, summed with the lineality space" picture:
every generator `y -ᵥ x` of `K.tangentCone F₀` splits as `(y -ᵥ x₀) + (x₀ -ᵥ x)`, a single-point
tangent direction plus a lineal direction (`x, x₀ ∈ F₀`), giving `≤`; the reverse inclusion is
`tangentCone_mono_right` (`{x₀} ≤ F₀`) together with `PointedCone.lineal_le`. Used to reduce
`IsPolytope.tangentCone_fg` to `IsPolytope.tangentCone_singleton_fg` plus finite generation of the
lineality space. -/
theorem tangentCone_eq_tangentCone_singleton_sup_lineal {F₀ : ConvexSet R P}
    (hF₀K : F₀.IsFaceOf K) {x₀ : P} (hx₀ : x₀ ∈ F₀) :
    K.tangentCone F₀ = K.tangentCone ({x₀} : ConvexSet R P) ⊔
      ((K.tangentCone F₀).lineal : PointedCone R M) := by
  have hF₀ne : (F₀ : Set P).Nonempty := ⟨x₀, hx₀⟩
  apply le_antisymm
  · rw [tangentCone]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, x, hx, rfl⟩
    have h1 : y -ᵥ x₀ ∈ K.tangentCone ({x₀} : ConvexSet R P) :=
      PointedCone.subset_hull ⟨y, hy, x₀, rfl, rfl⟩
    have h2 : x₀ -ᵥ x ∈ ((K.tangentCone F₀).lineal : PointedCone R M) := by
      rw [tangentCone_lineal hF₀K hF₀ne, direction_affineSpan, vectorSpan_def]
      exact Submodule.subset_span ⟨x₀, hx₀, x, hx, rfl⟩
    rw [SetLike.mem_coe,
      show y -ᵥ x = (y -ᵥ x₀) + (x₀ -ᵥ x) from (vsub_add_vsub_cancel y x₀ x).symm]
    exact Submodule.add_mem _ (SetLike.le_def.mp le_sup_left h1)
      (SetLike.le_def.mp le_sup_right h2)
  · exact sup_le (tangentCone_mono_right (Set.singleton_subset_iff.mpr hx₀) K)
      (PointedCone.lineal_le (K.tangentCone F₀))

/-- **Faces of `K.tangentCone F₀` correspond exactly to faces of `K` above `F₀`**, when `F₀`
itself is already a face of `K` (`hF₀K`) — the payoff of `IsFaceOf.tangentCone` /
`tangentCone_vadd_inf` / `mem_iff_mem_tangentCone`. (There is no room here for `F₀` to be some
smaller convex set with `F₀ ≤ F` for a genuinely bigger minimal containing face `F`: since `F₀` is
already a face, it is trivially its own smallest containing face — any `G : Face K` with
`F₀ ≤ G` and `G ≤ F₀` forces `G = F₀`. So the target is `Set.Ici` of `F₀` itself, bundled as a
face via `hF₀K`, not a separate `F`.) -/
def tangentCone_ici_orderIso (F₀ : ConvexSet R P) (hF₀K : F₀.IsFaceOf K)
    (hF₀ne : (F₀ : Set P).Nonempty) :
    PointedCone.Face (K.tangentCone F₀) ≃o Set.Ici (⟨F₀, hF₀K⟩ : Face K) where
  toFun G := ⟨Face.vadd_inf G, fun x hx => (mem_Face_vadd_inf G).mpr
    ⟨hF₀K.le hx, x, hx, by rw [vsub_self]; exact G.toPointedCone.zero_mem⟩⟩
  invFun G := G.1.tangentCone (G.2 : (⟨F₀, hF₀K⟩ : Face K) ≤ G.1) hF₀ne
  left_inv G := by
    apply PointedCone.Face.toPointedCone_eq_iff.mp
    change (Face.vadd_inf G : ConvexSet R P).tangentCone F₀ = (G : PointedCone R M)
    exact tangentCone_vadd_inf hF₀K hF₀ne G
  right_inv G := by
    apply Subtype.ext
    ext y
    change y ∈ Face.vadd_inf
      (G.1.tangentCone (G.2 : (⟨F₀, hF₀K⟩ : Face K) ≤ G.1) hF₀ne) ↔ y ∈ G.1
    rw [mem_Face_vadd_inf]
    exact (mem_iff_mem_tangentCone G.1 (G.2 : (⟨F₀, hF₀K⟩ : Face K) ≤ G.1) hF₀ne).symm
  map_rel_iff' {G₁ G₂} := by
    constructor
    · intro hG
      change G₁.toPointedCone ≤ G₂.toPointedCone
      rw [← tangentCone_vadd_inf hF₀K hF₀ne G₁, ← tangentCone_vadd_inf hF₀K hF₀ne G₂]
      exact tangentCone_mono hG F₀
    · intro hG y hy
      change y ∈ Face.vadd_inf G₁ at hy
      change y ∈ Face.vadd_inf G₂
      rw [mem_Face_vadd_inf] at hy ⊢
      obtain ⟨hyK, x, hx, hyx⟩ := hy
      exact ⟨hyK, x, hx, hG hyx⟩


end Field

end ConvexSet

end Convexity
