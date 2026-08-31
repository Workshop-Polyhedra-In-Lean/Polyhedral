
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

noncomputable section

namespace Convexity

open Pointwise

namespace ConvexSet

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P] --[ConvexSpace R P] [IsAffineConvexSpace R M P]

local instance : ConvexSpace R P := AddTorsor.toConvexSpace

variable {K : ConvexSet R P} {C : PointedCone R M} {x : P}

/-- The tangent cone over a face `F` a convex set `K`. -/
def tangentCone (K : ConvexSet R P) (F : Face K) : PointedCone R M :=
  PointedCone.hull R {y -ᵥ x | (y ∈ K) (x ∈ F)}

-- @[simp] lemma tangentCone_cone_coe_zero_eq_self (C : PointedCone R M) :
--     (C : ConvexSet R M).tangentCone (0 : M) = C := by simp [tangentCone]

end Ring

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P] -- [ConvexSpace R P] [IsAffineConvexSpace R M P]

local instance : ConvexSpace R P := AddTorsor.toConvexSpace

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

variable {K : ConvexSet R P} {C : PointedCone R M} {x : P}

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

private lemma vsub_set_isConvex (H : ConvexSet R P) (x : P) :
    IsConvexSet R {y -ᵥ x | y ∈ H} := by
  apply IsConvexSet.of_convexCombPair_mem
  rintro a b ha hb hab _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  refine ⟨convexCombPair a b ha hb hab p q,
    H.isConvexSet.convexCombPair_mem hp hq ha hb hab, ?_⟩
  rw [show convexCombPair a b ha hb hab (p -ᵥ x) (q -ᵥ x) =
    a • (p -ᵥ x) + b • (q -ᵥ x) from convexCombPair_eq_sum ..]
  exact convexCombPair_vsub a b ha hb hab p q x

lemma IsFaceOf.vadd_inf {x : P} {F : PointedCone R M} (hF : F.IsFaceOf (K.tangentCone x)) :
    IsFaceOf ((F.toConvexSet +ᵥ {x}) ⊓ K) K := by
  refine ⟨inf_le_right, ?_⟩
  intro p hp q hq z hz hzo
  rcases hzo with ⟨a, b, ha, hb, hab, hcomb⟩
  have hpT : p -ᵥ x ∈ K.tangentCone x := PointedCone.subset_hull ⟨p, hp, rfl⟩
  have hqT : q -ᵥ x ∈ K.tangentCone x := PointedCone.subset_hull ⟨q, hq, rfl⟩
  have hzF : z -ᵥ x ∈ F := by
    have hz' := hz.1
    change z ∈ ((F : Set M) +ᵥ ({x} : Set P)) at hz'
    rw [Set.vadd_singleton] at hz'
    rcases hz' with ⟨v, hv, rfl⟩
    simpa using hv
  have hsum : a • (p -ᵥ x) + b • (q -ᵥ x) ∈ F := by
    rw [← convexCombPair_vsub a b ha.le hb.le hab p q x, hcomb]
    exact hzF
  have hpF := hF.mem_of_smul_add_smul_mem_left hpT hqT ha hb hsum
  refine ⟨?_, hp⟩
  change p ∈ ((F : Set M) +ᵥ ({x} : Set P))
  rw [Set.vadd_singleton]
  exact ⟨p -ᵥ x, hpF, vsub_vadd p x⟩

def Face.vadd_inf {x : P} (F : PointedCone.Face (K.tangentCone x)) : Face K :=
  ⟨_, IsFaceOf.vadd_inf F.isFaceOf⟩

@[simp] lemma mem_Face_vadd_inf {x y : P} (F : PointedCone.Face (K.tangentCone x)) :
    y ∈ Face.vadd_inf F ↔ y ∈ K ∧ y -ᵥ x ∈ F := by
  constructor
  · rintro ⟨hy, hyK⟩
    change y ∈ ((F : Set M) +ᵥ {x}) at hy
    rw [Set.vadd_singleton] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨hyK, by simpa⟩
  · rintro ⟨hyK, hy⟩
    constructor
    · change y ∈ ((F : Set M) +ᵥ {x})
      rw [Set.vadd_singleton]
      exact ⟨y -ᵥ x, hy, vsub_vadd y x⟩
    · exact hyK

private lemma mem_tangentCone_iff (H : ConvexSet R P) {x : P} (hx : x ∈ H) (v : M) :
    v ∈ H.tangentCone x ↔ ∃ r : R, 0 ≤ r ∧ ∃ y ∈ H, r • (y -ᵥ x) = v := by
  rw [tangentCone]
  have hs : {y -ᵥ x | y ∈ H}.Nonempty := ⟨0, ⟨x, hx, vsub_self x⟩⟩
  have hc : IsConvexSet R {y -ᵥ x | y ∈ H} := vsub_set_isConvex H x
  have heq : v ∈ PointedCone.hull R {y -ᵥ x | y ∈ H} ↔
      v ∈ Set.Ici (0 : R) • {y -ᵥ x | y ∈ H} :=
    Set.ext_iff.mp (PointedCone.hull_eq_smul hs hc) v
  constructor
  · intro hv
    obtain ⟨r, hr, d, ⟨y, hy, rfl⟩, hd⟩ := heq.mp hv
    exact ⟨r, hr, y, hy, hd⟩
  · rintro ⟨r, hr, y, hy, hd⟩
    apply heq.mpr
    exact ⟨r, hr, y -ᵥ x, ⟨y, hy, rfl⟩, hd⟩

lemma IsFaceOf.tangentCone {F : ConvexSet R P} (hF : F.IsFaceOf K) (x : P) (hx : x ∈ F) :
    (F.tangentCone x).IsFaceOf (K.tangentCone x) := by
  refine ⟨PointedCone.hull_mono (fun _ ⟨y, hy, e⟩ ↦ ⟨y, hF.le hy, e⟩), ?_⟩
  intro u v a hu hv ha huv
  by_cases hu0 : u = 0
  · subst u
    exact (F.tangentCone x).zero_mem
  obtain ⟨r, hr, p, hp, hpu⟩ := (mem_tangentCone_iff K (hF.le hx) u).mp hu
  obtain ⟨s, hs, q, hq, hqv⟩ := (mem_tangentCone_iff K (hF.le hx) v).mp hv
  obtain ⟨t, ht, z, hz, hzw⟩ := (mem_tangentCone_iff F hx (a • u + v)).mp huv
  have hr0 : 0 < r := lt_of_le_of_ne hr <| by
    intro hr0
    apply hu0
    rw [← hpu, ← hr0, zero_smul]
  let D : R := 1 + a * r + s + t
  let c : R := D⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcD : c * D = 1 := by
    dsimp [c]
    exact inv_mul_cancel₀ (ne_of_gt hD)
  let A := c * a * r
  let B := c * s
  let C := c * t
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAB : A + B < 1 := by
    dsimp [A, B, D] at hcD ⊢
    have hrest : 0 < c * (1 + t) := mul_pos hc (by linarith)
    nlinarith
  have hC1 : C < 1 := by
    dsimp [C, D] at hcD ⊢
    have hrest : 0 < c * (1 + a * r + s) := mul_pos hc (by positivity)
    nlinarith
  have h1A : 0 < 1 - A := sub_pos.mpr
    (lt_of_le_of_lt (le_add_of_nonneg_right hB) hAB)
  have hratio0 : 0 ≤ B / (1 - A) := div_nonneg hB h1A.le
  have hratio1 : B / (1 - A) ≤ 1 := by
    apply (div_le_one h1A).2
    linarith
  let Q := convexCombPair (B / (1 - A)) (1 - B / (1 - A)) hratio0
    (sub_nonneg.mpr hratio1) (by ring) q x
  have hQK : Q ∈ K := K.isConvexSet.convexCombPair_mem hq (hF.le hx)
    hratio0 (sub_nonneg.mpr hratio1) (by ring)
  let w := convexCombPair A (1 - A) hA.le h1A.le (by ring) p Q
  have hwK : w ∈ K := K.isConvexSet.convexCombPair_mem hp hQK hA.le h1A.le (by ring)
  have hwopen : w ∈ openSegment R p Q := ⟨A, 1 - A, hA, h1A, by ring, rfl⟩
  have hwF : w ∈ F := by
    have heq : w = convexCombPair C (1 - C) hC (sub_nonneg.mpr hC1.le) (by ring) z x := by
      apply (vsub_left_injective x)
      dsimp [w, Q]
      rw [convexCombPair_vsub, convexCombPair_vsub, convexCombPair_vsub]
      rw [vsub_self, smul_zero, add_zero]
      dsimp [A, B, C]
      field_simp [ne_of_gt h1A]
      simp only [mul_smul]
      rw [hpu]
      have hden : 1 - c * a * r ≠ 0 := by
        dsimp [A] at h1A
        exact ne_of_gt h1A
      have hcoef : (1 - c * a * r) * (c * s / (1 - c * a * r)) = c * s := by
        field_simp [hden]
      rw [← mul_smul (1 - c * a * r) (c * s / (1 - c * a * r)) (q -ᵥ x)]
      rw [hcoef, mul_smul, hqv]
      rw [hzw]
      simp only [smul_zero, add_zero]
      module
    rw [heq]
    exact F.isConvexSet.convexCombPair_mem hz hx hC (sub_nonneg.mpr hC1.le) (by ring)
  have hpF := hF.left_mem_of_mem_openSegment hp hQK hwF hwopen
  rw [← hpu]
  exact (F.tangentCone x).smul_mem hr (PointedCone.subset_hull ⟨p, hpF, rfl⟩)

def Face.tangentCone {F : Face K} {x : P} (h : x ∈ F) : PointedCone.Face (K.tangentCone x) :=
  ⟨_, F.isFaceOf.tangentCone x h⟩

lemma convexHull_tagentCone_eq_hull_vsub (s : Set P) (x : P) :
    (convexHull R s).tangentCone x = PointedCone.hull R {v -ᵥ x | (v ∈ s)} := by
  let T : ConvexSet R M := convexHull R {v -ᵥ x | v ∈ s}
  have hvsub : {v -ᵥ x | v ∈ (convexHull R s : ConvexSet R P)} = (T : Set M) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hsU : s ⊆ ((T +ᵥ ({x} : ConvexSet R P)) : Set P) := by
        intro z hz
        change z ∈ ((T : Set M) +ᵥ ({x} : Set P))
        rw [Set.vadd_singleton]
        exact ⟨z -ᵥ x, Convexity.subset_convexHull_self ⟨z, hz, rfl⟩, vsub_vadd z x⟩
      have hyU : y ∈ T +ᵥ ({x} : ConvexSet R P) :=
        Convexity.convexHull_min hsU (T +ᵥ ({x} : ConvexSet R P)).isConvexSet hy
      have hyU' : y ∈ ((T : Set M) +ᵥ ({x} : Set P)) := hyU
      rw [Set.vadd_singleton] at hyU'
      obtain ⟨v, hv, rfl⟩ := hyU'
      simpa using hv
    · apply Convexity.convexHull_min
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, Convexity.subset_convexHull_self hy, rfl⟩
      · exact vsub_set_isConvex (convexHull R s) x
  rw [tangentCone, hvsub]
  exact PointedCone.hull_convexHull _

lemma IsPolytope.tangentCone_fg (hK : IsPolytope R (K : Set P)) (x : P) :
    (K.tangentCone x).FG := by classical
  obtain ⟨s, hs⟩ := hK
  use s.image fun y => y -ᵥ x
  rw [coe_eq_convexHull_iff] at hs
  rw [hs, convexHull_tagentCone_eq_hull_vsub, Finset.coe_image]
  congr

@[simp] lemma tangentCone_vadd_inf (x : P) (G : PointedCone.Face (K.tangentCone x)) :
    (Face.vadd_inf G : ConvexSet R P).tangentCone x = G := by
  rw [tangentCone]
  change PointedCone.hull R _ = G.toSubmodule
  rw [← G.isFaceOf.hull_inter_face_hull_inf_face]
  congr 1
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ Face.vadd_inf G at hy
    rw [mem_Face_vadd_inf] at hy
    exact ⟨⟨y, hy.1, rfl⟩, hy.2⟩
  · rintro ⟨⟨y, hyK, rfl⟩, hyG⟩
    exact ⟨y, mem_Face_vadd_inf G |>.2 ⟨hyK, hyG⟩, rfl⟩

@[simp] lemma vadd_inf_tangentCone (H : Face K) {x : P} (hx : x ∈ H) :
    Face.vadd_inf (H.tangentCone hx) = H := by
  ext y
  rw [mem_Face_vadd_inf]
  constructor
  · rintro ⟨hyK, hyT⟩
    by_cases hyx : y = x
    · simpa [hyx] using hx
    have hd0 : y -ᵥ x ≠ 0 := vsub_ne_zero.mpr hyx
    have hc : IsConvexSet R {z -ᵥ x | z ∈ (H : ConvexSet R P)} :=
      vsub_set_isConvex (H : ConvexSet R P) x
    change y -ᵥ x ∈ (H : ConvexSet R P).tangentCone x at hyT
    rw [tangentCone,
      PointedCone.mem_hull_iff_mem_pos_smul_of_convex_nonzero hc hd0] at hyT
    obtain ⟨r, hr, d, ⟨z, hz, rfl⟩, hd⟩ := hyT
    change r • (z -ᵥ x) = y -ᵥ x at hd
    have hyform : r • (z -ᵥ x) +ᵥ x = y := by
      rw [hd, vsub_vadd]
    by_cases hr1 : r ≤ 1
    · have hcomb := H.toConvexSet.isConvexSet.convexCombPair_mem hz hx
          hr.le (sub_nonneg.mpr hr1) (by ring)
      rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply, hyform] at hcomb
      exact hcomb
    · have h1r : 1 < r := lt_of_not_ge hr1
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      have hinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1r
      have hzform : r⁻¹ • (y -ᵥ x) +ᵥ x = z := by
        rw [← hd, ← mul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul, vsub_vadd]
      apply H.isFaceOf.left_mem_of_mem_openSegment hyK (H.isFaceOf.le hx) hz
      refine ⟨r⁻¹, 1 - r⁻¹, hinv, sub_pos.mpr hinv1, by ring, ?_⟩
      rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply, hzform]
  · intro hy
    exact ⟨H.isFaceOf.le hy, PointedCone.subset_hull ⟨y, hy, rfl⟩⟩

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
lemma tangentCone_mono {A B : ConvexSet R P} (hAB : A ≤ B) (x : P) :
    A.tangentCone x ≤ B.tangentCone x := by
  apply PointedCone.hull_mono
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hAB hy, rfl⟩

def tangentCone_ici_orderIso (x : P) {F : Face K} (h : x ∈ relint (F : ConvexSet R P)) :
    PointedCone.Face (K.tangentCone x) ≃o Set.Ici F where
  toFun G := ⟨Face.vadd_inf G, Face.le_of_mem_relint h <|
    mem_Face_vadd_inf G |>.2 ⟨F.isFaceOf.le (relint_le h), by
      rw [vsub_self]
      exact G.toPointedCone.zero_mem⟩⟩
  invFun G := G.1.tangentCone (G.2 (relint_le h))
  left_inv G := by
    simp [Face.tangentCone]
  right_inv G := by
    apply Subtype.ext
    exact vadd_inf_tangentCone G.1 (G.2 (relint_le h))
  map_rel_iff' {G₁ G₂} := by
    constructor
    · intro hG
      change G₁.toPointedCone ≤ G₂.toPointedCone
      rw [← tangentCone_vadd_inf x G₁, ← tangentCone_vadd_inf x G₂]
      exact tangentCone_mono hG x
    · intro hG y hy
      change y ∈ Face.vadd_inf G₁ at hy
      change y ∈ Face.vadd_inf G₂
      rw [mem_Face_vadd_inf] at hy ⊢
      exact ⟨hy.1, hG hy.2⟩

lemma foo (F G : Face K) (hF : F ≤ G) (x : P) (h : x ∈ relint (F : ConvexSet R P)) :
    Module.finrank R (affineSpan R (G : Set P)).direction
      = Module.finrank R (Submodule.span R ((tangentCone_ici_orderIso x h).symm ⟨G, hF⟩ : Set M)) :=
    sorry

end Field

end ConvexSet

end Convexity
