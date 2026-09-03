/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.HPolyhedron
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic


section Homogenization

open Convexity Pointwise Set PointedCone Submodule
open Convexity.ConvexSet

section Field

-- TODO: Several results in this file could be stated for rings
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {V' : Type*} [AddCommGroup V'] [Module 𝕜 V']
variable {W : Type*} [AddCommGroup W] [Module 𝕜 W]

variable {A : Type*} [AddTorsor V A]


attribute [local instance] AddTorsor.toConvexSpace

section Homogenize

open Convex

variable [IsModuleConvexSpace 𝕜 W]
variable [hom : Affine.IsHomogenization 𝕜 A W]


lemma dehomogenize_homogenize_isHPolyhedron {P : Set A} (hP : IsHPolyhedron 𝕜 P) :
    ∃C : PointedCone 𝕜 W,
      IsHPolyhedral .id C ∧
      ((C ⊔ homogenize W hP.toConvexSet).dehomogenize A) = P := by
  obtain ⟨H, h_gen⟩ := hP
  sorry


-- def homogenize_inequalities (H : Finset (A →ᵃ[𝕜] 𝕜)) :=
--   (H.map (⇑hom.lift 𝕜)).insert (hom.weight)

-- lemma dehomogenize_homogenize_inequalities (H : Finset (A →ᵃ[𝕜] 𝕜)) :
--     ⋂ dehomogenize (homogenize_inequalities H) = ⋂ H :=
--   sorry

-- Could be for `ConvexSet` (to avoid polluting the `Set` namespace)
-- This definiton assigns ⊤ as the recession cone of ∅
-- The ∀ could be an ∃ (we could prove it's equivalent for polytopes)
-- For `ConvexSet`, the ∀a is not necessary
variable (𝕜) in
def Convex.Set.recessionCone (P : Set A) : PointedCone 𝕜 V where
  carrier := { v : V | ∀ x ∈ P, ∀ a : 𝕜, 0 ≤ a → a • v +ᵥ x ∈ P }
  add_mem' {_ b} ha hb x hx c hc := by simp [add_vadd, ha (c • b +ᵥ x) (hb x hx c hc) c hc]
  zero_mem' _ hx _ _ := by simp [hx]
  smul_mem' := fun ⟨c, hc⟩ _ h y hy a ha ↦ by
    simp [smul_smul, h y hy (a * c) (Right.mul_nonneg ha hc)]

lemma Convex.Set.mem_recessionCone {P : Set A} {v : V} :
    v ∈ P.recessionCone 𝕜 ↔ ∀ x ∈ P, ∀ a : 𝕜, 0 ≤ a → a • v +ᵥ x ∈ P := Iff.rfl


-- TODO-status the following lemma currently use complicated AI generated stuff
-- should be doable easier.
/-- For a nonempty H-polyhedron, membership in the recession cone can be tested at a single
point: a direction recedes from every point as soon as it recedes from one. -/
lemma IsHPolyhedron.mem_recessionCone_iff_exists {P : Set A} (hP : IsHPolyhedron 𝕜 P)
    (hne : P.Nonempty) {v : V} :
    v ∈ P.recessionCone 𝕜 ↔ ∃ x ∈ P, ∀ a : 𝕜, 0 ≤ a → a • v +ᵥ x ∈ P := by
  rw [Convex.Set.mem_recessionCone]
  exact hP.forall_smul_vadd_mem_iff_exists hne

-- status: seems good and useful
/-- The sup of two recession cones is contained in the recession cone of the Minkowski sum -/
lemma Convex.Set.sup_recessionCone_le_recessionCone_vadd
    {P : Set V} {Q : Set A} :
    P.recessionCone 𝕜 ⊔ Q.recessionCone 𝕜 ≤ (P +ᵥ Q).recessionCone 𝕜 := by
  intro v hv
  rw [Submodule.mem_sup] at hv
  rcases hv with ⟨y, hy, z, hz, rfl⟩
  intro a ha r hr
  rw [Set.mem_vadd] at ha
  rcases ha with ⟨p, hp, q, hq, rfl⟩
  have h1 : r • y +ᵥ p ∈ P := hy p hp r hr
  have h2 : r • z +ᵥ q ∈ Q := hz q hq r hr
  have : (r • y +ᵥ p) +ᵥ (r • z +ᵥ q) ∈ P +ᵥ Q := Set.vadd_mem_vadd h1 h2
  simpa [← add_vadd, add_comm, add_assoc]

-- status: seems good and useful
/-- The recession cone cannot shrink when adding a set -/
lemma Convex.Set.recessionCone_le_recessionCone_vadd_left
    {P : Set V} {Q : Set A} :
    P.recessionCone 𝕜 ≤ (P +ᵥ Q).recessionCone 𝕜 :=
  le_trans le_sup_left sup_recessionCone_le_recessionCone_vadd

-- status: seems good and useful
/-- The recession cone cannot shrink when adding a set -/
lemma Convex.Set.recessionCone_le_recessionCone_vadd_right
    {P : Set V} {Q : Set A} :
    Q.recessionCone 𝕜 ≤ (P +ᵥ Q).recessionCone 𝕜 :=
  le_trans le_sup_right sup_recessionCone_le_recessionCone_vadd

-- status: seems good and useful
/-- The recession cone of a cone is the cone itself. -/
lemma PointedCone.recessionCone_eq_self (C : PointedCone 𝕜 V) :
    (C : Set V).recessionCone 𝕜 = C := by
  ext x
  constructor
  · intro hx
    simpa using hx 0 C.zero_mem 1
  · intro hx y hy a ha
    have hax : a • x ∈ C := C.smul_mem ha hx
    exact C.add_mem hax hy

-- status: needs to be proven, using MW for cones or a weak MW version that does
-- not explicitly talk about the recession cone.
-- potential strategy for the difficult (not yet proven) direction:
-- write C as an intersection of a half-space and linear inequalities.
-- need to prove that v lies in that halfspace and satisfies all the
-- inequalities. Use that v lies in the recession cone of C + Q.
-- That means, for all a in 𝕜, x in C + Q, we have that x + a • v
-- is still in C + Q. Assume v violates one of the defining inequalities
-- of C. Choose an a that's large enough such that a • v violates this
-- defining inequality by more than any point in the (bounded) polytope Q
-- can "repair" it. This gives a contradiction to v being in the recession cone.
--
-- This requires some notion of boundedness of a polytope w.r.t. a linear form
-- (namely the considered defining linear inequality of C).
-- That should probably follow from basic convexity, but I am unsure how much
-- is implemented in Geometry/Convex and available in mathlib / PRs.
lemma PointedCone.recessionCone_vadd_eq_left
    (C : PointedCone 𝕜 V) {Q : Set A}
    (hC : C.IsHPolyhedral .id)
    (hQ : IsPolytope 𝕜 Q) (hne : Q.Nonempty) :
    ((C : Set V) +ᵥ Q).recessionCone 𝕜 = C := by
  ext v
  constructor
  · intro hv
    sorry
  · intro h
    apply Convex.Set.recessionCone_le_recessionCone_vadd_left
    rw [recessionCone_eq_self]
    exact h


-- TODO status: this should follow from the previous lemma without too much
-- hassle, needs to be proven.
lemma Convex.Set.recessionCone_vadd {P : Set V} {Q : Set A}
    (hP : IsHPolyhedron 𝕜 P) (hQ : IsHPolyhedron 𝕜 Q) :
    (P +ᵥ Q).recessionCone 𝕜 = P.recessionCone 𝕜 ⊔ Q.recessionCone 𝕜 := by
  ext v
  constructor
  · intro hv
    sorry
  · apply sup_recessionCone_le_recessionCone_vadd

-- TODO-status: this was generated by Moritz, but it seems fine.
-- Potentially it can alternatively be deduced from the lemmas above.
/-- Minkowski addition of a set P and its recession cone leaves P unchanged. -/
lemma Convex.Set.recessionCone_vadd_self {P : Set A} :
    (P.recessionCone 𝕜 : Set V) +ᵥ P = P := by
  ext x
  refine ⟨fun ⟨v, hv, y, hy, h⟩ ↦ ?_,
    fun hx ↦ ⟨0, (P.recessionCone 𝕜).zero_mem, x, hx, zero_vadd _ _⟩⟩
  simpa [h] using (Convex.Set.mem_recessionCone.mp hv) y hy 1 zero_le_one


-- TODO-status: this was generated by Moritz, it should now be MUCH easier with
-- the lemmas above.
/-- The recession cone of a nonempty polytope is trivial: any nonzero direction admits a
linear functional positive on it, which is bounded on the convex hull of the finitely many
generators. -/
lemma Convexity.IsPolytope.recessionCone_eq_bot {P : Set A} (hP : IsPolytope 𝕜 P)
    (hne : P.Nonempty) : P.recessionCone 𝕜 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra! hv0
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝕜 V, f v ≠ 0 := by
    by_contra! hcon
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff 𝕜 v).mp hcon)
  obtain ⟨x₀, hx₀⟩ := hne
  set g : Module.Dual 𝕜 V := (f v)⁻¹ • f with hg
  set h : A →ᵃ[𝕜] 𝕜 := g.toAffineMap.comp (AffineEquiv.vaddConst 𝕜 x₀).symm.toAffineMap
    with hhdef
  obtain ⟨t, rfl⟩ := hP
  have hte : t.Nonempty := by
    obtain rfl | hte := Finset.eq_empty_or_nonempty t
    · simp at hx₀
    · exact hte
  have hbound : ∀ y ∈ Convexity.convexHull 𝕜 (t : Set A), h y ≤ t.sup' hte h := by
    intro y hy
    exact convexHull_min (fun s hs => Finset.le_sup' h hs)
      ((isConvexSet_Iic (t.sup' hte h)).preimage h.isAffineMap) hy
  have hray : ∀ a : 𝕜, 0 ≤ a → a ≤ t.sup' hte h := by
    intro a ha
    have hb := hbound _ ((Convex.Set.mem_recessionCone.mp hv) x₀ hx₀ a ha)
    simp_all
  have h0 : (0 : 𝕜) ≤ t.sup' hte h := hray 0 le_rfl
  have := hray (t.sup' hte h + 1) (by linarith)
  linarith

-- TODO-status: unclear whether we use / want the lemma here.
-- It's not in good shape, and it should probably fall out of our MW proof machinery
-- somehow.
#click_suggestions
lemma IsHPolyhedron.recessionCone_isHPolyhedral {P : Set A} (hP : IsHPolyhedron 𝕜 P) :
    IsHPolyhedral .id (P.recessionCone 𝕜) := by
  classical
  by_cases h : ∅ = P
  · simp only [Convex.Set.recessionCone, h.symm, mem_empty_iff_false, imp_false, not_le,
      IsEmpty.forall_iff, implies_true, ofPred_true]
    exact IsHPolyhedral.top _
  -- We need to use a point in `P` for the proof below
  obtain ⟨x, hx : x ∈ P⟩ := Set.nonempty_iff_empty_ne.mpr h
  sorry
--   obtain ⟨H₁, ⟨S₁, rfl⟩⟩ := hP

--   unfold IsHPolyhedral Set.recessionCone
--   let P := (⋂ h ∈ H₁, ⇑h ⁻¹' Ici 0) ∩ ↑S₁
--   let C := H₁.image (·.linear)

--   simp only [IsHPolyhedral, Set.recessionCone, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici,
--     SetLike.mem_coe, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, and_imp,
--     exists_and_left]
--   use (PointedCone.dual .id C)
--   constructor
--   · exact DualFG.dual_of_finset .id C
--   · use S₁.direction
--     ext v
--     simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_ofPred_eq,
--       Finset.coe_preimage, mem_inf, PointedCone.mem_dual, mem_preimage,
--       SetLike.mem_coe, restrictScalars_mem]

--     constructor
--     · intro h
--       specialize h x
--       specialize h (by
--         intro i hi
--         simp at hx
--         simp [hi, hx]
--       )
--       sorry
--       -- specialize h (by
--       --   simp at hx
--       --   simp [hx]
--       --   sorry
--       -- )
--       -- constructor
--       -- · intro w hw
--       --   -- have hf : ∃f ∈ H₁, p w = f.linear := match (hC' (p w)).mp hw with
--       --   --   | ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ => ⟨f, ⟨hf, h_eq⟩⟩
--       --   -- have h_zero : ∃a ∈ A, (p w) a = 0,
--       --   -- obtain ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ := (hC' (p w)).mp hw
--       --   -- let ker := f ⁻¹' {0}
--       --   -- let k := f.linear.zero
--       --   -- have i := p w
--       --   sorry
--       -- · sorry
--     · intro ⟨hv, hvs⟩ y hyP hyS a ha
--       constructor
--       · intro i hi
--         have hiP := hyP i hi
--         -- have hc := (hC i).mp hi
--         sorry
--       · have h_av : a • v ∈ S₁.direction := by exact Submodule.smul_mem S₁.direction a hvs
--         exact (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h_av).mpr hyS

variable (W) in
def homogenize_with_recession (S : ConvexSet 𝕜 A) : PointedCone 𝕜 W :=
  homogenize W S ⊔ ((S : Set A).recessionCone 𝕜).map hom.ofVector

-- TODO: This lemma doesn't need Field
/-- A convex cone is contained in the same submodules as its generators. -/
lemma PointedCone.hull_le {G : Set V} {S : Submodule 𝕜 V} (hG : G ⊆ S)
    : PointedCone.hull 𝕜 G ≤ S := by
  intro x hx
  obtain ⟨c, ⟨hc₁, hc₂, rfl⟩⟩ := PointedCone.mem_hull_set.mp hx
  apply Submodule.finsuppSum_mem
  intro y hy
  specialize hc₂ y
  rw [smul_mem_iff]
  · apply mem_of_subset_of_mem (subset_trans hc₁ hG)
    simp [c.mem_support_iff.mpr hy]
  · -- NOTE: Why does linarith fail here?
    exact lt_of_le_of_ne hc₂ hy.symm

#click_suggestions
lemma homogenize_with_recession_nonneg (S : ConvexSet 𝕜 A) :
    (homogenize_with_recession W S) ≤ hom.weight.nonneg := by
  unfold homogenize_with_recession
  apply sup_le
  · unfold homogenize
    have h := hom.ofPoint_range_eq_preimage_weight_one
    -- have h' := PointedCone.hull_le
    sorry
  · have h := hom.ofVector_range_eq_weight_ker
    sorry

def PointedCone.homogenized_recessionCone (C : PointedCone 𝕜 W) : PointedCone 𝕜 W :=
  C ⊓ PointedCone.ofSubmodule hom.weight.ker

noncomputable
def PointedCone.homogenized_pos {C : PointedCone 𝕜 W} (hC : C.FG) : PointedCone 𝕜 W := by
  classical
  unfold PointedCone.FG Submodule.FG at hC
  choose S hS using hC

  sorry


-- def dehomogenize_with_recession (C : PointedCone 𝕜 W) : ConvexSet 𝕜 A :=
--   ⟨hom.ofPoint ⁻¹' C⟩

end Homogenize
end Field
end Homogenization
