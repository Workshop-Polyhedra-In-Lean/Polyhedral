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

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {V' : Type*} [AddCommGroup V'] [Module R V']
variable {W : Type*} [AddCommGroup W] [Module R W]

variable {A : Type*} [AddTorsor V A]


attribute [local instance] AddTorsor.toConvexSpace

section Homogenize

open Convex

variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]


-- Could be for `ConvexSet` (to avoid polluting the `Set` namespace)
-- This definiton assigns ⊤ as the recession cone of ∅
-- The ∀ could be an ∃ (we could prove it's equivalent for polytopes)
-- For `ConvexSet`, the ∀a is not necessary
variable (R) in
def Convex.Set.recessionCone (P : Set A) : PointedCone R V where
  carrier := { v : V | ∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P }
  add_mem' {_ b} ha hb x hx c hc := by simp [add_vadd, ha (c • b +ᵥ x) (hb x hx c hc) c hc]
  zero_mem' _ hx _ _ := by simp [hx]
  smul_mem' := fun ⟨c, hc⟩ _ h y hy a ha ↦ by
    simp [smul_smul, h y hy (a * c) (Right.mul_nonneg ha hc)]

lemma Convex.Set.mem_recessionCone {P : Set A} {v : V} :
    v ∈ P.recessionCone R ↔ ∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P := Iff.rfl

/-- For a nonempty H-polyhedron, membership in the recession cone can be tested at a single
point: a direction recedes from every point as soon as it recedes from one. -/
lemma IsHPolyhedron.mem_recessionCone_iff_exists {P : Set A} (hP : IsHPolyhedron R P)
    (hne : P.Nonempty) {v : V} :
    v ∈ P.recessionCone R ↔ ∃ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P := by
  rw [Convex.Set.mem_recessionCone]
  exact hP.forall_smul_vadd_mem_iff_exists hne

/-- The sup of two recession cones is contained in the recession cone of the Minkowski sum -/
lemma Convex.Set.sup_recessionCone_le_recessionCone_vadd
    {P : Set V} {Q : Set A} :
    P.recessionCone R ⊔ Q.recessionCone R ≤ (P +ᵥ Q).recessionCone R := by
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

/-- The recession cone cannot shrink when adding a set -/
lemma Convex.Set.recessionCone_le_recessionCone_vadd_left
    {P : Set V} {Q : Set A} :
    P.recessionCone R ≤ (P +ᵥ Q).recessionCone R :=
  le_trans le_sup_left sup_recessionCone_le_recessionCone_vadd

/-- The recession cone cannot shrink when adding a set -/
lemma Convex.Set.recessionCone_le_recessionCone_vadd_right
    {P : Set V} {Q : Set A} :
    Q.recessionCone R ≤ (P +ᵥ Q).recessionCone R :=
  le_trans le_sup_right sup_recessionCone_le_recessionCone_vadd

-- TODO this probably needs MW to be proven, so it cannot be used to prove MW.
lemma Convex.Set.recessionCone_vadd {P : Set V} {Q : Set A}
    (hP : IsHPolyhedron R P) (hQ : IsHPolyhedron R Q) :
    (P +ᵥ Q).recessionCone R = P.recessionCone R ⊔ Q.recessionCone R := by
  ext v
  constructor
  · sorry
  · apply sup_recessionCone_le_recessionCone_vadd

/-- Minkowski addition of a set P and its recession cone leaves P unchanged. -/
lemma Convex.Set.recessionCone_vadd_self {P : Set A} :
    (P.recessionCone R : Set V) +ᵥ P = P := by
  ext x
  constructor
  · rintro ⟨v, hv, y, hy, rfl⟩
    simpa using (Convex.Set.mem_recessionCone.mp hv) y hy 1 zero_le_one
  · intro hx
    exact ⟨0, (P.recessionCone R).zero_mem, x, hx, zero_vadd _ _⟩

/-- The recession cone of a cone is the cone itself. -/
lemma PointedCone.recessionCone_eq_self (C : PointedCone R V) :
    (C : Set V).recessionCone R = C := by
  ext x
  constructor
  · intro hx
    simpa using hx 0 C.zero_mem 1
  · intro hx y hy a ha
    have hax : a • x ∈ C := C.smul_mem ha hx
    exact C.add_mem hax hy


/-- The recession cone of a nonempty polytope is trivial: any nonzero direction admits a
linear functional positive on it, which is bounded on the convex hull of the finitely many
generators. -/
lemma Convexity.IsPolytope.recessionCone_eq_bot {P : Set A} (hP : IsPolytope R P)
    (hne : P.Nonempty) : P.recessionCone R = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual R V, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff R v).mp hcon)
  obtain ⟨x₀, hx₀⟩ := hne
  set g : Module.Dual R V := (f v)⁻¹ • f with hg
  have hgv : g v = 1 := by simp [hg, inv_mul_cancel₀ hf]
  set h : A →ᵃ[R] R := g.toAffineMap.comp (AffineEquiv.vaddConst R x₀).symm.toAffineMap
    with hhdef
  have happ : ∀ y : A, h y = g (y -ᵥ x₀) := fun y => by simp [hhdef]
  obtain ⟨t, rfl⟩ := hP
  have hte : t.Nonempty := by
    rcases Finset.eq_empty_or_nonempty t with rfl | hte
    · simp at hx₀
    · exact hte
  have hbound : ∀ y ∈ Convexity.convexHull R (t : Set A), h y ≤ t.sup' hte h := by
    intro y hy
    refine convexHull_min (fun s hs => ?_)
      ((isConvexSet_Iic (t.sup' hte h)).preimage h.isAffineMap) hy
    exact Finset.le_sup' h hs
  have hray : ∀ a : R, 0 ≤ a → a ≤ t.sup' hte h := by
    intro a ha
    have hb := hbound _ ((Convex.Set.mem_recessionCone.mp hv) x₀ hx₀ a ha)
    rwa [happ, vadd_vsub, map_smul, smul_eq_mul, hgv, mul_one] at hb
  have h0 : (0 : R) ≤ t.sup' hte h := hray 0 le_rfl
  have := hray (t.sup' hte h + 1) (by linarith)
  linarith

-- this lemma does not seem to be used.
#click_suggestions
lemma IsHPolyhedron.recessionCone_isHPolyhedral {P : Set A} (hP : IsHPolyhedron R P) :
    IsHPolyhedral .id (P.recessionCone R) := by
  classical
  by_cases h : ∅ = P
  · simp only [Convex.Set.recessionCone, h.symm, mem_empty_iff_false, imp_false, not_le,
      IsEmpty.forall_iff, implies_true, ofPred_true]
    exact IsHPolyhedral.top _
  -- We need to use a point in `P` for the proof below
  obtain ⟨x, hx : x ∈ P⟩ := Set.nonempty_iff_empty_ne.mpr h

  obtain ⟨H₁, ⟨S₁, rfl⟩⟩ := hP

  unfold IsHPolyhedral Set.recessionCone
  let P := (⋂ h ∈ H₁, ⇑h ⁻¹' Ici 0) ∩ ↑S₁
  let C := H₁.image (·.linear)

  simp only [IsHPolyhedral, Set.recessionCone, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici,
    SetLike.mem_coe, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, and_imp,
    exists_and_left]
  use (PointedCone.dual .id C)
  constructor
  · exact DualFG.dual_of_finset .id C
  · use S₁.direction
    ext v
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_ofPred_eq,
      Finset.coe_preimage, mem_inf, PointedCone.mem_dual, mem_preimage,
      SetLike.mem_coe, restrictScalars_mem]

    constructor
    · intro h
      specialize h x
      specialize h (by
        intro i hi
        simp at hx
        simp [hi, hx]
      )
      sorry
      -- specialize h (by
      --   simp at hx
      --   simp [hx]
      --   sorry
      -- )
      -- constructor
      -- · intro w hw
      --   -- have hf : ∃f ∈ H₁, p w = f.linear := match (hC' (p w)).mp hw with
      --   --   | ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ => ⟨f, ⟨hf, h_eq⟩⟩
      --   -- have h_zero : ∃a ∈ A, (p w) a = 0,
      --   -- obtain ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ := (hC' (p w)).mp hw
      --   -- let ker := f ⁻¹' {0}
      --   -- let k := f.linear.zero
      --   -- have i := p w
      --   sorry
      -- · sorry
    · intro ⟨hv, hvs⟩ y hyP hyS a ha
      constructor
      · intro i hi
        have hiP := hyP i hi
        -- have hc := (hC i).mp hi
        sorry
      · have h_av : a • v ∈ S₁.direction := by exact Submodule.smul_mem S₁.direction a hvs
        exact (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h_av).mpr hyS

end Homogenize
end Field
end Homogenization
