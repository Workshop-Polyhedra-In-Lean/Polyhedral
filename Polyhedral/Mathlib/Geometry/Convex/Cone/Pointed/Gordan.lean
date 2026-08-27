import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K] [PartialOrder K] [IsStrictOrderedRing K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

variable (K) in
def Submodule.IsLatticeIn (Λ : Submodule R V) : Prop :=
  ∃ (n : ℕ) (v : Fin n → Λ),
    LinearIndependent K (Subtype.val ∘ v) ∧ Submodule.span R (Set.range v) = ⊤

abbrev PointedCone.latticePoints (C : PointedCone K V) (Λ : Submodule R V) : AddSubmonoid V :=
  C.toAddSubmonoid ⊓ Λ.toAddSubmonoid

variable (Λ : Submodule R V)
variable (n : ℕ) (r : Fin n → Λ)

#check ConvexCone.hull
variable (K) in
abbrev C : PointedCone K V := (PointedCone.hull K (Set.range (Subtype.val ∘ r)))

theorem gordan (hΛ : Λ.IsLatticeIn K) (hC : (C K Λ n r).toConvexCone.Salient) :
    ((C K Λ n r).latticePoints Λ).FG := by
  sorry

#check AddMonoid.FG
