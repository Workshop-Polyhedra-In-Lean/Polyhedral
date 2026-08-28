import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Algebra.Module.Lattice.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Defs

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- The monoid of lattice points of a pointed cone in a lattice. -/
abbrev PointedCone.latticePoints (C : PointedCone K V) (Λ : Submodule ℤ V) : AddSubmonoid V :=
  C.toAddSubmonoid ⊓ Λ.toAddSubmonoid

namespace Gordan

variable (Λ : Submodule ℤ V)
variable (r : Fin (Module.finrank K V) → Λ)

abbrev C : PointedCone K V := (PointedCone.hull K (Set.range (Subtype.val ∘ r)))

noncomputable def parallelepiped : Set V :=
    (Finsupp.linearCombination K (Subtype.val ∘ r)) '' { μ | ∀ i, 0 ≤ μ i ∧ μ i < 1 }

theorem parallelepiped_inter_lattice_finite :
    (parallelepiped K Λ r ∩ Λ).Finite := sorry

def generators : Set V := ((parallelepiped K Λ r) ∩ Λ) ∪ Set.range (Subtype.val ∘ r)

theorem generators_finite : (generators K Λ r).Finite := by
  unfold generators
  apply Set.Finite.union
  · apply parallelepiped_inter_lattice_finite
  · apply Finite.Set.finite_range

noncomputable def generatorsFinset : Finset V := Set.Finite.toFinset (generators_finite K Λ r)

theorem gordan (hΛ : Λ.IsLattice' K) (hC : (C K Λ r).toConvexCone.Salient) :
    ((C K Λ r).latticePoints K Λ).FG := by
  use generatorsFinset K Λ r
  apply AddSubmonoid.closure_eq_of_le
  · sorry
  · intro γ hγ
    rw [AddSubmonoid.mem_closure_finset]
    
    sorry
    

end Gordan
