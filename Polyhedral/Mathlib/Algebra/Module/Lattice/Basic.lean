/-
Copyright (c) 2026 Anouk Brose, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Justus Springer
-/

import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Lattice

variable {R : Type*} (K : Type*) [CommRing R] [CommRing K] [Algebra R K]
variable (V : Type*) [AddCommMonoid V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- Our lattice definition. Should replace the mathlib one? -/
class Submodule.IsLattice' (M : Submodule R V) : Prop where
  fg : M.FG
  linearIndepOn : ∀ s ⊆ (M : Set V), LinearIndepOn R id s → LinearIndepOn K id s

namespace Submodule

-- The following is AI slop, maybe we don't need all of this (and should instead
-- work on upstreaming it and changing the mathlib file).
section Basic

variable (M N : Submodule R V)

variable {K M N}

theorem IsLattice'.rank_eq [IsDomain R] [M.IsLattice' K] :
    Module.rank R M = Module.rank K (span K (M : Set V)) := sorry

theorem IsLattice'.finrank_eq [IsDomain R] [M.IsLattice' (K := K)] :
    Module.finrank R M = Module.finrank K (span K (M : Set V)) := sorry

theorem IsLattice'.finite [M.IsLattice' K] : Module.Finite R M := sorry

/-- `⊥` is a lattice. -/
instance : (⊥ : Submodule R V).IsLattice' K := sorry

theorem isLattice'_span_of_linearIndepOn {s : Set V} (hs : s.Finite)
    (h : LinearIndepOn K id s) : (span R s).IsLattice' K := sorry

theorem IsLattice'.mono [IsNoetherianRing R] [N.IsLattice' (K := K)] (h : M ≤ N) :
    M.IsLattice'  K := sorry

instance [IsNoetherianRing R] [M.IsLattice' K] [N.IsLattice' K] :
    (M ⊓ N).IsLattice' K := sorry

/-- Intersecting a lattice with a `K`-subspace gives a lattice. This is the source of
non-full lattices, and the reason we do not bundle `span K M = ⊤`. -/
instance [IsNoetherianRing R] [M.IsLattice' K] (W : Submodule K V) :
    (M ⊓ W.restrictScalars R).IsLattice' K := sorry

/-- Sums of lattices are lattices. -/
instance [IsNoetherianRing R] [M.IsLattice' K] [N.IsLattice' K] :
    (M ⊔ N).IsLattice' K := sorry

end Basic

section PID

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable (M : Submodule R V)

variable [IsDomain R] [IsPrincipalIdealRing R] [FaithfulSMul R K]

/-- **Over a PID, a lattice has a `K`-linearly independent `R`-basis.**  This is the main
structural theorem: `IsLattice'` is equivalent to the naive "spanned by a `K`-linearly
independent set" definition. -/
theorem isLattice'_iff_exists_linearIndepOn :
    M.IsLattice' K ↔ ∃ s : Set V, s.Finite ∧ LinearIndepOn K id s ∧ span R s = M := sorry

theorem IsLattice'.free [M.IsLattice' K] : Module.Free R M := sorry

end PID

section FractionRing

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable (M : Submodule R V)

variable [IsDomain R] [IsFractionRing R K]

/-- When `K` is the fraction field of `R`, the second axiom is automatic: finite generation
alone suffices.  This is why `Submodule.IsLattice` gets away with only `fg` + `span_eq_top`. -/
theorem IsLattice'.of_fg (h : M.FG) : M.IsLattice' (K := K) := sorry

/-- Comparison with mathlib's `Submodule.IsLattice`: it is the *full* case of ours. -/
theorem isLattice_iff : IsLattice K M ↔ M.IsLattice' (K := K) ∧ span K (M : Set V) = ⊤ := sorry

end FractionRing

end Submodule
