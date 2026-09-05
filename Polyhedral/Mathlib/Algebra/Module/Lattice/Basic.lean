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

/-!
# Lattices

A generalization of mathlib's `Submodule.IsLattice` to make it useful for Polyhedral.
This definition is used in the proof of Gordan's lemma, see
`Polyhedral/Mathlib/Geometry/Convex/Cone/Pointed/Gordan.lean`.

We (The Ehrhart group from the workshop) will work on upstreaming this into mathlib,
to replace the existing definition. See Zulip discussion:

https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Definitions.20of.20lattices/with/620077176

-/

open Module
open scoped Pointwise

universe v w

variable {R : Type*} [CommRing R]

namespace Submodule

/-- Let `K` be a `R`-algebra and `V` a `K`-module.
A lattice is a `R`-submodule `M ≤ V` that is finitely generated such that every `R`-independent
subset of `M` is `K`-linearly independent. Equivalently, the `R`-rank of `M` equals the
`K`-dimension of its `K`-span, see `Submodule.isLattice'_iff_fg_and_finrank_eq`. -/
class IsLattice' (A : outParam Type*) [CommRing A] [Algebra R A] {V : Type v} [AddCommMonoid V]
    [Module R V] [Module A V] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  linearIndepOn : ∀ s ⊆ (M : Set V), LinearIndepOn R id s → LinearIndepOn A id s

namespace IsLattice'

section CommRing

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type v} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

/-- Any `R`-independent family of vectors in a lattice is `K`-linearly independent. -/
theorem linearIndependent [IsLattice' A M] {ι : Type*} {v : ι → V}
    (hv : ∀ i, v i ∈ M) (h : LinearIndependent R v) : LinearIndependent A v := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R A).codomain_trivial
    exact linearIndependent_of_subsingleton
  exact (linearIndepOn_id_range_iff h.injective).mp <|
    IsLattice'.linearIndepOn _ (Set.range_subset_iff.mpr hv) h.linearIndepOn_id

/-- Any basis of an `R`-lattice in `V` is `K`-linearly independent. -/
theorem basis_linearIndependent {I : Type w} {M : Submodule R V}
    [IsLattice' A M] (b : Basis I R M) : LinearIndependent A (fun i ↦ (b i).val) :=
  IsLattice'.linearIndependent A M (fun i ↦ (b i).2)
    (b.linearIndependent.map' M.subtype (Submodule.ker_subtype _))

/-- Any `R`-lattice is finite. -/
instance finite [IsLattice' A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice'.fg

theorem mono_of_fg {M N : Submodule R V} (hle : M ≤ N) (hfg : M.FG) [IsLattice' A N] :
    IsLattice' A M where
  fg := hfg
  linearIndepOn s hs hli := linearIndepOn s (hs.trans hle) hli

/-- Over a Noetherian ring, any submodule of a lattice is a lattice. -/
theorem mono [IsNoetherianRing R] {M N : Submodule R V} (hle : M ≤ N) [IsLattice' A N] :
    IsLattice' A M :=
  mono_of_fg A hle (isNoetherian_submodule.mp inferInstance M hle)

/-- Over a Noetherian ring, the intersection of two lattices is a lattice. -/
instance inf [IsNoetherianRing R] (M N : Submodule R V) [IsLattice' A M] [IsLattice' A N] :
    IsLattice' A (M ⊓ N) :=
  mono A inf_le_left

end CommRing

section Field

variable (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
variable {V : Type v} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable (M : Submodule R V)

-- This has been merged into mathlib: #43297
theorem rank_span_le_rank : Module.rank K (span K (M : Set V)) ≤ Module.rank R M := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain ⟨b, hbM, hbspan, hbli⟩ := exists_linearIndependent K (M : Set V)
  rw [← hbspan, rank_span_set hbli]
  have hb : LinearIndependent R (fun x : b ↦ (⟨x.1, hbM x.2⟩ : M)) :=
    LinearIndependent.of_comp M.subtype (hbli.restrict_scalars' R)
  exact hb.cardinal_le_rank

/-- The `R`-rank of a lattice equals the `K`-dimension of its `K`-span. -/
theorem rank_eq_rank_span [IsLattice' K M] :
    Module.rank R M = Module.rank K (span K (M : Set V)) := by
  -- AI slop, needs refactor
  refine le_antisymm ?_ (rank_span_le_rank K M)
  rw [Module.rank]
  apply ciSup_le'
  intro ⟨s, hs⟩
  have hR : LinearIndependent R (fun x : s ↦ ((x : M) : V)) :=
    hs.map' M.subtype (Submodule.ker_subtype _)
  have hK : LinearIndependent K (fun x : s ↦ ((x : M) : V)) :=
    IsLattice'.linearIndependent K M (fun x ↦ (x : M).2) hR
  have hmem : ∀ x : s, ((x : M) : V) ∈ span K (M : Set V) := fun x ↦ subset_span (x : M).2
  have hW : LinearIndependent K
      (fun x : s ↦ (⟨((x : M) : V), hmem x⟩ : span K (M : Set V))) :=
    LinearIndependent.of_comp (span K (M : Set V)).subtype hK
  exact hW.cardinal_le_rank

/-- The `R`-rank of a lattice equals the `K`-dimension
of its `K`-span. This is the finrank version of `rank_eq_rank_span`. -/
theorem finrank_eq_finrank_span [IsLattice' K M] :
    finrank R M = finrank K (span K (M : Set V)) :=
  congrArg Cardinal.toNat (rank_eq_rank_span K M)


/-- An `R`-module `M` is a lattice in an ambient `K`-module `V` if and only if `M`
is finitely generated, and its `R`-rank equals the `K`-dimension of its `K`-span. -/
theorem _root_.Submodule.isLattice'_iff_fg_and_finrank_eq :
    IsLattice' K M ↔ M.FG ∧ finrank R M = finrank K (span K (M : Set V)) := by
  refine ⟨fun hM ↦ ⟨hM.fg, finrank_eq_finrank_span _ _⟩, ?_⟩
  rintro ⟨hfg, hrank⟩
  refine ⟨hfg, fun s hsM hsRli ↦ ?_⟩
  obtain ⟨b, hbs, hbspan, hbKli ⟩ := exists_linearIndependent K s
  obtain ⟨c, hcM, hbc, hMspanc, hcKli⟩ :=
    exists_linearIndepOn_id_extension hbKli (hbs.trans hsM)
  have hcRli : LinearIndepOn R id c := hcKli.linearIndependent.restrict_scalars' R
  have hcbKli : LinearIndepOn K id (b ∪ (c \ b)) := by
    simpa [Set.union_sdiff_cancel hbc] using hcKli
  have hdisjK : Disjoint ((span K s).restrictScalars R) ((span K (c \ b)).restrictScalars R) := by
    rw [Submodule.disjoint_restrictScalars_iff, ← hbspan]
    exact ((linearIndepOn_id_union_iff Set.disjoint_sdiff_right).mp hcbKli).2.2
  have hdisjR : Disjoint (span R s) (span R (c \ b)) :=
    hdisjK.mono
      (Submodule.span_le_restrictScalars R K s)
      (Submodule.span_le_restrictScalars R K (c \ b))
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hdisjSet : Disjoint (s : Set V) ((c \ b) : Set V) :=
    hdisjR.of_span₀ fun h0 ↦ hsRli.ne_zero h0 rfl
  have : Module.Finite R M := Module.Finite.of_fg hfg
  have hsfin : s.Finite :=
    (hsRli.linearIndependent.codRestrict M (fun x ↦ hsM x.2)).finite
  have hcfin : c.Finite :=
    (hcRli.linearIndependent.codRestrict M (fun x ↦ hcM x.2)).finite
  have hchain : s.ncard + (c \ b).ncard ≤ b.ncard + (c \ b).ncard := calc
     s.ncard + (c \ b).ncard = (s ∪ (c \ b)).ncard := by
      rw [Set.ncard_union_eq hdisjSet hsfin hcfin.sdiff]
    _ = finrank R (span R (s ∪ (c \ b))) := by
      rw [Module.finrank, rank_span_set (hsRli.id_union (hcRli.mono Set.sdiff_subset) hdisjR)]
      rfl
    _ ≤ finrank R M := by
      exact Submodule.finrank_mono
       (span_le.mpr (Set.union_subset hsM (Set.sdiff_subset.trans hcM)))
    _ = finrank K (span K (M : Set V)) := hrank
    _ = c.ncard := by
      rw [le_antisymm (span_le.mpr hMspanc) (span_mono hcM), Module.finrank, rank_span_set hcKli]
      rfl
    _ = b.ncard + (c \ b).ncard  := by
      simpa [add_comm] using (Set.ncard_sdiff_add_ncard_of_subset hbc hcfin).symm
  simpa [((Set.subset_iff_eq_of_ncard_le (Nat.le_of_add_le_add_right hchain)
    hsfin).mp hbs).symm, hbKli]



section IsPrincipalIdealRing

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Any lattice over a PID is a free `R`-module. -/
instance free (M : Submodule R V) [IsLattice' K M] : Module.Free R M := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

/-- A lattice over a PID has a basis that's `K`-linearly independent. -/
theorem exists_basis_linearIndependent (M : Submodule R V) [IsLattice' K M] :
    ∃ (I : Type v) (b : Basis I R M), LinearIndependent K (fun i ↦ (b i).val) := by
  obtain ⟨I, b⟩ := Module.Free.exists_basis R M
  exact ⟨I, b, basis_linearIndependent K b⟩

end IsPrincipalIdealRing

section IsFractionRing

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K` is the field of fractions of `R`, any finitely generated `R`-submodule of `V`
is a lattice. -/
theorem of_fg {M : Submodule R V} (hM : M.FG) : IsLattice' K M where
  fg := hM
  linearIndepOn v hvM hv := by
    exact (LinearIndependent.iff_fractionRing R K).mp hv

end IsFractionRing

end Field

end IsLattice'

end Submodule
