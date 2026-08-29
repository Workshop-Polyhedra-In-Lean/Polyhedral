/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
## (Finite) Dimension of an affine subspace

This file defines the dimension of affine subspace to be `⊥` for the empty subspace,
and otherwise equal to the `Module.rank` of the direction of the subspace. The finite dimension
is similary defined using `Module.finrank`.

## Main definitions

* `AffineSubspace.dim`: Dimension expressed as `WithBot Cardinal`
* `AffineSubspace.findim`: Dimension expressed as `WithBot ℕ` with a junk value of 0 for infinite
  dimensional spaces.

## TODO

* Relate `dim`/`findim` to `AffineBasis`
* All of `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean` needs to be audited and possibly
  integrated with this file. i.e. `Collinear`/`Coplanar` should be redefined. Should other lemmas
  be re-stated?
-/

namespace AffineSubspace

universe u v v' a a'

variable {R : Type u} {V : Type v} {V' : Type v'} {A : Type a} {A' : Type a'}
variable [AddCommGroup V] [AddTorsor V A] [AddCommGroup V'] [AddTorsor V' A']

section Ring

variable [Ring R] [Module R V] [Module R V']
variable {s t : AffineSubspace R A}

-- TODO: Should live with definition of direction
@[simp]
theorem direction_eq_bot_iff : s.direction = ⊥ ↔ (s : Set A).Subsingleton := by
  simp [AffineSubspace.direction]

-- TODO: Should live with definiton of Singleton until it goes upstream
@[simp]
theorem singleton_ne_bot (x : A) : ({x} : AffineSubspace R A) ≠ ⊥ := by
  simp [← coe_eq_bot_iff]

-- TODO: Useful below but looks like it shouldn't be
@[simp]
theorem direction_singleton_eq_bot (x : A) : ({x} : AffineSubspace R A).direction = ⊥ := by
  simp

@[simp]
theorem coe_affineSpan_eq_singleton_iff {s : Set A} (x : A) : affineSpan R s = {x} ↔ s = {x} := by
  refine ⟨fun h ↦ ?_, by simp +contextual [AffineSubspace.ext_iff]⟩
  refine Set.Nonempty.subset_singleton_iff ?_ |>.mp (by simpa using affineSpan_le.mp h.le)
  exact affineSpan_nonempty R |>.mp (by simp [h])

open Classical in
/-- The dimension of `s` is equal to `⊥` if `s = ⊥`, and otherwise it is equal to the dimension of
`s` interpreted as a linear space. -/
noncomputable def dim (s : AffineSubspace R A) : WithBot Cardinal :=
  if s = ⊥ then ⊥
  else Module.rank R s.direction

/-- The dimension of `s` is equal to `⊥` if `s = ⊥`, and otherwise it is equal to the finite
dimension of `s` interpreted as a linear space. Note that this inherits `Module.finrank`s junk
value: `AffineSubspace.findim s = 0` for infinite dimensional subspaces. -/
noncomputable def findim (s : AffineSubspace R A) : WithBot ℕ :=
  WithBot.map Cardinal.toNat (dim s)

@[simp]
theorem dim_lt_aleph0 [StrongRankCondition R] (s : AffineSubspace R A)
    [Module.Finite R s.direction] : dim s < Cardinal.aleph0 := by
  dsimp [dim]
  split_ifs <;> simp [Module.rank_lt_aleph0]

@[simp]
theorem dim_bot : dim (⊥ : AffineSubspace R A) = ⊥ := by
  simp [dim]

@[simp]
theorem findim_bot : findim (⊥ : AffineSubspace R A) = ⊥ := by
  simp [findim]

@[simp]
theorem dim_singleton [Nontrivial R] (x : A) :
    dim ({x} : AffineSubspace R A) = 0 := by
  dsimp [dim]
  rw [direction_singleton_eq_bot]
  simp

@[simp]
theorem findim_singleton [Nontrivial R] (x : A) : findim ({x} : AffineSubspace R A) = 0 := by
  simp [findim]

@[simp]
theorem dim_eq_bot_iff : dim s = ⊥ ↔ s = ⊥ := by
  simp [dim]

@[simp]
theorem findim_eq_bot_iff : findim s = ⊥ ↔ s = ⊥ := by
  simp [findim]

theorem dim_ne_bot_iff : dim s ≠ ⊥ ↔ (s : Set A).Nonempty := by
  contrapose!
  simp

theorem findim_ne_bot_iff : findim s ≠ ⊥ ↔ (s : Set A).Nonempty := by
  contrapose!
  simp

theorem dim_eq_rank (h : s ≠ ⊥) : dim s = Module.rank R s.direction := by
  simpa [dim]

theorem findim_eq_finrank (h : s ≠ ⊥) : findim s = Module.finrank R s.direction := by
  simp [findim, dim_eq_rank h]
  norm_cast

theorem findim_eq_map_dim_toNat : (findim s) = (dim s).map Cardinal.toNat := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [findim, dim_eq_rank hs]

@[mono]
theorem dim_mono (h : s ≤ t) : dim s ≤ dim t := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [dim_eq_rank hs, dim_eq_rank (ne_bot_of_le_ne_bot hs h),
    Submodule.rank_mono (direction_le h)]

@[mono]
theorem findim_mono [StrongRankCondition R] [Module.Finite R t.direction] (h : s ≤ t) :
    findim s ≤ findim t := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [findim_eq_finrank hs, findim_eq_finrank (ne_bot_of_le_ne_bot hs h),
    Submodule.finrank_mono (direction_le h)]

theorem map_lift_dim_map_le (f : A →ᵃ[R] A') (s : AffineSubspace R A) :
    WithBot.map Cardinal.lift.{v} (map f s).dim ≤
      WithBot.map Cardinal.lift.{v'} s.dim := by
  by_cases hs : map f s = ⊥
  · simp [hs]
  rw [dim_eq_rank hs, dim_eq_rank (by contrapose! hs; simpa), map_direction]
  simp [lift_rank_map_le]

theorem findim_map_le_findim [StrongRankCondition R] (f : A →ᵃ[R] A') (s : AffineSubspace R A)
    [Module.Finite R s.direction] : (map f s).findim ≤ s.findim := by
  by_cases hs : (map f s) = ⊥
  · simp [hs]
  rw [findim_eq_finrank hs, findim_eq_finrank (by contrapose! hs; simpa), map_direction]
  simp [Submodule.finrank_map_le]

theorem map_lift_dim_map_eq_of_injective {f : A →ᵃ[R] A'} (hf : Function.Injective f)
    (s : AffineSubspace R A) :
    WithBot.map Cardinal.lift.{v} (map f s).dim =
      WithBot.map Cardinal.lift.{v'} s.dim := by
  by_cases hs : map f s = ⊥
  · simp_all
  rw [dim_eq_rank hs, dim_eq_rank (by contrapose! hs; simpa), map_direction]
  simp only [WithBot.map_coe, WithBot.coe_inj]
  refine LinearEquiv.lift_rank_eq <| (Submodule.equivMapOfInjective _ ?_ _).symm
  exact (AffineMap.linear_injective_iff f).mpr hf

theorem findim_map_eq_findim_of_injective {f : A →ᵃ[R] A'} (hf : Function.Injective f)
    (s : AffineSubspace R A) : (map f s).findim = s.findim := by
  by_cases hs : map f s = ⊥
  · simp_all
  rw [findim_eq_finrank hs, findim_eq_finrank (by contrapose! hs; simpa), map_direction]
  norm_cast
  refine LinearEquiv.finrank_eq <| (Submodule.equivMapOfInjective _ ?_ _).symm
  exact (AffineMap.linear_injective_iff f).mpr hf

end Ring

section DivisionRing

variable [DivisionRing R] [Module R V]
variable {s : AffineSubspace R A}

@[simp]
theorem dim_le_zero_iff_subsingleton : dim s ≤ 0 ↔ (s : Set A).Subsingleton := by
  by_cases hs : s = ⊥ <;> simp [dim_eq_rank, hs]

@[simp]
theorem findim_le_zero_iff_subsingleton [Module.Finite R s.direction] :
    findim s ≤ 0 ↔ (s : Set A).Subsingleton := by
  by_cases hs : s = ⊥ <;> simp [findim_eq_finrank, hs]

@[simp]
theorem dim_eq_zero_iff : dim s = 0 ↔ ∃ x : A, s = {x} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₁ : (s : Set A).Nonempty := dim_ne_bot_iff.mp (by simp [h])
    have h₂ := dim_le_zero_iff_subsingleton.mp (le_of_eq h)
    obtain ⟨x, hx⟩ := Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨h₁, h₂⟩
    exact ⟨x, (AffineSubspace.ext_iff _ _).mpr hx⟩
  · obtain ⟨x, rfl⟩ := h
    simp [dim]

-- TODO: Necessary? Many Module.finrank + vectorSpan lemmas are stated over Set.range, do we want
-- helpers in a different form?
theorem finrank_vectorSpan_pair {x y : A} (h : x ≠ y) :
    Module.finrank R (vectorSpan R {x, y}) = 1 := by
  have := (affineIndependent_of_ne R h).finrank_vectorSpan (n := 1) (by simp)
  rwa [Matrix.range_cons_cons_empty] at this

-- TOOD: Derive from the below?
theorem dim_eq_one_iff :
    dim s = 1 ↔ ∃ x y : A, x ≠ y ∧ s = affineSpan R {x, y} := by
  by_cases hs : s = ⊥
  · simp [hs]
    grind [affineSpan_eq_bot]
  rw [dim_eq_rank hs, WithBot.coe_eq_one]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : (s : Set A).Nonempty := dim_ne_bot_iff.mp (by simp [hs])
    obtain ⟨⟨x, hx⟩, h₁, h₂⟩ := rank_eq_one_iff.mp h
    obtain ⟨y, hy⟩ := h'
    have hne : y ≠ x +ᵥ y := fun heq ↦ by
      simp [eq_vadd_iff_vsub_eq] at heq
      simp [heq] at h₁
    refine ⟨y, x +ᵥ y, hne, ?_⟩
    have hxy := vadd_mem_of_mem_direction hx hy
    refine eq_iff_direction_eq_of_mem hxy (right_mem_affineSpan_pair ..) |>.mpr ?_
    let := FiniteDimensional.of_rank_eq_one h
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_ |>.symm
    · exact direction_le <| affineSpan_le.mpr <| Set.pair_subset hy hxy
    · rw [direction_affineSpan, finrank_vectorSpan_pair hne,
        Module.rank_eq_one_iff_finrank_eq_one.mp (by simpa using h)]
  · obtain ⟨_, _, h₁, h₂⟩ := h
    rw [Module.rank_eq_one_iff_finrank_eq_one, h₂, direction_affineSpan]
    exact finrank_vectorSpan_pair h₁

-- TODO should be stated for `dim` in terms of cardinal and then re-derived for findim?
-- TODO: Weaken V being finite dimensional to (affineSpan R s).direction being finite.
theorem exists_affineIndependent_of_finiteDimensional (s : Set A) [FiniteDimensional R V] :
    ∃ t ⊆ s, affineSpan R t = affineSpan R s ∧ AffineIndependent R ((↑) : t → A) ∧
      t.ncard = (affineSpan R s).findim.succ := by
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_affineIndependent R V s
  refine ⟨t, ht1, ht2, ht3, ?_⟩
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp_all
  rw [findim_eq_finrank (by contrapose! hs; simpa using hs), ← ht2, direction_affineSpan,
    WithBot.succ_natCast]
  have : t.Finite := finite_set_of_fin_dim_affineIndependent R ht3
  have : Fintype { x // x ∈ t } := Set.Finite.fintype this
  have : t.ncard ≠ 0 := by
    grind [Set.ncard_eq_zero, affineSpan_eq_bot, Set.not_nonempty_empty]
  have := ht3.finrank_vectorSpan (n := t.ncard - 1) (by simp [Nat.sub_one_add_one this])
  rw [Subtype.range_coe] at this
  lia

end DivisionRing

end AffineSubspace
