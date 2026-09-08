/-
Copyright (c) 2026 Louis Theran, Vlad Tskylevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Set.Card
import Mathlib.Order.Basic

/-! # Connectivity via ranking functions and well-founded relations

Two ways to certify that a graph is connected by "always being able to move towards a fixed
vertex `x`":

* `connected_of_greedy_ascent`: a ranking function `f` into a partial order, on a *finite* vertex
  set, with every vertex other than `x` having a neighbor of strictly larger rank.
* `connected_iff_exists_wellFounded_uniqueMin`: connectivity is characterized by the
  existence of a well-founded relation on the vertices that has a unique minimum and its
  support on the edges. -/

namespace SimpleGraph

variable {V α : Type*} [PartialOrder α] {G : SimpleGraph V}

section WellFounded

variable {G : SimpleGraph V}

-- IDEA:
-- G-relation is like ∃ relhom to Adj
-- WF G-relation
/-- `r` is a *`G`-relation* if it only ever relates adjacent vertices. -/
def IsGRelation (G : SimpleGraph V) (r : V → V → Prop) : Prop := ∀ x y, r x y → G.Adj x y

/-- If `G` admits a well-founded `G`-relation with a unique minimum, then it is
  connected. -/
theorem connected_of_wellFounded_uniqueMin (r : V → V → Prop) (hwf : WellFounded r)
    (hGr : G.IsGRelation r) (x : V) (huniq : ∀ y, (∀ z, ¬ r z y) → y = x) :
    G.Connected := by
  have : Nonempty V := ⟨x⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨x, fun y => ?_⟩
  suffices h : G.Reachable y x from h.symm
  induction y using hwf.induction with
  | _ y ih =>
    by_cases hyx : y = x
    · rw [hyx]
    · have hnotmin : ¬ ∀ z, ¬ r z y := fun hcon => hyx (huniq y hcon)
      push Not at hnotmin
      obtain ⟨z, hzy⟩ := hnotmin
      exact (hGr z y hzy).symm.reachable.trans (ih z hzy)

theorem connected_of_wellFounded_step (r : V → V → Prop) (hwf : WellFounded r)
  (hrAdj : Subrelation r G.Adj) (x : V) (hstep : ∀ y, y ≠ x → ∃ z, r z y):
    G.Connected := by
  have : Nonempty V := ⟨x⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨x, fun y => ?_⟩
  suffices h : G.Reachable y x from h.symm
  induction y using hwf.induction with
  | _ y ih =>
    by_cases hyx : y = x
    · rw [hyx]
    · obtain ⟨z, hzy⟩ := hstep y (by simpa)
      exact (hrAdj hzy).symm.reachable.trans (ih z hzy)









/-- If `G` is finite, a ranking function into a partial order with the property
  that all but one vertex `x` has a larger neighbor certifies connectivity. -/
theorem connected_of_greedy_ascent [Finite V] (f : V → α) (x : V)
    (hstep : ∀ y, y ≠ x → ∃ z, G.Adj y z ∧ f y < f z) :
    G.Connected := by
  set measure : V → ℕ := fun y => {w : V | f y < f w}.ncard with hmeasure_def
  set r : V → V → Prop := fun z y => G.Adj z y ∧ f y < f z with hr_def
  have hGr : G.IsGRelation r := fun z y hzy => hzy.1
  have hwf : WellFounded r := by
    apply Subrelation.wf (r := InvImage (· < ·) measure) (h₂ := InvImage.wf measure Nat.lt_wfRel.wf)
    intro z y hzy
    have hsub : {w : V | f z < f w} ⊂ {w : V | f y < f w} :=
      ⟨fun w hw => hzy.2.trans hw, fun hcontra => absurd (hcontra hzy.2) (lt_irrefl (f z))⟩
    exact Set.ncard_lt_ncard hsub
  apply connected_of_wellFounded_uniqueMin r hwf hGr x
  intro y hy
  by_contra hyx
  obtain ⟨z, hadj, hlt⟩ := hstep y hyx
  exact hy z ⟨hadj.symm, hlt⟩

omit [PartialOrder α] in
/-- For any vertices `x ≠ y` of a connected graph `G`, `y` has a neighbor that is
  closer to `x` in the graph metric. -/
theorem Connected.exists_adj_lt_dist (hconn : G.Connected) {x y : V} (hxy : y ≠ x) :
    ∃ z, G.Adj y z ∧ G.dist x z < G.dist x y := by
  obtain ⟨p, -, hlen⟩ := hconn.exists_path_of_dist x y
  have hp : ¬p.Nil := p.not_nil_of_ne hxy.symm
  have hadj : G.Adj p.penultimate y := p.adj_penultimate hp
  have h1 : G.dist x p.penultimate ≤ p.dropLast.length := G.dist_le p.dropLast
  have h2 : p.dropLast.length + 1 = p.length := p.length_dropLast_add_one hp
  have h3 : 0 < G.dist x y := hconn.pos_dist_of_ne hxy.symm
  exact ⟨p.penultimate, hadj.symm, by omega⟩

omit [PartialOrder α] in
/-- Connectivity is characterized by `G` admitting a well-founded `G`-relations with a unique
minimum. -/
theorem connected_iff_exists_wellFounded_uniqueMin :
    G.Connected ↔ ∃ r : V → V → Prop, WellFounded r ∧ G.IsGRelation r ∧ ∃! x, ∀ z, ¬ r z x := by
  constructor
  · intro hconn
    obtain ⟨x⟩ := hconn.nonempty
    have hswf : WellFounded (fun y z => G.dist x y < G.dist x z) :=
      InvImage.wf (G.dist x) Nat.lt_wfRel.wf
    refine ⟨fun y z => G.Adj y z ∧ G.dist x y < G.dist x z,
      Subrelation.wf (fun hyz => hyz.2) hswf, fun _ _ hyz => hyz.1, x, ?_, ?_⟩
    · intro z hzx
      have h0 : G.dist x x = 0 := G.dist_self
      exact absurd hzx.2 (by omega)
    · intro y hy
      by_contra hyx
      obtain ⟨z, hadj, hzy⟩ := hconn.exists_adj_lt_dist hyx
      exact hy z ⟨hadj.symm, hzy⟩
  · rintro ⟨r, hwf, hGr, x, -, huniq⟩
    exact connected_of_wellFounded_uniqueMin r hwf hGr x huniq

end WellFounded

end SimpleGraph
