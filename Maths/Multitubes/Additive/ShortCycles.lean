/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Cycles
public import Mathlib.Data.Set.Finite.Lemmas

import Mathlib.Data.Set.Finite.List

/-!
# Short-cycle completeness for additive transport

On a finite vertex set, checking additive closed-walk inequalities only up to
the number of vertices is complete.  A violated bound is already violated on a simple cycle
(`Maths.AdditiveTransport.exists_simpleCycle_mean_gt_of_closedWalk`), and a simple cycle has
at most one edge per vertex (`Maths.EdgeGraph.Walk.IsSimpleCycle.length_le_card`).  Neither
step requires a finite edge type or decidable equality.

Applied to uniformly shifted weights, this gives a bounded-cycle version of
the exact one-sided residual threshold.  Thus every obstruction has a closed
walk witness of length at most `Fintype.card V`.

## Main definitions

* `Maths.AdditiveTransport.shortClosedEdgeLists`: the edge lists realized by
  nonempty closed walks of length at most the number of vertices.  It is a finite set, which
  is what makes a maximizer available.
* `Maths.AdditiveTransport.edgeListMean`: the mean weight of an edge list.  It is
  only used on lists coming from nonempty closed walks.

## Main results

* `Maths.AdditiveTransport.worstDirectedResidualAtMost_iff_shortClosedWalk_le`: a
  one-sided residual threshold holds exactly when it holds on closed walks of length at most
  `Fintype.card V`.
* `Maths.AdditiveTransport.exists_short_closedWalk_of_not_worstDirectedResidualAtMost`:
  the witness form of the same fact - a failing threshold is refuted by one short closed walk.
* `Maths.AdditiveTransport.exists_short_closedWalk_maximizing_mean`: if any
  nonempty closed walk exists, one of length at most `Fintype.card V` attains the maximum mean
  among all nonempty closed walks.
* `Maths.AdditiveTransport.exists_short_closedWalk_realizing_residual_threshold`:
  that maximizer decides the threshold, so the optimal residual is its mean.  Note the
  nonemptiness hypothesis is required: with no nonempty closed walk there is no maximizer and
  every real threshold is attainable.
* `Maths.AdditiveTransport.exists_negative_residual_bound`: strictly negative nonempty cycle
  weights admit one uniformly negative residual bound on a finite graph.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

open MaxPlusPotential

/-- It is enough to check closed-walk affine bounds on cycles of length at
most the number of vertices. -/
theorem closedWalk_le_length_mul_of_short [Fintype V]
    (weight : E → ℝ) (level : ℝ)
    (hshort : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → cycle.length ≤ Fintype.card V →
        walkSum weight cycle ≤ cycle.length * level) :
    ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSum weight cycle ≤ cycle.length * level := by
  intro vertex cycle
  by_contra hnot
  obtain ⟨base, simple, hsimple, hgt⟩ :=
    exists_simpleCycle_mean_gt_of_closedWalk weight level cycle (lt_of_not_ge hnot)
  exact (hshort base simple hsimple.1 hsimple.length_le_card).not_gt hgt

/-- If every nonempty closed walk of length at most the number of vertices has
nonpositive weight, then every closed walk has nonpositive weight. -/
theorem closedWalk_nonpos_of_short [Fintype V] (weight : E → ℝ)
    (hshort : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → cycle.length ≤ Fintype.card V →
        walkSum weight cycle ≤ 0) :
    ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSum weight cycle ≤ 0 := fun vertex cycle => by
  simpa using closedWalk_le_length_mul_of_short weight 0
    (fun vertex cycle hpos hcard => by simpa using hshort vertex cycle hpos hcard) vertex cycle

/-- **Short-cycle exact threshold.**  On a finite graph, every obstruction to
a one-sided residual threshold occurs on a nonempty closed walk of
length at most the number of vertices. -/
theorem worstDirectedResidualAtMost_iff_shortClosedWalk_le
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    WorstDirectedResidualAtMost G weight level ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → cycle.length ≤ Fintype.card V →
          walkSum weight cycle ≤ cycle.length * level := by
  rw [worstDirectedResidualAtMost_iff_closedWalk_le]
  exact ⟨fun hall vertex cycle _ _ => hall vertex cycle,
    closedWalk_le_length_mul_of_short weight level⟩

/-- Failure of a residual threshold has a short positive shifted cycle
witness. -/
theorem exists_short_closedWalk_of_not_worstDirectedResidualAtMost
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ)
    (hfailure : ¬WorstDirectedResidualAtMost G weight level) :
    ∃ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length ∧ cycle.length ≤ Fintype.card V ∧
        cycle.length * level < walkSum weight cycle := by
  grind [worstDirectedResidualAtMost_iff_shortClosedWalk_le]

/-! ## Attainment of the maximum cycle mean -/

/-- Every nonempty closed walk contains some nonempty closed walk of length at
most the number of vertices. -/
theorem exists_short_closedWalk_of_nonempty [Fintype V]
    {vertex : V} (cycle : G.Walk vertex vertex) (hcycle : 0 < cycle.length) :
    ∃ (middle : V) (short : G.Walk middle middle),
      0 < short.length ∧ short.length ≤ Fintype.card V := by
  obtain ⟨middle, short, hsimple, -⟩ :=
    exists_simpleCycle_cycleMeanDominates (fun _ => 0) cycle hcycle
  exact ⟨middle, short, hsimple.1, hsimple.length_le_card⟩

/-- Edge lists realized by nonempty closed walks no longer than the number of
vertices. -/
def shortClosedEdgeLists [Fintype V] (G : EdgeGraph V E) : Set (List E) :=
  {edges | ∃ (vertex : V) (cycle : G.Walk vertex vertex),
    0 < cycle.length ∧ cycle.length ≤ Fintype.card V ∧ cycle.edges = edges}

theorem finite_shortClosedEdgeLists [Fintype V] [Finite E]
    (G : EdgeGraph V E) :
    (shortClosedEdgeLists G).Finite := by
  apply (List.finite_length_le E (Fintype.card V)).subset
  rintro edges ⟨vertex, cycle, _, hcard, rfl⟩
  change cycle.edges.length ≤ Fintype.card V
  simpa only [EdgeGraph.Walk.edges_length] using hcard

/-- Mean weight of a nonempty edge list.  It is only used on lists known to
come from nonempty closed walks. -/
def edgeListMean (weight : E → ℝ) (edges : List E) : ℝ :=
  (edges.map weight).sum / edges.length

/-- **Maximum cycle-mean attainment.**  If the finite graph has any nonempty
closed walk, one of length at most the number of vertices attains the maximum
mean among all nonempty closed walks. -/
theorem exists_short_closedWalk_maximizing_mean
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (hexists : ∃ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length) :
    ∃ (vertex : V) (best : G.Walk vertex vertex),
      0 < best.length ∧ best.length ≤ Fintype.card V ∧
        ∀ (otherVertex : V) (other : G.Walk otherVertex otherVertex),
          0 < other.length →
            walkSum weight other / other.length ≤
              walkSum weight best / best.length := by
  obtain ⟨vertex, cycle, hcycle⟩ := hexists
  obtain ⟨shortVertex, short, hshortPos, hshortCard⟩ :=
    exists_short_closedWalk_of_nonempty cycle hcycle
  have hsetNonempty : (shortClosedEdgeLists G).Nonempty :=
    ⟨short.edges, shortVertex, short, hshortPos, hshortCard, rfl⟩
  obtain ⟨bestEdges, hbestEdges, hmax⟩ := Set.exists_max_image
    (shortClosedEdgeLists G) (edgeListMean weight)
      (finite_shortClosedEdgeLists G) hsetNonempty
  obtain ⟨bestVertex, best, hbestPos, hbestCard, hbestEq⟩ := hbestEdges
  refine ⟨bestVertex, best, hbestPos, hbestCard, ?_⟩
  have hshortBound (middle : V) (candidate : G.Walk middle middle)
      (hpos : 0 < candidate.length) (hcard : candidate.length ≤ Fintype.card V) :
      walkSum weight candidate ≤
        candidate.length * (walkSum weight best / best.length) := by
    have hcandidateMem : candidate.edges ∈ shortClosedEdgeLists G :=
      ⟨middle, candidate, hpos, hcard, rfl⟩
    have hmean := hmax candidate.edges hcandidateMem
    rw [edgeListMean, edgeListMean, ← hbestEq] at hmean
    simp only [EdgeGraph.Walk.edges_length] at hmean
    have hlengthPos : (0 : ℝ) < candidate.length := by exact_mod_cast hpos
    have hbound := (div_le_iff₀ hlengthPos).mp hmean
    simpa only [walkSum, mul_comm] using hbound
  have hall := closedWalk_le_length_mul_of_short weight
    (walkSum weight best / best.length) hshortBound
  intro otherVertex other hotherPos
  have hbound := hall otherVertex other
  have hlengthPos : (0 : ℝ) < other.length := by exact_mod_cast hotherPos
  apply (div_le_iff₀ hlengthPos).mpr
  simpa only [mul_comm] using hbound

/-- The optimal one-sided residual threshold is attained by one short closed
walk whenever any nonempty closed walk exists. -/
theorem exists_short_closedWalk_realizing_residual_threshold
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (hexists : ∃ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length) :
    ∃ (vertex : V) (best : G.Walk vertex vertex),
      0 < best.length ∧ best.length ≤ Fintype.card V ∧
        ∀ level : ℝ,
          WorstDirectedResidualAtMost G weight level ↔
            walkSum weight best / best.length ≤ level := by
  obtain ⟨vertex, best, hbestPos, hbestCard, hbest⟩ :=
    exists_short_closedWalk_maximizing_mean G weight hexists
  refine ⟨vertex, best, hbestPos, hbestCard, fun level => ?_⟩
  rw [worstDirectedResidualAtMost_iff_closedWalk_le]
  constructor
  · intro hall
    have hbound := hall vertex best
    have hlengthPos : (0 : ℝ) < best.length := by exact_mod_cast hbestPos
    apply (div_le_iff₀ hlengthPos).mpr
    simpa only [mul_comm] using hbound
  · intro hlevel otherVertex other
    by_cases hotherZero : other.length = 0
    · cases other with
      | nil => simp [walkSum]
      | concat edge initial => simp at hotherZero
    · have hotherPos : 0 < other.length := Nat.pos_of_ne_zero hotherZero
      have hmean := (hbest otherVertex other hotherPos).trans hlevel
      have hlengthPos : (0 : ℝ) < other.length := by
        exact_mod_cast hotherPos
      have hbound := (div_le_iff₀ hlengthPos).mp hmean
      simpa only [mul_comm] using hbound

/-- Strict negativity on nonempty closed walks up to the number of vertices gives a uniformly
negative residual bound on a finite graph. Acyclic graphs are included. -/
theorem exists_negative_residual_bound_of_short [Fintype V] [Finite E]
    (G : EdgeGraph V E) (weight : E → ℝ)
    (hnegative : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → cycle.length ≤ Fintype.card V → walkSum weight cycle < 0) :
    ∃ level : ℝ, level < 0 ∧ WorstDirectedResidualAtMost G weight level := by
  classical
  by_cases hexists : ∃ (vertex : V) (cycle : G.Walk vertex vertex), 0 < cycle.length
  · obtain ⟨vertex, best, hpos, hcard, hthreshold⟩ :=
      exists_short_closedWalk_realizing_residual_threshold G weight hexists
    refine ⟨walkSum weight best / best.length, ?_, (hthreshold _).mpr le_rfl⟩
    exact div_neg_of_neg_of_pos (hnegative vertex best hpos hcard) (by exact_mod_cast hpos)
  · refine ⟨-1, by norm_num, ?_⟩
    apply (worstDirectedResidualAtMost_iff_closedWalk_le G weight (-1)).mpr
    intro vertex cycle
    cases cycle with
    | nil => simp [walkSum]
    | concat edge walk =>
        exact (hexists ⟨G.target edge, walk.concat edge, by simp⟩).elim

/-- On a finite graph, strict negativity on every nonempty closed walk gives a potential
whose edge residuals have one strictly negative upper bound. Acyclic graphs are included. -/
theorem exists_negative_residual_bound [Fintype V] [Finite E]
    (G : EdgeGraph V E) (weight : E → ℝ)
    (hnegative : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → walkSum weight cycle < 0) :
    ∃ level : ℝ, level < 0 ∧ WorstDirectedResidualAtMost G weight level :=
  exists_negative_residual_bound_of_short G weight fun vertex cycle hpos _ =>
    hnegative vertex cycle hpos

end AdditiveTransport

end

end Maths
