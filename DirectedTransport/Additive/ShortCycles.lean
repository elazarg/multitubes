/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Quantitative
public import Mathlib.Data.Set.Finite.Lemmas

import Mathlib.Data.Set.Finite.List

/-!
# Short-cycle completeness for additive transport

On a finite vertex set, checking additive closed-walk inequalities only up to
the number of vertices is complete.  The proof removes a nonempty closed
subwalk from the prefix of any longer cycle and inducts on length.  It does not
require finite edge type, decidable equality, or a pre-existing simple-cycle
datatype.

Applied to uniformly shifted weights, this gives a bounded-cycle version of
the exact one-sided residual threshold.  Thus every obstruction has a closed
walk witness of length at most `Fintype.card V`.

## Main definitions

* `DirectedTransport.AdditiveTransport.shortClosedEdgeLists`: the edge lists realized by
  nonempty closed walks of length at most the number of vertices.  It is a finite set, which
  is what makes a maximizer available.
* `DirectedTransport.AdditiveTransport.edgeListMean`: the mean weight of an edge list.  It is
  only used on lists coming from nonempty closed walks.

## Main results

* `DirectedTransport.AdditiveTransport.worstDirectedResidualAtMost_iff_shortClosedWalk_le`: a
  one-sided residual threshold holds exactly when it holds on closed walks of length at most
  `Fintype.card V`.
* `DirectedTransport.AdditiveTransport.exists_short_closedWalk_of_not_worstDirectedResidualAtMost`:
  the witness form of the same fact — a failing threshold is refuted by one short closed walk.
* `DirectedTransport.AdditiveTransport.exists_short_closedWalk_maximizing_mean`: if any
  nonempty closed walk exists, one of length at most `Fintype.card V` attains the maximum mean
  among all nonempty closed walks.
* `DirectedTransport.AdditiveTransport.exists_short_closedWalk_realizing_residual_threshold`:
  that maximizer decides the threshold, so the optimal residual is its mean.  Note the
  nonemptiness hypothesis is required: with no nonempty closed walk there is no maximizer and
  every real threshold is attainable.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

open MaxPlusPotential

/-- If every nonempty closed walk of length at most the number of vertices has
nonpositive weight, then every closed walk has nonpositive weight. -/
theorem closedWalk_nonpos_of_short [Fintype V] (weight : E → ℝ)
    (hshort : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → cycle.length ≤ Fintype.card V →
        walkWeight weight cycle ≤ 0) :
    ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ 0 := by
  intro vertex cycle
  suffices hbounded : ∀ bound : ℕ, cycle.length ≤ bound →
      walkWeight weight cycle ≤ 0 by
    exact hbounded cycle.length le_rfl
  intro bound
  induction bound generalizing vertex cycle with
  | zero =>
      intro hlength
      have hzero : cycle.length = 0 := Nat.eq_zero_of_le_zero hlength
      cases cycle with
      | nil => simp [walkWeight]
      | concat before edge legal => simp at hzero
  | succ bound ih =>
      intro hlength
      by_cases hcard : cycle.length ≤ Fintype.card V
      · by_cases hnil : cycle.length = 0
        · cases cycle with
          | nil => simp [walkWeight]
          | concat before edge legal => simp at hnil
        · exact hshort vertex cycle (Nat.pos_of_ne_zero hnil) hcard
      · cases cycle with
        | nil => simp [walkWeight]
        | concat initial edge legal =>
            have hinitialDup : ¬initial.visited.Nodup := by
              intro hnodup
              have hlengthCard := hnodup.length_le_card
              rw [EdgeGraph.Walk.length_visited] at hlengthCard
              simp only [EdgeGraph.Walk.length_concat] at hcard
              exact hcard hlengthCard
            obtain ⟨middle, before, inner, after, hinnerPos, hedges⟩ :=
              initial.exists_closedSubwalk_of_not_nodup hinitialDup
            let remainder : G.Walk (G.target edge) (G.target edge) :=
              (before.append after).concat edge legal
            have hlengthEq : (initial.concat edge legal).length =
                inner.length + remainder.length := by
              have hedgeLength := congrArg List.length hedges
              simp only [List.length_append, EdgeGraph.Walk.edges_length] at hedgeLength
              simp only [EdgeGraph.Walk.length_concat,
                EdgeGraph.Walk.length_append, remainder]
              omega
            have hremainderPos : 0 < remainder.length := by
              simp [remainder]
            have hinnerLe : inner.length ≤ bound := by omega
            have hremainderLe : remainder.length ≤ bound := by omega
            have hinnerWeight := ih middle inner hinnerLe
            have hremainderWeight := ih (G.target edge) remainder hremainderLe
            have hweightEq : walkWeight weight (initial.concat edge legal) =
                walkWeight weight inner + walkWeight weight remainder := by
              simp only [walkWeight, EdgeGraph.Walk.edges_concat,
                EdgeGraph.Walk.edges_append, remainder, hedges,
                List.map_append, List.sum_append]
              ring
            rw [hweightEq]
            linarith

/-- It is enough to check closed-walk affine bounds on cycles of length at
most the number of vertices. -/
theorem closedWalk_le_length_mul_of_short [Fintype V]
    (weight : E → ℝ) (level : ℝ)
    (hshort : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → cycle.length ≤ Fintype.card V →
        walkWeight weight cycle ≤ cycle.length * level) :
    ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * level := by
  have hnonpos := closedWalk_nonpos_of_short
    (G := G) (fun edge => weight edge - level) (by
      intro vertex cycle hpos hcard
      rw [walkWeight_sub_const]
      have hbound := hshort vertex cycle hpos hcard
      linarith)
  intro vertex cycle
  have hbound := hnonpos vertex cycle
  rw [walkWeight_sub_const] at hbound
  linarith

/-- **Short-cycle exact threshold.**  On a finite graph, every obstruction to
a one-sided residual threshold occurs on a nonempty closed walk of
length at most the number of vertices. -/
theorem worstDirectedResidualAtMost_iff_shortClosedWalk_le
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    WorstDirectedResidualAtMost G weight level ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → cycle.length ≤ Fintype.card V →
          walkWeight weight cycle ≤ cycle.length * level := by
  rw [worstDirectedResidualAtMost_iff_closedWalk_le]
  constructor
  · intro hall vertex cycle _ _
    exact hall vertex cycle
  · exact closedWalk_le_length_mul_of_short weight level

/-- Failure of a residual threshold has a short positive shifted cycle
witness. -/
theorem exists_short_closedWalk_of_not_worstDirectedResidualAtMost
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ)
    (hfailure : ¬WorstDirectedResidualAtMost G weight level) :
    ∃ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length ∧ cycle.length ≤ Fintype.card V ∧
        cycle.length * level < walkWeight weight cycle := by
  rw [worstDirectedResidualAtMost_iff_shortClosedWalk_le] at hfailure
  push Not at hfailure
  exact hfailure

/-! ## Attainment of the maximum cycle mean -/

/-- Every nonempty closed walk contains some nonempty closed walk of length at
most the number of vertices. -/
theorem exists_short_closedWalk_of_nonempty [Fintype V]
    {vertex : V} (cycle : G.Walk vertex vertex) (hcycle : 0 < cycle.length) :
    ∃ (middle : V) (short : G.Walk middle middle),
      0 < short.length ∧ short.length ≤ Fintype.card V := by
  by_contra hnone
  have hnonpos := closedWalk_nonpos_of_short
    (G := G) (fun _ : E => (1 : ℝ)) (by
      intro middle short hpos hcard
      exfalso
      apply hnone
      exact ⟨middle, short, hpos, hcard⟩)
  have himpossible := hnonpos vertex cycle
  have hweight : walkWeight (fun _ : E => (1 : ℝ)) cycle = cycle.length := by
    simp [walkWeight, EdgeGraph.Walk.edges_length, nsmul_eq_mul]
  rw [hweight] at himpossible
  have hpositive : (0 : ℝ) < cycle.length := by exact_mod_cast hcycle
  linarith

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
            walkWeight weight other / other.length ≤
              walkWeight weight best / best.length := by
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
      walkWeight weight candidate ≤
        candidate.length * (walkWeight weight best / best.length) := by
    have hcandidateMem : candidate.edges ∈ shortClosedEdgeLists G :=
      ⟨middle, candidate, hpos, hcard, rfl⟩
    have hmean := hmax candidate.edges hcandidateMem
    rw [edgeListMean, edgeListMean, ← hbestEq] at hmean
    simp only [EdgeGraph.Walk.edges_length] at hmean
    have hlengthPos : (0 : ℝ) < candidate.length := by exact_mod_cast hpos
    have hbound := (div_le_iff₀ hlengthPos).mp hmean
    simpa only [walkWeight, mul_comm] using hbound
  have hall := closedWalk_le_length_mul_of_short weight
    (walkWeight weight best / best.length) hshortBound
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
            walkWeight weight best / best.length ≤ level := by
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
      | nil => simp [walkWeight]
      | concat initial edge legal => simp at hotherZero
    · have hotherPos : 0 < other.length := Nat.pos_of_ne_zero hotherZero
      have hmean := (hbest otherVertex other hotherPos).trans hlevel
      have hlengthPos : (0 : ℝ) < other.length := by
        exact_mod_cast hotherPos
      have hbound := (div_le_iff₀ hlengthPos).mp hmean
      simpa only [mul_comm] using hbound

end AdditiveTransport

end

end DirectedTransport
