/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Quantitative

/-!
# Simple-cycle reduction for additive transport

A nonempty closed walk is simple when it has no decomposition into two
nonempty closed walks at a repeated vertex.  Every nonempty closed walk is
dominated in mean weight by such a simple cycle.  Consequently all closed-walk
mean inequalities can be checked on simple cycles alone.

## Main definitions

* `Maths.AdditiveTransport.IsSimpleCycle`: a nonempty closed walk with no
  decomposition into two nonempty closed walks at a repeated vertex.  This is the
  decomposition-invariant form of a simple directed cycle, and it includes one-edge loops.
* `Maths.AdditiveTransport.CycleMeanDominates`: one closed walk has mean weight at
  least that of another, stated by cross-multiplication so that it is meaningful without
  dividing by a length.

## Main results

* `Maths.AdditiveTransport.exists_simpleCycle_cycleMeanDominates`: every nonempty
  closed walk is dominated in mean weight by some simple cycle.  This is the engine of the
  file and needs no finiteness assumption.
* `Maths.AdditiveTransport.forall_closedWalk_mean_le_iff_simpleCycle`: a cycle-mean
  bound holds for all closed walks exactly when it holds for the simple ones.
* `Maths.AdditiveTransport.worstDirectedResidualAtMost_iff_simpleCycles_le`: the
  additive worst-residual threshold can be tested on simple cycles alone.  Unlike the two
  results above, this one assumes `Finite E`, inherited from the residual duality it
  rewrites through.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- A closed walk with no proper nonempty closed subwalk whose removal leaves
a nonempty closed walk.  This is the decomposition-invariant form of a simple
directed cycle and includes one-edge loops. -/
def IsSimpleCycle {base : V} (cycle : G.Walk base base) : Prop :=
  0 < cycle.length ∧
    ∀ (vertex : V) (before : G.Walk base vertex)
      (inner : G.Walk vertex vertex) (after : G.Walk vertex base),
      cycle.edges = before.edges ++ inner.edges ++ after.edges →
      0 < inner.length → 0 < before.length + after.length → False

/-- Cross-multiplied comparison of cycle means, avoiding division and defined
safely for an empty reference walk. -/
def CycleMeanDominates (weight : E → ℝ) {firstBase secondBase : V}
    (first : G.Walk firstBase firstBase)
    (second : G.Walk secondBase secondBase) : Prop :=
  second.length * MaxPlusPotential.walkWeight weight first ≥
    first.length * MaxPlusPotential.walkWeight weight second

private theorem cycle_weight_eq_of_decomposition (weight : E → ℝ)
    {base vertex : V} (cycle : G.Walk base base)
    (before : G.Walk base vertex) (inner : G.Walk vertex vertex)
    (after : G.Walk vertex base)
    (hedges : cycle.edges = before.edges ++ inner.edges ++ after.edges) :
    MaxPlusPotential.walkWeight weight cycle =
      MaxPlusPotential.walkWeight weight inner +
        MaxPlusPotential.walkWeight weight (before.append after) := by
  simp only [MaxPlusPotential.walkWeight, hedges, List.map_append,
    List.sum_append, EdgeGraph.Walk.edges_append]
  ring

private theorem cycle_length_eq_of_decomposition
    {base vertex : V} (cycle : G.Walk base base)
    (before : G.Walk base vertex) (inner : G.Walk vertex vertex)
    (after : G.Walk vertex base)
    (hedges : cycle.edges = before.edges ++ inner.edges ++ after.edges) :
    cycle.length = inner.length + (before.append after).length := by
  rw [← cycle.edges_length, hedges]
  simp [Nat.add_comm, Nat.add_assoc]

/-- **Simple-cycle domination.**  Every nonempty closed walk has a simple
cycle whose mean weight is at least as large. -/
theorem exists_simpleCycle_cycleMeanDominates (weight : E → ℝ)
    {base : V} (reference : G.Walk base base) (hne : 0 < reference.length) :
    ∃ (simpleBase : V) (simple : G.Walk simpleBase simpleBase),
      IsSimpleCycle simple ∧ CycleMeanDominates weight simple reference := by
  classical
  let Good : ℕ → Prop := fun length =>
    ∃ (candidateBase : V) (candidate : G.Walk candidateBase candidateBase),
      0 < candidate.length ∧ candidate.length = length ∧
        CycleMeanDominates weight candidate reference
  have hexists : ∃ length, Good length :=
    ⟨reference.length, base, reference, hne, rfl, le_rfl⟩
  let minimum := Nat.find hexists
  obtain ⟨candidateBase, candidate, hcandidateNe, hlength, hdominates⟩ :=
    Nat.find_spec hexists
  refine ⟨candidateBase, candidate, ⟨hcandidateNe, ?_⟩, hdominates⟩
  intro vertex before inner after hedges hinner hremainder
  let remainder : G.Walk candidateBase candidateBase := before.append after
  have hremainder' : 0 < remainder.length := by
    simpa [remainder] using hremainder
  have hweight := cycle_weight_eq_of_decomposition
    weight candidate before inner after hedges
  have hlen := cycle_length_eq_of_decomposition
    candidate before inner after hedges
  have hcomponent :
      CycleMeanDominates weight inner reference ∨
        CycleMeanDominates weight remainder reference := by
    by_contra hnot
    push Not at hnot
    simp only [CycleMeanDominates] at hdominates hnot
    dsimp [remainder] at hnot
    have hinnerLt := lt_of_not_ge hnot.1
    have hremainderLt := lt_of_not_ge hnot.2
    have hlenReal : (candidate.length : ℝ) =
        inner.length + (before.append after).length := by
      exact_mod_cast hlen
    have hcandidateLt :
        reference.length * MaxPlusPotential.walkWeight weight candidate <
          candidate.length * MaxPlusPotential.walkWeight weight reference := by
      rw [hweight, hlenReal]
      nlinarith
    exact (not_lt_of_ge hdominates) hcandidateLt
  have hminimal {length} (hgood : Good length) : minimum ≤ length :=
    Nat.find_min' hexists hgood
  rcases hcomponent with hinnerDominates | hremainderDominates
  · have hgood : Good inner.length :=
      ⟨vertex, inner, hinner, rfl, hinnerDominates⟩
    have hle := hminimal hgood
    have hlength' : candidate.length = minimum := hlength
    have hle' : candidate.length ≤ inner.length := hlength'.trans_le hle
    have hremainder'' : 0 < (before.append after).length := by
      simpa [remainder] using hremainder'
    have hlt : inner.length < candidate.length := by omega
    exact (not_lt_of_ge hle') hlt
  · have hgood : Good remainder.length :=
      ⟨candidateBase, remainder, hremainder', rfl, hremainderDominates⟩
    have hle := hminimal hgood
    have hlength' : candidate.length = minimum := hlength
    have hle' : candidate.length ≤ remainder.length := hlength'.trans_le hle
    have hlt : remainder.length < candidate.length := by
      dsimp [remainder]
      omega
    exact (not_lt_of_ge hle') hlt

/-- A strict violation of a cycle-mean threshold has a simple-cycle witness. -/
theorem exists_simpleCycle_mean_gt_of_closedWalk
    (weight : E → ℝ) (level : ℝ) {base : V}
    (cycle : G.Walk base base)
    (hviolation : cycle.length * level <
      MaxPlusPotential.walkWeight weight cycle) :
    ∃ (simpleBase : V) (simple : G.Walk simpleBase simpleBase),
      IsSimpleCycle simple ∧
        simple.length * level < MaxPlusPotential.walkWeight weight simple := by
  have hne : 0 < cycle.length := by
    by_contra hnot
    have hzero : cycle.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hempty : cycle.edges = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hzero
    simp [MaxPlusPotential.walkWeight, hzero, hempty] at hviolation
  obtain ⟨simpleBase, simple, hsimple, hdominates⟩ :=
    exists_simpleCycle_cycleMeanDominates weight cycle hne
  refine ⟨simpleBase, simple, hsimple, ?_⟩
  simp only [CycleMeanDominates] at hdominates
  have hsimplePos : (0 : ℝ) < simple.length := by exact_mod_cast hsimple.1
  have hcyclePos : (0 : ℝ) < cycle.length := by exact_mod_cast hne
  have hscaledViolation := mul_lt_mul_of_pos_left hviolation hsimplePos
  by_contra hnot
  have hsimpleLe : MaxPlusPotential.walkWeight weight simple ≤
      simple.length * level := le_of_not_gt hnot
  have hscaledSimple := mul_le_mul_of_nonneg_left hsimpleLe hcyclePos.le
  nlinarith

/-- Closed-walk cycle-mean bounds are equivalent to their restriction to
simple cycles. -/
theorem forall_closedWalk_mean_le_iff_simpleCycle
    (weight : E → ℝ) (level : ℝ) :
    (∀ (base : V) (cycle : G.Walk base base),
      MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level) ↔
    (∀ (base : V) (cycle : G.Walk base base),
      IsSimpleCycle cycle →
        MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level) := by
  constructor
  · intro hall base cycle _
    exact hall base cycle
  · intro hsimple base cycle
    by_contra hnot
    have hviolation : cycle.length * level <
        MaxPlusPotential.walkWeight weight cycle := lt_of_not_ge hnot
    obtain ⟨simpleBase, simple, hs, hgt⟩ :=
      exists_simpleCycle_mean_gt_of_closedWalk weight level cycle hviolation
    exact (not_lt_of_ge (hsimple simpleBase simple hs)) hgt

/-- The additive worst-residual threshold can be tested on simple cycles. -/
theorem worstDirectedResidualAtMost_iff_simpleCycles_le
    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    WorstDirectedResidualAtMost G weight level ↔
      ∀ (base : V) (cycle : G.Walk base base),
        IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level := by
  rw [worstDirectedResidualAtMost_iff_closedWalk_le,
    forall_closedWalk_mean_le_iff_simpleCycle]

end AdditiveTransport

end

end Maths
