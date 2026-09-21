/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Cycles
public import Maths.Graph.Circulation
import Mathlib.Algebra.BigOperators.Field

/-!
# Circuit characterization of symmetric additive transport

Doubling every edge by its reverse orientation turns the symmetric additive
residual problem into an ordinary directed residual problem.  Hence its
normalized signed-circulation dual is equivalent, at every threshold, to
testing closed walks in the doubled graph, and then to testing simple circuits
alone.

## Main definitions

* `Maths.AdditiveTransport.signedGraph`: the doubled graph, whose edges are the two
  orientations of each original edge.
* `Maths.AdditiveTransport.circuitCoefficient`: the normalized edge-multiplicity
  vector of a circuit in the doubled graph, read as a signed-circulation certificate.

## Main results

* `Maths.AdditiveTransport.symmetricResidualAtMost_iff_signedGraph`: the structural
  step the rest of the file rests on - symmetric residual feasibility on `G` is ordinary
  directed residual feasibility on `signedGraph G`.  It needs no finiteness.
* `Maths.AdditiveTransport.circuitCoefficient_isNormalizedCertificate`: every
  nonempty circuit in the doubled graph is a normalized signed-circulation certificate.
* `Maths.AdditiveTransport.symmetricResidualAtMost_iff_signedClosedWalk_le` and
  `symmetricResidualAtMost_iff_simpleSignedCycles_le`: symmetric feasibility is the mean bound
  on every circuit of the doubled graph, and testing simple circuits alone suffices.
* `Maths.AdditiveTransport.normalizedSignedDual_le_iff_signedClosedWalk_le` and
  `normalizedSignedDual_le_iff_simpleSignedCycles_le`: the dual reading of the same pair -
  normalized signed circulations and directed circuits impose exactly the same thresholds.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE}

/-- The directed graph containing both orientations of every edge identity. -/
def signedGraph (G : EdgeGraph V E) : EdgeGraph V (SignedEdge E) where
  source
    | (edge, false) => G.source edge
    | (edge, true) => G.target edge
  target
    | (edge, false) => G.target edge
    | (edge, true) => G.source edge

@[simp] theorem signedGraph_source_false (G : EdgeGraph V E) (edge : E) :
    (signedGraph G).source (edge, false) = G.source edge := rfl

@[simp] theorem signedGraph_source_true (G : EdgeGraph V E) (edge : E) :
    (signedGraph G).source (edge, true) = G.target edge := rfl

@[simp] theorem signedGraph_target_false (G : EdgeGraph V E) (edge : E) :
    (signedGraph G).target (edge, false) = G.target edge := rfl

@[simp] theorem signedGraph_target_true (G : EdgeGraph V E) (edge : E) :
    (signedGraph G).target (edge, true) = G.source edge := rfl

/-- Signed rows are the target-minus-source incidence rows of the doubled
graph. -/
theorem signedDelta_eq_signedGraph_incidence [DecidableEq V]
    (G : EdgeGraph V E) (edge : SignedEdge E) (vertex : V) :
    signedDelta G edge vertex =
      (if vertex = (signedGraph G).target edge then 1 else 0) -
        (if vertex = (signedGraph G).source edge then 1 else 0) := by
  rcases edge with ⟨edge, orientation⟩
  cases orientation <;> rfl

@[simp] theorem defect_signedGraph_false (G : EdgeGraph V E)
    (weight : E → ℝ) (potential : V → ℝ) (edge : E) :
    MaxPlusPotential.defect (signedGraph G) (signedBase weight) potential
        (edge, false) =
      MaxPlusPotential.defect G weight potential edge := rfl

@[simp] theorem defect_signedGraph_true (G : EdgeGraph V E)
    (weight : E → ℝ) (potential : V → ℝ) (edge : E) :
    MaxPlusPotential.defect (signedGraph G) (signedBase weight) potential
        (edge, true) =
      -MaxPlusPotential.defect G weight potential edge := by
  simp [MaxPlusPotential.defect, signedBase]
  ring

/-- The probability distribution of edge occurrences in a nonempty closed
walk. -/
def circuitCoefficient [DecidableEq E] {G : EdgeGraph V E} {base : V}
    (cycle : G.Walk base base) (edge : E) : ℝ :=
  cycle.edgeMultiplicity edge / cycle.length

private theorem sum_edgeMultiplicity_eq_length [Fintype E] [DecidableEq E]
    {G : EdgeGraph V E} {start finish : V} (walk : G.Walk start finish) :
    ∑ edge, walk.edgeMultiplicity edge = walk.length := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      simp only [EdgeGraph.Walk.edgeMultiplicity_concat,
        EdgeGraph.Walk.length_concat, Finset.sum_add_distrib, ih]
      simp

private theorem sum_edgeMultiplicity_mul_eq_walkWeight
    [Fintype E] [DecidableEq E] {G : EdgeGraph V E}
    (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) :
    ∑ edge, (walk.edgeMultiplicity edge : ℝ) * weight edge =
      MaxPlusPotential.walkWeight weight walk := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      simp only [EdgeGraph.Walk.edgeMultiplicity_concat, Nat.cast_add,
        add_mul, Finset.sum_add_distrib, ih,
        MaxPlusPotential.walkWeight_concat]
      simp

private theorem sum_edgeMultiplicity_mul_signedDelta_eq_zero
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : EdgeGraph V E) {base : V}
    (cycle : (signedGraph G).Walk base base) (vertex : V) :
    ∑ edge, (cycle.edgeMultiplicity edge : ℝ) * signedDelta G edge vertex = 0 := by
  have hbalance := cycle.edgeMultiplicity_balanced vertex
  have hbalanceReal :
      (∑ edge with (signedGraph G).source edge = vertex,
          (cycle.edgeMultiplicity edge : ℝ)) =
        ∑ edge with (signedGraph G).target edge = vertex,
          (cycle.edgeMultiplicity edge : ℝ) := by
    exact_mod_cast hbalance
  simp_rw [signedDelta_eq_signedGraph_incidence]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  /- Both endpoint maps turn the indicator sum into the corresponding filtered sum. -/
  have hfilter : ∀ endpoint : SignedEdge E → V,
      (∑ edge, if vertex = endpoint edge then (cycle.edgeMultiplicity edge : ℝ) else 0) =
        ∑ edge with endpoint edge = vertex, (cycle.edgeMultiplicity edge : ℝ) := by
    intro endpoint
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun edge _ => ?_
    by_cases h : vertex = endpoint edge
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  rw [hfilter, hfilter, hbalanceReal, sub_self]

/-- Every nonempty directed circuit in the doubled graph is a normalized
signed-circulation certificate. -/
theorem circuitCoefficient_isNormalizedCertificate
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) {base : V}
    (cycle : (signedGraph G).Walk base base) (hne : 0 < cycle.length) :
    FiniteInequality.IsNormalizedCertificate (signedDelta G)
      (circuitCoefficient cycle) := by
  refine ⟨fun edge => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_, ?_⟩
  · simp only [circuitCoefficient, ← Finset.sum_div]
    rw [show (∑ edge, (cycle.edgeMultiplicity edge : ℝ)) = cycle.length by
      exact_mod_cast sum_edgeMultiplicity_eq_length cycle]
    exact div_self (by exact_mod_cast hne.ne')
  · intro vertex
    simp only [circuitCoefficient, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_edgeMultiplicity_mul_signedDelta_eq_zero G cycle vertex, zero_div]

/-- The objective of a circuit certificate is its signed mean weight. -/
theorem certificateValue_circuitCoefficient
    [Fintype E] [DecidableEq E] (G : EdgeGraph V E) (weight : E → ℝ)
    {base : V} (cycle : (signedGraph G).Walk base base) :
    FiniteInequality.certificateValue (signedBase weight)
        (circuitCoefficient cycle) =
      MaxPlusPotential.walkWeight (signedBase weight) cycle / cycle.length := by
  simp only [FiniteInequality.certificateValue, circuitCoefficient,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_edgeMultiplicity_mul_eq_walkWeight]

theorem dotProduct_signedDelta_eq_signedGraph_difference
    [Fintype V] [DecidableEq V] (G : EdgeGraph V E)
    (edge : SignedEdge E) (potential : V → ℝ) :
    dotProduct (signedDelta G edge) potential =
      potential ((signedGraph G).target edge) -
        potential ((signedGraph G).source edge) := by
  rcases edge with ⟨edge, orientation⟩
  cases orientation with
  | false => exact dotProduct_signedDelta_false G edge potential
  | true => exact dotProduct_signedDelta_true G edge potential

/-- Directed residual feasibility on the doubled graph is the generic finite
row system for its signed incidence matrix. -/
theorem worstDirectedResidualAtMost_signedGraph_iff_finiteInequality
    [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    WorstDirectedResidualAtMost (signedGraph G) orientedWeight level ↔
      FiniteInequality.WorstResidualAtMost
        (signedDelta G) orientedWeight level := by
  apply exists_congr
  intro potential
  apply forall_congr'
  intro edge
  rw [dotProduct_signedDelta_eq_signedGraph_difference]
  simp only [MaxPlusPotential.defect]
  constructor <;> intro h <;> linarith

/-- **Full signed-circulation circuit duality.**  For every objective on the
two oriented copies, normalized signed circulations and directed circuits
impose exactly the same thresholds. -/
theorem normalizedSignedCirculationDual_le_iff_closedWalk_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue orientedWeight coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        MaxPlusPotential.walkWeight orientedWeight cycle ≤
          cycle.length * level := by
  rw [← FiniteInequality.worstResidualAtMost_iff_normalizedDual_le,
    ← worstDirectedResidualAtMost_signedGraph_iff_finiteInequality,
    worstDirectedResidualAtMost_iff_closedWalk_le]

/-- The full signed-circulation dual can be restricted to simple directed
circuits in the doubled graph. -/
theorem normalizedSignedCirculationDual_le_iff_simpleCycles_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue orientedWeight coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight orientedWeight cycle ≤
            cycle.length * level := by
  rw [normalizedSignedCirculationDual_le_iff_closedWalk_le,
    forall_closedWalk_mean_le_iff_simpleCycle]

/-- Symmetric residual feasibility is directed residual feasibility on the
doubled orientation graph. -/
theorem symmetricResidualAtMost_iff_signedGraph
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    SymmetricResidualAtMost G weight level ↔
      WorstDirectedResidualAtMost (signedGraph G) (signedBase weight) level := by
  apply exists_congr
  intro potential
  constructor
  · intro hsymmetric signed
    rcases signed with ⟨edge, orientation⟩
    cases orientation with
    | false =>
        simpa using (abs_le.mp (hsymmetric edge)).2
    | true =>
        have hlower := (abs_le.mp (hsymmetric edge)).1
        simp only [defect_signedGraph_true]
        linarith
  · intro hdirected edge
    apply abs_le.mpr
    constructor
    · have hreverse := hdirected (edge, true)
      simp only [defect_signedGraph_true] at hreverse
      linarith
    · simpa using hdirected (edge, false)

/-- **Exact symmetric circuit threshold.**  Symmetric residual feasibility is
equivalent to the mean bound on every circuit in the doubled graph. -/
theorem symmetricResidualAtMost_iff_signedClosedWalk_le
    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    SymmetricResidualAtMost G weight level ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        MaxPlusPotential.walkWeight (signedBase weight) cycle ≤
          cycle.length * level := by
  rw [symmetricResidualAtMost_iff_signedGraph,
    worstDirectedResidualAtMost_iff_closedWalk_le]

/-- It is enough to test simple circuits in the doubled graph. -/
theorem symmetricResidualAtMost_iff_simpleSignedCycles_le
    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    SymmetricResidualAtMost G weight level ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight (signedBase weight) cycle ≤
            cycle.length * level := by
  rw [symmetricResidualAtMost_iff_signedClosedWalk_le,
    forall_closedWalk_mean_le_iff_simpleCycle]

/-- Normalized signed circulations and directed circuits impose exactly the
same objective thresholds. -/
theorem normalizedSignedDual_le_iff_signedClosedWalk_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue
          (signedBase weight) coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        MaxPlusPotential.walkWeight (signedBase weight) cycle ≤
          cycle.length * level := by
  rw [← symmetricResidualAtMost_iff_normalizedSignedDual_le,
    symmetricResidualAtMost_iff_signedClosedWalk_le]

/-- Normalized signed circulations can equivalently be tested through simple
circuits alone. -/
theorem normalizedSignedDual_le_iff_simpleSignedCycles_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue
          (signedBase weight) coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight (signedBase weight) cycle ≤
            cycle.length * level := by
  rw [← symmetricResidualAtMost_iff_normalizedSignedDual_le,
    symmetricResidualAtMost_iff_simpleSignedCycles_le]

end AdditiveTransport

end

end Maths
