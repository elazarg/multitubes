/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Additive.Circuits
public import Mathlib.Analysis.Convex.Combination

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Set.Finite.List

/-!
# Literal circuit decomposition for symmetric additive transport

A normalized nonnegative circulation on the doubled orientation graph is a
convex combination of simple directed circuits.  Projecting the two copies of
each edge gives the usual signed circulation with `l1` norm at most one.

The doubled graph has one harmless degeneracy: traversing an edge and
immediately traversing the reverse copy is a simple two-edge cycle, but its
projected circulation and objective are zero.  We identify these immediate
backtracks explicitly.  Distinct antiparallel edge identities remain genuine
multigraph circuits.

## Main definitions

* `Maths.AdditiveTransport.IsUnitSignedCirculation`: the explicit signed-circulation
  polytope - vertex balance together with `l1` mass at most one.
* `Maths.AdditiveTransport.signedProjection` and `signedCircuitVector`: the
  difference of the forward and reverse masses over each original edge, and its value on a
  doubled-graph circuit.
* `Maths.AdditiveTransport.IsImmediateSignedBacktrack` and
  `IsGenuineSignedCircuit`: the degenerate circuit traversing one edge identity and then its
  own reverse copy, and a simple circuit that is not one of those.  Two *distinct* antiparallel
  edge identities form a genuine circuit, not a backtrack.
* `Maths.AdditiveTransport.signedCirculationObjective` and
  `absoluteSignedCircuitValues`: the objective pairing a circulation with edge data, and the
  set of absolute genuine-circuit means together with the zero circulation's value.

## Main results

* `Maths.AdditiveTransport.normalizedCertificate_mem_convexHull_simpleSignedCircuits`
  and `exists_simpleSignedCircuit_decomposition`: every normalized certificate lies in the
  convex hull of simple circuit certificates, in abstract and explicit finite-sum form.
* `Maths.AdditiveTransport.isUnitSignedCirculation_iff_exists_normalizedLift`: the
  concrete balance-and-`l1` conditions are exactly the projections of normalized doubled-graph
  certificates.
* `Maths.AdditiveTransport.exists_genuineSignedCircuitVector_decomposition`: the
  literal decomposition with backtrack terms erased.  The surviving coefficients are
  nonnegative with total mass at most one - not exactly one, since erasing backtracks discards
  mass - and every positively weighted cycle is a genuine multigraph circuit.
* `Maths.AdditiveTransport.unitSignedCirculationObjective_le_iff_genuineCircuitMean_le`:
  the support function of the polytope is controlled exactly by absolute signed means of
  genuine circuits.  The separate `0 ≤ level` conjunct is not redundant; it is the value
  contributed by the zero circulation.
* `Maths.AdditiveTransport.exists_absoluteSignedCircuitOptimum`: that support
  optimum is attained.

The decomposition results above all assume `Nonempty E`, because the canonical lift needs an
edge on which to park unused `l1` mass.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

/-- The normalized edge-count vector determined by an untyped edge list. -/
def edgeListCoefficient [DecidableEq E] (edges : List E) (edge : E) : ℝ :=
  edges.count edge / edges.length

theorem circuitCoefficient_eq_edgeListCoefficient [DecidableEq E]
    {G : EdgeGraph V E} {base : V} (cycle : G.Walk base base) :
    circuitCoefficient cycle = edgeListCoefficient cycle.edges := by
  funext edge
  simp only [circuitCoefficient, edgeListCoefficient,
    cycle.edgeMultiplicity_eq_count, EdgeGraph.Walk.edges_length]

/-- Coefficient vectors of nonempty simple circuits in the doubled graph. -/
def simpleSignedCircuitCoefficients [DecidableEq E] (G : EdgeGraph V E) :
    Set (SignedEdge E → ℝ) :=
  {coefficient | ∃ (base : V) (cycle : (signedGraph G).Walk base base),
    IsSimpleCycle cycle ∧ circuitCoefficient cycle = coefficient}

/-- A decomposition-simple cycle on a finite graph has at most one edge per
vertex. -/
theorem IsSimpleCycle.length_le_card [Fintype V] {G : EdgeGraph V E}
    {base : V} {cycle : G.Walk base base} (hsimple : IsSimpleCycle cycle) :
    cycle.length ≤ Fintype.card V := by
  classical
  by_contra hcard
  cases cycle with
  | nil => exact (Nat.not_lt_zero _ hsimple.1)
  | concat initial edge legal =>
      have hinitialDup : ¬initial.visited.Nodup := by
        intro hnodup
        have hlengthCard := hnodup.length_le_card
        rw [EdgeGraph.Walk.length_visited] at hlengthCard
        simp only [EdgeGraph.Walk.length_concat] at hcard
        exact hcard hlengthCard
      obtain ⟨middle, before, inner, after, hinnerPos, hedges⟩ :=
        initial.exists_closedSubwalk_of_not_nodup hinitialDup
      have hcycleEdges :
          (initial.concat edge legal).edges =
            before.edges ++ inner.edges ++ (after.concat edge legal).edges := by
        simp only [EdgeGraph.Walk.edges_concat, hedges, List.append_assoc]
      exact hsimple.2 middle before inner (after.concat edge legal)
        hcycleEdges hinnerPos (by simp)

/-- There are only finitely many normalized coefficient vectors of simple
signed circuits on a finite multigraph. -/
theorem finite_simpleSignedCircuitCoefficients
    [Fintype V] [Fintype E] [DecidableEq E] (G : EdgeGraph V E) :
    (simpleSignedCircuitCoefficients G).Finite := by
  let boundedLists : Set (List (SignedEdge E)) :=
    {edges | edges.length ≤ Fintype.card V}
  have hfinite : boundedLists.Finite := List.finite_length_le _ _
  apply (hfinite.image edgeListCoefficient).subset
  rintro coefficient ⟨base, cycle, hsimple, rfl⟩
  refine ⟨cycle.edges, ?_, ?_⟩
  · change cycle.edges.length ≤ Fintype.card V
    simpa only [EdgeGraph.Walk.edges_length] using hsimple.length_le_card
  · exact (circuitCoefficient_eq_edgeListCoefficient cycle).symm

private theorem continuousLinearMap_eq_certificateValue
    [Fintype E] [DecidableEq E]
    (functional : (SignedEdge E → ℝ) →L[ℝ] ℝ)
    (coefficient : SignedEdge E → ℝ) :
    functional coefficient =
      FiniteInequality.certificateValue
        (fun edge => functional (Pi.single edge 1)) coefficient := by
  calc
    functional coefficient =
        functional (∑ edge, Pi.single edge (coefficient edge)) := by
          rw [LinearMap.sum_single_apply]
    _ = ∑ edge, coefficient edge * functional (Pi.single edge 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro edge _
      conv_lhs =>
        rw [show coefficient edge = coefficient edge • (1 : ℝ) by simp,
          Pi.single_smul, map_smul, smul_eq_mul]
    _ = _ := rfl

private theorem sum_edgeMultiplicity_mul_eq_walkWeight_general
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

private theorem certificateValue_circuitCoefficient_general
    [Fintype E] [DecidableEq E] {G : EdgeGraph V E}
    (weight : E → ℝ) {base : V} (cycle : G.Walk base base) :
    FiniteInequality.certificateValue weight (circuitCoefficient cycle) =
      MaxPlusPotential.walkWeight weight cycle / cycle.length := by
  simp only [FiniteInequality.certificateValue, circuitCoefficient,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_edgeMultiplicity_mul_eq_walkWeight_general]

/-- **Literal normalized-circulation decomposition.**  Every normalized
nonnegative circulation on the doubled orientation graph belongs to the
convex hull of its simple-circuit coefficient vectors. -/
theorem normalizedCertificate_mem_convexHull_simpleSignedCircuits
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (hcoefficient :
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) :
    coefficient ∈ convexHull ℝ (simpleSignedCircuitCoefficients G) := by
  by_contra hnot
  let circuits := simpleSignedCircuitCoefficients G
  have hfinite : circuits.Finite := finite_simpleSignedCircuitCoefficients G
  obtain ⟨functional, level, hcircuit, hcoefficientLevel⟩ :=
    geometric_hahn_banach_closed_point
      (convex_convexHull ℝ circuits)
      (hfinite.isClosed_convexHull ℝ) hnot
  let orientedWeight : SignedEdge E → ℝ :=
    fun edge => functional (Pi.single edge 1)
  have hsimple (base : V) (cycle : (signedGraph G).Walk base base)
      (hcycle : IsSimpleCycle cycle) :
      MaxPlusPotential.walkWeight orientedWeight cycle ≤
        cycle.length * level := by
    have hmem : circuitCoefficient cycle ∈ circuits :=
      ⟨base, cycle, hcycle, rfl⟩
    have hstrict := hcircuit _ (subset_convexHull ℝ circuits hmem)
    rw [continuousLinearMap_eq_certificateValue functional,
      certificateValue_circuitCoefficient_general orientedWeight] at hstrict
    have hlength : (0 : ℝ) < cycle.length := by
      exact_mod_cast hcycle.1
    simpa only [mul_comm] using ((div_lt_iff₀ hlength).mp hstrict).le
  have hdual :=
    (normalizedSignedCirculationDual_le_iff_simpleCycles_le
      G orientedWeight level).mpr hsimple coefficient hcoefficient
  rw [← continuousLinearMap_eq_certificateValue functional coefficient] at hdual
  exact (not_lt_of_ge hdual) hcoefficientLevel

/-- An explicit finite convex decomposition of a normalized doubled-graph
circulation into genuine simple directed cycles. -/
theorem exists_simpleSignedCircuit_decomposition
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (hcoefficient :
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) :
    ∃ (ι : Type) (_ : Fintype ι) (convexWeight : ι → ℝ)
      (base : ι → V)
      (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
      (∀ i, 0 ≤ convexWeight i) ∧
      (∑ i, convexWeight i) = 1 ∧
      (∀ i, IsSimpleCycle (cycle i)) ∧
      ∀ edge, coefficient edge =
        ∑ i, convexWeight i * circuitCoefficient (cycle i) edge := by
  have hmem :=
    normalizedCertificate_mem_convexHull_simpleSignedCircuits
      G coefficient hcoefficient
  rw [mem_convexHull_iff_exists_fintype] at hmem
  obtain ⟨ι, inst, convexWeight, point, hnonneg, hsum, hpoint, hcoefficientSum⟩ :=
    hmem
  let base : ι → V := fun i => (hpoint i).choose
  let cycle : ∀ i, (signedGraph G).Walk (base i) (base i) :=
    fun i => (hpoint i).choose_spec.choose
  have hcycle (i : ι) : IsSimpleCycle (cycle i) :=
    (hpoint i).choose_spec.choose_spec.1
  have hpointEq (i : ι) : circuitCoefficient (cycle i) = point i :=
    (hpoint i).choose_spec.choose_spec.2
  refine ⟨ι, inst, convexWeight, base, cycle, hnonneg, hsum, hcycle, ?_⟩
  intro edge
  have heq := congrFun hcoefficientSum.symm edge
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpointEq] using heq

/-! ## Projection to ordinary signed circulations -/

/-- Difference of the forward and reverse masses over each original edge. -/
def signedProjection (coefficient : SignedEdge E → ℝ) (edge : E) : ℝ :=
  coefficient (edge, false) - coefficient (edge, true)

/-- The explicit signed-circulation polytope: vertex balance and `l1` mass at
most one. -/
def IsUnitSignedCirculation [Fintype E] [DecidableEq V]
    (G : EdgeGraph V E) (circulation : E → ℝ) : Prop :=
  (∀ vertex, ∑ edge, circulation edge * signedDelta G (edge, false) vertex = 0) ∧
    ∑ edge, |circulation edge| ≤ 1

private theorem signedDelta_true_eq_neg [DecidableEq V]
    (G : EdgeGraph V E) (edge : E) (vertex : V) :
    signedDelta G (edge, true) vertex = -signedDelta G (edge, false) vertex := by
  simp only [signedDelta]
  ring

/-- Projecting a normalized doubled-graph circulation gives a balanced signed
circulation of `l1` mass at most one. -/
theorem isUnitSignedCirculation_signedProjection
    [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (hcoefficient :
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) :
    IsUnitSignedCirculation G (signedProjection coefficient) := by
  classical
  constructor
  · intro vertex
    have hbalance := hcoefficient.2.2 vertex
    rw [Fintype.sum_prod_type] at hbalance
    simp only [Fintype.sum_bool, signedDelta_true_eq_neg] at hbalance
    simp only [signedProjection]
    rw [← hbalance]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  · calc
      ∑ edge, |signedProjection coefficient edge| ≤
          ∑ edge, (coefficient (edge, false) + coefficient (edge, true)) := by
        apply Finset.sum_le_sum
        intro edge _
        simp only [signedProjection]
        have habs := abs_sub (coefficient (edge, false)) (coefficient (edge, true))
        simpa only [abs_of_nonneg (hcoefficient.1 (edge, false)),
          abs_of_nonneg (hcoefficient.1 (edge, true))] using habs
      _ = ∑ edge : SignedEdge E, coefficient edge := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, add_comm]
      _ = 1 := hcoefficient.2.1

private theorem max_zero_add_max_neg_zero_eq_abs (value : ℝ) :
    max value 0 + max (-value) 0 = |value| := by
  by_cases hvalue : 0 ≤ value
  · rw [max_eq_left hvalue, max_eq_right (neg_nonpos.mpr hvalue),
      add_zero, abs_of_nonneg hvalue]
  · have hvalue' : value ≤ 0 := le_of_not_ge hvalue
    rw [max_eq_right hvalue', max_eq_left (neg_nonneg.mpr hvalue'),
      zero_add, abs_of_nonpos hvalue']

/-- Canonical lift of a signed circulation.  Unused `l1` mass is split
equally between the two orientations of `chosen`; this is precisely an
immediate-backtrack circulation. -/
def signedCirculationLift [Fintype E] [DecidableEq E]
    (chosen : E) (circulation : E → ℝ) : SignedEdge E → ℝ
  | (edge, false) =>
      max (circulation edge) 0 +
        if edge = chosen then (1 - ∑ other, |circulation other|) / 2 else 0
  | (edge, true) =>
      max (-circulation edge) 0 +
        if edge = chosen then (1 - ∑ other, |circulation other|) / 2 else 0

@[simp] theorem signedProjection_signedCirculationLift
    [Fintype E] [DecidableEq E] (chosen : E) (circulation : E → ℝ) :
    signedProjection (signedCirculationLift chosen circulation) = circulation := by
  funext edge
  simp only [signedProjection, signedCirculationLift]
  rw [add_sub_add_right_eq_sub, max_zero_sub_max_neg_zero_eq_self]

/-- The canonical lift realizes every explicitly balanced signed circulation
when an edge is available to carry canceled padding mass. -/
theorem signedCirculationLift_isNormalizedCertificate
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (chosen : E) (circulation : E → ℝ)
    (hcirculation : IsUnitSignedCirculation G circulation) :
    FiniteInequality.IsNormalizedCertificate (signedDelta G)
      (signedCirculationLift chosen circulation) := by
  let slack : ℝ := (1 - ∑ edge, |circulation edge|) / 2
  have hslack : 0 ≤ slack := by
    dsimp only [slack]
    linarith [hcirculation.2]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨edge, orientation⟩
    cases orientation <;>
      simp only [signedCirculationLift] <;> positivity
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, signedCirculationLift]
    change (∑ edge,
      ((max (-circulation edge) 0 + if edge = chosen then slack else 0) +
        (max (circulation edge) 0 + if edge = chosen then slack else 0))) = 1
    have hterm (edge : E) :
        max (-circulation edge) 0 +
              (if edge = chosen then slack else 0) +
            (max (circulation edge) 0 +
              if edge = chosen then slack else 0) =
          |circulation edge| +
            if edge = chosen then 2 * slack else 0 := by
      have habs := max_zero_add_max_neg_zero_eq_abs (circulation edge)
      split_ifs <;> linarith
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [slack]
    ring
  · intro vertex
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, signedCirculationLift,
      signedDelta_true_eq_neg]
    change (∑ edge,
      ((max (-circulation edge) 0 + if edge = chosen then slack else 0) *
          -signedDelta G (edge, false) vertex +
        (max (circulation edge) 0 + if edge = chosen then slack else 0) *
          signedDelta G (edge, false) vertex)) = 0
    calc
      _ = ∑ edge, circulation edge * signedDelta G (edge, false) vertex := by
        apply Finset.sum_congr rfl
        intro edge _
        have hsplit := max_zero_sub_max_neg_zero_eq_self (circulation edge)
        rw [show
          (max (-circulation edge) 0 +
                if edge = chosen then slack else 0) *
                -signedDelta G (edge, false) vertex +
              (max (circulation edge) 0 +
                if edge = chosen then slack else 0) *
                signedDelta G (edge, false) vertex =
            (max (circulation edge) 0 - max (-circulation edge) 0) *
              signedDelta G (edge, false) vertex by ring,
          hsplit]
      _ = 0 := hcirculation.1 vertex

/-- For nonempty edge type, the concrete balance-and-`l1` conditions are
exactly the projections of normalized doubled-graph certificates. -/
theorem isUnitSignedCirculation_iff_exists_normalizedLift
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (circulation : E → ℝ) :
    IsUnitSignedCirculation G circulation ↔
      ∃ coefficient : SignedEdge E → ℝ,
        FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient ∧
          signedProjection coefficient = circulation := by
  constructor
  · intro hcirculation
    let chosen : E := Classical.choice inferInstance
    exact ⟨signedCirculationLift chosen circulation,
      signedCirculationLift_isNormalizedCertificate G chosen circulation hcirculation,
      signedProjection_signedCirculationLift chosen circulation⟩
  · rintro ⟨coefficient, hcoefficient, rfl⟩
    exact isUnitSignedCirculation_signedProjection G coefficient hcoefficient

/-! ## Genuine underlying-multigraph circuits -/

/-- Signed incidence of an original edge in a doubled-graph circuit. -/
def signedCircuitVector [DecidableEq E] {G : EdgeGraph V E} {base : V}
    (cycle : (signedGraph G).Walk base base) : E → ℝ :=
  signedProjection (circuitCoefficient cycle)

/-- The degenerate doubled-graph circuit which traverses one edge identity and
then its own reverse copy.  A two-edge circuit made from two distinct
antiparallel edge identities does not satisfy this predicate. -/
def IsImmediateSignedBacktrack {G : EdgeGraph V E} {base : V}
    (cycle : (signedGraph G).Walk base base) : Prop :=
  ∃ edge : E,
    cycle.edges = [(edge, false), (edge, true)] ∨
      cycle.edges = [(edge, true), (edge, false)]

/-- A genuine circuit of the underlying directed multigraph, equipped with a
choice of traversal direction for each edge. -/
def IsGenuineSignedCircuit {G : EdgeGraph V E} {base : V}
    (cycle : (signedGraph G).Walk base base) : Prop :=
  IsSimpleCycle cycle ∧ ¬IsImmediateSignedBacktrack cycle

/-- Immediate backtracks carry no signed circulation. -/
theorem signedCircuitVector_eq_zero_of_immediateBacktrack
    [DecidableEq E] {G : EdgeGraph V E} {base : V}
    {cycle : (signedGraph G).Walk base base}
    (hbacktrack : IsImmediateSignedBacktrack cycle) :
    signedCircuitVector cycle = 0 := by
  funext candidate
  /- The two orientations of the backtrack run the same argument against their own edge list. -/
  obtain ⟨edge, hedges | hedges⟩ := hbacktrack
  all_goals
    have hlength : cycle.length = 2 := by
      rw [← cycle.edges_length, hedges]
      simp
    by_cases hc : candidate = edge
    · subst candidate
      simp [signedCircuitVector, signedProjection, circuitCoefficient,
        cycle.edgeMultiplicity_eq_count, hedges, hlength]
    · have hzero : ∀ orientation : Bool,
          cycle.edgeMultiplicity (candidate, orientation) = 0 := by
        intro orientation
        apply Nat.eq_zero_of_not_pos
        rw [cycle.edgeMultiplicity_pos_iff_mem_edges, hedges]
        simp [Prod.ext_iff, hc]
      simp only [signedCircuitVector, signedProjection, circuitCoefficient, hlength]
      rw [hzero false, hzero true]
      simp

/-- Every nonempty doubled-graph circuit projects into the concrete signed
circulation polytope. -/
theorem isUnitSignedCirculation_signedCircuitVector
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) {base : V}
    (cycle : (signedGraph G).Walk base base) (hne : 0 < cycle.length) :
    IsUnitSignedCirculation G (signedCircuitVector cycle) :=
  isUnitSignedCirculation_signedProjection G _
    (circuitCoefficient_isNormalizedCertificate G cycle hne)

/-- The objective pairing between a signed circulation and edge data. -/
def signedCirculationObjective [Fintype E]
    (weight circulation : E → ℝ) : ℝ :=
  ∑ edge, circulation edge * weight edge

/-- A circuit's signed-circulation objective is its signed mean weight. -/
theorem signedCirculationObjective_signedCircuitVector
    [Fintype E] [DecidableEq E] (G : EdgeGraph V E) (weight : E → ℝ)
    {base : V} (cycle : (signedGraph G).Walk base base) :
    signedCirculationObjective weight (signedCircuitVector cycle) =
      MaxPlusPotential.walkWeight (signedBase weight) cycle / cycle.length := by
  rw [← certificateValue_circuitCoefficient G weight cycle]
  simp only [signedCirculationObjective, signedCircuitVector, signedProjection,
    FiniteInequality.certificateValue, Fintype.sum_prod_type, Fintype.sum_bool,
    signedBase]
  apply Finset.sum_congr rfl
  intro edge _
  ring

/-- **Literal signed-circulation decomposition.**  When the edge type is
nonempty, every balanced `l1`-unit signed circulation is a convex combination
of projected simple circuits.  The decomposition may use zero-valued immediate
backtracks to account for unused `l1` mass. -/
theorem exists_simpleSignedCircuitVector_decomposition
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (circulation : E → ℝ)
    (hcirculation : IsUnitSignedCirculation G circulation) :
    ∃ (ι : Type) (_ : Fintype ι) (convexWeight : ι → ℝ)
      (base : ι → V)
      (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
      (∀ i, 0 ≤ convexWeight i) ∧
      (∑ i, convexWeight i) = 1 ∧
      (∀ i, IsSimpleCycle (cycle i)) ∧
      ∀ edge, circulation edge =
        ∑ i, convexWeight i * signedCircuitVector (cycle i) edge := by
  obtain ⟨coefficient, hcoefficient, hprojection⟩ :=
    (isUnitSignedCirculation_iff_exists_normalizedLift G circulation).mp hcirculation
  obtain ⟨ι, inst, convexWeight, base, cycle, hnonneg, hsum, hsimple,
      hcoefficientSum⟩ :=
    exists_simpleSignedCircuit_decomposition G coefficient hcoefficient
  refine ⟨ι, inst, convexWeight, base, cycle, hnonneg, hsum, hsimple, ?_⟩
  intro edge
  have hforward := hcoefficientSum (edge, false)
  have hreverse := hcoefficientSum (edge, true)
  have hproject := congrFun hprojection.symm edge
  simp only [signedProjection] at hproject
  rw [hproject, hforward, hreverse]
  simp only [signedCircuitVector, signedProjection, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- When the edge type is nonempty, immediate-backtrack terms can be erased.
The surviving nonnegative coefficients have total mass at most one, and every
positively weighted cycle is a genuine underlying-multigraph circuit. -/
theorem exists_genuineSignedCircuitVector_decomposition
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (circulation : E → ℝ)
    (hcirculation : IsUnitSignedCirculation G circulation) :
    ∃ (ι : Type) (_ : Fintype ι) (circuitWeight : ι → ℝ)
      (base : ι → V)
      (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
      (∀ i, 0 ≤ circuitWeight i) ∧
      (∑ i, circuitWeight i) ≤ 1 ∧
      (∀ i, 0 < circuitWeight i → IsGenuineSignedCircuit (cycle i)) ∧
      ∀ edge, circulation edge =
        ∑ i, circuitWeight i * signedCircuitVector (cycle i) edge := by
  classical
  obtain ⟨ι, inst, convexWeight, base, cycle, hnonneg, hsum, hsimple,
      hcirculationSum⟩ :=
    exists_simpleSignedCircuitVector_decomposition G circulation hcirculation
  let circuitWeight : ι → ℝ := fun i =>
    if IsImmediateSignedBacktrack (cycle i) then 0 else convexWeight i
  have hcircuitNonneg (i : ι) : 0 ≤ circuitWeight i := by
    dsimp only [circuitWeight]
    split_ifs
    · exact le_rfl
    · exact hnonneg i
  have hcircuitLe (i : ι) : circuitWeight i ≤ convexWeight i := by
    dsimp only [circuitWeight]
    split_ifs
    · exact hnonneg i
    · exact le_rfl
  refine ⟨ι, inst, circuitWeight, base, cycle, hcircuitNonneg, ?_, ?_, ?_⟩
  · calc
      ∑ i, circuitWeight i ≤ ∑ i, convexWeight i :=
        Finset.sum_le_sum fun i _ => hcircuitLe i
      _ = 1 := hsum
  · intro i hpositive
    refine ⟨hsimple i, ?_⟩
    intro hbacktrack
    simp only [circuitWeight, if_pos hbacktrack] at hpositive
    exact (lt_irrefl 0) hpositive
  · intro edge
    rw [hcirculationSum edge]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hbacktrack : IsImmediateSignedBacktrack (cycle i)
    · rw [signedCircuitVector_eq_zero_of_immediateBacktrack hbacktrack]
      simp [circuitWeight]
    · simp [circuitWeight, hbacktrack]

/-! ## Absolute circuit optimum -/

@[simp] theorem isUnitSignedCirculation_zero
    [Fintype E] [DecidableEq V] (G : EdgeGraph V E) :
    IsUnitSignedCirculation G (0 : E → ℝ) := by
  simp [IsUnitSignedCirculation]

private theorem signedCirculationObjective_eq_sum_of_decomposition
    {ι : Type*} [Fintype E] [Fintype ι] (weight circulation : E → ℝ)
    (circuitWeight : ι → ℝ) (circuit : ι → E → ℝ)
    (hcirculation : ∀ edge, circulation edge =
      ∑ i, circuitWeight i * circuit i edge) :
    signedCirculationObjective weight circulation =
      ∑ i, circuitWeight i * signedCirculationObjective weight (circuit i) := by
  simp only [signedCirculationObjective, hcirculation]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro edge _
  ring

/-- **Absolute-circuit support formula, objective form.**  For a nonempty edge
type, the absolute value of every `l1`-unit signed-circulation objective is at
most `level` exactly when `level` is nonnegative and the same bound holds on
genuine circuits. -/
theorem unitSignedCirculationObjective_le_iff_genuineCircuitObjective_le
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    (∀ circulation : E → ℝ, IsUnitSignedCirculation G circulation →
      |signedCirculationObjective weight circulation| ≤ level) ↔
      0 ≤ level ∧
        ∀ (base : V) (cycle : (signedGraph G).Walk base base),
          IsGenuineSignedCircuit cycle →
            |signedCirculationObjective weight (signedCircuitVector cycle)| ≤ level := by
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · simpa [signedCirculationObjective] using
        hall 0 (isUnitSignedCirculation_zero G)
    · intro base cycle hcycle
      exact hall _
        (isUnitSignedCirculation_signedCircuitVector G cycle hcycle.1.1)
  · rintro ⟨hlevel, hcircuit⟩ circulation hcirculation
    obtain ⟨ι, inst, circuitWeight, base, cycle, hnonneg, hsum, hgenuine,
        hdecomposition⟩ :=
      exists_genuineSignedCircuitVector_decomposition G circulation hcirculation
    rw [signedCirculationObjective_eq_sum_of_decomposition
      weight circulation circuitWeight
      (fun i => signedCircuitVector (cycle i)) hdecomposition]
    calc
      |∑ i, circuitWeight i *
          signedCirculationObjective weight (signedCircuitVector (cycle i))| ≤
          ∑ i, |circuitWeight i *
            signedCirculationObjective weight (signedCircuitVector (cycle i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, circuitWeight i * level := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hzero : circuitWeight i = 0
        · simp [hzero]
        · have hpositive : 0 < circuitWeight i :=
            lt_of_le_of_ne (hnonneg i) (Ne.symm hzero)
          rw [abs_mul, abs_of_nonneg (hnonneg i)]
          exact mul_le_mul_of_nonneg_left
            (hcircuit (base i) (cycle i) (hgenuine i hpositive)) (hnonneg i)
      _ = (∑ i, circuitWeight i) * level := by rw [Finset.sum_mul]
      _ ≤ 1 * level := mul_le_mul_of_nonneg_right hsum hlevel
      _ = level := one_mul level

/-- **Absolute-circuit support formula, manuscript form.**  For a nonempty
edge type, the support function of balanced signed circulations of `l1` mass
at most one is controlled exactly by the absolute signed mean of genuine
underlying-multigraph circuits.  The separate `0 ≤ level` term is the value of
the zero circulation. -/
theorem unitSignedCirculationObjective_le_iff_genuineCircuitMean_le
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    (∀ circulation : E → ℝ, IsUnitSignedCirculation G circulation →
      |signedCirculationObjective weight circulation| ≤ level) ↔
      0 ≤ level ∧
        ∀ (base : V) (cycle : (signedGraph G).Walk base base),
          IsGenuineSignedCircuit cycle →
            |MaxPlusPotential.walkWeight (signedBase weight) cycle| ≤
              cycle.length * level := by
  rw [unitSignedCirculationObjective_le_iff_genuineCircuitObjective_le]
  apply and_congr_right'
  constructor
  · intro hnormalized base cycle hgenuine
    have hbound := hnormalized base cycle hgenuine
    rw [signedCirculationObjective_signedCircuitVector, abs_div,
      show |(cycle.length : ℝ)| = cycle.length by
        exact abs_of_nonneg (Nat.cast_nonneg cycle.length)] at hbound
    have hlength : (0 : ℝ) < cycle.length := by
      exact_mod_cast hgenuine.1.1
    simpa only [mul_comm] using (div_le_iff₀ hlength).mp hbound
  · intro hraw base cycle hgenuine
    have hbound := hraw base cycle hgenuine
    rw [signedCirculationObjective_signedCircuitVector, abs_div,
      show |(cycle.length : ℝ)| = cycle.length by
        exact abs_of_nonneg (Nat.cast_nonneg cycle.length)]
    have hlength : (0 : ℝ) < cycle.length := by
      exact_mod_cast hgenuine.1.1
    apply (div_le_iff₀ hlength).mpr
    simpa only [mul_comm] using hbound

/-- Absolute signed means of genuine circuits, together with the zero
circulation value. -/
def absoluteSignedCircuitValues [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (weight : E → ℝ) : Set ℝ :=
  {0} ∪
    {value | ∃ (base : V) (cycle : (signedGraph G).Walk base base),
      IsGenuineSignedCircuit cycle ∧
        value = |signedCirculationObjective weight (signedCircuitVector cycle)|}

/-- The absolute circuit-value set of a finite multigraph is finite. -/
theorem finite_absoluteSignedCircuitValues
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (weight : E → ℝ) :
    (absoluteSignedCircuitValues G weight).Finite := by
  let values : Set ℝ :=
    (fun coefficient =>
      |FiniteInequality.certificateValue (signedBase weight) coefficient|) ''
        simpleSignedCircuitCoefficients G
  have hvalues : values.Finite :=
    (finite_simpleSignedCircuitCoefficients G).image _
  apply Set.Finite.union (Set.finite_singleton 0) hvalues |>.subset
  rintro value (rfl | ⟨base, cycle, hgenuine, rfl⟩)
  · exact Or.inl rfl
  · right
    refine ⟨circuitCoefficient cycle, ⟨base, cycle, hgenuine.1, rfl⟩, ?_⟩
    change
      |FiniteInequality.certificateValue (signedBase weight)
          (circuitCoefficient cycle)| =
        |signedCirculationObjective weight (signedCircuitVector cycle)|
    rw [certificateValue_circuitCoefficient G weight,
      signedCirculationObjective_signedCircuitVector]

/-- **Attained absolute-circuit optimum.**  A finite multigraph with a
nonempty edge type has a largest absolute genuine-circuit mean after adjoining
the zero circulation.  This number is exactly the support-function optimum
over all balanced signed circulations of `l1` mass at most one. -/
theorem exists_absoluteSignedCircuitOptimum
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : EdgeGraph V E) (weight : E → ℝ) :
    ∃ optimum ∈ absoluteSignedCircuitValues G weight,
      (∀ value ∈ absoluteSignedCircuitValues G weight, value ≤ optimum) ∧
      (∀ circulation : E → ℝ, IsUnitSignedCirculation G circulation →
        |signedCirculationObjective weight circulation| ≤ optimum) ∧
      ∀ level,
        (∀ circulation : E → ℝ, IsUnitSignedCirculation G circulation →
          |signedCirculationObjective weight circulation| ≤ level) ↔
            optimum ≤ level := by
  let values := absoluteSignedCircuitValues G weight
  have hfinite : values.Finite := finite_absoluteSignedCircuitValues G weight
  have hnonempty : values.Nonempty := ⟨0, Or.inl rfl⟩
  obtain ⟨optimum, hoptimumMem, hgreatest⟩ :=
    Set.exists_max_image values id hfinite hnonempty
  have hoptimumGreatest (value : ℝ) (hvalue : value ∈ values) : value ≤ optimum := by
    simpa using hgreatest value hvalue
  have hoptimumNonneg : 0 ≤ optimum :=
    hoptimumGreatest 0 (Or.inl rfl)
  have hcircuit :
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        IsGenuineSignedCircuit cycle →
          |signedCirculationObjective weight (signedCircuitVector cycle)| ≤ optimum := by
    intro base cycle hgenuine
    exact hoptimumGreatest _ (Or.inr ⟨base, cycle, hgenuine, rfl⟩)
  have hsupport :
      ∀ circulation : E → ℝ, IsUnitSignedCirculation G circulation →
        |signedCirculationObjective weight circulation| ≤ optimum :=
    (unitSignedCirculationObjective_le_iff_genuineCircuitObjective_le
      G weight optimum).mpr ⟨hoptimumNonneg, hcircuit⟩
  refine ⟨optimum, hoptimumMem, hoptimumGreatest, hsupport, ?_⟩
  intro level
  constructor
  · intro hall
    rcases hoptimumMem with rfl | ⟨base, cycle, hgenuine, rfl⟩
    · simpa [signedCirculationObjective] using
        hall 0 (isUnitSignedCirculation_zero G)
    · exact hall _
        (isUnitSignedCirculation_signedCircuitVector G cycle hgenuine.1.1)
  · intro hlevel circulation hcirculation
    exact (hsupport circulation hcirculation).trans hlevel

end AdditiveTransport

end

end Maths
