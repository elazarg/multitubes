/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Exact
public import DirectedTransport.MaxAffine.Duality
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import DirectedTransport.FiniteInequality.Quantitative

/-!
# Recession regimes and slope gauges for max-affine transport

The recession reduction for max-affine branch rows classifies the mixed
subunit/unit and superunit/unit regimes, including their cycle criteria.  A
multiplicative slope gauge gives an intrinsic description of the critical
subsystem.

The slope-flat converse requires strong connectivity.  Without it, a DAG can
satisfy every cycle-product equation vacuously while carrying a zero slope.

## Main definitions

* `DirectedTransport.MaxAffineTransport.unitSlopeGraph`,
  `DirectedTransport.MaxAffineTransport.unitSlopeShift`: the subgraph of unit-slope edges and
  the shift carried by such an edge.
* `DirectedTransport.MaxAffineTransport.walkSlopeProduct`: the product of scalar slopes along
  a walk.
* `DirectedTransport.MaxAffineTransport.IsNonexpansiveGauge`,
  `DirectedTransport.MaxAffineTransport.IsExpansiveGauge`: a positive vertex gauge making
  every normalized edge slope at most, respectively at least, one.

## Main results

* `MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one`:
  when every slope is at most one, feasibility reduces exactly to the affine rows of the unit-slope
  edges; floors and strictly subunit rows are noncritical.
* `MaxAffineTransport.exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one`:
  the resulting cycle criterion — a lax section exists exactly when every closed walk of the
  unit-slope subgraph has nonpositive shift sum.
* `MaxAffineTransport.exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_one_le_slope`:
  the same criterion in the superunit regime, which additionally requires every floor absent.
* `DirectedTransport.MaxAffineTransport.exists_nonexpansiveGauge_iff_cycleProduct_le_one`:
  **positive gauge theorem** — for nonnegative slopes on a finite graph, a nonexpansive gauge
  exists exactly when every directed cycle product is at most one.
* `DirectedTransport.MaxAffineTransport.exists_expansiveGauge_iff_one_le_cycleProduct`: the
  dual statement, under the stronger hypothesis that every slope is strictly positive.
* `MaxAffineTransport.cycleProduct_eq_one_iff_exists_slopeGauge_of_stronglyConnected`:
  **multiplicative holonomy equivalence** — on a strongly connected graph, nonnegative slopes
  have unit product around every closed walk exactly when they are ratios of one positive
  vertex gauge. Strong connectivity is needed: see the DAG remark above.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## Constant recession directions -/

section RecessionRegimes

variable [Fintype V] [DecidableEq V] [Fintype E]
variable {G : EdgeGraph V E} {label : E → Label}

/-! A branch row paired with a constant direction.  Affine rows see
`constant * (1 - slope)`; genuine floor rows see `constant`. -/
omit [Fintype E] in
theorem dotProduct_branchDelta_const (branch : Branch label) (constant : ℝ) :
    dotProduct (branchDelta G label branch) (fun _ : V ↦ constant) =
      match branch.1 with
      | Sum.inl edge => constant * (1 - (label edge).slope)
      | Sum.inr _ => constant := by
  rcases branch with ⟨action, hgenuine⟩
  cases action with
  | inl edge =>
      rw [branchDelta, dotProduct_rowDelta_inl]
      ring
  | inr edge =>
      rcases (label edge).floor_cases with hfloor | ⟨floor, hfloor⟩
      · exact (hgenuine hfloor).elim
      · rw [branchDelta, dotProduct_rowDelta_inr_of_floor_coe hfloor]

/-- If every slope is at most one, feasibility reduces exactly to the affine
rows of unit-slope edges.  All floors and strictly subunit rows are noncritical. -/
theorem exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one
    (hslope : ∀ edge : E, (label edge).slope ≤ 1) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge) := by
  classical
  let direction : V → ℝ := fun _ ↦ 1
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_const]
    cases branch.1 with
    | inl edge => simp only [one_mul]; linarith [hslope edge]
    | inr edge => norm_num
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) direction hrecession
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hedge ↦ ?_⟩
    have hrow := (isLaxSection_iff_forall_branch G label potential).mp
      hpotential ⟨Sum.inl edge, trivial⟩
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    rw [hedge] at hrow
    linarith
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    have hcriticalRows (branch : Branch label)
        (hcritical : FiniteInequality.Recession.IsCritical
          (branchDelta G label) direction branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_const] at hcritical
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          change 1 * (1 - (label edge).slope) = 0 at hcritical
          have hedge : (label edge).slope = 1 := by
            simp only [one_mul] at hcritical
            linarith
          have hunit := hcriticalPotential edge hedge
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          rw [hedge]
          linarith
      | inr edge =>
          change (1 : ℝ) = 0 at hcritical
          norm_num at hcritical
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

/-- Unit-slope edges as a directed subgraph. -/
abbrev UnitSlopeEdge (label : E → Label) :=
  {edge : E // (label edge).slope = 1}

/-- The directed graph containing exactly the unit-slope edges. -/
def unitSlopeGraph (G : EdgeGraph V E) (label : E → Label) :
    EdgeGraph V (UnitSlopeEdge label) where
  source edge := G.source edge.1
  target edge := G.target edge.1

/-- The shift on a unit-slope edge. -/
def unitSlopeShift (label : E → Label) (edge : UnitSlopeEdge label) : ℝ :=
  (label edge.1).shift

/-- Complete cycle criterion in the mixed subunit/unit regime. -/
theorem exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one
    (hslope : ∀ edge : E, (label edge).slope ≤ 1) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ 0 := by
  rw [exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one hslope]
  constructor
  · rintro ⟨potential, hpotential⟩
    apply (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
      (G := unitSlopeGraph G label) (unitSlopeShift label)).mp
    exact ⟨potential, fun edge ↦ by
      simpa [unitSlopeGraph, unitSlopeShift, add_comm] using
        hpotential edge.1 edge.2⟩
  · intro hcycles
    obtain ⟨potential, hpotential⟩ :=
      (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := unitSlopeGraph G label) (unitSlopeShift label)).mpr hcycles
    exact ⟨potential, fun edge hedge ↦ by
      simpa [unitSlopeGraph, unitSlopeShift, add_comm] using
        hpotential (⟨edge, hedge⟩ : UnitSlopeEdge label)⟩

/-- In a floorless all-superunit/unit system, the direction `-1` reduces
feasibility to the same unit-slope affine subsystem. -/
theorem exists_isLaxSection_iff_exists_unitSlopePotential_of_one_le_slope
    (hslope : ∀ edge : E, 1 ≤ (label edge).slope)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge) := by
  classical
  let direction : V → ℝ := fun _ ↦ -1
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_const]
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge => simp only [neg_mul, one_mul]; linarith [hslope edge]
    | inr edge => exact (hgenuine (hfloor edge)).elim
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) direction hrecession
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hedge ↦ ?_⟩
    have hrow := (isLaxSection_iff_forall_branch G label potential).mp
      hpotential ⟨Sum.inl edge, trivial⟩
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    rw [hedge] at hrow
    linarith
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    have hcriticalRows (branch : Branch label)
        (hcritical : FiniteInequality.Recession.IsCritical
          (branchDelta G label) direction branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_const] at hcritical
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          change -1 * (1 - (label edge).slope) = 0 at hcritical
          have hedge : (label edge).slope = 1 := by
            simp only [neg_mul, one_mul] at hcritical
            linarith
          have hunit := hcriticalPotential edge hedge
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          rw [hedge]
          linarith
      | inr edge => exact (hgenuine (hfloor edge)).elim
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

/-- Complete cycle criterion in the floorless mixed superunit/unit regime. -/
theorem exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_one_le_slope
    (hslope : ∀ edge : E, 1 ≤ (label edge).slope)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ 0 := by
  rw [exists_isLaxSection_iff_exists_unitSlopePotential_of_one_le_slope
    hslope hfloor]
  constructor
  · rintro ⟨potential, hpotential⟩
    apply (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
      (G := unitSlopeGraph G label) (unitSlopeShift label)).mp
    exact ⟨potential, fun edge ↦ by
      simpa [unitSlopeGraph, unitSlopeShift, add_comm] using
        hpotential edge.1 edge.2⟩
  · intro hcycles
    obtain ⟨potential, hpotential⟩ :=
      (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := unitSlopeGraph G label) (unitSlopeShift label)).mpr hcycles
    exact ⟨potential, fun edge hedge ↦ by
      simpa [unitSlopeGraph, unitSlopeShift, add_comm] using
        hpotential (⟨edge, hedge⟩ : UnitSlopeEdge label)⟩

end RecessionRegimes

/-! ## Intrinsic multiplicative slope gauges -/

section Gauges

variable {G : EdgeGraph V E} (slope : E → ℝ)

/-- Product of scalar slopes along a typed walk. -/
def walkSlopeProduct {start finish : V} (walk : G.Walk start finish) : ℝ :=
  (walk.edges.map slope).prod

@[simp] theorem walkSlopeProduct_nil (vertex : V) :
    walkSlopeProduct slope (.nil : G.Walk vertex vertex) = 1 := rfl

@[simp] theorem walkSlopeProduct_concat {start finish : V}
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    walkSlopeProduct slope (walk.concat edge legal) =
      walkSlopeProduct slope walk * slope edge := by
  simp [walkSlopeProduct]

@[simp] theorem walkSlopeProduct_append {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    walkSlopeProduct slope (first.append second) =
    walkSlopeProduct slope first * walkSlopeProduct slope second := by
  simp [walkSlopeProduct, List.map_append, List.prod_append]

/-- Edgewise gauge equality telescopes along a walk, without requiring a
global equality assumption on edges outside that walk. -/
theorem walkSlopeProduct_mul_gauge_eq_of_forall_mem
    {gauge : V → ℝ} {start finish : V} (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges,
      slope edge * gauge (G.source edge) = gauge (G.target edge)) :
    walkSlopeProduct slope walk * gauge start = gauge finish := by
  induction walk with
  | nil => simp
  | @concat finish walk edge legal ih =>
      subst legal
      have hbefore (candidate : E) (hcandidate : candidate ∈ walk.edges) :
          slope candidate * gauge (G.source candidate) =
            gauge (G.target candidate) :=
        hedge candidate (by simp [hcandidate])
      have hfinal := hedge edge (by simp)
      rw [walkSlopeProduct_concat]
      calc
        (walkSlopeProduct slope walk * slope edge) * gauge start =
            slope edge * (walkSlopeProduct slope walk * gauge start) := by
          ring
        _ = slope edge * gauge (G.source edge) := by rw [ih hbefore]
        _ = gauge (G.target edge) := hfinal

/-- A positive vertex gauge making all normalized slopes nonexpansive. -/
def IsNonexpansiveGauge (gauge : V → ℝ) : Prop :=
  (∀ vertex, 0 < gauge vertex) ∧
    ∀ edge, slope edge * gauge (G.source edge) ≤ gauge (G.target edge)

/-- A nonexpansive gauge controls the product along every forward walk. -/
theorem walkSlopeProduct_mul_gauge_le
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    walkSlopeProduct slope walk * gauge start ≤ gauge finish := by
  induction walk with
  | nil => simp
  | @concat finish walk edge legal ih =>
      subst legal
      rw [walkSlopeProduct_concat]
      calc
        (walkSlopeProduct slope walk * slope edge) * gauge start =
            slope edge * (walkSlopeProduct slope walk * gauge start) := by ring
        _ ≤ slope edge * gauge (G.source edge) :=
          mul_le_mul_of_nonneg_left ih (hnonneg edge)
        _ ≤ gauge (G.target edge) := hgauge.2 edge

/-- If one traversed edge is strictly noncritical for a nonexpansive gauge,
the path product satisfies a strict endpoint inequality. -/
theorem walkSlopeProduct_mul_gauge_lt_of_exists_strict
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    (∃ edge ∈ walk.edges,
      slope edge * gauge (G.source edge) < gauge (G.target edge)) →
      walkSlopeProduct slope walk * gauge start < gauge finish := by
  intro hstrict
  induction walk with
  | nil => simp at hstrict
  | @concat finish walk edge legal ih =>
      subst legal
      rcases hstrict with ⟨candidate, hcandidate, hstrictCandidate⟩
      rw [EdgeGraph.Walk.edges_concat, List.mem_append] at hcandidate
      rcases hcandidate with hbefore | hlast
      · have hprefix := ih ⟨candidate, hbefore, hstrictCandidate⟩
        rw [walkSlopeProduct_concat]
        by_cases hzero : slope edge = 0
        · rw [hzero]
          simpa using hgauge.1 (G.target edge)
        · have hpositive : 0 < slope edge :=
            lt_of_le_of_ne (hnonneg edge) (Ne.symm hzero)
          calc
            (walkSlopeProduct slope walk * slope edge) * gauge start =
                slope edge *
                  (walkSlopeProduct slope walk * gauge start) := by ring
            _ < slope edge * gauge (G.source edge) :=
              mul_lt_mul_of_pos_left hprefix hpositive
            _ ≤ gauge (G.target edge) := hgauge.2 edge
      · simp only [List.mem_singleton] at hlast
        subst candidate
        have hprefix :=
          walkSlopeProduct_mul_gauge_le slope hnonneg hgauge walk
        rw [walkSlopeProduct_concat]
        calc
          (walkSlopeProduct slope walk * slope edge) * gauge start =
              slope edge *
                (walkSlopeProduct slope walk * gauge start) := by ring
          _ ≤ slope edge * gauge (G.source edge) :=
            mul_le_mul_of_nonneg_left hprefix (hnonneg edge)
          _ < gauge (G.target edge) := hstrictCandidate

/-- Every nonexpansive gauge forces every directed cycle product below one. -/
theorem cycleProduct_le_one_of_nonexpansiveGauge
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkSlopeProduct slope cycle ≤ 1 := by
  have hwalk := walkSlopeProduct_mul_gauge_le slope hnonneg hgauge cycle
  apply le_of_mul_le_mul_right (a := gauge base) _ (hgauge.1 base)
  simpa using hwalk

/-- A cycle using a strictly noncritical edge of a nonexpansive gauge has
product strictly below one. -/
theorem cycleProduct_lt_one_of_nonexpansiveGauge_of_exists_strict
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base)
    (hstrict : ∃ edge ∈ cycle.edges,
      slope edge * gauge (G.source edge) < gauge (G.target edge)) :
    walkSlopeProduct slope cycle < 1 := by
  have hwalk := walkSlopeProduct_mul_gauge_lt_of_exists_strict
    slope hnonneg hgauge cycle hstrict
  nlinarith [hgauge.1 base]

/-- Under a nonexpansive positive gauge, a cycle has product one exactly when
every traversed edge is gauge-critical. -/
theorem cycleProduct_eq_one_iff_forall_gaugeCritical_of_nonexpansiveGauge
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkSlopeProduct slope cycle = 1 ↔
      ∀ edge ∈ cycle.edges,
        slope edge * gauge (G.source edge) = gauge (G.target edge) := by
  constructor
  · intro hproduct edge hedge
    by_contra hnoncritical
    have hstrict :=
      cycleProduct_lt_one_of_nonexpansiveGauge_of_exists_strict
        slope hnonneg hgauge cycle ⟨edge, hedge,
          lt_of_le_of_ne (hgauge.2 edge) hnoncritical⟩
    linarith
  · intro hcritical
    have htelescope :=
      walkSlopeProduct_mul_gauge_eq_of_forall_mem slope cycle hcritical
    nlinarith [hgauge.1 base]

/-- Positive-slope edges, used to take logarithms without imposing positivity
on zero-slope edges. -/
abbrev PositiveSlopeEdge := {edge : E // 0 < slope edge}

abbrev positiveSlopeGraph : EdgeGraph V (PositiveSlopeEdge slope) where
  source edge := G.source edge.1
  target edge := G.target edge.1

/-- Forget positivity proofs on a walk. -/
def forgetPositiveWalk {start : V} :
    {finish : V} → (positiveSlopeGraph (G := G) slope).Walk start finish →
      G.Walk start finish
  | _, .nil => .nil
  | _, .concat walk edge legal =>
      (forgetPositiveWalk walk).concat edge.1 legal

@[simp] theorem edges_forgetPositiveWalk {start finish : V}
    (walk : (positiveSlopeGraph (G := G) slope).Walk start finish) :
    (forgetPositiveWalk slope walk).edges = walk.edges.map Subtype.val := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      change G.source edge.1 = _ at legal
      rw [forgetPositiveWalk]
      simp only [EdgeGraph.Walk.edges_concat, List.map_append, List.map_singleton]
      rw [ih]

@[simp] theorem walkSlopeProduct_forgetPositiveWalk {start finish : V}
    (walk : (positiveSlopeGraph (G := G) slope).Walk start finish) :
    walkSlopeProduct slope (forgetPositiveWalk slope walk) =
      walkSlopeProduct (fun edge : PositiveSlopeEdge slope ↦ slope edge.1) walk := by
  simp [walkSlopeProduct]

/-- Exponentiating the log-weight of a positive-edge walk recovers its slope
product. -/
theorem exp_walkWeight_log_eq_walkSlopeProduct {start finish : V}
    (walk : (positiveSlopeGraph (G := G) slope).Walk start finish) :
    Real.exp (MaxPlusPotential.walkWeight
      (fun edge : PositiveSlopeEdge slope ↦ Real.log (slope edge.1)) walk) =
      walkSlopeProduct (fun edge : PositiveSlopeEdge slope ↦ slope edge.1) walk := by
  induction walk with
  | nil => simp [MaxPlusPotential.walkWeight, walkSlopeProduct]
  | concat walk edge legal ih =>
      rw [MaxPlusPotential.walkWeight_concat, walkSlopeProduct_concat,
        Real.exp_add, ih, Real.exp_log edge.2]

/-- **Positive gauge theorem.**  On a finite graph with nonnegative slopes,
all directed cycle products are at most one exactly when a positive vertex
gauge makes every normalized edge slope at most one. -/
theorem exists_nonexpansiveGauge_iff_cycleProduct_le_one
    [Fintype V] [Finite E] (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∃ gauge : V → ℝ, IsNonexpansiveGauge (G := G) slope gauge) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        walkSlopeProduct slope cycle ≤ 1 := by
  constructor
  · rintro ⟨gauge, hgauge⟩ base cycle
    exact cycleProduct_le_one_of_nonexpansiveGauge slope hnonneg hgauge cycle
  · intro hcycle
    have hlogCycle (base : V)
        (cycle : (positiveSlopeGraph (G := G) slope).Walk base base) :
        MaxPlusPotential.walkWeight
          (fun edge : PositiveSlopeEdge slope ↦ Real.log (slope edge.1)) cycle ≤ 0 := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_zero, exp_walkWeight_log_eq_walkSlopeProduct]
      rw [← walkSlopeProduct_forgetPositiveWalk]
      exact hcycle base (forgetPositiveWalk slope cycle)
    obtain ⟨potential, hpotential⟩ :=
      (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := positiveSlopeGraph (G := G) slope)
        (fun edge : PositiveSlopeEdge slope ↦ Real.log (slope edge.1))).mpr hlogCycle
    let gauge : V → ℝ := fun vertex ↦ Real.exp (potential vertex)
    refine ⟨gauge, fun vertex ↦ Real.exp_pos _, fun edge ↦ ?_⟩
    by_cases hedge : 0 < slope edge
    · have hrow := hpotential (⟨edge, hedge⟩ : PositiveSlopeEdge slope)
      apply Real.exp_le_exp.mp
      simpa [positiveSlopeGraph, gauge, Real.exp_add, Real.exp_log hedge,
        mul_comm] using
        Real.exp_le_exp.mpr hrow
    · have hzero : slope edge = 0 := le_antisymm (le_of_not_gt hedge) (hnonneg edge)
      rw [hzero, zero_mul]
      exact (Real.exp_pos _).le

/-! ### The dual expansive gauge -/

/-- A positive vertex gauge making every normalized slope expansive. -/
def IsExpansiveGauge (gauge : V → ℝ) : Prop :=
  (∀ vertex, 0 < gauge vertex) ∧
    ∀ edge, gauge (G.target edge) ≤ slope edge * gauge (G.source edge)

/-- An expansive gauge controls every forward walk from below. -/
theorem gauge_le_walkSlopeProduct_mul
    (hpos : ∀ edge, 0 < slope edge)
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    gauge finish ≤ walkSlopeProduct slope walk * gauge start := by
  induction walk with
  | nil => simp [walkSlopeProduct]
  | @concat finish walk edge legal ih =>
      subst legal
      rw [walkSlopeProduct_concat]
      calc
        gauge (G.target edge) ≤
            slope edge * gauge (G.source edge) := hgauge.2 edge
        _ ≤ slope edge *
            (walkSlopeProduct slope walk * gauge start) :=
          mul_le_mul_of_nonneg_left ih (hpos edge).le
        _ = (walkSlopeProduct slope walk * slope edge) * gauge start := by
          ring

/-- If one traversed edge is strictly noncritical for an expansive gauge,
the path product satisfies a strict endpoint inequality. -/
theorem gauge_lt_walkSlopeProduct_mul_of_exists_strict
    (hpos : ∀ edge, 0 < slope edge)
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    (∃ edge ∈ walk.edges,
      gauge (G.target edge) < slope edge * gauge (G.source edge)) →
      gauge finish < walkSlopeProduct slope walk * gauge start := by
  intro hstrict
  induction walk with
  | nil => simp at hstrict
  | @concat finish walk edge legal ih =>
      subst legal
      rcases hstrict with ⟨candidate, hcandidate, hstrictCandidate⟩
      rw [EdgeGraph.Walk.edges_concat, List.mem_append] at hcandidate
      rcases hcandidate with hbefore | hlast
      · have hprefix := ih ⟨candidate, hbefore, hstrictCandidate⟩
        rw [walkSlopeProduct_concat]
        calc
          gauge (G.target edge) ≤
              slope edge * gauge (G.source edge) := hgauge.2 edge
          _ < slope edge *
              (walkSlopeProduct slope walk * gauge start) :=
            mul_lt_mul_of_pos_left hprefix (hpos edge)
          _ = (walkSlopeProduct slope walk * slope edge) * gauge start := by
            ring
      · simp only [List.mem_singleton] at hlast
        subst candidate
        have hprefix := gauge_le_walkSlopeProduct_mul slope hpos hgauge walk
        rw [walkSlopeProduct_concat]
        calc
          gauge (G.target edge) <
              slope edge * gauge (G.source edge) := hstrictCandidate
          _ ≤ slope edge *
              (walkSlopeProduct slope walk * gauge start) :=
            mul_le_mul_of_nonneg_left hprefix (hpos edge).le
          _ = (walkSlopeProduct slope walk * slope edge) * gauge start := by
            ring

/-- Every expansive gauge forces every directed cycle product above one. -/
theorem one_le_cycleProduct_of_expansiveGauge
    (hpos : ∀ edge, 0 < slope edge)
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    1 ≤ walkSlopeProduct slope cycle := by
  have hwalk := gauge_le_walkSlopeProduct_mul slope hpos hgauge cycle
  nlinarith [hgauge.1 base]

/-- A cycle using a strictly noncritical edge of an expansive gauge has
product strictly above one. -/
theorem one_lt_cycleProduct_of_expansiveGauge_of_exists_strict
    (hpos : ∀ edge, 0 < slope edge)
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base)
    (hstrict : ∃ edge ∈ cycle.edges,
      gauge (G.target edge) < slope edge * gauge (G.source edge)) :
    1 < walkSlopeProduct slope cycle := by
  have hwalk := gauge_lt_walkSlopeProduct_mul_of_exists_strict
    slope hpos hgauge cycle hstrict
  nlinarith [hgauge.1 base]

/-- Under an expansive positive gauge, a cycle has product one exactly when
every traversed edge is gauge-critical. -/
theorem cycleProduct_eq_one_iff_forall_gaugeCritical_of_expansiveGauge
    (hpos : ∀ edge, 0 < slope edge)
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkSlopeProduct slope cycle = 1 ↔
      ∀ edge ∈ cycle.edges,
        slope edge * gauge (G.source edge) = gauge (G.target edge) := by
  constructor
  · intro hproduct edge hedge
    by_contra hnoncritical
    have hstrict :=
      one_lt_cycleProduct_of_expansiveGauge_of_exists_strict
        slope hpos hgauge cycle ⟨edge, hedge,
          lt_of_le_of_ne (hgauge.2 edge)
            (fun heq => hnoncritical heq.symm)⟩
    linarith
  · intro hcritical
    have htelescope :=
      walkSlopeProduct_mul_gauge_eq_of_forall_mem slope cycle hcritical
    nlinarith [hgauge.1 base]

/-- **Dual positive gauge theorem.**  For positive slopes on a finite graph,
all directed cycle products are at least one exactly when a positive vertex
gauge makes every normalized edge slope at least one. -/
theorem exists_expansiveGauge_iff_one_le_cycleProduct
    [Fintype V] [Finite E] (hpos : ∀ edge, 0 < slope edge) :
    (∃ gauge : V → ℝ, IsExpansiveGauge (G := G) slope gauge) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        1 ≤ walkSlopeProduct slope cycle := by
  constructor
  · rintro ⟨gauge, hgauge⟩ base cycle
    exact one_le_cycleProduct_of_expansiveGauge slope hpos hgauge cycle
  · intro hcycle
    have hlogCycle (base : V) (cycle : G.Walk base base) :
        MaxPlusPotential.walkWeight
          (fun edge => -Real.log (slope edge)) cycle ≤ 0 := by
      have hlogNonneg : 0 ≤ MaxPlusPotential.walkWeight
          (fun edge => Real.log (slope edge)) cycle := by
        apply Real.exp_le_exp.mp
        have hexp {start finish : V} (walk : G.Walk start finish) :
            Real.exp (MaxPlusPotential.walkWeight
              (fun edge => Real.log (slope edge)) walk) =
                walkSlopeProduct slope walk := by
          induction walk with
          | nil => simp [MaxPlusPotential.walkWeight, walkSlopeProduct]
          | concat walk edge legal ih =>
              rw [MaxPlusPotential.walkWeight_concat, walkSlopeProduct_concat,
                Real.exp_add, ih, Real.exp_log (hpos edge)]
        rw [Real.exp_zero, hexp cycle]
        exact hcycle base cycle
      have hneg : MaxPlusPotential.walkWeight
          (fun edge => -Real.log (slope edge)) cycle =
            -MaxPlusPotential.walkWeight
              (fun edge => Real.log (slope edge)) cycle := by
        have hnegGeneral {start finish : V} (walk : G.Walk start finish) :
            MaxPlusPotential.walkWeight
                (fun edge => -Real.log (slope edge)) walk =
              -MaxPlusPotential.walkWeight
                (fun edge => Real.log (slope edge)) walk := by
          induction walk with
          | nil => simp [MaxPlusPotential.walkWeight]
          | concat walk edge legal ih =>
              rw [MaxPlusPotential.walkWeight_concat,
                MaxPlusPotential.walkWeight_concat, ih]
              ring
        exact hnegGeneral cycle
      rw [hneg]
      linarith
    obtain ⟨potential, hpotential⟩ :=
      (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := G) (fun edge => -Real.log (slope edge))).mpr hlogCycle
    let gauge : V → ℝ := fun vertex => Real.exp (-potential vertex)
    refine ⟨gauge, fun vertex => Real.exp_pos _, fun edge => ?_⟩
    have hrow := hpotential edge
    have hexponent : -potential (G.target edge) ≤
        Real.log (slope edge) - potential (G.source edge) := by
      linarith
    change Real.exp (-potential (G.target edge)) ≤
      slope edge * Real.exp (-potential (G.source edge))
    calc
      Real.exp (-potential (G.target edge)) ≤
          Real.exp (Real.log (slope edge) - potential (G.source edge)) :=
        Real.exp_le_exp.mpr hexponent
      _ = slope edge * Real.exp (-potential (G.source edge)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hpos edge)]

/-! ### Strongly connected slope-flat systems -/

/-- Under multiplicative flatness and strong connectivity, every edge slope is
forced to be positive; zero slopes cannot recur with product one. -/
theorem slope_pos_of_cycleProduct_eq_one_of_stronglyConnected
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    (hflat : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSlopeProduct slope cycle = 1) (edge : E) :
    0 < slope edge := by
  let back := (hconnected.nonempty_walk (G.target edge) (G.source edge)).some
  have hcycle := hflat (G.source edge)
    ((EdgeGraph.Walk.singleton (G := G) edge).append back)
  rw [walkSlopeProduct_append] at hcycle
  have hsingle : walkSlopeProduct slope
      (EdgeGraph.Walk.singleton (G := G) edge) = slope edge := by
    simp [walkSlopeProduct]
  rw [hsingle] at hcycle
  have hback : 0 ≤ walkSlopeProduct slope back := by
    unfold walkSlopeProduct
    apply List.prod_nonneg
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨candidate, _, rfl⟩
    exact hnonneg candidate
  by_contra hnot
  have hzero : slope edge = 0 := le_antisymm (le_of_not_gt hnot) (hnonneg edge)
  rw [hzero, zero_mul] at hcycle
  norm_num at hcycle

/-- **Corrected slope-flat theorem.**  On a strongly connected graph,
multiplicatively flat nonnegative slopes are exact positive ratios of vertex
gauges. -/
theorem exists_slopeGauge_of_cycleProduct_eq_one_of_stronglyConnected
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    (hflat : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSlopeProduct slope cycle = 1) :
    ∃ gauge : V → ℝ, (∀ vertex, 0 < gauge vertex) ∧
      ∀ edge, slope edge = gauge (G.target edge) / gauge (G.source edge) := by
  have hpos : ∀ edge, 0 < slope edge :=
    slope_pos_of_cycleProduct_eq_one_of_stronglyConnected slope hconnected
      hnonneg hflat
  have hzero : CycleCoboundary.HasZeroCycleSums G (fun edge ↦ Real.log (slope edge)) := by
    have hexp {start finish : V} (walk : G.Walk start finish) :
        Real.exp (walkSum
          (fun edge ↦ Real.log (slope edge)) walk) =
          walkSlopeProduct slope walk := by
      induction walk with
      | nil => simp [walkSum, walkSlopeProduct]
      | concat walk edge legal ih =>
          rw [walkSum_concat, walkSlopeProduct_concat,
            Real.exp_add, ih, Real.exp_log (hpos edge)]
    intro vertex cycle
    apply Real.exp_injective
    rw [Real.exp_zero, hexp cycle, hflat vertex cycle]
  obtain ⟨potential, hpotential⟩ :=
    (CycleCoboundary.isCoboundary_iff_hasZeroCycleSums hconnected).mpr hzero
  let gauge : V → ℝ := fun vertex ↦ Real.exp (potential vertex)
  refine ⟨gauge, fun vertex ↦ Real.exp_pos _, fun edge ↦ ?_⟩
  have hedge := hpotential edge
  rw [CycleCoboundary.coboundary_apply] at hedge
  change Real.log (slope edge) =
    potential (G.target edge) - potential (G.source edge) at hedge
  calc
    slope edge = Real.exp (Real.log (slope edge)) :=
      (Real.exp_log (hpos edge)).symm
    _ = Real.exp (potential (G.target edge) - potential (G.source edge)) := by
      rw [hedge]
    _ = gauge (G.target edge) / gauge (G.source edge) := by
      rw [Real.exp_sub]

/-- Exact gauge ratios telescope along every directed walk. -/
theorem walkSlopeProduct_mul_gauge_eq_of_slopeGauge
    {gauge : V → ℝ} (hgauge : ∀ vertex, 0 < gauge vertex)
    (hedge : ∀ edge,
      slope edge = gauge (G.target edge) / gauge (G.source edge))
    {start finish : V} (walk : G.Walk start finish) :
    walkSlopeProduct slope walk * gauge start = gauge finish := by
  induction walk with
  | nil => simp [walkSlopeProduct]
  | @concat middle walk edge legal ih =>
      subst legal
      rw [walkSlopeProduct_concat, hedge edge]
      have hsource : gauge (G.source edge) ≠ 0 :=
        (hgauge (G.source edge)).ne'
      calc
        (walkSlopeProduct slope walk *
              (gauge (G.target edge) / gauge (G.source edge))) *
            gauge start =
            (walkSlopeProduct slope walk * gauge start) *
              (gauge (G.target edge) / gauge (G.source edge)) := by ring
        _ = gauge (G.source edge) *
              (gauge (G.target edge) / gauge (G.source edge)) := by rw [ih]
        _ = gauge (G.target edge) := by field_simp

/-- Exact gauge ratios have unit multiplicative holonomy on every cycle. -/
theorem cycleProduct_eq_one_of_slopeGauge
    {gauge : V → ℝ} (hgauge : ∀ vertex, 0 < gauge vertex)
    (hedge : ∀ edge,
      slope edge = gauge (G.target edge) / gauge (G.source edge))
    {base : V} (cycle : G.Walk base base) :
    walkSlopeProduct slope cycle = 1 := by
  have htel := walkSlopeProduct_mul_gauge_eq_of_slopeGauge
    slope hgauge hedge cycle
  exact (mul_right_cancel₀ (hgauge base).ne') (by simpa using htel)

/-- **Multiplicative holonomy equivalence.**  On a strongly connected graph,
nonnegative slopes have unit product around every closed walk exactly when
they are exact ratios of one positive vertex gauge. -/
theorem cycleProduct_eq_one_iff_exists_slopeGauge_of_stronglyConnected
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSlopeProduct slope cycle = 1) ↔
      ∃ gauge : V → ℝ, (∀ vertex, 0 < gauge vertex) ∧
        ∀ edge,
          slope edge = gauge (G.target edge) / gauge (G.source edge) := by
  constructor
  · exact exists_slopeGauge_of_cycleProduct_eq_one_of_stronglyConnected
      slope hconnected hnonneg
  · rintro ⟨gauge, hgauge, hedge⟩ vertex cycle
    exact cycleProduct_eq_one_of_slopeGauge slope hgauge hedge cycle

end Gauges

end MaxAffineTransport

end

end DirectedTransport
