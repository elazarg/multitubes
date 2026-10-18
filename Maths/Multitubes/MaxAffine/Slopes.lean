/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Exact
public import Maths.Multitubes.MaxAffine.Duality
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Maths.Multitubes.FiniteInequality.Quantitative

/-!
# Recession regimes and slope gauges for max-affine transport

The recession reduction for max-affine branch rows classifies the mixed
subunit/unit and superunit/unit regimes, including their cycle criteria.  A
multiplicative slope gauge gives an intrinsic description of the critical
subsystem.

The two regimes are one statement.  Pairing a branch row with a constant
direction leaves `constant * (1 - slope)` on an affine row and `constant` on a
genuine floor row, so along any *nonzero* constant the critical rows are exactly
the affine rows of unit slope, whatever the constant is.  Only recession depends
on its sign: a positive constant is receded along by every subunit row and by
every floor row, a negative one by every superunit row and by no floor row at
all.  Hence the subunit regime and the floorless superunit regime are
`Maths.MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction`
read at `1` and at `-1`, and both are kept below as the corollaries one reaches
for.

The slope-flat converse requires strong connectivity.  Without it, a DAG can
satisfy every cycle-product equation vacuously while carrying a zero slope.

## Main definitions

* `Maths.MaxAffineTransport.unitSlopeGraph`,
  `Maths.MaxAffineTransport.unitSlopeShift`: the subgraph of unit-slope edges and
  the shift carried by such an edge.
* `Maths.MaxAffineTransport.IsNonexpansiveGauge`,
  `Maths.MaxAffineTransport.IsExpansiveGauge`: a positive vertex gauge making
  every normalized edge slope at most, respectively at least, one.

## Main results

* `Maths.MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction`:
  **along any nonzero constant recession direction, feasibility reduces exactly to the affine rows
  of the unit-slope edges.**  The two slope regimes are its instances at `1` and at `-1`.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one`:
  when every slope is at most one, feasibility reduces exactly to the affine rows of the unit-slope
  edges; floors and strictly subunit rows are noncritical.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_one_le_slope`:
  the superunit companion, where floorlessness is what the sign change costs.
* `Maths.MaxAffineTransport.exists_unitSlopePotential_iff_unitSlopeCycles_nonpos`: the additive
  duality read on the unit-slope subgraph, with no slope regime and an arbitrary vertex type.
  Composed with either reduction it gives a cycle criterion.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one`:
  the resulting cycle criterion - a lax section exists exactly when every closed walk of the
  unit-slope subgraph has nonpositive shift sum.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_one_le_slope`:
  the same criterion in the superunit regime, which additionally requires every floor absent.
* `Maths.MaxAffineTransport.exists_nonexpansiveGauge_iff_cycleProduct_le_one`:
  **positive gauge theorem** - for nonnegative slopes and finitely many edges, a nonexpansive
  gauge exists exactly when every directed cycle product is at most one.  The vertex type is
  arbitrary.
* `Maths.MaxAffineTransport.exists_expansiveGauge_iff_one_le_cycleProduct`: the
  dual statement, under the stronger hypothesis that every slope is strictly positive.
* `Maths.MaxAffineTransport.cycleProduct_eq_one_iff_exists_slopeGauge_of_stronglyConnected`:
  **multiplicative holonomy equivalence** - on a strongly connected graph, nonnegative slopes
  have unit product around every closed walk exactly when they are ratios of one positive
  vertex gauge. Strong connectivity is needed: see the DAG remark above.
-/

@[expose] public section

namespace Maths

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

/-- **Feasibility along a constant recession direction reduces to the unit-slope rows.**  Pairing
a branch row with a nonzero constant leaves `constant * (1 - slope)` on an affine row and
`constant` on a genuine floor row, so a row is critical exactly when it is affine of unit slope:
the constant cancels, and no floor row is ever critical.  Recession is therefore the only thing
a sign of the constant decides, and both slope regimes below are this statement read at
`constant = 1` and at `constant = -1`. -/
theorem exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction
    (constant : ℝ) (hconstant : constant ≠ 0)
    (hrecession : ∀ branch : Branch label,
      0 ≤ dotProduct (branchDelta G label branch) (fun _ : V ↦ constant)) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge) := by
  classical
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) (fun _ : V ↦ constant) hrecession
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
          (branchDelta G label) (fun _ : V ↦ constant) branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_const] at hcritical
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          change constant * (1 - (label edge).slope) = 0 at hcritical
          have hedge : (label edge).slope = 1 := by
            rcases mul_eq_zero.mp hcritical with hzero | hzero
            · exact absurd hzero hconstant
            · linarith
          have hunit := hcriticalPotential edge hedge
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          rw [hedge]
          linarith
      | inr edge =>
          change constant = 0 at hcritical
          exact absurd hcritical hconstant
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

/-- If every slope is at most one, feasibility reduces exactly to the affine
rows of unit-slope edges.  All floors and strictly subunit rows are noncritical.
This is the constant direction `1`, which every floor row and every subunit row
recedes along. -/
theorem exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one
    (hslope : ∀ edge : E, (label edge).slope ≤ 1) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge) := by
  refine exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction 1
    one_ne_zero fun branch ↦ ?_
  rw [dotProduct_branchDelta_const]
  cases branch.1 with
  | inl edge => simp only [one_mul]; linarith [hslope edge]
  | inr edge => norm_num

/-- Unit-slope edges as a directed subgraph. -/
abbrev UnitSlopeEdge (label : E → Label) :=
  ↥{edge : E | (label edge).slope = 1}

/-- The directed graph containing exactly the unit-slope edges. -/
abbrev unitSlopeGraph (G : EdgeGraph V E) (label : E → Label) :
    EdgeGraph V (UnitSlopeEdge label) :=
  G.restrictEdges {edge | (label edge).slope = 1}

/-- The shift on a unit-slope edge. -/
def unitSlopeShift (label : E → Label) (edge : UnitSlopeEdge label) : ℝ :=
  (label edge.1).shift

omit [Fintype V] [DecidableEq V] in
/-- **A unit-slope potential is a max-plus potential of the unit-slope subgraph.**  This is the
additive duality of `Maths.Multitubes.Additive.Potentials` read on that subgraph, and it
mentions no slope regime: it is the second half of both cycle criteria below.  Only the edges
need be finite, and the vertex type is arbitrary; the regimes are where the rest of the
hypotheses come from. -/
theorem exists_unitSlopePotential_iff_unitSlopeCycles_nonpos :
    (∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge)) ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        walkSum (unitSlopeShift label) cycle ≤ 0 := by
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

/-- Complete cycle criterion in the mixed subunit/unit regime. -/
theorem exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one
    (hslope : ∀ edge : E, (label edge).slope ≤ 1) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        walkSum (unitSlopeShift label) cycle ≤ 0 :=
  (exists_isLaxSection_iff_exists_unitSlopePotential_of_slope_le_one hslope).trans
    exists_unitSlopePotential_iff_unitSlopeCycles_nonpos

/-- In a floorless all-superunit/unit system, the direction `-1` reduces
feasibility to the same unit-slope affine subsystem.  Floorlessness is what the
sign change costs: a genuine floor row pairs with `-1` to `-1`, so it recedes
along no negative constant. -/
theorem exists_isLaxSection_iff_exists_unitSlopePotential_of_one_le_slope
    (hslope : ∀ edge : E, 1 ≤ (label edge).slope)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope = 1 →
          (label edge).shift + potential (G.source edge) ≤
            potential (G.target edge) := by
  refine exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction (-1)
    (by norm_num) fun branch ↦ ?_
  rw [dotProduct_branchDelta_const]
  rcases branch with ⟨action, hgenuine⟩
  cases action with
  | inl edge => simp only [neg_mul, one_mul]; linarith [hslope edge]
  | inr edge => exact (hgenuine (hfloor edge)).elim

/-- Complete cycle criterion in the floorless mixed superunit/unit regime. -/
theorem exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_one_le_slope
    (hslope : ∀ edge : E, 1 ≤ (label edge).slope)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        walkSum (unitSlopeShift label) cycle ≤ 0 :=
  (exists_isLaxSection_iff_exists_unitSlopePotential_of_one_le_slope hslope hfloor).trans
    exists_unitSlopePotential_iff_unitSlopeCycles_nonpos

end RecessionRegimes

/-! ## Intrinsic multiplicative slope gauges -/

section Gauges

variable {G : EdgeGraph V E} (slope : E → ℝ)

/-- Edgewise gauge equality telescopes along a walk, without requiring a
global equality assumption on edges outside that walk. -/
theorem walkProd_mul_gauge_eq_of_forall_mem
    {gauge : V → ℝ} {start finish : V} (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges,
      slope edge * gauge (G.source edge) = gauge (G.target edge)) :
    walkProd slope walk * gauge start = gauge finish := by
  have h := (ofSMul G ℝ slope).walkMap_rel_of_forall_mem_edges (family := gauge)
    (R := fun _ => Eq) (fun _ => rfl) (fun _ => Eq.trans) walk
    (fun _ _ _ _ hxy => congrArg _ hxy) hedge
  rwa [walkMap_ofSMul_eq_walkLabel_smul, walkLabel_eq_walkProd, smul_eq_mul] at h

/-- A positive vertex gauge making all normalized slopes nonexpansive. -/
def IsNonexpansiveGauge (gauge : V → ℝ) : Prop :=
  (∀ vertex, 0 < gauge vertex) ∧
    ∀ edge, slope edge * gauge (G.source edge) ≤ gauge (G.target edge)

/-- A nonexpansive gauge controls the product along every forward walk. -/
theorem walkProd_mul_gauge_le
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    walkProd slope walk * gauge start ≤ gauge finish := by
  have h := (ofSMul G ℝ slope).walkMap_rel_of_forall_mem_edges (family := gauge)
    (R := fun _ => (· ≤ ·)) (fun _ => le_rfl) (fun _ => le_trans) walk
    (fun edge _ _ _ hxy => mul_le_mul_of_nonneg_left hxy (hnonneg edge)) fun edge _ => hgauge.2 edge
  rwa [walkMap_ofSMul_eq_walkLabel_smul, walkLabel_eq_walkProd, smul_eq_mul] at h

/-- If one traversed edge is strictly noncritical for a nonexpansive gauge,
the path product satisfies a strict endpoint inequality. -/
theorem walkProd_mul_gauge_lt_of_exists_strict
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    (∃ edge ∈ walk.edges,
      slope edge * gauge (G.source edge) < gauge (G.target edge)) →
      walkProd slope walk * gauge start < gauge finish := by
  intro hstrict
  induction walk with
  | nil => simp at hstrict
  | concat edge walk ih =>
      rcases hstrict with ⟨candidate, hcandidate, hstrictCandidate⟩
      rw [EdgeGraph.Walk.edges_concat, List.mem_append] at hcandidate
      rcases hcandidate with hbefore | hlast
      · have hprefix := ih ⟨candidate, hbefore, hstrictCandidate⟩
        rw [walkProd_concat]
        by_cases hzero : slope edge = 0
        · rw [hzero]
          simpa using hgauge.1 (G.target edge)
        · have hpositive : 0 < slope edge :=
            lt_of_le_of_ne (hnonneg edge) (Ne.symm hzero)
          calc
            (walkProd slope walk * slope edge) * gauge start =
                slope edge *
                  (walkProd slope walk * gauge start) := by ring
            _ < slope edge * gauge (G.source edge) :=
              mul_lt_mul_of_pos_left hprefix hpositive
            _ ≤ gauge (G.target edge) := hgauge.2 edge
      · simp only [List.mem_singleton] at hlast
        subst candidate
        have hprefix :=
          walkProd_mul_gauge_le slope hnonneg hgauge walk
        rw [walkProd_concat]
        calc
          (walkProd slope walk * slope edge) * gauge start =
              slope edge *
                (walkProd slope walk * gauge start) := by ring
          _ ≤ slope edge * gauge (G.source edge) :=
            mul_le_mul_of_nonneg_left hprefix (hnonneg edge)
          _ < gauge (G.target edge) := hstrictCandidate

/-- Every nonexpansive gauge forces every directed cycle product below one. -/
theorem cycleProduct_le_one_of_nonexpansiveGauge
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkProd slope cycle ≤ 1 := by
  have hwalk := walkProd_mul_gauge_le slope hnonneg hgauge cycle
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
    walkProd slope cycle < 1 := by
  have hwalk := walkProd_mul_gauge_lt_of_exists_strict
    slope hnonneg hgauge cycle hstrict
  nlinarith [hgauge.1 base]

/-- Under a nonexpansive positive gauge, a cycle has product one exactly when
every traversed edge is gauge-critical. -/
theorem cycleProduct_eq_one_iff_forall_gaugeCritical_of_nonexpansiveGauge
    (hnonneg : ∀ edge, 0 ≤ slope edge)
    {gauge : V → ℝ} (hgauge : IsNonexpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkProd slope cycle = 1 ↔
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
      walkProd_mul_gauge_eq_of_forall_mem slope cycle hcritical
    nlinarith [hgauge.1 base]

/-- Positive-slope edges, used to take logarithms without imposing positivity
on zero-slope edges. -/
abbrev PositiveSlopeEdge := ↥{edge : E | 0 < slope edge}

/-- The subgraph of positive-slope edges. -/
abbrev positiveSlopeGraph : EdgeGraph V (PositiveSlopeEdge slope) :=
  G.restrictEdges {edge | 0 < slope edge}

/-- Exponentiating the log-weight of a walk recovers its slope product, when every slope of the
ambient graph is positive.  On a graph with zero slopes it applies to
`Maths.MaxAffineTransport.positiveSlopeGraph`. -/
theorem exp_walkSum_log_eq_walkProd (hpos : ∀ edge, 0 < slope edge)
    {start finish : V} (walk : G.Walk start finish) :
    Real.exp (walkSum (fun edge => Real.log (slope edge)) walk) =
      walkProd slope walk := by
  induction walk with
  | nil => simp [walkSum, walkProd]
  | concat edge walk ih =>
      rw [walkSum_concat, walkProd_concat,
        Real.exp_add, ih, Real.exp_log (hpos edge)]

/-- **Positive gauge theorem.**  With finitely many edges and nonnegative
slopes, all directed cycle products are at most one exactly when a positive
vertex gauge makes every normalized edge slope at most one.  The vertex type is
arbitrary, as in the additive duality this rests on. -/
theorem exists_nonexpansiveGauge_iff_cycleProduct_le_one
    [Finite E] (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∃ gauge : V → ℝ, IsNonexpansiveGauge (G := G) slope gauge) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        walkProd slope cycle ≤ 1 := by
  constructor
  · rintro ⟨gauge, hgauge⟩ base cycle
    exact cycleProduct_le_one_of_nonexpansiveGauge slope hnonneg hgauge cycle
  · intro hcycle
    have hlogCycle (base : V)
        (cycle : (positiveSlopeGraph (G := G) slope).Walk base base) :
        walkSum
          (fun edge : PositiveSlopeEdge slope ↦ Real.log (slope edge.1)) cycle ≤ 0 := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_zero,
        exp_walkSum_log_eq_walkProd (fun edge : PositiveSlopeEdge slope ↦ slope edge.1)
          (fun edge ↦ edge.2)]
      rw [← walkProd_ofRestrictEdges]
      exact hcycle base cycle.ofRestrictEdges
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

variable {slope} in
/-- An expansive gauge forces every slope to be positive: a positive target gauge is bounded by
the slope times a positive source gauge. -/
theorem IsExpansiveGauge.slope_pos {gauge : V → ℝ}
    (hgauge : IsExpansiveGauge (G := G) slope gauge) (edge : E) : 0 < slope edge :=
  pos_of_mul_pos_left ((hgauge.1 (G.target edge)).trans_le (hgauge.2 edge))
    (hgauge.1 (G.source edge)).le

/-- An expansive gauge controls every forward walk from below. -/
theorem gauge_le_walkProd_mul
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    gauge finish ≤ walkProd slope walk * gauge start := by
  have h := (ofSMul G ℝ slope).walkMap_rel_of_forall_mem_edges (family := gauge)
    (R := fun _ => (· ≥ ·)) (fun _ => le_rfl) (fun _ _ _ _ hxy hyz => hyz.trans hxy) walk
    (fun edge _ _ _ hxy => mul_le_mul_of_nonneg_left hxy (hgauge.slope_pos edge).le)
    fun edge _ => hgauge.2 edge
  rwa [walkMap_ofSMul_eq_walkLabel_smul, walkLabel_eq_walkProd, smul_eq_mul] at h

/-- If one traversed edge is strictly noncritical for an expansive gauge,
the path product satisfies a strict endpoint inequality. -/
theorem gauge_lt_walkProd_mul_of_exists_strict
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {start finish : V} (walk : G.Walk start finish) :
    (∃ edge ∈ walk.edges,
      gauge (G.target edge) < slope edge * gauge (G.source edge)) →
      gauge finish < walkProd slope walk * gauge start := by
  intro hstrict
  induction walk with
  | nil => simp at hstrict
  | concat edge walk ih =>
      rcases hstrict with ⟨candidate, hcandidate, hstrictCandidate⟩
      rw [EdgeGraph.Walk.edges_concat, List.mem_append] at hcandidate
      rcases hcandidate with hbefore | hlast
      · have hprefix := ih ⟨candidate, hbefore, hstrictCandidate⟩
        rw [walkProd_concat]
        calc
          gauge (G.target edge) ≤
              slope edge * gauge (G.source edge) := hgauge.2 edge
          _ < slope edge *
              (walkProd slope walk * gauge start) :=
            mul_lt_mul_of_pos_left hprefix (hgauge.slope_pos edge)
          _ = (walkProd slope walk * slope edge) * gauge start := by
            ring
      · simp only [List.mem_singleton] at hlast
        subst candidate
        have hprefix := gauge_le_walkProd_mul slope hgauge walk
        rw [walkProd_concat]
        calc
          gauge (G.target edge) <
              slope edge * gauge (G.source edge) := hstrictCandidate
          _ ≤ slope edge *
              (walkProd slope walk * gauge start) :=
            mul_le_mul_of_nonneg_left hprefix (hgauge.slope_pos edge).le
          _ = (walkProd slope walk * slope edge) * gauge start := by
            ring

/-- Every expansive gauge forces every directed cycle product above one. -/
theorem one_le_cycleProduct_of_expansiveGauge
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    1 ≤ walkProd slope cycle := by
  have hwalk := gauge_le_walkProd_mul slope hgauge cycle
  nlinarith [hgauge.1 base]

/-- A cycle using a strictly noncritical edge of an expansive gauge has
product strictly above one. -/
theorem one_lt_cycleProduct_of_expansiveGauge_of_exists_strict
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base)
    (hstrict : ∃ edge ∈ cycle.edges,
      gauge (G.target edge) < slope edge * gauge (G.source edge)) :
    1 < walkProd slope cycle := by
  have hwalk := gauge_lt_walkProd_mul_of_exists_strict
    slope hgauge cycle hstrict
  nlinarith [hgauge.1 base]

/-- Under an expansive positive gauge, a cycle has product one exactly when
every traversed edge is gauge-critical. -/
theorem cycleProduct_eq_one_iff_forall_gaugeCritical_of_expansiveGauge
    {gauge : V → ℝ} (hgauge : IsExpansiveGauge (G := G) slope gauge)
    {base : V} (cycle : G.Walk base base) :
    walkProd slope cycle = 1 ↔
      ∀ edge ∈ cycle.edges,
        slope edge * gauge (G.source edge) = gauge (G.target edge) := by
  constructor
  · intro hproduct edge hedge
    by_contra hnoncritical
    have hstrict :=
      one_lt_cycleProduct_of_expansiveGauge_of_exists_strict
        slope hgauge cycle ⟨edge, hedge,
          lt_of_le_of_ne (hgauge.2 edge)
            (fun heq => hnoncritical heq.symm)⟩
    linarith
  · intro hcritical
    have htelescope :=
      walkProd_mul_gauge_eq_of_forall_mem slope cycle hcritical
    nlinarith [hgauge.1 base]

/-- **Dual positive gauge theorem.**  For positive slopes and finitely many
edges, all directed cycle products are at least one exactly when a positive
vertex gauge makes every normalized edge slope at least one.  The vertex type is
arbitrary. -/
theorem exists_expansiveGauge_iff_one_le_cycleProduct
    [Finite E] (hpos : ∀ edge, 0 < slope edge) :
    (∃ gauge : V → ℝ, IsExpansiveGauge (G := G) slope gauge) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        1 ≤ walkProd slope cycle := by
  constructor
  · rintro ⟨gauge, hgauge⟩ base cycle
    exact one_le_cycleProduct_of_expansiveGauge slope hgauge cycle
  · intro hcycle
    have hlogCycle (base : V) (cycle : G.Walk base base) :
        walkSum
          (fun edge => -Real.log (slope edge)) cycle ≤ 0 := by
      have hlogNonneg : 0 ≤ walkSum
          (fun edge => Real.log (slope edge)) cycle := by
        apply Real.exp_le_exp.mp
        rw [Real.exp_zero, exp_walkSum_log_eq_walkProd slope hpos cycle]
        exact hcycle base cycle
      rw [walkSum_neg]
      linarith
    obtain ⟨potential, hpotential⟩ :=
      (MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := G) (fun edge => -Real.log (slope edge))).mpr hlogCycle
    let gauge : V → ℝ := fun vertex => Real.exp (-potential vertex)
    refine ⟨gauge, fun vertex => Real.exp_pos _, fun edge => ?_⟩
    have hrow := hpotential.le edge
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
      walkProd slope cycle = 1) (edge : E) :
    0 < slope edge := by
  let back := (hconnected.nonempty_walk (G.target edge) (G.source edge)).some
  have hcycle := hflat (G.source edge)
    ((EdgeGraph.Walk.singleton (G := G) edge).append back)
  rw [walkProd_append] at hcycle
  have hsingle : walkProd slope
      (EdgeGraph.Walk.singleton (G := G) edge) = slope edge := by
    simp [walkProd]
  rw [hsingle] at hcycle
  have hback : 0 ≤ walkProd slope back := by
    unfold walkProd
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
      walkProd slope cycle = 1) :
    ∃ gauge : V → ℝ, (∀ vertex, 0 < gauge vertex) ∧
      ∀ edge, slope edge = gauge (G.target edge) / gauge (G.source edge) := by
  have hpos : ∀ edge, 0 < slope edge :=
    slope_pos_of_cycleProduct_eq_one_of_stronglyConnected slope hconnected
      hnonneg hflat
  have hzero : HasZeroCycleSums G (fun edge ↦ Real.log (slope edge)) := by
    intro vertex cycle
    apply Real.exp_injective
    rw [Real.exp_zero, exp_walkSum_log_eq_walkProd slope hpos cycle, hflat vertex cycle]
  obtain ⟨potential, hpotential⟩ :=
    (CycleCoboundary.isCoboundary_iff_hasZeroCycleSums hconnected).mpr hzero
  let gauge : V → ℝ := fun vertex ↦ Real.exp (potential vertex)
  refine ⟨gauge, fun vertex ↦ Real.exp_pos _, fun edge ↦ ?_⟩
  have hedge := hpotential edge
  rw [coboundary_apply] at hedge
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
theorem walkProd_mul_gauge_eq_of_slopeGauge
    {gauge : V → ℝ} (hgauge : ∀ vertex, 0 < gauge vertex)
    (hedge : ∀ edge,
      slope edge = gauge (G.target edge) / gauge (G.source edge))
    {start finish : V} (walk : G.Walk start finish) :
    walkProd slope walk * gauge start = gauge finish :=
  walkProd_mul_gauge_eq_of_forall_mem slope walk fun edge _ => by
    rw [hedge edge, div_mul_cancel₀ _ (hgauge (G.source edge)).ne']

/-- Exact gauge ratios have unit multiplicative holonomy on every cycle. -/
theorem cycleProduct_eq_one_of_slopeGauge
    {gauge : V → ℝ} (hgauge : ∀ vertex, 0 < gauge vertex)
    (hedge : ∀ edge,
      slope edge = gauge (G.target edge) / gauge (G.source edge))
    {base : V} (cycle : G.Walk base base) :
    walkProd slope cycle = 1 := by
  have htel := walkProd_mul_gauge_eq_of_slopeGauge
    slope hgauge hedge cycle
  exact (mul_right_cancel₀ (hgauge base).ne') (by simpa using htel)

/-- **Multiplicative holonomy equivalence.**  On a strongly connected graph,
nonnegative slopes have unit product around every closed walk exactly when
they are exact ratios of one positive vertex gauge. -/
theorem cycleProduct_eq_one_iff_exists_slopeGauge_of_stronglyConnected
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkProd slope cycle = 1) ↔
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

end Maths
