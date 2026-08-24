/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.MaxAffine.GaugeFeasibility
public import DirectedTransport.MaxAffine.Relaxation

import DirectedTransport.MaxAffine.Scalar

/-!
# Raw holonomy formulas on gauge-critical paths

The additive critical graph records shifts divided by the target gauge.  This
file connects that normalized description back to the original max-affine
path coefficients.  On a critical path, the raw slope is the endpoint gauge
ratio, the raw shift is the terminal gauge times the normalized walk weight,
and the uniform-relaxation mass is the terminal gauge times a reciprocal-target
mass.  In particular, a critical cycle has raw slope one and its exact uniform
slack mean is the normalized shift sum divided by the reciprocal-target mass.

## Main definitions

* `DirectedTransport.MaxAffineTransport.forgetGaugeCriticalWalk`,
  `DirectedTransport.MaxAffineTransport.gaugeCriticalLabelList`: a critical walk read back as a walk
  of the original graph, and the original max-affine labels along it.
* `DirectedTransport.MaxAffineTransport.walkReciprocalTargetMass`: the sum of reciprocal target
  gauges along a critical walk, the quantity `S_C` of the raw formulas.
* `DirectedTransport.MaxAffineTransport.HasPrefixedCycleHolonomies`: every original cycle holonomy
  has a pre-fixed point.

## Main results

* `DirectedTransport.MaxAffineTransport.pathSlope_gaugeCriticalLabelList`: the raw slope product
  along a critical path is the endpoint gauge ratio, so a critical cycle has raw slope one.
* `DirectedTransport.MaxAffineTransport.pathShift_gaugeCriticalLabelList`,
  `MaxAffineTransport.pathRelaxationMass_gaugeCriticalLabelList`: the raw affine shift and the
  raw uniform-relaxation mass are the terminal gauge times the normalized walk weight and the
  reciprocal-target mass respectively. Both require a positive gauge.
* `DirectedTransport.MaxAffineTransport.rawCycleMean_eq_gaugeCriticalCycleRatio`: the raw max-affine
  cycle mean is the `gaugeCriticalCycleRatio` used by the quantitative feasibility theorems. Both
  sides take the value `0` on the empty cycle by totalized division.
* `DirectedTransport.MaxAffineTransport.hasCyclicSlack_gaugeCriticalCycle_iff_cycleRatio_le`: on a
  nonempty critical cycle, the exact original slack criterion is that ratio bound. Floors stay
  arbitrary - at raw product one they do not move the threshold.
* `MaxAffineTransport.exists_isLaxSection_iff_prefixedCycleHolonomies_of_nonexpansiveGauge`,
  `MaxAffineTransport.exists_isLaxSection_iff_prefixedCycleHolonomies_of_expansiveGauge`:
  feasibility is equivalent to pre-fixedness of every *original* cycle holonomy, not only the
  critical ones. The expansive form assumes floors absent.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE}
variable {G : EdgeGraph V E} {label : E → Label} {gauge : V → ℝ}

/-- Forget the criticality proof on every edge of a critical walk. -/
def forgetGaugeCriticalWalk {start : V} :
    {finish : V} →
      (gaugeCriticalGraph (G := G) label gauge).Walk start finish →
        G.Walk start finish
  | _, .nil => .nil
  | _, .concat walk edge legal =>
      (forgetGaugeCriticalWalk walk).concat edge.1 legal

@[simp] theorem edges_forgetGaugeCriticalWalk {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    (forgetGaugeCriticalWalk walk).edges = walk.edges.map Subtype.val := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      change G.source edge.1 = _ at legal
      rw [forgetGaugeCriticalWalk]
      simp only [EdgeGraph.Walk.edges_concat, List.map_append,
        List.map_singleton]
      rw [ih]

/-- Original max-affine labels along a critical walk. -/
def gaugeCriticalLabelList {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    List Label :=
  walk.edges.map fun edge => label edge.1

@[simp] theorem edgeLabels_forgetGaugeCriticalWalk {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    (forgetGaugeCriticalWalk walk).edges.map label =
      gaugeCriticalLabelList walk := by
  simp [gaugeCriticalLabelList]

@[simp] theorem gaugeCriticalLabelList_nil (vertex : V) :
    gaugeCriticalLabelList
      (.nil : (gaugeCriticalGraph (G := G) label gauge).Walk vertex vertex) = [] :=
  rfl

@[simp] theorem gaugeCriticalLabelList_concat {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish)
    (edge : GaugeCriticalEdge (G := G) label gauge)
    (legal : G.source edge.1 = finish) :
    gaugeCriticalLabelList (walk.concat edge legal) =
      gaugeCriticalLabelList walk ++ [label edge.1] := by
  simp [gaugeCriticalLabelList]

/-- Sum of reciprocal target gauges along a critical path. -/
def walkReciprocalTargetMass {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) : ℝ :=
  (walk.edges.map fun edge => 1 / gauge (G.target edge.1)).sum

@[simp] theorem walkReciprocalTargetMass_nil (vertex : V) :
    walkReciprocalTargetMass
      (.nil : (gaugeCriticalGraph (G := G) label gauge).Walk vertex vertex) = 0 :=
  rfl

@[simp] theorem walkReciprocalTargetMass_concat {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish)
    (edge : GaugeCriticalEdge (G := G) label gauge)
    (legal : G.source edge.1 = finish) :
    walkReciprocalTargetMass (walk.concat edge legal) =
      walkReciprocalTargetMass walk + 1 / gauge (G.target edge.1) := by
  simp [walkReciprocalTargetMass]

/-- The local reciprocal-mass sum is the additive walk weight used by the
gauge-feasibility API. -/
@[simp] theorem walkReciprocalTargetMass_eq_walkWeight_gaugeCriticalMass
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    walkReciprocalTargetMass walk =
      MaxPlusPotential.walkWeight (gaugeCriticalMass gauge) walk := by
  rfl

private theorem slope_eq_gauge_ratio
    (hgauge : ∀ vertex, 0 < gauge vertex)
    (edge : GaugeCriticalEdge (G := G) label gauge) :
    (label edge.1).slope =
      gauge (G.target edge.1) / gauge (G.source edge.1) := by
  apply (eq_div_iff (hgauge (G.source edge.1)).ne').mpr
  exact edge.2

/-- The raw slope product on a critical path is its endpoint gauge ratio. -/
theorem pathSlope_gaugeCriticalLabelList
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    Label.pathSlope (gaugeCriticalLabelList walk) = gauge finish / gauge start := by
  induction walk with
  | nil =>
      simp only [gaugeCriticalLabelList_nil, Label.pathSlope_nil]
      rw [div_self (hgauge _).ne']
  | @concat finish walk edge legal ih =>
      change G.source edge.1 = finish at legal
      subst finish
      change Label.pathSlope (gaugeCriticalLabelList walk) =
        gauge (G.source edge.1) / gauge start at ih
      change Label.pathSlope (gaugeCriticalLabelList (walk.concat edge rfl)) =
        gauge (G.target edge.1) / gauge start
      rw [gaugeCriticalLabelList_concat, Label.pathSlope_append]
      simp only [Label.pathSlope_cons, Label.pathSlope_nil, mul_one]
      rw [ih, slope_eq_gauge_ratio hgauge edge]
      field_simp [(hgauge (G.source edge.1)).ne',
        (hgauge (G.target edge.1)).ne', (hgauge start).ne']

/-- The raw affine shift is the terminal gauge times the normalized critical
walk weight. -/
theorem pathShift_gaugeCriticalLabelList
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    Label.pathShift (gaugeCriticalLabelList walk) =
      gauge finish * MaxPlusPotential.walkWeight
        (gaugeCriticalShift label gauge) walk := by
  induction walk with
  | nil => simp [MaxPlusPotential.walkWeight]
  | @concat finish walk edge legal ih =>
      change G.source edge.1 = finish at legal
      subst finish
      change Label.pathShift (gaugeCriticalLabelList walk) =
        gauge (G.source edge.1) *
          MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) walk at ih
      change Label.pathShift (gaugeCriticalLabelList (walk.concat edge rfl)) =
        gauge (G.target edge.1) *
          MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge)
            (walk.concat edge rfl)
      rw [gaugeCriticalLabelList_concat, Label.pathShift_append]
      simp only [Label.pathShift_cons, Label.pathShift_nil,
        Label.pathSlope_cons, Label.pathSlope_nil, mul_one, one_mul, zero_add,
        MaxPlusPotential.walkWeight_concat]
      rw [ih]
      have hcritical := edge.2
      have htarget : gauge (G.target edge.1) ≠ 0 :=
        (hgauge (G.target edge.1)).ne'
      dsimp [gaugeCriticalShift]
      calc
        (label edge.1).shift +
            (label edge.1).slope *
              (gauge (G.source edge.1) *
                MaxPlusPotential.walkWeight
                  (gaugeCriticalShift label gauge) walk) =
            (label edge.1).shift + gauge (G.target edge.1) *
              MaxPlusPotential.walkWeight
                (gaugeCriticalShift label gauge) walk := by
          rw [← mul_assoc, hcritical]
        _ = gauge (G.target edge.1) *
            (MaxPlusPotential.walkWeight
                (gaugeCriticalShift label gauge) walk +
              (label edge.1).shift / gauge (G.target edge.1)) := by
          field_simp
          ring

/-- The raw common-relaxation coefficient is the terminal gauge times the
sum of reciprocal target gauges. -/
theorem pathRelaxationMass_gaugeCriticalLabelList
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    Label.pathRelaxationMass (gaugeCriticalLabelList walk) =
      gauge finish * walkReciprocalTargetMass walk := by
  induction walk with
  | nil => simp
  | @concat finish walk edge legal ih =>
      change G.source edge.1 = finish at legal
      subst finish
      change Label.pathRelaxationMass (gaugeCriticalLabelList walk) =
        gauge (G.source edge.1) * walkReciprocalTargetMass walk at ih
      change Label.pathRelaxationMass
          (gaugeCriticalLabelList (walk.concat edge rfl)) =
        gauge (G.target edge.1) *
          walkReciprocalTargetMass (walk.concat edge rfl)
      rw [gaugeCriticalLabelList_concat,
        Label.pathRelaxationMass_append]
      simp only [Label.pathRelaxationMass_cons,
        Label.pathRelaxationMass_nil, Label.pathSlope_cons,
        Label.pathSlope_nil, mul_one, zero_add,
        walkReciprocalTargetMass_concat]
      rw [ih]
      have hcritical := edge.2
      have htarget : gauge (G.target edge.1) ≠ 0 :=
        (hgauge (G.target edge.1)).ne'
      calc
        1 + (label edge.1).slope *
            (gauge (G.source edge.1) * walkReciprocalTargetMass walk) =
            1 + gauge (G.target edge.1) *
              walkReciprocalTargetMass walk := by
          rw [← mul_assoc, hcritical]
        _ = gauge (G.target edge.1) *
            (walkReciprocalTargetMass walk +
              1 / gauge (G.target edge.1)) := by
          field_simp
          ring

/-- Division form of the raw-shift bridge. -/
theorem walkWeight_gaugeCriticalShift_eq_pathShift_div
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) walk =
      Label.pathShift (gaugeCriticalLabelList walk) / gauge finish := by
  rw [pathShift_gaugeCriticalLabelList hgauge]
  field_simp [(hgauge finish).ne']

/-- Division form of the relaxation-mass bridge. -/
theorem walkReciprocalTargetMass_eq_pathRelaxationMass_div
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    walkReciprocalTargetMass walk =
      Label.pathRelaxationMass (gaugeCriticalLabelList walk) / gauge finish := by
  rw [pathRelaxationMass_gaugeCriticalLabelList hgauge]
  field_simp [(hgauge finish).ne']

/-- Reciprocal target mass is positive on every nonempty critical walk. -/
theorem walkReciprocalTargetMass_pos
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish)
    (hwalk : 0 < walk.length) :
    0 < walkReciprocalTargetMass walk := by
  unfold walkReciprocalTargetMass
  apply List.sum_pos
  · intro value hvalue
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hvalue
    exact one_div_pos.mpr (hgauge (G.target edge.1))
  · apply List.length_pos_iff.mp
    simpa only [List.length_map, EdgeGraph.Walk.edges_length] using hwalk

/-- On a critical cycle, the exact raw uniform-slack mean is the normalized
critical shift sum divided by reciprocal target mass.  Both sides are `0` on
the empty cycle by totalized division. -/
theorem rawCycleMean_eq_gaugeCriticalMean
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base) :
    Label.pathShift (gaugeCriticalLabelList cycle) /
        Label.pathRelaxationMass (gaugeCriticalLabelList cycle) =
      MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle /
        walkReciprocalTargetMass cycle := by
  rw [pathShift_gaugeCriticalLabelList hgauge,
    pathRelaxationMass_gaugeCriticalLabelList hgauge]
  field_simp [(hgauge base).ne']

/-- The raw max-affine cycle mean is the gauge-critical ratio used by the
quantitative feasibility theorems.  Both sides use the value `0` on the empty
cycle; semantic threshold criteria impose positive length. -/
theorem rawCycleMean_eq_gaugeCriticalCycleRatio
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base) :
    Label.pathShift (gaugeCriticalLabelList cycle) /
        Label.pathRelaxationMass (gaugeCriticalLabelList cycle) =
      gaugeCriticalCycleRatio label gauge cycle := by
  rw [rawCycleMean_eq_gaugeCriticalMean hgauge cycle,
    walkReciprocalTargetMass_eq_walkWeight_gaugeCriticalMass]
  rfl

/-- Exact original max-affine slack criterion on a nonempty gauge-critical
cycle.  Floors remain arbitrary: at raw product one they do not affect the
threshold. -/
theorem hasCyclicSlack_gaugeCriticalCycle_iff
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base)
    (hcycle : 0 < cycle.length) (level : ℝ) :
    Label.HasCyclicSlack (gaugeCriticalLabelList cycle) level ↔
      MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle /
        walkReciprocalTargetMass cycle ≤ level := by
  have hne : gaugeCriticalLabelList cycle ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [gaugeCriticalLabelList, List.length_map,
      EdgeGraph.Walk.edges_length, List.length_nil] at hlength
    omega
  have hslope (candidate : Label) (hcandidate : candidate ∈ gaugeCriticalLabelList cycle) :
      0 ≤ candidate.slope := by
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hcandidate
    rw [slope_eq_gauge_ratio hgauge edge]
    exact div_nonneg (hgauge _).le (hgauge _).le
  have hproduct : Label.pathSlope (gaugeCriticalLabelList cycle) = 1 := by
    rw [pathSlope_gaugeCriticalLabelList hgauge,
      div_self (hgauge base).ne']
  rw [Label.hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one
    hne hslope hproduct]
  rw [rawCycleMean_eq_gaugeCriticalMean hgauge cycle]

/-- Existing-ratio form of the exact original max-affine slack criterion. -/
theorem hasCyclicSlack_gaugeCriticalCycle_iff_cycleRatio_le
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base)
    (hcycle : 0 < cycle.length) (level : ℝ) :
    Label.HasCyclicSlack (gaugeCriticalLabelList cycle) level ↔
      gaugeCriticalCycleRatio label gauge cycle ≤ level := by
  rw [hasCyclicSlack_gaugeCriticalCycle_iff hgauge cycle hcycle,
    walkReciprocalTargetMass_eq_walkWeight_gaugeCriticalMass]
  rfl

/-- Coefficient-level bridge to the original max-affine holonomy. -/
theorem compList_gaugeCriticalCycle
    (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base) :
    Label.compList (gaugeCriticalLabelList cycle) =
      ⟨Label.pathFloor (gaugeCriticalLabelList cycle),
        gauge base * MaxPlusPotential.walkWeight
          (gaugeCriticalShift label gauge) cycle, 1⟩ := by
  have hslope (candidate : Label) (hcandidate : candidate ∈ gaugeCriticalLabelList cycle) :
      0 ≤ candidate.slope := by
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hcandidate
    rw [slope_eq_gauge_ratio hgauge edge]
    exact div_nonneg (hgauge _).le (hgauge _).le
  rw [Label.compList_eq_pathCoefficients hslope,
    pathShift_gaugeCriticalLabelList hgauge,
    pathSlope_gaugeCriticalLabelList hgauge]
  simp [(hgauge base).ne']

/-! ## Original cycle holonomy -/

/-- A strictly contractive composite of nonnegative-slope edge labels has a
pre-fixed point.  This statement uses the original, unnormalized walk
holonomy and allows arbitrary floors. -/
theorem exists_holonomyApply_le_self_of_cycleProduct_lt_one
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    {base : V} (cycle : G.Walk base base)
    (hproduct : walkSlopeProduct (fun edge => (label edge).slope) cycle < 1) :
    ∃ point : ℝ, holonomyApply label cycle point ≤ point := by
  let composite := Label.compList (cycle.edges.map label)
  have hcomposite : composite.slope < 1 := by
    dsimp [composite]
    rw [Label.slope_compList_eq_pathSlope]
    simpa [Label.pathSlope, walkSlopeProduct, List.map_map]
  obtain ⟨point, hpoint⟩ :=
    (Label.exists_apply_le_self_iff composite).mpr (Or.inl hcomposite)
  refine ⟨point, ?_⟩
  rw [← apply_compList_edges hslope cycle point]
  exact hpoint

/-- A strictly expansive composite of floorless nonnegative-slope edge labels
has a pre-fixed point. -/
theorem exists_holonomyApply_le_self_of_one_lt_cycleProduct_of_floorless
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥)
    {base : V} (cycle : G.Walk base base)
    (hproduct : 1 < walkSlopeProduct (fun edge => (label edge).slope) cycle) :
    ∃ point : ℝ, holonomyApply label cycle point ≤ point := by
  let composite := Label.compList (cycle.edges.map label)
  have hlabelSlope (candidate : Label) (hcandidate : candidate ∈ cycle.edges.map label) :
      0 ≤ candidate.slope := by
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hcandidate
    exact hslope edge
  have hlabelFloor (candidate : Label) (hcandidate : candidate ∈ cycle.edges.map label) :
      candidate.floor = ⊥ := by
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hcandidate
    exact hfloor edge
  have hcompositeSlope : 1 < composite.slope := by
    dsimp [composite]
    rw [Label.slope_compList_eq_pathSlope]
    simpa [Label.pathSlope, walkSlopeProduct, List.map_map]
  have hcompositeFloor : composite.floor = ⊥ :=
    Label.floor_compList_eq_bot_of_floorless hlabelSlope hlabelFloor
  obtain ⟨point, hpoint⟩ :=
    (Label.exists_apply_le_self_iff composite).mpr
      (Or.inr (Or.inr ⟨hcompositeSlope, by rw [hcompositeFloor]; exact bot_le⟩))
  refine ⟨point, ?_⟩
  rw [← apply_compList_edges hslope cycle point]
  exact hpoint

/-- A cycle containing a noncritical edge of a nonexpansive gauge has a
pre-fixed point in the original max-affine coordinates. -/
theorem exists_holonomyApply_le_self_of_noncriticalCycle_of_nonexpansiveGauge
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    {base : V} (cycle : G.Walk base base)
    (hnoncritical : ∃ edge ∈ cycle.edges,
      (label edge).slope * gauge (G.source edge) ≠ gauge (G.target edge)) :
    ∃ point : ℝ, holonomyApply label cycle point ≤ point := by
  have hstrict : ∃ edge ∈ cycle.edges,
      (label edge).slope * gauge (G.source edge) < gauge (G.target edge) := by
    obtain ⟨edge, hedge, hne⟩ := hnoncritical
    exact ⟨edge, hedge, lt_of_le_of_ne (hgauge.2 edge) hne⟩
  have hproduct :=
    cycleProduct_lt_one_of_nonexpansiveGauge_of_exists_strict
      (fun edge => (label edge).slope) hslope hgauge cycle hstrict
  exact exists_holonomyApply_le_self_of_cycleProduct_lt_one
    hslope cycle hproduct

/-- A cycle containing a noncritical edge of an expansive gauge has a
pre-fixed point when every original label is floorless. -/
theorem exists_holonomyApply_le_self_of_noncriticalCycle_of_expansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥)
    {base : V} (cycle : G.Walk base base)
    (hnoncritical : ∃ edge ∈ cycle.edges,
      (label edge).slope * gauge (G.source edge) ≠ gauge (G.target edge)) :
    ∃ point : ℝ, holonomyApply label cycle point ≤ point := by
  have hpos (edge : E) : 0 < (label edge).slope := by
    have hmul : 0 < (label edge).slope * gauge (G.source edge) :=
      (hgauge.1 (G.target edge)).trans_le (hgauge.2 edge)
    nlinarith [hgauge.1 (G.source edge)]
  have hstrict : ∃ edge ∈ cycle.edges,
      gauge (G.target edge) <
        (label edge).slope * gauge (G.source edge) := by
    obtain ⟨edge, hedge, hne⟩ := hnoncritical
    exact ⟨edge, hedge, lt_of_le_of_ne (hgauge.2 edge) hne.symm⟩
  have hproduct :=
    one_lt_cycleProduct_of_expansiveGauge_of_exists_strict
      (fun edge => (label edge).slope) hpos hgauge cycle hstrict
  exact
    exists_holonomyApply_le_self_of_one_lt_cycleProduct_of_floorless
      (fun edge => (hpos edge).le) hfloor cycle hproduct

/-- Every original max-affine cycle holonomy has a pre-fixed point. -/
def HasPrefixedCycleHolonomies (G : EdgeGraph V E) (label : E → Label) : Prop :=
  ∀ (base : V) (cycle : G.Walk base base),
    ∃ point : ℝ, holonomyApply label cycle point ≤ point

/-- Under a nonexpansive positive gauge and nonnegative slopes, feasibility is
equivalent to pre-fixedness of every original max-affine cycle holonomy.  The
reverse implication restricts to critical cycles; the forward implication
shows that all noncritical cycles are automatic once the section exists. -/
theorem exists_isLaxSection_iff_prefixedCycleHolonomies_of_nonexpansiveGauge
    [Fintype V] [DecidableEq V] [Fintype E]
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      HasPrefixedCycleHolonomies G label := by
  constructor
  · rintro ⟨potential, hpotential⟩ base cycle
    exact ⟨potential base,
      holonomyApply_cycle_le hslope hpotential cycle⟩
  · intro hprefixed
    apply
      (exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_nonexpansiveGauge
        gauge hgauge).mpr
    intro base cycle
    obtain ⟨point, hpoint⟩ :=
      hprefixed base (forgetGaugeCriticalWalk cycle)
    rw [← apply_compList_edges hslope, edgeLabels_forgetGaugeCriticalWalk,
      compList_gaugeCriticalCycle hgauge.1 cycle] at hpoint
    rw [Label.apply_le_self_iff_of_slope_eq_one _ rfl] at hpoint
    nlinarith [hgauge.1 base]

/-- With an expansive positive gauge and absent floors, feasibility is
equivalent to pre-fixedness of every original max-affine cycle holonomy. -/
theorem exists_isLaxSection_iff_prefixedCycleHolonomies_of_expansiveGauge
    [Fintype V] [DecidableEq V] [Fintype E]
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge : E, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      HasPrefixedCycleHolonomies G label := by
  have hslope (edge : E) : 0 ≤ (label edge).slope := by
    have hmul : 0 < (label edge).slope * gauge (G.source edge) :=
      (hgauge.1 (G.target edge)).trans_le (hgauge.2 edge)
    nlinarith [hgauge.1 (G.source edge)]
  constructor
  · rintro ⟨potential, hpotential⟩ base cycle
    exact ⟨potential base,
      holonomyApply_cycle_le hslope hpotential cycle⟩
  · intro hprefixed
    apply
      (exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_expansiveGauge
        gauge hgauge hfloor).mpr
    intro base cycle
    obtain ⟨point, hpoint⟩ :=
      hprefixed base (forgetGaugeCriticalWalk cycle)
    rw [← apply_compList_edges hslope, edgeLabels_forgetGaugeCriticalWalk,
      compList_gaugeCriticalCycle hgauge.1 cycle] at hpoint
    rw [Label.apply_le_self_iff_of_slope_eq_one _ rfl] at hpoint
    nlinarith [hgauge.1 base]

end MaxAffineTransport

end

end DirectedTransport
