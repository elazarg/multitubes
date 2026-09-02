/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Additive.Cycles
public import Maths.Multitube.MaxAffine.Slopes

import Maths.Multitube.MaxAffine.Additive

/-!
# Gauge-critical cycle criteria for max-affine feasibility

A positive slope gauge supplies a recession direction.  In the nonexpansive
case all floor rows and all strictly contracting affine rows are noncritical.
In the expansive case the negative gauge is a recession direction, provided
floors are absent.  Both systems reduce to the same unit-slope problem on the
gauge-critical edge subgraph after dividing vertex coordinates by the gauge.
At a raw residual level, the exact critical-cycle bound is `T_C / S_C`, where
`T_C` is normalized total shift and `S_C` is reciprocal target-gauge mass.

## Main definitions

* `Maths.MaxAffineTransport.GaugeCriticalEdge`,
  `Maths.MaxAffineTransport.gaugeCriticalGraph`: the edges on which a positive gauge
  makes the normalized slope exactly one, and the subgraph they span.
* `Maths.MaxAffineTransport.gaugeCriticalShift`: the shift of a critical edge after
  rescaling the target coordinate by the gauge.
* `Maths.MaxAffineTransport.CriticalAffineResidualAtMost`: a raw residual bound imposed
  only on the gauge-critical affine rows.
* `Maths.MaxAffineTransport.gaugeCriticalCycleRatio`: the ratio `T_C / S_C` of
  normalized shift to reciprocal-gauge mass on a critical cycle. On the empty cycle this is Lean's
  totalized `0 / 0 = 0`; the criteria below impose positive cycle length wherever it matters.

## Main results

* `Maths.MaxAffineTransport.defect_gaugeConjugate`: **gauge conjugation** - dividing a
  candidate by the gauge carries the raw affine residual of a critical edge, less the level, to
  the additive defect of the rescaled critical graph over the gauge at the target.  Every
  identification below of critical affine inequalities with additive ones is this one identity
  read at some level.
* `MaxAffineTransport.worstResidualAtMost_iff_criticalAffineResidualAtMost_of_nonexpansiveGauge`:
  at every raw residual threshold, a nonexpansive gauge deletes exactly the noncritical branch rows
  - floors and strictly contracting rows never bind.
* `MaxAffineTransport.worstResidualAtMost_iff_criticalAffineResidualAtMost_of_expansiveGauge`:
  the same reduction for an expansive gauge, which additionally requires every floor absent.
* `Maths.MaxAffineTransport.worstResidualAtMost_iff_cycleRatio_le_of_nonexpansiveGauge`,
  `MaxAffineTransport.worstResidualAtMost_iff_cycleRatio_le_of_expansiveGauge`: the
  **quantitative gauge theorems** - the exact raw worst-residual threshold is the supremum of
  `gaugeCriticalCycleRatio` over *nonempty* critical cycles, in both gauge regimes.
* `MaxAffineTransport.exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_nonexpansiveGauge`,
  `MaxAffineTransport.exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_expansiveGauge`:
  feasibility holds exactly when every critical cycle has nonpositive normalized shift sum. The
  expansive form assumes floors absent.
* `MaxAffineTransport.exists_isLaxSection_iff_gaugeCriticalHolonomy_prefixed_of_nonexpansiveGauge`,
  `MaxAffineTransport.exists_isLaxSection_iff_gaugeCriticalHolonomy_prefixed_of_expansiveGauge`:
  the same criteria restated as pre-fixedness of every normalized critical-cycle holonomy.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

section

variable [Fintype V] [DecidableEq V] [Fintype E]
variable {G : EdgeGraph V E} {label : E → Label}

omit [Fintype E] in
/-- Branch pairing with an arbitrary vertex direction. -/
theorem dotProduct_branchDelta_direction (direction : V → ℝ)
    (branch : Branch label) :
    dotProduct (branchDelta G label branch) direction =
      match branch.1 with
      | Sum.inl edge =>
          direction (G.target edge) -
            (label edge).slope * direction (G.source edge)
      | Sum.inr edge => direction (G.target edge) := by
  rcases branch with ⟨action, hgenuine⟩
  cases action with
  | inl edge =>
      rw [branchDelta, dotProduct_rowDelta_inl]
  | inr edge =>
      rcases (label edge).floor_cases with hfloor | ⟨floor, hfloor⟩
      · exact (hgenuine hfloor).elim
      · rw [branchDelta, dotProduct_rowDelta_inr_of_floor_coe hfloor]

/-- Edges on which a positive gauge makes the normalized slope exactly one. -/
abbrev GaugeCriticalEdge (label : E → Label) (gauge : V → ℝ) :=
  {edge : E //
    (label edge).slope * gauge (G.source edge) = gauge (G.target edge)}

/-- Gauge-critical edge subgraph. -/
abbrev gaugeCriticalGraph (label : E → Label) (gauge : V → ℝ) :
    EdgeGraph V (GaugeCriticalEdge (G := G) label gauge) where
  source edge := G.source edge.1
  target edge := G.target edge.1

/-- Shift after rescaling the target coordinate by the gauge. -/
def gaugeCriticalShift (label : E → Label) (gauge : V → ℝ)
    (edge : GaugeCriticalEdge (G := G) label gauge) : ℝ :=
  (label edge.1).shift / gauge (G.target edge.1)

/-- A bound on the additive residuals of the gauge-critical graph. -/
def GaugeCriticalResidualAtMost (label : E → Label) (gauge : V → ℝ)
    (level : ℝ) : Prop :=
  AdditiveTransport.WorstDirectedResidualAtMost
    (gaugeCriticalGraph (G := G) label gauge)
    (gaugeCriticalShift label gauge) level

/-- A target-gauge-normalized residual bound on the critical affine rows. -/
def CriticalAffineGaugeResidualAtMost (label : E → Label)
    (gauge : V → ℝ) (level : ℝ) : Prop :=
  ∃ potential : V → ℝ, ∀ edge : E,
    (label edge).slope * gauge (G.source edge) = gauge (G.target edge) →
      ((label edge).shift +
          (label edge).slope * potential (G.source edge) -
        potential (G.target edge)) / gauge (G.target edge) ≤ level

/-- A raw residual bound restricted to gauge-critical affine rows. -/
def CriticalAffineResidualAtMost (label : E → Label)
    (gauge : V → ℝ) (level : ℝ) : Prop :=
  ∃ potential : V → ℝ, ∀ edge : E,
    (label edge).slope * gauge (G.source edge) = gauge (G.target edge) →
      (label edge).shift +
          (label edge).slope * potential (G.source edge) -
        potential (G.target edge) ≤ level

/-- Reciprocal target-gauge mass of a critical edge. -/
def gaugeCriticalMass (gauge : V → ℝ)
    (edge : GaugeCriticalEdge (G := G) label gauge) : ℝ :=
  1 / gauge (G.target edge.1)

/-- Raw critical residuals become additive weights after gauge rescaling and
subtracting the candidate level. -/
def gaugeCriticalRelaxedShift (label : E → Label) (gauge : V → ℝ)
    (level : ℝ) (edge : GaugeCriticalEdge (G := G) label gauge) : ℝ :=
  ((label edge.1).shift - level) / gauge (G.target edge.1)

/-- Ratio of total gauge-normalized shift to total reciprocal-gauge mass on a
critical cycle.  The empty cycle uses Lean's totalized convention `0 / 0 = 0`;
criterion theorems impose positive cycle length where division matters. -/
def gaugeCriticalCycleRatio (label : E → Label) (gauge : V → ℝ)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base) : ℝ :=
  MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle /
    MaxPlusPotential.walkWeight (gaugeCriticalMass gauge) cycle

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- Relaxing by nothing is the plain gauge-normalized shift. -/
@[simp] theorem gaugeCriticalRelaxedShift_zero (label : E → Label) (gauge : V → ℝ) :
    gaugeCriticalRelaxedShift (G := G) label gauge 0 = gaugeCriticalShift label gauge := by
  funext edge
  simp [gaugeCriticalRelaxedShift, gaugeCriticalShift]

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- Dividing by a positive gauge and multiplying by it again is the identity. -/
theorem gaugeConjugate_mul_div (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (scaled : V → ℝ) :
    (fun vertex => gauge vertex * scaled vertex / gauge vertex) = scaled := by
  funext vertex
  exact mul_div_cancel_left₀ _ (hgauge vertex).ne'

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- **Gauge conjugation.**  Dividing a candidate by a positive gauge turns the raw affine
residual of a gauge-critical edge, less the level, into the additive defect of the rescaled
critical graph, divided by the gauge at the target.  On a critical edge the slope is the ratio
of the gauge across the edge, which is exactly what makes the source term rescale correctly.
Every identification of critical affine inequalities with additive ones in this file is this
identity read at some level. -/
theorem defect_gaugeConjugate (label : E → Label) (gauge : V → ℝ)
    (hgauge : ∀ vertex, 0 < gauge vertex) (level : ℝ) (potential : V → ℝ)
    (edge : GaugeCriticalEdge (G := G) label gauge) :
    MaxPlusPotential.defect (gaugeCriticalGraph (G := G) label gauge)
        (gaugeCriticalRelaxedShift label gauge level)
        (fun vertex => potential vertex / gauge vertex) edge =
      ((label edge.1).shift + (label edge.1).slope * potential (G.source edge.1) -
        potential (G.target edge.1) - level) / gauge (G.target edge.1) := by
  have hsource : gauge (G.source edge.1) ≠ 0 := (hgauge (G.source edge.1)).ne'
  have htarget : gauge (G.target edge.1) ≠ 0 := (hgauge (G.target edge.1)).ne'
  have hslope : (label edge.1).slope =
      gauge (G.target edge.1) / gauge (G.source edge.1) :=
    ((div_eq_iff hsource).2 edge.2.symm).symm
  simp only [MaxPlusPotential.defect, gaugeCriticalRelaxedShift]
  rw [hslope]
  field_simp
  ring

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- Rescaling vertex coordinates identifies critical affine residuals with
ordinary additive residuals on the gauge-critical graph. -/
theorem criticalAffineGaugeResidualAtMost_iff_gaugeCriticalResidualAtMost
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineGaugeResidualAtMost (G := G) label gauge level ↔
      GaugeCriticalResidualAtMost (G := G) label gauge level := by
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨fun vertex => potential vertex / gauge vertex, fun edge => ?_⟩
    have hkey := defect_gaugeConjugate (G := G) label gauge hgauge 0 potential edge
    rw [gaugeCriticalRelaxedShift_zero, sub_zero] at hkey
    rw [hkey]
    exact hpotential edge.1 edge.2
  · rintro ⟨scaled, hscaled⟩
    refine ⟨fun vertex => gauge vertex * scaled vertex, fun edge hcritical => ?_⟩
    have hkey := defect_gaugeConjugate (G := G) label gauge hgauge 0
      (fun vertex => gauge vertex * scaled vertex) ⟨edge, hcritical⟩
    rw [gaugeConjugate_mul_div gauge hgauge, gaugeCriticalRelaxedShift_zero,
      sub_zero] at hkey
    rw [← hkey]
    exact hscaled ⟨edge, hcritical⟩

omit [Fintype V] [DecidableEq V] in
/-- **Quantitative gauge-critical cycle-mean theorem.**  A normalized
critical affine residual threshold is attainable exactly when every critical
closed walk has mean shift at most that threshold. -/
theorem criticalAffineGaugeResidualAtMost_iff_closedWalk_mean_le
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineGaugeResidualAtMost (G := G) label gauge level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤
          cycle.length * level := by
  rw [criticalAffineGaugeResidualAtMost_iff_gaugeCriticalResidualAtMost
    gauge hgauge]
  exact AdditiveTransport.worstDirectedResidualAtMost_iff_closedWalk_le
    (gaugeCriticalGraph (G := G) label gauge)
    (gaugeCriticalShift label gauge) level

omit [Fintype V] [DecidableEq V] in
/-- The quantitative gauge-critical criterion can be restricted to simple
critical cycles. -/
theorem criticalAffineGaugeResidualAtMost_iff_simpleCycle_mean_le
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineGaugeResidualAtMost (G := G) label gauge level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        AdditiveTransport.IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤
            cycle.length * level := by
  rw [criticalAffineGaugeResidualAtMost_iff_closedWalk_mean_le gauge hgauge,
    AdditiveTransport.forall_closedWalk_mean_le_iff_simpleCycle]

omit [Fintype V] [DecidableEq V] [Fintype E] in
private theorem criticalAffineResidualAtMost_iff_isPotential
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineResidualAtMost (G := G) label gauge level ↔
      ∃ scaled : V → ℝ,
        MaxPlusPotential.IsPotential
          (gaugeCriticalGraph (G := G) label gauge)
          (gaugeCriticalRelaxedShift label gauge level) scaled := by
  simp only [MaxPlusPotential.isPotential_iff_forall_defect_nonpos]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨fun vertex => potential vertex / gauge vertex, fun edge => ?_⟩
    rw [defect_gaugeConjugate (G := G) label gauge hgauge level potential edge,
      div_le_iff₀ (hgauge (G.target edge.1)), zero_mul, sub_nonpos]
    exact hpotential edge.1 edge.2
  · rintro ⟨scaled, hscaled⟩
    refine ⟨fun vertex => gauge vertex * scaled vertex, fun edge hcritical => ?_⟩
    have hkey := hscaled ⟨edge, hcritical⟩
    rw [← gaugeConjugate_mul_div gauge hgauge scaled,
      defect_gaugeConjugate (G := G) label gauge hgauge level _ ⟨edge, hcritical⟩,
      div_le_iff₀ (hgauge (G.target edge)), zero_mul, sub_nonpos] at hkey
    exact hkey

omit [Fintype V] [DecidableEq V] [Fintype E] in
private theorem walkWeight_gaugeCriticalRelaxedShift
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) {start finish : V}
    (walk : (gaugeCriticalGraph (G := G) label gauge).Walk start finish) :
    MaxPlusPotential.walkWeight
        (gaugeCriticalRelaxedShift label gauge level) walk =
      MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) walk -
        level * MaxPlusPotential.walkWeight (gaugeCriticalMass gauge) walk := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      rw [MaxPlusPotential.walkWeight_concat,
        MaxPlusPotential.walkWeight_concat,
        MaxPlusPotential.walkWeight_concat, ih]
      dsimp [gaugeCriticalRelaxedShift, gaugeCriticalShift,
        gaugeCriticalMass]
      have htarget : gauge (G.target edge.1) ≠ 0 :=
        (hgauge (G.target edge.1)).ne'
      field_simp [htarget]
      all_goals ring

omit [Fintype V] [DecidableEq V] in
/-- **Raw gauge-critical cycle formula.**  A raw affine residual threshold is
attainable exactly when every critical cycle satisfies `T_C ≤ level * S_C`,
where `T_C` is normalized total shift and `S_C` is reciprocal-gauge mass. -/
theorem criticalAffineResidualAtMost_iff_closedWalk_ratio_mul_le
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineResidualAtMost (G := G) label gauge level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤
          level * MaxPlusPotential.walkWeight
            (gaugeCriticalMass gauge) cycle := by
  rw [criticalAffineResidualAtMost_iff_isPotential gauge hgauge,
    MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos]
  apply forall_congr'
  intro base
  apply forall_congr'
  intro cycle
  rw [walkWeight_gaugeCriticalRelaxedShift gauge hgauge]
  constructor <;> intro h <;> linarith

omit [Fintype V] [DecidableEq V] [Fintype E] in
private theorem sum_pos_of_mem_pos {values : List ℝ} (hne : values ≠ [])
    (hpos : ∀ value ∈ values, 0 < value) :
    0 < values.sum := by
  induction values with
  | nil => exact (hne rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil => simpa using hpos first (List.mem_cons_self ..)
      | cons next tail =>
          have hfirst := hpos first (List.mem_cons_self ..)
          have hrest (value : ℝ) (hvalue : value ∈ next :: tail) : 0 < value :=
            hpos value (List.mem_cons_of_mem _ hvalue)
          have hsum := ih (by simp) hrest
          change 0 < first + (next :: tail).sum
          exact add_pos hfirst hsum

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- Reciprocal-gauge mass is positive on every nonempty critical cycle. -/
theorem gaugeCriticalCycleMass_pos
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    {base : V}
    (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base)
    (hne : 0 < cycle.length) :
    0 < MaxPlusPotential.walkWeight (gaugeCriticalMass gauge) cycle := by
  apply sum_pos_of_mem_pos
  · intro hempty
    have hedges : cycle.edges = [] := by simpa using hempty
    have : cycle.edges.length = 0 := by rw [hedges]; rfl
    rw [cycle.edges_length] at this
    omega
  · intro value hvalue
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hvalue
    exact one_div_pos.mpr (hgauge (G.target edge.1))

omit [Fintype V] [DecidableEq V] in
/-- Quotient form `T_C / S_C` of the raw gauge-critical cycle theorem. -/
theorem criticalAffineResidualAtMost_iff_cycleRatio_le
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineResidualAtMost (G := G) label gauge level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        0 < cycle.length →
          gaugeCriticalCycleRatio label gauge cycle ≤ level := by
  rw [criticalAffineResidualAtMost_iff_closedWalk_ratio_mul_le gauge hgauge]
  constructor
  · intro hall base cycle hne
    exact (div_le_iff₀ (gaugeCriticalCycleMass_pos gauge hgauge cycle hne)).2
      (hall base cycle)
  · intro hratio base cycle
    by_cases hne : 0 < cycle.length
    · exact (div_le_iff₀ (gaugeCriticalCycleMass_pos gauge hgauge cycle hne)).1
        (hratio base cycle hne)
    · have hzero : cycle.length = 0 := Nat.eq_zero_of_not_pos hne
      have hedges : cycle.edges = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hzero
      simp [MaxPlusPotential.walkWeight, hedges]

omit [Fintype E] in
private theorem worstResidualAtMost_iff_shiftedRows (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      ∃ potential : V → ℝ, ∀ branch : Branch label,
        branchBase label branch - level ≤
          dotProduct (branchDelta G label branch) potential := by
  apply exists_congr
  intro potential
  apply forall_congr'
  intro branch
  simp only [branchResidual]
  constructor <;> intro h <;> linarith

/-- Both gauge regimes reduce to the gauge-critical affine rows through one recession argument.
All that is asked of the direction is that every branch recede along it, that it annihilate an
affine row exactly at the gauge-critical edges, and that it never annihilate a genuine floor row.
The nonexpansive regime supplies the gauge itself and the expansive one its negative. -/
private theorem worstResidualAtMost_iff_criticalAffineResidualAtMost_of_direction
    (gauge direction : V → ℝ)
    (hrecession : ∀ branch : Branch label,
      0 ≤ dotProduct (branchDelta G label branch) direction)
    (hcritical : ∀ edge : E,
      dotProduct (branchDelta G label ⟨Sum.inl edge, trivial⟩) direction = 0 ↔
        (label edge).slope * gauge (G.source edge) = gauge (G.target edge))
    (hfloor : ∀ (edge : E) (hgenuine : IsGenuineBranch label (Sum.inr edge)),
      dotProduct (branchDelta G label ⟨Sum.inr edge, hgenuine⟩) direction ≠ 0)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      CriticalAffineResidualAtMost (G := G) label gauge level := by
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
      (branchDelta G label)
      (fun branch => branchBase label branch - level) direction hrecession
  rw [worstResidualAtMost_iff_shiftedRows, hreduction]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hedge => ?_⟩
    have hrow := hpotential ⟨Sum.inl edge, trivial⟩ ((hcritical edge).mpr hedge)
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun branch hcrit => ?_⟩
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        have hrow := hpotential edge ((hcritical edge).mp hcrit)
        rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
        linarith
    | inr edge => exact (hfloor edge hgenuine hcrit).elim

/-- At every raw residual threshold, a nonexpansive gauge removes exactly the
noncritical branch rows. -/
theorem worstResidualAtMost_iff_criticalAffineResidualAtMost_of_nonexpansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      CriticalAffineResidualAtMost (G := G) label gauge level := by
  refine worstResidualAtMost_iff_criticalAffineResidualAtMost_of_direction gauge gauge
    (fun branch => ?_) (fun edge => ?_) (fun edge _ => ?_) level
  · rw [dotProduct_branchDelta_direction]
    cases branch.1 with
    | inl edge => exact sub_nonneg.mpr (hgauge.2 edge)
    | inr edge => exact (hgauge.1 _).le
  · rw [dotProduct_branchDelta_direction]
    constructor <;> intro h <;> linarith
  · rw [dotProduct_branchDelta_direction]
    exact ne_of_gt (hgauge.1 _)

/-- At every raw residual threshold, an expansive gauge with absent floors
removes exactly the noncritical affine rows. -/
theorem worstResidualAtMost_iff_criticalAffineResidualAtMost_of_expansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge, (label edge).floor = ⊥)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      CriticalAffineResidualAtMost (G := G) label gauge level := by
  refine worstResidualAtMost_iff_criticalAffineResidualAtMost_of_direction gauge
    (fun vertex => -gauge vertex) (fun branch => ?_) (fun edge => ?_)
    (fun edge hgenuine => absurd (hfloor edge) hgenuine) level
  · rw [dotProduct_branchDelta_direction]
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge => nlinarith [hgauge.2 edge]
    | inr edge => exact (hgenuine (hfloor edge)).elim
  · rw [dotProduct_branchDelta_direction]
    constructor <;> intro h <;> linarith

/-- **Quantitative nonexpansive gauge theorem.**  The exact raw worst-residual
threshold is the supremum of `T_C / S_C` over nonempty critical cycles. -/
theorem worstResidualAtMost_iff_cycleRatio_le_of_nonexpansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        0 < cycle.length →
          gaugeCriticalCycleRatio label gauge cycle ≤ level := by
  rw [worstResidualAtMost_iff_criticalAffineResidualAtMost_of_nonexpansiveGauge
    gauge hgauge]
  exact criticalAffineResidualAtMost_iff_cycleRatio_le gauge hgauge.1 level

/-- **Quantitative expansive gauge theorem.**  With absent floors, the exact
raw worst-residual threshold is the same critical-cycle ratio supremum. -/
theorem worstResidualAtMost_iff_cycleRatio_le_of_expansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge, (label edge).floor = ⊥)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        0 < cycle.length →
          gaugeCriticalCycleRatio label gauge cycle ≤ level := by
  rw [worstResidualAtMost_iff_criticalAffineResidualAtMost_of_expansiveGauge
    gauge hgauge hfloor]
  exact criticalAffineResidualAtMost_iff_cycleRatio_le gauge hgauge.1 level

omit [Fintype V] [DecidableEq V] in
/-- Critical affine inequalities are equivalent to an additive potential on
the rescaled critical graph. -/
theorem exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex) :
    (∃ potential : V → ℝ, ∀ edge : E,
      (label edge).slope * gauge (G.source edge) = gauge (G.target edge) →
        (label edge).shift +
            (label edge).slope * potential (G.source edge) ≤
          potential (G.target edge)) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤ 0 := by
  have hzero := criticalAffineResidualAtMost_iff_isPotential
    (G := G) (label := label) gauge hgauge 0
  rw [gaugeCriticalRelaxedShift_zero] at hzero
  rw [← MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos, ← hzero]
  exact exists_congr fun _ =>
    forall_congr' fun _ => imp_congr_right fun _ => sub_nonpos.symm

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- Nonpositive critical-cycle weight is equivalent to every normalized
critical holonomy having a pre-fixed point. -/
theorem forall_gaugeCriticalCycles_nonpos_iff_holonomy_prefixed
    (gauge : V → ℝ) :
    (∀ (base : V)
      (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
      MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤ 0) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        ∃ point : ℝ,
          holonomyApply
              (fun edge => translationLabel
                (gaugeCriticalShift label gauge edge)) cycle point ≤ point := by
  simp [holonomyApply_translationLabel]

/-- The feasibility companion of the residual reduction above, asking the same three things of
the recession direction: that every branch recede along it, that it annihilate an affine row
exactly at the gauge-critical edges, and that it never annihilate a genuine floor row. -/
private theorem exists_isLaxSection_iff_exists_criticalAffinePotential_of_direction
    (gauge direction : V → ℝ)
    (hrecession : ∀ branch : Branch label,
      0 ≤ dotProduct (branchDelta G label branch) direction)
    (hcritical : ∀ edge : E,
      dotProduct (branchDelta G label ⟨Sum.inl edge, trivial⟩) direction = 0 ↔
        (label edge).slope * gauge (G.source edge) = gauge (G.target edge))
    (hfloor : ∀ (edge : E) (hgenuine : IsGenuineBranch label (Sum.inr edge)),
      dotProduct (branchDelta G label ⟨Sum.inr edge, hgenuine⟩) direction ≠ 0) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      (∃ potential : V → ℝ, ∀ edge : E,
        (label edge).slope * gauge (G.source edge) = gauge (G.target edge) →
          (label edge).shift + (label edge).slope * potential (G.source edge) ≤
            potential (G.target edge)) := by
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) direction hrecession
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge _ => ?_⟩
    have hrow := (isLaxSection_iff_forall_branch G label potential).mp
      hpotential ⟨Sum.inl edge, trivial⟩
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    have hcriticalRows (branch : Branch label)
        (hcrit : FiniteInequality.Recession.IsCritical
          (branchDelta G label) direction branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          have hrow := hcriticalPotential edge ((hcritical edge).mp hcrit)
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          linarith
      | inr edge => exact (hfloor edge hgenuine hcrit).elim
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

/-- **Nonexpansive gauge feasibility.**  Floors and strictly contracting rows
cannot obstruct existence; the exact obstruction is a positive-shift cycle in
the gauge-critical subgraph. -/
theorem exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_nonexpansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤ 0 := by
  rw [← exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos gauge hgauge.1]
  refine exists_isLaxSection_iff_exists_criticalAffinePotential_of_direction gauge gauge
    (fun branch => ?_) (fun edge => ?_) (fun edge _ => ?_)
  · rw [dotProduct_branchDelta_direction]
    cases branch.1 with
    | inl edge => exact sub_nonneg.mpr (hgauge.2 edge)
    | inr edge => exact (hgauge.1 _).le
  · rw [dotProduct_branchDelta_direction]
    constructor <;> intro h <;> linarith
  · rw [dotProduct_branchDelta_direction]
    exact ne_of_gt (hgauge.1 _)

/-- **Expansive gauge feasibility.**  With floors absent, the negative gauge
is a recession direction and produces the same critical-cycle criterion. -/
theorem exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_expansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        MaxPlusPotential.walkWeight (gaugeCriticalShift label gauge) cycle ≤ 0 := by
  rw [← exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos gauge hgauge.1]
  refine exists_isLaxSection_iff_exists_criticalAffinePotential_of_direction gauge
    (fun vertex => -gauge vertex) (fun branch => ?_) (fun edge => ?_)
    (fun edge hgenuine => absurd (hfloor edge) hgenuine)
  · rw [dotProduct_branchDelta_direction]
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge => nlinarith [hgauge.2 edge]
    | inr edge => exact (hgenuine (hfloor edge)).elim
  · rw [dotProduct_branchDelta_direction]
    constructor <;> intro h <;> linarith

/-- Nonexpansive gauge feasibility is equivalently pre-fixedness of every
normalized critical-cycle holonomy. -/
theorem exists_isLaxSection_iff_gaugeCriticalHolonomy_prefixed_of_nonexpansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        ∃ point : ℝ,
          holonomyApply
              (fun edge => translationLabel
                (gaugeCriticalShift label gauge edge)) cycle point ≤ point := by
  rw [exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_nonexpansiveGauge
    gauge hgauge,
    forall_gaugeCriticalCycles_nonpos_iff_holonomy_prefixed]

/-- Expansive gauge feasibility with absent floors is equivalently
pre-fixedness of every normalized critical-cycle holonomy. -/
theorem exists_isLaxSection_iff_gaugeCriticalHolonomy_prefixed_of_expansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsExpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (hfloor : ∀ edge, (label edge).floor = ⊥) :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ (base : V)
        (cycle : (gaugeCriticalGraph (G := G) label gauge).Walk base base),
        ∃ point : ℝ,
          holonomyApply
              (fun edge => translationLabel
                (gaugeCriticalShift label gauge edge)) cycle point ≤ point := by
  rw [exists_isLaxSection_iff_gaugeCriticalCycles_nonpos_of_expansiveGauge
    gauge hgauge hfloor,
    forall_gaugeCriticalCycles_nonpos_iff_holonomy_prefixed]

end

end MaxAffineTransport

end

end Maths
