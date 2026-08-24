/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Cycles
public import DirectedTransport.MaxAffine.Slopes

import DirectedTransport.MaxAffine.Additive

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

* `DirectedTransport.MaxAffineTransport.GaugeCriticalEdge`,
  `DirectedTransport.MaxAffineTransport.gaugeCriticalGraph`: the edges on which a positive gauge
  makes the normalized slope exactly one, and the subgraph they span.
* `DirectedTransport.MaxAffineTransport.gaugeCriticalShift`: the shift of a critical edge after
  rescaling the target coordinate by the gauge.
* `DirectedTransport.MaxAffineTransport.CriticalAffineResidualAtMost`: a raw residual bound imposed
  only on the gauge-critical affine rows.
* `DirectedTransport.MaxAffineTransport.gaugeCriticalCycleRatio`: the ratio `T_C / S_C` of
  normalized shift to reciprocal-gauge mass on a critical cycle. On the empty cycle this is Lean's
  totalized `0 / 0 = 0`; the criteria below impose positive cycle length wherever it matters.

## Main results

* `MaxAffineTransport.worstResidualAtMost_iff_criticalAffineResidualAtMost_of_nonexpansiveGauge`:
  at every raw residual threshold, a nonexpansive gauge deletes exactly the noncritical branch rows
  - floors and strictly contracting rows never bind.
* `MaxAffineTransport.worstResidualAtMost_iff_criticalAffineResidualAtMost_of_expansiveGauge`:
  the same reduction for an expansive gauge, which additionally requires every floor absent.
* `DirectedTransport.MaxAffineTransport.worstResidualAtMost_iff_cycleRatio_le_of_nonexpansiveGauge`,
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

namespace DirectedTransport

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
/-- Rescaling vertex coordinates identifies critical affine residuals with
ordinary additive residuals on the gauge-critical graph. -/
theorem criticalAffineGaugeResidualAtMost_iff_gaugeCriticalResidualAtMost
    (gauge : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex)
    (level : ℝ) :
    CriticalAffineGaugeResidualAtMost (G := G) label gauge level ↔
      GaugeCriticalResidualAtMost (G := G) label gauge level := by
  constructor
  · rintro ⟨potential, hpotential⟩
    let scaled : V → ℝ := fun vertex => potential vertex / gauge vertex
    refine ⟨scaled, fun edge => ?_⟩
    have hrow := hpotential edge.1 edge.2
    have hsource : gauge (G.source edge.1) ≠ 0 :=
      (hgauge (G.source edge.1)).ne'
    have htarget : gauge (G.target edge.1) ≠ 0 :=
      (hgauge (G.target edge.1)).ne'
    have hslope : (label edge.1).slope =
        gauge (G.target edge.1) / gauge (G.source edge.1) :=
      ((div_eq_iff hsource).2 edge.2.symm).symm
    have hid :
        MaxPlusPotential.defect
            (gaugeCriticalGraph (G := G) label gauge)
            (gaugeCriticalShift label gauge) scaled edge =
          ((label edge.1).shift +
              (label edge.1).slope * potential (G.source edge.1) -
            potential (G.target edge.1)) / gauge (G.target edge.1) := by
      simp only [MaxPlusPotential.defect, gaugeCriticalShift, scaled]
      rw [hslope]
      (field_simp; ring)
    rw [hid]
    exact hrow
  · rintro ⟨scaled, hscaled⟩
    let potential : V → ℝ := fun vertex => gauge vertex * scaled vertex
    refine ⟨potential, fun edge hcritical => ?_⟩
    let critical : GaugeCriticalEdge (G := G) label gauge :=
      ⟨edge, hcritical⟩
    have hrow := hscaled critical
    have hsource : gauge (G.source edge) ≠ 0 :=
      (hgauge (G.source edge)).ne'
    have htarget : gauge (G.target edge) ≠ 0 :=
      (hgauge (G.target edge)).ne'
    have hslope : (label edge).slope =
        gauge (G.target edge) / gauge (G.source edge) :=
      ((div_eq_iff hsource).2 hcritical.symm).symm
    have hid :
        ((label edge).shift +
              (label edge).slope * potential (G.source edge) -
            potential (G.target edge)) / gauge (G.target edge) =
          MaxPlusPotential.defect
            (gaugeCriticalGraph (G := G) label gauge)
            (gaugeCriticalShift label gauge) scaled critical := by
      dsimp [MaxPlusPotential.defect, gaugeCriticalShift, potential, critical]
      rw [hslope]
      (field_simp; ring)
    rw [hid]
    exact hrow

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
  constructor
  · rintro ⟨potential, hpotential⟩
    let scaled : V → ℝ := fun vertex => potential vertex / gauge vertex
    refine ⟨scaled, fun edge => ?_⟩
    have hrow := hpotential edge.1 edge.2
    have hsource : gauge (G.source edge.1) ≠ 0 :=
      (hgauge (G.source edge.1)).ne'
    have htarget : gauge (G.target edge.1) ≠ 0 :=
      (hgauge (G.target edge.1)).ne'
    have hslope : (label edge.1).slope =
        gauge (G.target edge.1) / gauge (G.source edge.1) :=
      ((div_eq_iff hsource).2 edge.2.symm).symm
    have hleft : gauge (G.target edge.1) *
          (scaled (G.source edge.1) +
            gaugeCriticalRelaxedShift label gauge level edge) =
        (label edge.1).slope * potential (G.source edge.1) +
          (label edge.1).shift - level := by
      dsimp [scaled, gaugeCriticalRelaxedShift]
      rw [hslope]
      field_simp [hsource, htarget]
      all_goals ring
    have hright : gauge (G.target edge.1) * scaled (G.target edge.1) =
        potential (G.target edge.1) := by
      dsimp [scaled]
      field_simp [htarget]
    apply le_of_mul_le_mul_left _ (hgauge (G.target edge.1))
    change gauge (G.target edge.1) *
        (scaled (G.source edge.1) +
          gaugeCriticalRelaxedShift label gauge level edge) ≤
      gauge (G.target edge.1) * scaled (G.target edge.1)
    rw [hleft, hright]
    linarith
  · rintro ⟨scaled, hscaled⟩
    let potential : V → ℝ := fun vertex => gauge vertex * scaled vertex
    refine ⟨potential, fun edge hcritical => ?_⟩
    let critical : GaugeCriticalEdge (G := G) label gauge :=
      ⟨edge, hcritical⟩
    have hrow := hscaled critical
    have htarget : gauge (G.target edge) ≠ 0 :=
      (hgauge (G.target edge)).ne'
    have hscaledRow : gauge (G.target edge) * scaled (G.source edge) +
          (label edge).shift - level ≤
        gauge (G.target edge) * scaled (G.target edge) := by
      have hmul := mul_le_mul_of_nonneg_left hrow (hgauge (G.target edge)).le
      dsimp [gaugeCriticalRelaxedShift, critical] at hmul
      rw [mul_add, mul_div_cancel₀ _ htarget] at hmul
      linarith
    dsimp [potential]
    calc
      (label edge).shift +
            (label edge).slope * (gauge (G.source edge) * scaled (G.source edge)) -
          gauge (G.target edge) * scaled (G.target edge) =
        (gauge (G.target edge) * scaled (G.source edge) +
            (label edge).shift) -
          gauge (G.target edge) * scaled (G.target edge) := by
            rw [← mul_assoc, hcritical]
            ring
      _ ≤ level := by linarith

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

/-- At every raw residual threshold, a nonexpansive gauge removes exactly the
noncritical branch rows. -/
theorem worstResidualAtMost_iff_criticalAffineResidualAtMost_of_nonexpansiveGauge
    (gauge : V → ℝ)
    (hgauge : IsNonexpansiveGauge (G := G)
      (fun edge => (label edge).slope) gauge)
    (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      CriticalAffineResidualAtMost (G := G) label gauge level := by
  let direction : V → ℝ := gauge
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_direction]
    cases branch.1 with
    | inl edge => exact sub_nonneg.mpr (hgauge.2 edge)
    | inr edge => exact (hgauge.1 _).le
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
      (branchDelta G label)
      (fun branch => branchBase label branch - level) direction hrecession
  rw [worstResidualAtMost_iff_shiftedRows]
  rw [hreduction]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hcritical => ?_⟩
    let branch : Branch label := ⟨Sum.inl edge, trivial⟩
    have hbranchCritical : FiniteInequality.Recession.IsCritical
        (branchDelta G label) direction branch := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_direction]
      dsimp [direction, branch]
      linarith
    have hrow := hpotential branch hbranchCritical
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun branch hcritical => ?_⟩
    rw [FiniteInequality.Recession.IsCritical,
      dotProduct_branchDelta_direction] at hcritical
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        have hedge : (label edge).slope * gauge (G.source edge) =
            gauge (G.target edge) := by
          dsimp [direction] at hcritical
          linarith
        have hrow := hpotential edge hedge
        rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
        linarith
    | inr edge =>
        dsimp [direction] at hcritical
        exact (ne_of_gt (hgauge.1 _) hcritical).elim

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
  let direction : V → ℝ := fun vertex => -gauge vertex
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_direction]
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        dsimp [direction]
        nlinarith [hgauge.2 edge]
    | inr edge => exact (hgenuine (hfloor edge)).elim
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
      (branchDelta G label)
      (fun branch => branchBase label branch - level) direction hrecession
  rw [worstResidualAtMost_iff_shiftedRows]
  rw [hreduction]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hcritical => ?_⟩
    let branch : Branch label := ⟨Sum.inl edge, trivial⟩
    have hbranchCritical : FiniteInequality.Recession.IsCritical
        (branchDelta G label) direction branch := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_direction]
      dsimp [direction, branch]
      linarith
    have hrow := hpotential branch hbranchCritical
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun branch hcritical => ?_⟩
    rw [FiniteInequality.Recession.IsCritical,
      dotProduct_branchDelta_direction] at hcritical
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        have hedge : (label edge).slope * gauge (G.source edge) =
            gauge (G.target edge) := by
          dsimp [direction] at hcritical
          linarith
        have hrow := hpotential edge hedge
        rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
        linarith
    | inr edge => exact (hgenuine (hfloor edge)).elim

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
  rw [← MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos]
  constructor
  · rintro ⟨potential, hpotential⟩
    let scaled : V → ℝ := fun vertex => potential vertex / gauge vertex
    refine ⟨scaled, fun edge => ?_⟩
    have hrow := hpotential edge.1 edge.2
    have hsource : gauge (G.source edge.1) ≠ 0 :=
      (hgauge (G.source edge.1)).ne'
    have htarget : gauge (G.target edge.1) ≠ 0 :=
      (hgauge (G.target edge.1)).ne'
    have hratio : gauge (G.target edge.1) / gauge (G.source edge.1) =
        (label edge.1).slope :=
      (div_eq_iff hsource).mpr edge.2.symm
    have hleft : gauge (G.target edge.1) *
          (scaled (G.source edge.1) + gaugeCriticalShift label gauge edge) =
        (label edge.1).slope * potential (G.source edge.1) +
          (label edge.1).shift := by
      dsimp [scaled, gaugeCriticalShift]
      rw [mul_add, mul_div_cancel₀ _ htarget]
      calc
        gauge (G.target edge.1) *
              (potential (G.source edge.1) / gauge (G.source edge.1)) +
            (label edge.1).shift =
            (gauge (G.target edge.1) / gauge (G.source edge.1)) *
                potential (G.source edge.1) + (label edge.1).shift := by
          field_simp [hsource]
        _ = _ := by rw [hratio]
    have hright : gauge (G.target edge.1) *
          scaled (G.target edge.1) = potential (G.target edge.1) := by
      dsimp [scaled]
      field_simp [htarget]
    apply le_of_mul_le_mul_left _ (hgauge (G.target edge.1))
    change gauge (G.target edge.1) *
        (scaled (G.source edge.1) + gaugeCriticalShift label gauge edge) ≤
      gauge (G.target edge.1) * scaled (G.target edge.1)
    rw [hleft, hright]
    linarith
  · rintro ⟨scaled, hscaled⟩
    let potential : V → ℝ := fun vertex => gauge vertex * scaled vertex
    refine ⟨potential, fun edge hcritical => ?_⟩
    have hrow := hscaled
      (⟨edge, hcritical⟩ : GaugeCriticalEdge (G := G) label gauge)
    have htarget : gauge (G.target edge) ≠ 0 :=
      (hgauge (G.target edge)).ne'
    have hscaledRow : gauge (G.target edge) * scaled (G.source edge) +
          (label edge).shift ≤
        gauge (G.target edge) * scaled (G.target edge) := by
      have hmul := mul_le_mul_of_nonneg_left hrow (hgauge (G.target edge)).le
      dsimp [gaugeCriticalShift] at hmul
      rw [mul_add, mul_div_cancel₀ _ htarget] at hmul
      exact hmul
    dsimp [potential]
    calc
      (label edge).shift +
          (label edge).slope * (gauge (G.source edge) * scaled (G.source edge)) =
          gauge (G.target edge) * scaled (G.source edge) +
            (label edge).shift := by
        rw [← mul_assoc, hcritical]
        ring
      _ ≤ gauge (G.target edge) * scaled (G.target edge) := hscaledRow

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
  constructor
  · intro hnonpos base cycle
    refine ⟨0, ?_⟩
    rw [holonomyApply_translationLabel]
    simpa using hnonpos base cycle
  · intro hprefixed base cycle
    obtain ⟨point, hpoint⟩ := hprefixed base cycle
    rw [holonomyApply_translationLabel] at hpoint
    linarith

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
  let direction : V → ℝ := gauge
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_direction]
    cases branch.1 with
    | inl edge => exact sub_nonneg.mpr (hgauge.2 edge)
    | inr edge => exact (hgauge.1 _).le
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) direction hrecession
  rw [← exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos
    gauge hgauge.1]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hcritical => ?_⟩
    have hrow := (isLaxSection_iff_forall_branch G label potential).mp
      hpotential ⟨Sum.inl edge, trivial⟩
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    have hcriticalRows (branch : Branch label)
        (hcritical : FiniteInequality.Recession.IsCritical
          (branchDelta G label) direction branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_direction] at hcritical
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          have hedge : (label edge).slope * gauge (G.source edge) =
              gauge (G.target edge) := by linarith
          have hrow := hcriticalPotential edge hedge
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          linarith
      | inr edge =>
          have : gauge (G.target edge) = 0 := hcritical
          exact (ne_of_gt (hgauge.1 _) this).elim
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

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
  let direction : V → ℝ := fun vertex => -gauge vertex
  have hrecession (branch : Branch label) :
      0 ≤ dotProduct (branchDelta G label branch) direction := by
    rw [dotProduct_branchDelta_direction]
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        dsimp [direction]
        nlinarith [hgauge.2 edge]
    | inr edge => exact (hgenuine (hfloor edge)).elim
  have hreduction :=
    FiniteInequality.Recession.exists_potential_iff_exists_critical_potential
    (branchDelta G label) (branchBase label) direction hrecession
  rw [← exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos
    gauge hgauge.1]
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, fun edge hcritical => ?_⟩
    have hrow := (isLaxSection_iff_forall_branch G label potential).mp
      hpotential ⟨Sum.inl edge, trivial⟩
    rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl] at hrow
    linarith
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    have hcriticalRows (branch : Branch label)
        (hcritical : FiniteInequality.Recession.IsCritical
          (branchDelta G label) direction branch) :
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) criticalPotential := by
      rw [FiniteInequality.Recession.IsCritical,
        dotProduct_branchDelta_direction] at hcritical
      rcases branch with ⟨action, hgenuine⟩
      cases action with
      | inl edge =>
          dsimp [direction] at hcritical
          have hedge : (label edge).slope * gauge (G.source edge) =
              gauge (G.target edge) := by linarith
          have hrow := hcriticalPotential edge hedge
          rw [branchBase, branchDelta, rowBase, dotProduct_rowDelta_inl]
          linarith
      | inr edge => exact (hgenuine (hfloor edge)).elim
    obtain ⟨potential, hpotential⟩ := hreduction.mpr
      ⟨criticalPotential, hcriticalRows⟩
    exact ⟨potential,
      (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩

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

end DirectedTransport
