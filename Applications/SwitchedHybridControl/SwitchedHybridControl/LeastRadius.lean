/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import SwitchedHybridControl.WeightedError
public import Maths.Multitubes.MaxAffine.RadiusFixedPoint

/-!
# Least invariant error radii

A contraction gauge selects a canonical invariant radius above any prescribed lower data.  The
selected radius is pointwise least, so an upper budget is feasible exactly when it contains this
radius.  This file expresses the reusable max-affine fixed-point construction in the vocabulary
of affine error comparisons.

## Main definitions

* `SwitchedHybridControl.ErrorComparison.leastErrorRadius`: the least invariant error radius
  above prescribed lower data.

## Main results

* `SwitchedHybridControl.ErrorComparison.leastErrorRadius_isRadiusFamily`: the selected radius
  is invariant under every comparison edge.
* `SwitchedHybridControl.ErrorComparison.leastErrorRadius_le`: every feasible radius above the
  lower data dominates the selected radius.
* `SwitchedHybridControl.ErrorComparison.exists_radius_bounded_iff_leastErrorRadius_le`: an
  upper budget admits a radius exactly when it contains the selected radius.
* `SwitchedHybridControl.weightedRadius_eq_leastErrorRadius`: the displayed radii of the weighted
  example are the radii selected by the general construction.

## Tags

switched systems, hybrid systems, invariant radius, Bellman fixed point, synthesis
-/

@[expose] public section

namespace SwitchedHybridControl

open Maths.MaxAffineTransport

universe uV uE uC uA

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}
variable {Concrete : V → Type uC} {Approximate : V → Type uA}
variable {concrete : Maths.Transport G Concrete} {approximate : Maths.Transport G Approximate}

namespace ErrorComparison

section Finite

variable [Fintype E] [Fintype V] [DecidableEq V]

/-- The least invariant error radius above `lower`, obtained in contraction-gauge coordinates. -/
noncomputable def leastErrorRadius (comparison : ErrorComparison concrete approximate)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge) : V → ℝ :=
  leastRadius G comparison.bias comparison.gain lower gauge hrate hlt
    comparison.gain_nonneg hgauge

/-- The selected radius lies above the prescribed lower data. -/
theorem lower_le_leastErrorRadius (comparison : ErrorComparison concrete approximate)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge) :
    lower ≤ comparison.leastErrorRadius lower gauge hrate hlt hgauge :=
  (leastRadius_feasible G comparison.bias comparison.gain lower gauge hrate hlt
    comparison.gain_nonneg hgauge).1

/-- The selected radius is invariant under every affine comparison edge. -/
theorem leastErrorRadius_isRadiusFamily (comparison : ErrorComparison concrete approximate)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge) :
    IsRadiusFamily comparison (comparison.leastErrorRadius lower gauge hrate hlt hgauge) :=
  (leastRadius_feasible G comparison.bias comparison.gain lower gauge hrate hlt
    comparison.gain_nonneg hgauge).2

/-- Every invariant radius above the lower data dominates the selected radius. -/
theorem leastErrorRadius_le (comparison : ErrorComparison concrete approximate)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge)
    {radius : V → ℝ} (hlower : lower ≤ radius) (hradius : IsRadiusFamily comparison radius) :
    comparison.leastErrorRadius lower gauge hrate hlt hgauge ≤ radius :=
  leastRadius_le G comparison.bias comparison.gain lower gauge hrate hlt
    comparison.gain_nonneg hgauge ⟨hlower, hradius⟩

/-- An upper budget admits an invariant radius above `lower` exactly when it contains the least
such radius. -/
theorem exists_radius_bounded_iff_leastErrorRadius_le
    (comparison : ErrorComparison concrete approximate) (lower gauge upper : V → ℝ)
    {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge) :
    (∃ radius : V → ℝ,
      lower ≤ radius ∧ IsRadiusFamily comparison radius ∧ radius ≤ upper) ↔
      comparison.leastErrorRadius lower gauge hrate hlt hgauge ≤ upper := by
  rw [leastErrorRadius]
  constructor
  · rintro ⟨radius, hlower, hradius, hupper⟩
    exact (leastRadius_le G comparison.bias comparison.gain lower gauge hrate hlt
      comparison.gain_nonneg hgauge ⟨hlower, hradius⟩).trans hupper
  · intro hupper
    refine ⟨leastRadius G comparison.bias comparison.gain lower gauge hrate hlt
      comparison.gain_nonneg hgauge, ?_, ?_, hupper⟩
    · exact (leastRadius_feasible G comparison.bias comparison.gain lower gauge hrate hlt
        comparison.gain_nonneg hgauge).1
    · exact (leastRadius_feasible G comparison.bias comparison.gain lower gauge hrate hlt
        comparison.gain_nonneg hgauge).2

end Finite

end ErrorComparison

/-- The explicit weighted-example radii coincide with the general least-radius construction. -/
theorem weightedRadius_eq_leastErrorRadius :
    weightedRadius = weightedExecutionComparison.leastErrorRadius
      (fun _ => 0) expandingGauge (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) expandingGain_contractive := by
  apply le_antisymm
  · apply Pi.le_def.mpr
    exact weightedRadius_le_of_isRadiusFamily
      (weightedExecutionComparison.leastErrorRadius_isRadiusFamily
        (fun _ => 0) expandingGauge (by norm_num) (by norm_num) expandingGain_contractive)
  · exact weightedExecutionComparison.leastErrorRadius_le
      (fun _ => 0) expandingGauge (by norm_num) (by norm_num) expandingGain_contractive
      (by intro vertex; cases vertex <;> norm_num [weightedRadius])
      weightedRadius_isRadiusFamily

end SwitchedHybridControl
