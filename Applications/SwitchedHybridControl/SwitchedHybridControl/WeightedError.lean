/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import SwitchedHybridControl.ErrorBounds
public import Maths.Multitubes.MaxAffine.ContractiveGauge

import Mathlib.Data.Fintype.Order

/-!
# Geometric error decay and disturbance margins

A positive gauge with a common normalized rate allows some transitions to amplify error.
Excess above any invariant radius has a geometric bound with walk length, and that bound decays
when the rate is below one.
A normalized bias increase of `delta` is absorbed by increasing each radius by its gauge
times `delta / (1 - rate)`.

For finite graphs, strict contraction of every nonempty cycle guarantees existence of an
invariant radius above any prescribed lower data. Upper budgets still need a separate check.

## Main definitions

* `SwitchedHybridControl.expandingGain`: a two-mode comparison with an amplifying transition.
* `SwitchedHybridControl.expandingGauge`: scales witnessing contraction of that comparison.
* `SwitchedHybridControl.weightedConcreteTransport`: affine real-valued example executions.
* `SwitchedHybridControl.weightedExecutionComparison`: their error comparison with unit data.
* `SwitchedHybridControl.weightedRadius`: invariant radii for the actual executions.

## Main results

* `SwitchedHybridControl.ErrorComparison.walk_error_le_geometric`: a geometric excess bound.
* `SwitchedHybridControl.ErrorComparison.radius_of_bias_bound`: a gauge-scaled invariant radius.
* `SwitchedHybridControl.ErrorComparison.radius_perturbation`: robust radii under bias changes.
* `SwitchedHybridControl.ErrorComparison.exists_radius_of_cycle_contraction`: existence above
  arbitrary lower bounds when every nonempty cycle contracts.
* `SwitchedHybridControl.expandingGain_contractive`: an edge gain of two with contraction
  rate one half after scaling.
* `SwitchedHybridControl.weightedRadius_isRadiusFamily`: invariance of radii `3 / 2` and `4`.
* `SwitchedHybridControl.weightedRadius_le_of_isRadiusFamily`: these radii are pointwise least.
* `SwitchedHybridControl.weightedExecution_walk_geometric`: a geometric error estimate for every
  concrete execution along every walk.
-/

@[expose] public section

namespace SwitchedHybridControl

open Maths.MaxAffineTransport

universe uV uE uC uA

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}
variable {Concrete : V → Type uC} {Approximate : V → Type uA}
variable {concrete : Maths.Transport G Concrete} {approximate : Maths.Transport G Approximate}

namespace ErrorComparison

/-- Excess above an invariant radius is bounded geometrically along every walk. The initial
excess is measured in units of the source gauge; when `rate < 1`, the bound decays. -/
theorem walk_error_le_geometric (comparison : ErrorComparison concrete approximate)
    {rate : ℝ} (hrate : 0 ≤ rate) {gauge : V → ℝ}
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge)
    {radius : V → ℝ} (hradius : IsRadiusFamily comparison radius)
    {excess : ℝ} (hexcess : 0 ≤ excess) {start finish : V}
    (walk : G.Walk start finish) (c : Concrete start) (a : Approximate start)
    (hinitial : comparison.error start c a ≤ radius start + excess * gauge start) :
    comparison.error finish (concrete.walkMap walk c) (approximate.walkMap walk a) ≤
      radius finish + rate ^ walk.length * excess * gauge finish := by
  induction walk with
  | nil => simpa using hinitial
  | concat walk edge legal ih =>
      cases legal
      rw [Maths.Transport.walkMap_concat, Maths.Transport.walkMap_concat,
        Maths.EdgeGraph.Walk.length_concat, pow_succ]
      calc
        comparison.error _ (concrete.edgeMap edge _) (approximate.edgeMap edge _) ≤
            comparison.bias edge + comparison.gain edge *
              comparison.error _ (concrete.walkMap walk c) (approximate.walkMap walk a) :=
          comparison.step_le edge _ _
        _ ≤ comparison.bias edge + comparison.gain edge *
            (radius _ + rate ^ walk.length * excess * gauge _) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih (comparison.gain_nonneg edge))
        _ = (comparison.bias edge + comparison.gain edge * radius _) +
            (rate ^ walk.length * excess) * (comparison.gain edge * gauge _) := by ring
        _ ≤ radius _ + (rate ^ walk.length * excess) * (rate * gauge _) :=
          add_le_add (hradius edge) (mul_le_mul_of_nonneg_left (hgauge.2 edge)
            (mul_nonneg (pow_nonneg hrate _) hexcess))
        _ = _ := by ring

/-- A uniform normalized bias bound supplies an invariant radius. -/
theorem radius_of_bias_bound (comparison : ErrorComparison concrete approximate)
    {rate : ℝ} {gauge : V → ℝ}
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hbias : ∀ edge, comparison.bias edge ≤ (1 - rate) * bound * gauge (G.target edge)) :
    IsRadiusFamily comparison (fun vertex => bound * gauge vertex) := by
  intro edge
  have hgain := mul_le_mul_of_nonneg_left (hgauge.2 edge) hbound
  have hstep := hbias edge
  dsimp
  nlinarith

/-- A bounded increase in additive bias preserves the radius certificate after adding the
normalized disturbance margin. Gains are unchanged, and `rate < 1` makes the margin finite. -/
theorem radius_perturbation (comparison changed : ErrorComparison concrete approximate)
    {rate : ℝ} (hrate : rate < 1) {gauge : V → ℝ}
    (hgauge : IsContractiveGauge (G := G) comparison.gain rate gauge)
    {radius : V → ℝ} (hradius : IsRadiusFamily comparison radius)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hgain : changed.gain = comparison.gain)
    (hbias : ∀ edge, changed.bias edge ≤
      comparison.bias edge + delta * gauge (G.target edge)) :
    IsRadiusFamily changed
      (fun vertex => radius vertex + delta / (1 - rate) * gauge vertex) := by
  have hden : 0 < 1 - rate := sub_pos.mpr hrate
  have hmargin : 0 ≤ delta / (1 - rate) := div_nonneg hdelta hden.le
  have hcancel : (delta / (1 - rate)) * (1 - rate) = delta :=
    div_mul_cancel₀ _ hden.ne'
  intro edge
  dsimp
  rw [hgain]
  have hscaled := mul_le_mul_of_nonneg_left (hgauge.2 edge) hmargin
  have hrow := hradius edge
  have hperturb := hbias edge
  have hidentity := congrArg (fun value : ℝ => value * gauge (G.target edge)) hcancel
  nlinarith

/-- Strict cycle contraction gives a radius family above arbitrary lower data on a finite
graph. This is an existence theorem; prescribed upper budgets may still be infeasible. -/
theorem exists_radius_of_cycle_contraction [Fintype V] [Finite E]
    (comparison : ErrorComparison concrete approximate) (lower : V → ℝ)
    (hcycles : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      0 < cycle.length → walkSlopeProduct comparison.gain cycle < 1) :
    ∃ radius : V → ℝ, (∀ vertex, lower vertex ≤ radius vertex) ∧
      IsRadiusFamily comparison radius := by
  obtain ⟨rate, gauge, _, hrate, hgauge⟩ :=
    (exists_contractiveGauge_iff_cycleProduct_lt_one comparison.gain
      comparison.gain_nonneg).mpr hcycles
  obtain ⟨biasBound, hbias⟩ := Finite.exists_le
    (fun edge => comparison.bias edge / ((1 - rate) * gauge (G.target edge)))
  obtain ⟨lowerBound, hlower⟩ := Finite.exists_le (fun vertex => lower vertex / gauge vertex)
  let bound := max 0 (max biasBound lowerBound)
  have hbound : 0 ≤ bound := le_max_left _ _
  have hb : biasBound ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have hl : lowerBound ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun vertex => bound * gauge vertex, fun vertex => ?_,
    comparison.radius_of_bias_bound hgauge hbound fun edge => ?_⟩
  · exact (div_le_iff₀ (hgauge.1 vertex)).mp ((hlower vertex).trans hl)
  · have hden : 0 < (1 - rate) * gauge (G.target edge) :=
      mul_pos (sub_pos.mpr hrate) (hgauge.1 _)
    have h := (div_le_iff₀ hden).mp ((hbias edge).trans hb)
    nlinarith

end ErrorComparison

/-- An amplifying forward transition and a contracting return transition. -/
noncomputable def expandingGain : ExampleEdge → ℝ
  | .expand => 2
  | .reset => 1 / 8

/-- Positive mode scales exposing the contraction behind an amplifying transition. -/
def expandingGauge : ExampleMode → ℝ
  | .bool => 1
  | .fin3 => 4

/-- Although the expansion gain is two, normalized gains are both one half. -/
theorem expandingGain_contractive :
    IsContractiveGauge (G := examplePhysicalGraph) expandingGain (1 / 2) expandingGauge := by
  constructor
  · intro vertex
    cases vertex <;> norm_num [expandingGauge]
  · intro edge
    cases edge <;> norm_num [expandingGain, expandingGauge, examplePhysicalGraph]

/-! ## Main definitions -/

/-- Both modes carry a real concrete state in the weighted execution example. -/
abbrev weightedConcreteState (_ : ExampleMode) : Type := ℝ

/-- Both modes discard their approximate state in the weighted execution example. -/
abbrev weightedApproximateState (_ : ExampleMode) : Type := Unit

/-- Affine concrete dynamics: expansion has slope two and reset has slope one eighth. -/
noncomputable def weightedConcreteStep : (edge : ExampleEdge) →
    weightedConcreteState (examplePhysicalGraph.source edge) →
      weightedConcreteState (examplePhysicalGraph.target edge)
  | .expand, state => 1 + 2 * state
  | .reset, state => 1 + (1 / 8) * state

/-- The concrete transport generated by the two affine transitions. -/
noncomputable def weightedConcreteTransport :
    Maths.Transport examplePhysicalGraph weightedConcreteState where
  edgeMap := weightedConcreteStep

/-- The unit-valued approximate transport corresponding to the affine executions. -/
def weightedApproximateTransport :
    Maths.Transport examplePhysicalGraph weightedApproximateState where
  edgeMap _ _ := ()

/-- Absolute concrete magnitude is the comparison error against unit approximate data. -/
noncomputable def weightedExecutionError (vertex : ExampleMode) :
    weightedConcreteState vertex → weightedApproximateState vertex → ℝ :=
  fun state _ => |state|

/-- Local affine error comparison realized by the concrete affine dynamics. -/
noncomputable def weightedExecutionComparison :
    ErrorComparison weightedConcreteTransport weightedApproximateTransport where
  error := weightedExecutionError
  bias := fun _ => 1
  gain := expandingGain
  gain_nonneg edge := by cases edge <;> norm_num [expandingGain]
  step_le edge state approximate := by
    cases edge with
    | expand =>
        change |1 + 2 * state| ≤ 1 + 2 * |state|
        calc
          |1 + 2 * state| ≤ |(1 : ℝ)| + |2 * state| := abs_add_le _ _
          _ = 1 + 2 * |state| := by norm_num [abs_mul, abs_of_nonneg]
    | reset =>
        change |1 + (1 / 8) * state| ≤ 1 + (1 / 8) * |state|
        calc
          |1 + (1 / 8) * state| ≤ |(1 : ℝ)| + |(1 / 8) * state| := abs_add_le _ _
          _ = 1 + (1 / 8) * |state| := by norm_num [abs_mul, abs_of_nonneg]

/-- Invariant radii `3 / 2` in Boolean mode and `4` in finite mode. -/
noncomputable def weightedRadius : ExampleMode → ℝ
  | .bool => 3 / 2
  | .fin3 => 4

/-- The weighted radii are invariant under both affine error comparisons. -/
theorem weightedRadius_isRadiusFamily :
    IsRadiusFamily weightedExecutionComparison weightedRadius := by
  intro edge
  cases edge <;>
    norm_num [weightedExecutionComparison, weightedRadius, expandingGain, examplePhysicalGraph]

/-- Every invariant radius family for the weighted example dominates the displayed radii. -/
theorem weightedRadius_le_of_isRadiusFamily {radius : ExampleMode → ℝ}
    (hradius : IsRadiusFamily weightedExecutionComparison radius) :
    ∀ vertex, weightedRadius vertex ≤ radius vertex := by
  have hexpand := hradius ExampleEdge.expand
  have hreset := hradius ExampleEdge.reset
  change 1 + 2 * radius .bool ≤ radius .fin3 at hexpand
  change 1 + (1 / 8) * radius .fin3 ≤ radius .bool at hreset
  intro vertex
  cases vertex <;> norm_num [weightedRadius] <;> nlinarith

/-- Every actual affine execution has geometric decay of excess above the invariant radius.
The expansion edge can double error, while gauge normalization gives rate one half globally. -/
theorem weightedExecution_walk_geometric {start finish : ExampleMode}
    (walk : examplePhysicalGraph.Walk start finish)
    (state : weightedConcreteState start) (approximate : weightedApproximateState start)
    {excess : ℝ} (hexcess : 0 ≤ excess)
    (hinitial : |state| ≤ weightedRadius start + excess * expandingGauge start) :
    |weightedConcreteTransport.walkMap walk state| ≤
      weightedRadius finish + (1 / 2) ^ walk.length * excess * expandingGauge finish := by
  exact weightedExecutionComparison.walk_error_le_geometric (by norm_num)
    expandingGain_contractive weightedRadius_isRadiusFamily hexcess walk state approximate hinitial

end SwitchedHybridControl
