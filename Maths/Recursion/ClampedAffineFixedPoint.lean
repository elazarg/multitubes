/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Recursion.TwoSidedReflection

import Mathlib.Analysis.Normed.MulAction
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Fixed points of clamped affine maps

The action of a clamped affine summary is a contraction when the absolute
value of its slope is strictly below one.  Its unique fixed point exists under
the weaker condition that the slope itself is below one, and is obtained by
clamping the fixed point of the unclamped affine branch.  The result is useful
for finite-buffer recurrences and for scalar obstacle operators.

## Main definitions

* `Maths.TransferSummary.ClampedAffineSummary.fixedPoint` - the clamped affine
  fixed-point candidate.

## Main results

* `Maths.TransferSummary.ClampedAffineSummary.apply_fixedPoint` - the candidate
  is a fixed point under a nonempty band and a slope below one.
* `Maths.TransferSummary.ClampedAffineSummary.fixedPoint_unique` - the
  candidate is the only fixed point.
* `Maths.TransferSummary.ClampedAffineSummary.tendsto_iterate_fixedPoint` -
  every orbit converges to the candidate under a contracting slope.

## Tags

clamped affine, contraction, fixed point, obstacle
-/

@[expose] public section

noncomputable section

namespace Maths.TransferSummary.ClampedAffineSummary

open Filter Function Set

/-! ## The explicit candidate -/

/-- The fixed point of the affine branch, clamped to the summary's band. -/
def fixedPoint (f : ClampedAffineSummary) : ℝ :=
  min f.hi (max f.lo (f.shift / (1 - f.slope)))

private theorem lipschitz_apply {f : ClampedAffineSummary} :
    LipschitzWith ‖f.slope‖₊ f.apply := by
  have haffine : LipschitzWith ‖f.slope‖₊
      (fun x : ℝ => f.shift + f.slope * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    rw [show (f.shift + f.slope * x) - (f.shift + f.slope * y) =
      f.slope * (x - y) by ring, abs_mul]
    simp
  exact (haffine.const_max f.lo).const_min f.hi

private theorem contracting (f : ClampedAffineSummary) (hcontract : |f.slope| < 1) :
    ContractingWith ‖f.slope‖₊ f.apply :=
  ⟨by exact_mod_cast hcontract, lipschitz_apply⟩

private theorem affine_fixedPoint_apply {f : ClampedAffineSummary}
    (hcontract : f.slope < 1) :
    f.shift + f.slope * (f.shift / (1 - f.slope)) = f.shift / (1 - f.slope) := by
  have hne : 1 - f.slope ≠ 0 := by linarith
  field_simp
  ring

/-! ## Fixed-point equation -/

/-- Clamping the affine fixed point produces a fixed point of the clamped map. -/
theorem apply_fixedPoint {f : ClampedAffineSummary} (hband : f.lo ≤ f.hi)
    (hcontract : f.slope < 1) :
    f.apply f.fixedPoint = f.fixedPoint := by
  have hpositive : 0 < 1 - f.slope := by linarith
  let affinePoint : ℝ := f.shift / (1 - f.slope)
  have hfixed : f.shift + f.slope * affinePoint = affinePoint := by
    dsimp [affinePoint]
    exact affine_fixedPoint_apply hcontract
  by_cases hlow : affinePoint ≤ f.lo
  · have hbranch : f.shift + f.slope * f.lo ≤ f.lo := by
      have hlow' := (div_le_iff₀ hpositive).mp hlow
      dsimp [affinePoint] at hlow
      nlinarith
    rw [fixedPoint, max_eq_left hlow, min_eq_right hband]
    rw [apply, max_eq_left hbranch, min_eq_right hband]
  · have hlow' : f.lo ≤ affinePoint := le_of_not_ge hlow
    by_cases hhigh : f.hi ≤ affinePoint
    · have hbranch : f.hi ≤ f.shift + f.slope * f.hi := by
        have hhigh' := (le_div_iff₀ hpositive).mp hhigh
        dsimp [affinePoint] at hhigh
        nlinarith
      rw [fixedPoint, max_eq_right (hband.trans hhigh), min_eq_left hhigh]
      rw [apply, max_eq_right (hband.trans hbranch), min_eq_left hbranch]
    · have hhigh' : affinePoint ≤ f.hi := le_of_not_ge hhigh
      rw [fixedPoint, max_eq_right hlow', min_eq_right hhigh']
      rw [apply, hfixed, max_eq_right hlow', min_eq_right hhigh']

/-- The explicit clamped affine fixed point lies in the summary's nonempty band. -/
theorem fixedPoint_mem_Icc {f : ClampedAffineSummary} (hband : f.lo ≤ f.hi) :
    f.fixedPoint ∈ Icc f.lo f.hi := by
  constructor
  · exact le_min hband (le_max_left _ _)
  · exact min_le_left _ _

/-! ## Uniqueness and convergence -/

/-- The clamped affine fixed point is the only fixed point. -/
theorem fixedPoint_unique {f : ClampedAffineSummary} (hband : f.lo ≤ f.hi)
    (hcontract : f.slope < 1) {x : ℝ}
    (hx : f.apply x = x) :
    x = f.fixedPoint := by
  by_cases hslope : 0 ≤ f.slope
  · have habs : |f.slope| < 1 := by simpa [abs_of_nonneg hslope] using hcontract
    let hcontraction := contracting f habs
    have hx' : IsFixedPt f.apply x := hx
    have hxp : x = hcontraction.fixedPoint := hcontraction.fixedPoint_unique hx'
    have heq : f.fixedPoint = hcontraction.fixedPoint :=
      hcontraction.fixedPoint_unique (apply_fixedPoint hband hcontract)
    exact hxp.trans heq.symm
  · have hslope' : f.slope ≤ 0 := le_of_not_ge hslope
    have hanti : Antitone f.apply := by
      intro first second hfirst
      change min f.hi (max f.lo (f.shift + f.slope * second)) ≤
        min f.hi (max f.lo (f.shift + f.slope * first))
      refine min_le_min le_rfl (max_le_max le_rfl ?_)
      nlinarith
    have hle : x ≤ f.fixedPoint := by
      by_cases hxy : x ≤ f.fixedPoint
      · exact hxy
      · have hyx : f.fixedPoint ≤ x := le_of_not_ge hxy
        have hfixed := apply_fixedPoint hband hcontract
        have hreverse := hanti hyx
        rw [hfixed, hx] at hreverse
        exact False.elim (by linarith)
    have hge : f.fixedPoint ≤ x := by
      by_cases hxy : f.fixedPoint ≤ x
      · exact hxy
      · have hyx : x ≤ f.fixedPoint := le_of_not_ge hxy
        have hfixed := apply_fixedPoint hband hcontract
        have hreverse := hanti hyx
        rw [hfixed, hx] at hreverse
        exact False.elim (by linarith)
    exact le_antisymm hle hge

/-- Iterating a contracting clamped affine map converges to its explicit fixed point. -/
theorem tendsto_iterate_fixedPoint {f : ClampedAffineSummary}
    (hband : f.lo ≤ f.hi) (hcontract : |f.slope| < 1) (x : ℝ) :
    Tendsto (fun n => f.apply^[n] x) atTop (nhds f.fixedPoint) := by
  let hcontraction := contracting f hcontract
  have hbanach := hcontraction.tendsto_iterate_fixedPoint x
  have hslope : f.slope < 1 := (le_abs_self f.slope).trans_lt hcontract
  have heq : f.fixedPoint = hcontraction.fixedPoint :=
    hcontraction.fixedPoint_unique (apply_fixedPoint hband hslope)
  rw [heq]
  exact hbanach

end Maths.TransferSummary.ClampedAffineSummary
