/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Recursion.TransferSummary
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Iterating a single affine summary

An affine summary `(shift, slope)` acts on the line by `x ↦ shift + slope * x`. Iterating one
fixed summary is a dichotomy governed entirely by the slope.

* When `slope ≠ 1` the map has exactly one fixed point,
  `AffineSummary.fixedPoint = shift / (1 - slope)`, and the whole orbit is explicit in it: the
  displacement from the fixed point is multiplied by the slope at every stage, so
  `f.apply^[n] x = slope ^ n * (x - fixedPoint) + fixedPoint`. When moreover `|slope| < 1` the
  geometric factor vanishes and every orbit converges to the fixed point, at a rate independent
  of the starting state.

* When `slope = 1` the map is the translation `x ↦ shift + x`, its `n`-th iterate is
  `x ↦ n * shift + x`, and it has a fixed point exactly when `shift = 0`, in which case it is
  the identity and every point is fixed.

## Main definitions

* `Maths.TransferSummary.AffineSummary.fixedPoint` -- the point
  `shift / (1 - slope)`.

## Main results

* `Maths.TransferSummary.AffineSummary.apply_fixedPoint` and
  `Maths.TransferSummary.AffineSummary.eq_fixedPoint_of_apply_eq` -- at slope `≠ 1`
  the fixed point is fixed and is the only fixed point, packaged as
  `Maths.TransferSummary.AffineSummary.existsUnique_apply_eq`.
* `Maths.TransferSummary.AffineSummary.apply_sub_fixedPoint` -- the displacement
  from the fixed point is multiplied by the slope.
* `Maths.TransferSummary.AffineSummary.iterate_apply` and
  `Maths.TransferSummary.AffineSummary.apply_pow_eq` -- the closed form of the
  orbit.
* `Maths.TransferSummary.AffineSummary.tendsto_iterate_apply` -- convergence to the
  fixed point at slope of absolute value `< 1`.
* `Maths.TransferSummary.AffineSummary.apply_of_slope_eq_one`,
  `Maths.TransferSummary.AffineSummary.iterate_apply_of_slope_eq_one` and
  `Maths.TransferSummary.AffineSummary.exists_apply_eq_iff_of_slope_eq_one` -- the
  degenerate translation case.

## Tags

affine map, fixed point, geometric convergence, contraction
-/

@[expose] public section

noncomputable section

namespace Maths.TransferSummary.AffineSummary

variable {f : AffineSummary}

/-- The fixed point `shift / (1 - slope)` of the affine map `x ↦ shift + slope * x`. It is a
genuine fixed point, and the only one, exactly when `slope ≠ 1` (`apply_fixedPoint`,
`eq_fixedPoint_of_apply_eq`); at `slope = 1` the expression degenerates and carries no
meaning. -/
def fixedPoint (f : AffineSummary) : ℝ := f.shift / (1 - f.slope)

/-- **The fixed point is fixed.** -/
@[simp] theorem apply_fixedPoint (h : f.slope ≠ 1) : f.apply f.fixedPoint = f.fixedPoint := by
  have hsub : 1 - f.slope ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
  have key : (1 - f.slope) * f.fixedPoint = f.shift := by
    rw [fixedPoint, mul_div_cancel₀ _ hsub]
  rw [apply, ← key]
  ring

/-- **The fixed point is the only fixed point** when the slope is not `1`. -/
theorem eq_fixedPoint_of_apply_eq (h : f.slope ≠ 1) {x : ℝ} (hx : f.apply x = x) :
    x = f.fixedPoint := by
  have hsub : 1 - f.slope ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
  rw [apply] at hx
  rw [fixedPoint, eq_div_iff hsub]
  linarith

/-- **An affine map of slope `≠ 1` has exactly one fixed point.** -/
theorem existsUnique_apply_eq (h : f.slope ≠ 1) : ∃! x : ℝ, f.apply x = x :=
  ⟨f.fixedPoint, apply_fixedPoint h, fun _ hx => eq_fixedPoint_of_apply_eq h hx⟩

/-- **One stage multiplies the displacement from the fixed point by the slope.** This is the
whole content of the closed form of the orbit. -/
theorem apply_sub_fixedPoint (h : f.slope ≠ 1) (x : ℝ) :
    f.apply x - f.fixedPoint = f.slope * (x - f.fixedPoint) := by
  have hsub : 1 - f.slope ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
  have key : (1 - f.slope) * f.fixedPoint = f.shift := by
    rw [fixedPoint, mul_div_cancel₀ _ hsub]
  rw [apply, ← key]
  ring

/-- **The closed form of the orbit of a single affine summary**: the displacement from the fixed
point decays -- or grows -- geometrically in the slope. -/
theorem iterate_apply (h : f.slope ≠ 1) (x : ℝ) :
    ∀ n : ℕ, f.apply^[n] x = f.slope ^ n * (x - f.fixedPoint) + f.fixedPoint
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_apply h x n, ← sub_eq_iff_eq_add,
      apply_sub_fixedPoint h, pow_succ]
    ring

/-- The closed form of the orbit, read off the `n`-th power of the summary in the monoid. -/
theorem apply_pow_eq (h : f.slope ≠ 1) (n : ℕ) (x : ℝ) :
    (f ^ n).apply x = f.slope ^ n * (x - f.fixedPoint) + f.fixedPoint := by
  rw [apply_pow, iterate_apply h]

/-- **Every orbit of a strictly contracting affine map converges to its fixed point.** The rate
is the geometric factor `|slope| ^ n` and does not depend on the starting state. -/
theorem tendsto_iterate_apply (h : |f.slope| < 1) (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => f.apply^[n] x) Filter.atTop (nhds f.fixedPoint) := by
  have hne : f.slope ≠ 1 := fun hone => by rw [hone] at h; simp at h
  have hpow : Filter.Tendsto (fun n : ℕ => f.slope ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr h
  have := (hpow.mul_const (x - f.fixedPoint)).add_const f.fixedPoint
  rw [zero_mul, zero_add] at this
  exact this.congr fun n => (iterate_apply hne x n).symm

/-! ### The degenerate case of unit slope -/

/-- At unit slope the affine map is the translation by its shift. -/
theorem apply_of_slope_eq_one (h : f.slope = 1) (x : ℝ) : f.apply x = f.shift + x := by
  rw [apply, h, one_mul]

/-- At unit slope the `n`-th iterate is the translation by `n` times the shift: the orbit is an
arithmetic progression and has no closed form around a fixed point. -/
theorem iterate_apply_of_slope_eq_one (h : f.slope = 1) (x : ℝ) :
    ∀ n : ℕ, f.apply^[n] x = n * f.shift + x
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_apply_of_slope_eq_one h x n,
      apply_of_slope_eq_one h]
    push_cast
    ring

/-- **A translation has a fixed point exactly when it is the identity.** At unit slope a nonzero
shift moves every point, and a zero shift fixes every point; so the dichotomy of
`existsUnique_apply_eq` fails at slope `1` in both directions -- there is either no fixed point
or a whole line of them. -/
theorem exists_apply_eq_iff_of_slope_eq_one (h : f.slope = 1) :
    (∃ x : ℝ, f.apply x = x) ↔ f.shift = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [apply_of_slope_eq_one h] at hx
    linarith
  · intro hshift
    exact ⟨0, by rw [apply_of_slope_eq_one h, hshift, zero_add]⟩

/-- At unit slope and zero shift every point is fixed. -/
theorem apply_eq_self_of_slope_eq_one (h : f.slope = 1) (hshift : f.shift = 0) (x : ℝ) :
    f.apply x = x := by
  rw [apply_of_slope_eq_one h, hshift, zero_add]

end Maths.TransferSummary.AffineSummary
