/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

/-!
# Linearizing one-dimensional rational recurrences in the inverse coordinate

A first-order recurrence of linear-fractional shape

`h (t + 1) = h t / (c + d * h t)`

becomes affine in the reciprocal coordinate `g = h⁻¹`:

`g (t + 1) = c * g t + d`,

and the affine recurrence has the closed form `g t = c ^ t * (g 0 - p) + p` around its fixed point
`p = d / (1 - c)`. This file develops that dictionary in three layers and then records the
`2 × 2` matrix reading.

* `affineStep` and `affineFixedPoint`, with the closed form `affine_eq_closedForm`, the degenerate
  `c = 1` form `affine_eq_closedForm_of_coeff_one`, monotonicity, and the limits at `1 < c` and
  `|c| < 1`.
* `linearFractionalStep`, its conjugacy to `affineStep` under `x ↦ x⁻¹`
  (`linearFractionalStep_eq_inv_affineStep_inv`), transport of the recurrence in both directions,
  and transport of interiority, strict monotonicity, and vanishing between the two coordinates.
* `IsHazardBalance`, the worked family `a * h (t + 1) * (1 - h t) = h t` with `1 < a`. Its inverse
  coordinate obeys `g (t + 1) = a * g t - a` with fixed point `a / (a - 1)`. The seeds of positive
  orbits are exactly `Set.Ioc 0 (hazardCeiling a)` - necessary by
  `IsHazardBalance.le_hazardCeiling` and realized by `hazardOrbit`, whose closed form is
  `isHazardBalance_hazardOrbit` - and among positive orbits the vanishing ones are exactly those
  with seed strictly below `hazardCeiling a = (a - 1) / a`.
* `affineTransferMatrix` and `linearFractionalTransferMatrix`, whose products compose the
  corresponding steps, are conjugate by `inversionMatrix`, and act on `OnePoint ℝ` by the Möbius
  action `OnePoint.instGLAction` through `linearFractionalGL`.
* `affineCycleMatrix`, the product transfer matrix of an `n`-phase coefficient cycle, and the
  classification of a `2 × 2` matrix by the sign of `projectiveDiscriminant`. A product of affine
  transfer matrices is again affine, with slope `affineCycleSlope` and shift `affineCycleShift`,
  so its discriminant is the square `(affineCycleSlope l - 1) ^ 2`: an affine cycle is never
  elliptic, and is hyperbolic exactly when its slope product differs from `1`.

The linear-fractional map is also called a Möbius transformation, a homographic map, or a
fractional linear transformation. The closed form of the affine recurrence is the
geometric-plus-fixed-point solution of a first-order linear difference equation. The matrix layer
is the transfer matrix or cocycle representation of the map, acting projectively on the one-point
compactification of the line.

The coordinate change used here is the exact reciprocal `h ↦ h⁻¹`, not the odds transform
`h ↦ h / (1 - h)`; the two agree only to first order at `0` and differ by the constant `1` on
`(0, 1)`, since `h⁻¹ = (h / (1 - h))⁻¹ + 1` there. Pointwise interiority transport is
`one_le_inv₀`.

## Main definitions

* `DirectedTransport.InverseCoordinate.affineStep`,
  `DirectedTransport.InverseCoordinate.affineFixedPoint`: the affine recurrence and its fixed
  point.
* `DirectedTransport.InverseCoordinate.linearFractionalStep`: the conjugate Möbius step.
* `DirectedTransport.InverseCoordinate.IsHazardBalance`,
  `DirectedTransport.InverseCoordinate.hazardCeiling`,
  `DirectedTransport.InverseCoordinate.hazardOrbit`: the worked family.
* `DirectedTransport.InverseCoordinate.affineTransferMatrix`,
  `DirectedTransport.InverseCoordinate.linearFractionalTransferMatrix`,
  `DirectedTransport.InverseCoordinate.inversionMatrix`,
  `DirectedTransport.InverseCoordinate.linearFractionalGL`: the matrix reading.
* `DirectedTransport.InverseCoordinate.affineCycleSlope`,
  `DirectedTransport.InverseCoordinate.affineCycleShift`,
  `DirectedTransport.InverseCoordinate.affineCycleStep`,
  `DirectedTransport.InverseCoordinate.affineCycleMatrix`: the `n`-phase cycle.
* `DirectedTransport.InverseCoordinate.projectiveDiscriminant`,
  `DirectedTransport.InverseCoordinate.IsProjectiveHyperbolic`,
  `DirectedTransport.InverseCoordinate.IsProjectiveParabolic`,
  `DirectedTransport.InverseCoordinate.IsProjectiveElliptic`: the classification.

## Main results

* `DirectedTransport.InverseCoordinate.affine_eq_closedForm`: the closed form of the affine
  recurrence.
* `DirectedTransport.InverseCoordinate.linearFractionalStep_eq_inv_affineStep_inv`: the
  inverse-coordinate conjugacy.
* `DirectedTransport.InverseCoordinate.IsHazardBalance.tendsto_zero_iff`: classification of the
  vanishing solutions of the worked family.
* `DirectedTransport.InverseCoordinate.affineTransferMatrix_mul`,
  `DirectedTransport.InverseCoordinate.linearFractionalTransferMatrix_mul`: composition is matrix
  multiplication.
* `DirectedTransport.InverseCoordinate.linearFractionalGL_smul_coe`,
  `DirectedTransport.InverseCoordinate.linearFractionalGL_cycle_smul`: the projective action.
* `DirectedTransport.InverseCoordinate.affineCycleMatrix_eq`,
  `DirectedTransport.InverseCoordinate.affineCycleStep_eq`: an `n`-phase affine cycle is a single
  affine step, at matrix and at scalar level.
* `DirectedTransport.InverseCoordinate.isProjectiveHyperbolic_or_parabolic_or_elliptic`: the
  trichotomy.
* `DirectedTransport.InverseCoordinate.not_isProjectiveElliptic_affineCycleMatrix`,
  `DirectedTransport.InverseCoordinate.isProjectiveHyperbolic_affineCycleMatrix_iff`,
  `DirectedTransport.InverseCoordinate.isProjectiveParabolic_affineCycleMatrix_iff`: the affine
  degeneration of the classification.
* `DirectedTransport.InverseCoordinate.affineCycleStep_eq_self_iff_of_slope_ne_one`,
  `DirectedTransport.InverseCoordinate.affineCycleStep_eq_self_iff_of_slope_one`: the periodic
  seeds of a cycle in each case.

## Implementation notes

`affineStep_comp` is proved directly from the coefficient formula rather than through a bundled
composition law, so this file is independent of
`DirectedTransport.TransferSummary`.

A coefficient cycle is a `List (ℝ × ℝ)` of slope-shift pairs, with the head applied last, so that
`affineCycleMatrix` is the plain product of the transfer matrices in list order. The shift
accumulates by Horner's rule, matching the coefficient law of `affineTransferMatrix_mul`.

## TODO

* The classification is stated for the discriminant of a `2 × 2` matrix and computed for products
  of affine transfer matrices, where the elliptic case is vacuous. The elliptic case itself, which
  needs matrices of negative determinant such as `inversionMatrix`, and the identification of the
  fixed points of a hyperbolic action as the roots of the associated quadratic, are not developed
  here.

## References

* A. F. Beardon, *The Geometry of Discrete Groups*, Springer, 1983, §4.3, for the classification
  of Möbius transformations by the trace of a representing matrix.

## Tags

linear-fractional recurrence, Möbius transformation, transfer matrix, difference equation,
projective line
-/

@[expose] public section

noncomputable section

open Filter Matrix Topology

namespace DirectedTransport.InverseCoordinate

/-! ### The affine recurrence -/

/-- One step of the first-order affine recurrence, `x ↦ c * x + d`. -/
def affineStep (c d x : ℝ) : ℝ := c * x + d

/-- The unique fixed point `d / (1 - c)` of `affineStep c d`, for `c ≠ 1`. -/
def affineFixedPoint (c d : ℝ) : ℝ := d / (1 - c)

/-- Unfolding lemma for `affineStep`. -/
theorem affineStep_apply (c d x : ℝ) : affineStep c d x = c * x + d := rfl

/-- `affineFixedPoint c d` is fixed by `affineStep c d` when `c ≠ 1`. -/
theorem affineStep_affineFixedPoint {c : ℝ} (d : ℝ) (hc : c ≠ 1) :
    affineStep c d (affineFixedPoint c d) = affineFixedPoint c d := by
  have hne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  unfold affineStep affineFixedPoint
  field_simp
  ring

/-- Affine steps compose to an affine step: this is the scalar shadow of
`affineTransferMatrix_mul`. -/
theorem affineStep_comp (c₁ d₁ c₂ d₂ x : ℝ) :
    affineStep c₁ d₁ (affineStep c₂ d₂ x) = affineStep (c₁ * c₂) (c₁ * d₂ + d₁) x := by
  unfold affineStep
  ring

/-- **Closed form of a first-order affine recurrence.** A geometric term around the fixed
point. -/
theorem affine_eq_closedForm {c d : ℝ} {g : ℕ → ℝ} (hc : c ≠ 1)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (t : ℕ) :
    g t = c ^ t * (g 0 - affineFixedPoint c d) + affineFixedPoint c d := by
  have hne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  induction t with
  | zero => simp
  | succ t ih =>
      rw [hrec t, ih, pow_succ]
      unfold affineFixedPoint
      field_simp
      ring

/-- The iterate form of `affine_eq_closedForm`. -/
theorem affineStep_iterate {c : ℝ} (d : ℝ) (hc : c ≠ 1) (x : ℝ) (t : ℕ) :
    (affineStep c d)^[t] x = c ^ t * (x - affineFixedPoint c d) + affineFixedPoint c d := by
  have hrec (s : ℕ) : (affineStep c d)^[s + 1] x = c * (affineStep c d)^[s] x + d := by
    rw [Function.iterate_succ_apply']
    rfl
  simpa using affine_eq_closedForm (g := fun s => (affineStep c d)^[s] x) hc hrec t

/-- Closed form in the degenerate case `c = 1`, where no fixed point exists unless `d = 0`: the
orbit is an arithmetic progression. -/
theorem affine_eq_closedForm_of_coeff_one {d : ℝ} {g : ℕ → ℝ}
    (hrec : ∀ t, g (t + 1) = g t + d) (t : ℕ) :
    g t = g 0 + t * d := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [hrec t, ih]
      push_cast
      ring

/-- An orbit started at the fixed point stays there. -/
theorem affine_eq_affineFixedPoint {c d : ℝ} {g : ℕ → ℝ} (hc : c ≠ 1)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (h0 : g 0 = affineFixedPoint c d) (t : ℕ) :
    g t = affineFixedPoint c d := by
  rw [affine_eq_closedForm hc hrec t, h0]
  ring

/-- Above the fixed point with expanding coefficient, the orbit is strictly increasing. -/
theorem strictMono_affine {c d : ℝ} {g : ℕ → ℝ} (hc : 1 < c)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (h0 : affineFixedPoint c d < g 0) :
    StrictMono g := by
  have hcne : c ≠ 1 := hc.ne'
  refine strictMono_nat_of_lt_succ fun t => ?_
  rw [affine_eq_closedForm hcne hrec t, affine_eq_closedForm hcne hrec (t + 1), pow_succ]
  have hpow : (0 : ℝ) < c ^ t := pow_pos (by linarith) t
  nlinarith [mul_pos (mul_pos hpow (sub_pos.mpr h0)) (sub_pos.mpr hc)]

/-- Below the fixed point with expanding coefficient, the orbit is strictly decreasing. -/
theorem strictAnti_affine {c d : ℝ} {g : ℕ → ℝ} (hc : 1 < c)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (h0 : g 0 < affineFixedPoint c d) :
    StrictAnti g := by
  have hcne : c ≠ 1 := hc.ne'
  refine strictAnti_nat_of_succ_lt fun t => ?_
  rw [affine_eq_closedForm hcne hrec t, affine_eq_closedForm hcne hrec (t + 1), pow_succ]
  have hpow : (0 : ℝ) < c ^ t := pow_pos (by linarith) t
  nlinarith [mul_pos hpow (sub_pos.mpr hc), sub_neg.2 h0]

/-- Above the fixed point with expanding coefficient, the orbit diverges. -/
theorem tendsto_affine_atTop {c d : ℝ} {g : ℕ → ℝ} (hc : 1 < c)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (h0 : affineFixedPoint c d < g 0) :
    Tendsto g atTop atTop := by
  have hpow : Tendsto (fun t : ℕ => c ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hc
  have hmul : Tendsto (fun t : ℕ => c ^ t * (g 0 - affineFixedPoint c d)) atTop atTop :=
    hpow.atTop_mul_const (sub_pos.mpr h0)
  have hsum :
      Tendsto (fun t : ℕ => c ^ t * (g 0 - affineFixedPoint c d) + affineFixedPoint c d)
        atTop atTop :=
    tendsto_atTop_add_const_right atTop (affineFixedPoint c d) hmul
  exact hsum.congr fun t => (affine_eq_closedForm hc.ne' hrec t).symm

/-- Below the fixed point with expanding coefficient, the orbit diverges to `atBot`. -/
theorem tendsto_affine_atBot {c d : ℝ} {g : ℕ → ℝ} (hc : 1 < c)
    (hrec : ∀ t, g (t + 1) = c * g t + d) (h0 : g 0 < affineFixedPoint c d) :
    Tendsto g atTop atBot := by
  have hpow : Tendsto (fun t : ℕ => c ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hc
  have hmul : Tendsto (fun t : ℕ => c ^ t * (g 0 - affineFixedPoint c d)) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg (sub_neg.2 h0)).2 hpow
  have hsum :
      Tendsto (fun t : ℕ => c ^ t * (g 0 - affineFixedPoint c d) + affineFixedPoint c d)
        atTop atBot :=
    tendsto_atBot_add_const_right atTop (affineFixedPoint c d) hmul
  exact hsum.congr fun t => (affine_eq_closedForm hc.ne' hrec t).symm

/-- With contracting coefficient the orbit converges to the fixed point, whatever the seed. -/
theorem tendsto_affine_affineFixedPoint {c d : ℝ} {g : ℕ → ℝ} (hc : |c| < 1)
    (hrec : ∀ t, g (t + 1) = c * g t + d) :
    Tendsto g atTop (𝓝 (affineFixedPoint c d)) := by
  have hcne : c ≠ 1 := by
    intro hval
    rw [hval] at hc
    simp at hc
  have hpow : Tendsto (fun t : ℕ => c ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc
  have hlim :
      Tendsto (fun t : ℕ => c ^ t * (g 0 - affineFixedPoint c d) + affineFixedPoint c d)
        atTop (𝓝 (affineFixedPoint c d)) := by
    simpa using (hpow.mul_const (g 0 - affineFixedPoint c d)).add_const (affineFixedPoint c d)
  exact hlim.congr fun t => (affine_eq_closedForm hcne hrec t).symm

/-! ### The inverse-coordinate conjugacy -/

/-- One step of the linear-fractional (Möbius) recurrence conjugate to `affineStep c d` under
`x ↦ x⁻¹`. -/
def linearFractionalStep (c d x : ℝ) : ℝ := x / (c + d * x)

/-- Unfolding lemma for `linearFractionalStep`. -/
theorem linearFractionalStep_apply (c d x : ℝ) :
    linearFractionalStep c d x = x / (c + d * x) := rfl

/-- **The inverse-coordinate conjugacy.** The linear-fractional step is the affine step read
through the reciprocal coordinate. -/
theorem linearFractionalStep_eq_inv_affineStep_inv {x : ℝ} (c d : ℝ) (hx : x ≠ 0) :
    linearFractionalStep c d x = (affineStep c d x⁻¹)⁻¹ := by
  have hval : affineStep c d x⁻¹ = (c + d * x) / x := by
    unfold affineStep
    field_simp
  rw [hval, inv_div, linearFractionalStep]

/-- The reciprocal of a linear-fractional step is the affine step of the reciprocal. -/
theorem inv_linearFractionalStep {x : ℝ} (c d : ℝ) (hx : x ≠ 0) :
    (linearFractionalStep c d x)⁻¹ = affineStep c d x⁻¹ := by
  rw [linearFractionalStep_eq_inv_affineStep_inv c d hx, inv_inv]

/-- Linear-fractional steps compose, with the same coefficient law as `affineStep_comp`, provided
the inner denominator does not vanish. -/
theorem linearFractionalStep_comp {c₂ d₂ x : ℝ} (c₁ d₁ : ℝ) (hx : x ≠ 0)
    (hden : c₂ + d₂ * x ≠ 0) :
    linearFractionalStep c₁ d₁ (linearFractionalStep c₂ d₂ x) =
      linearFractionalStep (c₁ * c₂) (c₁ * d₂ + d₁) x := by
  have hinner : linearFractionalStep c₂ d₂ x ≠ 0 :=
    div_ne_zero hx hden
  rw [linearFractionalStep_eq_inv_affineStep_inv c₁ d₁ hinner,
    inv_linearFractionalStep c₂ d₂ hx, affineStep_comp,
    ← linearFractionalStep_eq_inv_affineStep_inv _ _ hx]

/-- Transport of the recurrence from the inverse coordinate to the original one. -/
theorem linearFractional_of_affine {c d : ℝ} {h : ℕ → ℝ} (hne : ∀ t, h t ≠ 0)
    (hrec : ∀ t, (h (t + 1))⁻¹ = c * (h t)⁻¹ + d) (t : ℕ) :
    h (t + 1) = linearFractionalStep c d (h t) := by
  rw [linearFractionalStep_eq_inv_affineStep_inv c d (hne t), affineStep_apply, ← hrec t,
    inv_inv]

/-- Transport of the recurrence from the original coordinate to the inverse one. -/
theorem affine_of_linearFractional {c d : ℝ} {h : ℕ → ℝ} (hne : ∀ t, h t ≠ 0)
    (hrec : ∀ t, h (t + 1) = linearFractionalStep c d (h t)) (t : ℕ) :
    (h (t + 1))⁻¹ = c * (h t)⁻¹ + d := by
  rw [hrec t, inv_linearFractionalStep c d (hne t), affineStep_apply]

/-- Interiority transport: a positive point lies in `(0, 1]` exactly when its reciprocal is at
least `1`. -/
theorem mem_Ioc_iff_one_le_inv {x : ℝ} (hx : 0 < x) :
    x ∈ Set.Ioc (0 : ℝ) 1 ↔ 1 ≤ x⁻¹ := by
  rw [Set.mem_Ioc, one_le_inv₀ hx]
  exact ⟨fun hval => hval.2, fun hval => ⟨hx, hval⟩⟩

/-- Monotonicity transport: a positive sequence decreases strictly exactly when its reciprocal
increases strictly. -/
theorem strictAnti_iff_strictMono_inv {h : ℕ → ℝ} (hpos : ∀ t, 0 < h t) :
    StrictAnti h ↔ StrictMono fun t => (h t)⁻¹ :=
  ⟨fun hA _ _ hst => (inv_lt_inv₀ (hpos _) (hpos _)).2 (hA hst),
    fun hM _ _ hst => (inv_lt_inv₀ (hpos _) (hpos _)).1 (hM hst)⟩

/-- Vanishing transport: a positive sequence tends to `0` exactly when its reciprocal diverges. -/
theorem tendsto_zero_iff_tendsto_inv_atTop {h : ℕ → ℝ} (hpos : ∀ t, 0 < h t) :
    Tendsto h atTop (𝓝 0) ↔ Tendsto (fun t => (h t)⁻¹) atTop atTop := by
  constructor
  · intro htend
    have hwithin : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h htend
        (Eventually.of_forall hpos)
    exact hwithin.inv_tendsto_nhdsGT_zero
  · intro htend
    simpa [Pi.inv_def] using htend.inv_tendsto_atTop

/-! ### The worked family `a * h (t + 1) * (1 - h t) = h t` -/

/-- The balance recurrence `a * h (t + 1) * (1 - h t) = h t`: the gain `a` times the next hazard
times the current survival probability returns the current hazard. It is the linear-fractional
recurrence with coefficients `(a, -a)`. -/
def IsHazardBalance (a : ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ t, a * h (t + 1) * (1 - h t) = h t

/-- The stationary hazard `(a - 1) / a` of the family, the reciprocal of the affine fixed point
`a / (a - 1)`. -/
def hazardCeiling (a : ℝ) : ℝ := (a - 1) / a

/-- The fixed point of the coefficients `(a, -a)` is `a / (a - 1)`. -/
theorem affineFixedPoint_neg_self {a : ℝ} (ha : a ≠ 1) :
    affineFixedPoint a (-a) = a / (a - 1) := by
  have hne : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hne' : a - (1 : ℝ) ≠ 0 := sub_ne_zero.mpr ha
  unfold affineFixedPoint
  field_simp
  ring

/-- The hazard ceiling is positive when the gain exceeds `1`. -/
theorem hazardCeiling_pos {a : ℝ} (ha : 1 < a) : 0 < hazardCeiling a :=
  div_pos (by linarith) (by linarith)

/-- The hazard ceiling is below `1`. -/
theorem hazardCeiling_lt_one {a : ℝ} (ha : 1 < a) : hazardCeiling a < 1 := by
  rw [hazardCeiling, div_lt_one (by linarith)]
  linarith

/-- The hazard ceiling is the reciprocal of the affine fixed point. -/
theorem inv_hazardCeiling {a : ℝ} (ha : 1 < a) :
    (hazardCeiling a)⁻¹ = affineFixedPoint a (-a) := by
  rw [affineFixedPoint_neg_self ha.ne', hazardCeiling, inv_div]

/-- Seed comparison against the ceiling, read in either coordinate. -/
theorem lt_hazardCeiling_iff {a x : ℝ} (ha : 1 < a) (hx : 0 < x) :
    x < hazardCeiling a ↔ affineFixedPoint a (-a) < x⁻¹ := by
  rw [← inv_hazardCeiling ha, inv_lt_inv₀ (hazardCeiling_pos ha) hx]

/-- Seed comparison against the ceiling, in the other direction. -/
theorem hazardCeiling_lt_iff {a x : ℝ} (ha : 1 < a) (hx : 0 < x) :
    hazardCeiling a < x ↔ x⁻¹ < affineFixedPoint a (-a) := by
  rw [← inv_hazardCeiling ha, inv_lt_inv₀ hx (hazardCeiling_pos ha)]

/-- **The linearization of the family.** In the reciprocal coordinate the balance recurrence is
affine with coefficients `(a, -a)`. -/
theorem IsHazardBalance.inv_affine {a : ℝ} {h : ℕ → ℝ} (hb : IsHazardBalance a h)
    (hne : ∀ t, h t ≠ 0) (t : ℕ) :
    (h (t + 1))⁻¹ = a * (h t)⁻¹ + -a := by
  have hcur : h t ≠ 0 := hne t
  have hnext : h (t + 1) ≠ 0 := hne (t + 1)
  have hmul : (a * (h t)⁻¹ + -a) * h (t + 1) = 1 := by
    field_simp
    linear_combination hb t
  exact inv_eq_of_mul_eq_one_left hmul

/-- The reciprocal orbit of the family, in closed form. -/
theorem IsHazardBalance.inv_eq_closedForm {a : ℝ} {h : ℕ → ℝ} (ha : 1 < a)
    (hb : IsHazardBalance a h) (hne : ∀ t, h t ≠ 0) (t : ℕ) :
    (h t)⁻¹ = a ^ t * ((h 0)⁻¹ - a / (a - 1)) + a / (a - 1) := by
  have hclosed :=
    affine_eq_closedForm (g := fun s => (h s)⁻¹) ha.ne' (hb.inv_affine hne) t
  rwa [affineFixedPoint_neg_self ha.ne'] at hclosed

/-- The orbit of the family, in closed form. At `a = 2` and `h 0 = 1 / 3` this is
`h t = (2 ^ t + 2)⁻¹`. -/
theorem IsHazardBalance.eq_closedForm {a : ℝ} {h : ℕ → ℝ} (ha : 1 < a)
    (hb : IsHazardBalance a h) (hne : ∀ t, h t ≠ 0) (t : ℕ) :
    h t = (a ^ t * ((h 0)⁻¹ - a / (a - 1)) + a / (a - 1))⁻¹ := by
  rw [← hb.inv_eq_closedForm ha hne t, inv_inv]

/-- **Admissibility ceiling.** A positive orbit of the family cannot start above
`hazardCeiling a`: seeds above it drive the reciprocal coordinate below zero in finite time. -/
theorem IsHazardBalance.le_hazardCeiling {a : ℝ} {h : ℕ → ℝ} (ha : 1 < a)
    (hb : IsHazardBalance a h) (hpos : ∀ t, 0 < h t) :
    h 0 ≤ hazardCeiling a := by
  by_contra hcon
  rw [not_le] at hcon
  have hne (t : ℕ) : h t ≠ 0 := (hpos t).ne'
  have hseed : (h 0)⁻¹ < affineFixedPoint a (-a) :=
    (hazardCeiling_lt_iff ha (hpos 0)).1 hcon
  have hzero (t : ℕ) : 0 < (h t)⁻¹ := inv_pos.2 (hpos t)
  have hlim : Tendsto (fun t => (h t)⁻¹) atTop atBot :=
    tendsto_affine_atBot ha (hb.inv_affine hne) hseed
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_lt_atBot (0 : ℝ))).exists
  exact absurd ht (hzero t).asymm

/-- The stationary orbit: the seed `hazardCeiling a` is a fixed point of the family. -/
theorem IsHazardBalance.eq_hazardCeiling {a : ℝ} {h : ℕ → ℝ} (ha : 1 < a)
    (hb : IsHazardBalance a h) (hne : ∀ t, h t ≠ 0) (h0 : h 0 = hazardCeiling a) (t : ℕ) :
    h t = hazardCeiling a := by
  have hinv : (h t)⁻¹ = affineFixedPoint a (-a) := by
    refine affine_eq_affineFixedPoint (g := fun s => (h s)⁻¹) ha.ne' (hb.inv_affine hne) ?_ t
    rw [h0, inv_hazardCeiling ha]
  rw [← inv_inv (h t), hinv, ← inv_hazardCeiling ha, inv_inv]

/-- **Classification of the vanishing solutions.** A positive orbit of the family vanishes exactly
when its seed lies strictly below the ceiling. -/
theorem IsHazardBalance.tendsto_zero_iff {a : ℝ} {h : ℕ → ℝ} (ha : 1 < a)
    (hb : IsHazardBalance a h) (hpos : ∀ t, 0 < h t) :
    Tendsto h atTop (𝓝 0) ↔ h 0 < hazardCeiling a := by
  have hne (t : ℕ) : h t ≠ 0 := (hpos t).ne'
  constructor
  · intro htend
    rcases lt_or_eq_of_le (hb.le_hazardCeiling ha hpos) with hlt | heq
    · exact hlt
    · exfalso
      have hconst : Tendsto h atTop (𝓝 (hazardCeiling a)) :=
        tendsto_const_nhds.congr fun t => (hb.eq_hazardCeiling ha hne heq t).symm
      have := tendsto_nhds_unique htend hconst
      exact absurd this.symm (hazardCeiling_pos ha).ne'
  · intro hlt
    refine (tendsto_zero_iff_tendsto_inv_atTop hpos).2 ?_
    exact tendsto_affine_atTop ha (hb.inv_affine hne)
      ((lt_hazardCeiling_iff ha (hpos 0)).1 hlt)

/-- The reciprocal orbit of the family from a seed: the affine orbit with coefficients
`(a, -a)`. -/
def hazardInvOrbit (a h₀ : ℝ) (t : ℕ) : ℝ :=
  a ^ t * (h₀⁻¹ - a / (a - 1)) + a / (a - 1)

/-- The orbit of the family from a seed, in the closed form of `IsHazardBalance.eq_closedForm`.
At `a = 2` and `h₀ = 1 / 3` this is `t ↦ (2 ^ t + 2)⁻¹`. -/
def hazardOrbit (a h₀ : ℝ) (t : ℕ) : ℝ := (hazardInvOrbit a h₀ t)⁻¹

/-- The reciprocal orbit starts at the reciprocal of the seed. -/
theorem hazardInvOrbit_zero (a h₀ : ℝ) : hazardInvOrbit a h₀ 0 = h₀⁻¹ := by
  unfold hazardInvOrbit
  ring

/-- The reciprocal orbit obeys the affine recurrence with coefficients `(a, -a)`. -/
theorem hazardInvOrbit_succ {a : ℝ} (h₀ : ℝ) (ha : a ≠ 1) (t : ℕ) :
    hazardInvOrbit a h₀ (t + 1) = a * hazardInvOrbit a h₀ t + -a := by
  have hne : a - (1 : ℝ) ≠ 0 := sub_ne_zero.mpr ha
  unfold hazardInvOrbit
  rw [pow_succ]
  field_simp
  ring

/-- Below the ceiling the reciprocal orbit stays above the affine fixed point, hence above `1`. -/
theorem one_lt_hazardInvOrbit {a h₀ : ℝ} (ha : 1 < a) (h0 : 0 < h₀)
    (hle : h₀ ≤ hazardCeiling a) (t : ℕ) : 1 < hazardInvOrbit a h₀ t := by
  have hfix : a / (a - 1) ≤ h₀⁻¹ := by
    have hstep : (hazardCeiling a)⁻¹ ≤ h₀⁻¹ :=
      (inv_le_inv₀ (hazardCeiling_pos ha) h0).2 hle
    rwa [inv_hazardCeiling ha, affineFixedPoint_neg_self ha.ne'] at hstep
  have hone : 1 < a / (a - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hpow : (0 : ℝ) < a ^ t := pow_pos (by linarith) t
  have hterm : 0 ≤ a ^ t * (h₀⁻¹ - a / (a - 1)) :=
    mul_nonneg hpow.le (by linarith)
  unfold hazardInvOrbit
  linarith

/-- The orbit starts at its seed. -/
theorem hazardOrbit_zero (a h₀ : ℝ) : hazardOrbit a h₀ 0 = h₀ := by
  rw [hazardOrbit, hazardInvOrbit_zero, inv_inv]

/-- An admissible seed gives a positive orbit. -/
theorem hazardOrbit_pos {a h₀ : ℝ} (ha : 1 < a) (h0 : 0 < h₀)
    (hle : h₀ ≤ hazardCeiling a) (t : ℕ) : 0 < hazardOrbit a h₀ t :=
  inv_pos.2 (by linarith [one_lt_hazardInvOrbit ha h0 hle t])

/-- **Realizability of the admissible seeds.** Every seed in `Set.Ioc 0 (hazardCeiling a)` carries
a positive orbit of the family; together with `IsHazardBalance.le_hazardCeiling` this pins the
admissible seeds exactly. -/
theorem isHazardBalance_hazardOrbit {a h₀ : ℝ} (ha : 1 < a) (h0 : 0 < h₀)
    (hle : h₀ ≤ hazardCeiling a) : IsHazardBalance a (hazardOrbit a h₀) := by
  intro t
  have hgt : 1 < hazardInvOrbit a h₀ t := one_lt_hazardInvOrbit ha h0 hle t
  have hsucc : hazardInvOrbit a h₀ (t + 1) = a * hazardInvOrbit a h₀ t + -a :=
    hazardInvOrbit_succ h₀ ha.ne' t
  have hane : a ≠ 0 := by linarith
  unfold hazardOrbit
  rw [hsucc]
  generalize hazardInvOrbit a h₀ t = g at hgt ⊢
  have hg0 : g ≠ 0 := by linarith
  have hg1 : g - 1 ≠ 0 := sub_ne_zero.mpr (by linarith)
  have hden : a * g + -a = a * (g - 1) := by ring
  rw [hden]
  field_simp

/-! ### The transfer-matrix reading -/

/-- Transfer matrix of `affineStep c d`, acting projectively on the affine chart of the line. -/
def affineTransferMatrix (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, d; 0, 1]

/-- Transfer matrix of `linearFractionalStep c d`. -/
def linearFractionalTransferMatrix (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; d, c]

/-- The projective involution `x ↦ x⁻¹`, as a matrix. -/
def inversionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Composition of affine steps is the product of their transfer matrices. -/
theorem affineTransferMatrix_mul (c₁ d₁ c₂ d₂ : ℝ) :
    affineTransferMatrix c₁ d₁ * affineTransferMatrix c₂ d₂ =
      affineTransferMatrix (c₁ * c₂) (c₁ * d₂ + d₁) := by
  unfold affineTransferMatrix
  rw [Matrix.mul_fin_two]
  norm_num

/-- Composition of linear-fractional steps is the product of their transfer matrices, with the
same coefficient law as `affineTransferMatrix_mul`. -/
theorem linearFractionalTransferMatrix_mul (c₁ d₁ c₂ d₂ : ℝ) :
    linearFractionalTransferMatrix c₁ d₁ * linearFractionalTransferMatrix c₂ d₂ =
      linearFractionalTransferMatrix (c₁ * c₂) (c₁ * d₂ + d₁) := by
  unfold linearFractionalTransferMatrix
  rw [Matrix.mul_fin_two]
  norm_num
  ring

/-- **The conjugacy at matrix level.** Conjugating the affine transfer matrix by the inversion
recovers the linear-fractional transfer matrix. -/
theorem inversionMatrix_conj_affineTransferMatrix (c d : ℝ) :
    inversionMatrix * affineTransferMatrix c d * inversionMatrix =
      linearFractionalTransferMatrix c d := by
  unfold inversionMatrix affineTransferMatrix linearFractionalTransferMatrix
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-- The determinant of the linear-fractional transfer matrix is its coefficient `c`. -/
theorem det_linearFractionalTransferMatrix (c d : ℝ) :
    (linearFractionalTransferMatrix c d).det = c := by
  unfold linearFractionalTransferMatrix
  rw [Matrix.det_fin_two_of]
  ring

/-- The determinant of the affine transfer matrix is its coefficient `c`. -/
theorem det_affineTransferMatrix (c d : ℝ) : (affineTransferMatrix c d).det = c := by
  unfold affineTransferMatrix
  rw [Matrix.det_fin_two_of]
  ring

/-- The linear-fractional transfer matrix as an element of `GL (Fin 2) ℝ`, available exactly when
the matrix is nonsingular. -/
def linearFractionalGL {c : ℝ} (d : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (linearFractionalTransferMatrix c d)
    (by rw [det_linearFractionalTransferMatrix]; exact hc.isUnit)

/-- `linearFractionalGL` has the expected underlying matrix. -/
@[simp] theorem coe_linearFractionalGL {c : ℝ} (d : ℝ) (hc : c ≠ 0) :
    (linearFractionalGL d hc : Matrix (Fin 2) (Fin 2) ℝ) =
      linearFractionalTransferMatrix c d := rfl

/-- **Action compatibility.** On the affine chart, and away from the pole, the Möbius action
`OnePoint.instGLAction` of the transfer matrix is the linear-fractional step. -/
theorem linearFractionalGL_smul_coe {c d x : ℝ} (hc : c ≠ 0) (hden : c + d * x ≠ 0) :
    linearFractionalGL d hc • (x : OnePoint ℝ) =
      ((linearFractionalStep c d x : ℝ) : OnePoint ℝ) := by
  have h00 : (linearFractionalGL d hc) 0 0 = 1 := rfl
  have h01 : (linearFractionalGL d hc) 0 1 = 0 := rfl
  have h10 : (linearFractionalGL d hc) 1 0 = d := rfl
  have h11 : (linearFractionalGL d hc) 1 1 = c := rfl
  rw [OnePoint.smul_some_eq_ite, h00, h01, h10, h11,
    if_neg (by rw [add_comm]; exact hden), linearFractionalStep_apply]
  ring_nf

/-- The transfer matrices of a coefficient cycle multiply. -/
theorem linearFractionalGL_mul {c₁ c₂ : ℝ} (d₁ d₂ : ℝ) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    linearFractionalGL d₁ h₁ * linearFractionalGL d₂ h₂ =
      linearFractionalGL (c := c₁ * c₂) (c₁ * d₂ + d₁) (mul_ne_zero h₁ h₂) := by
  refine Units.ext ?_
  change linearFractionalTransferMatrix c₁ d₁ * linearFractionalTransferMatrix c₂ d₂ = _
  rw [linearFractionalTransferMatrix_mul]
  rfl

/-- **The cocycle reading.** A two-phase coefficient cycle acts by the product transfer matrix,
everywhere on `OnePoint ℝ` and with no pole hypothesis; so periodic orbits of the cycle are the
fixed points of the product. -/
theorem linearFractionalGL_cycle_smul {c₁ c₂ : ℝ} (d₁ d₂ : ℝ) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (z : OnePoint ℝ) :
    linearFractionalGL d₁ h₁ • (linearFractionalGL d₂ h₂ • z) =
      linearFractionalGL (c := c₁ * c₂) (c₁ * d₂ + d₁) (mul_ne_zero h₁ h₂) • z := by
  rw [← mul_smul, linearFractionalGL_mul]

/-! ### `n`-phase cycles and the discriminant classification -/

/-- The slope of an `n`-phase affine coefficient cycle: the product of the individual slopes. -/
def affineCycleSlope (l : List (ℝ × ℝ)) : ℝ := (l.map Prod.fst).prod

/-- The shift of an `n`-phase affine coefficient cycle, accumulated by Horner's rule. -/
def affineCycleShift : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (c, d) :: l => c * affineCycleShift l + d

/-- The composite of an `n`-phase cycle of affine steps, the head applied last. -/
def affineCycleStep : List (ℝ × ℝ) → ℝ → ℝ
  | [], x => x
  | (c, d) :: l, x => affineStep c d (affineCycleStep l x)

/-- The product transfer matrix of an `n`-phase affine coefficient cycle. -/
def affineCycleMatrix (l : List (ℝ × ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  (l.map fun p => affineTransferMatrix p.1 p.2).prod

/-- The slope of a cycle is multiplicative over concatenation. -/
theorem affineCycleSlope_cons (c d : ℝ) (l : List (ℝ × ℝ)) :
    affineCycleSlope ((c, d) :: l) = c * affineCycleSlope l := by
  simp [affineCycleSlope]

/-- **The `n`-phase product transfer matrix.** A product of affine transfer matrices is again
one, with the cycle's slope and shift as coefficients. -/
theorem affineCycleMatrix_eq (l : List (ℝ × ℝ)) :
    affineCycleMatrix l = affineTransferMatrix (affineCycleSlope l) (affineCycleShift l) := by
  induction l with
  | nil =>
      simp [affineCycleMatrix, affineCycleSlope, affineCycleShift, affineTransferMatrix,
        Matrix.one_fin_two]
  | cons p l ih =>
      obtain ⟨c, d⟩ := p
      rw [affineCycleMatrix, List.map_cons, List.prod_cons, ← affineCycleMatrix, ih,
        affineTransferMatrix_mul, affineCycleSlope_cons]
      rfl

/-- **The composite of a cycle of affine steps** is the affine step of the cycle's slope and
shift; this is the scalar shadow of `affineCycleMatrix_eq`. -/
theorem affineCycleStep_eq (l : List (ℝ × ℝ)) (x : ℝ) :
    affineCycleStep l x = affineStep (affineCycleSlope l) (affineCycleShift l) x := by
  induction l with
  | nil => simp [affineCycleStep, affineStep, affineCycleSlope, affineCycleShift]
  | cons p l ih =>
      obtain ⟨c, d⟩ := p
      rw [affineCycleStep, ih, affineStep_comp, affineCycleSlope_cons]
      rfl

/-- The determinant of the product transfer matrix of an affine cycle is the cycle's slope. -/
theorem det_affineCycleMatrix (l : List (ℝ × ℝ)) :
    (affineCycleMatrix l).det = affineCycleSlope l := by
  rw [affineCycleMatrix_eq, det_affineTransferMatrix]

/-- The trace of the product transfer matrix of an affine cycle is the cycle's slope plus one. -/
theorem trace_affineCycleMatrix (l : List (ℝ × ℝ)) :
    (affineCycleMatrix l).trace = affineCycleSlope l + 1 := by
  rw [affineCycleMatrix_eq, affineTransferMatrix, Matrix.trace_fin_two_of]

/-- The discriminant `trace ^ 2 - 4 * det` of a `2 × 2` matrix, whose sign classifies the fixed
points of the induced projective action. -/
def projectiveDiscriminant (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M.trace ^ 2 - 4 * M.det

/-- A matrix is *hyperbolic* when its projective action has two real fixed points, that is when
the discriminant is positive. -/
def IsProjectiveHyperbolic (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := 0 < projectiveDiscriminant M

/-- A matrix is *parabolic* when its projective action has a single real fixed point, that is when
the discriminant vanishes. -/
def IsProjectiveParabolic (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := projectiveDiscriminant M = 0

/-- A matrix is *elliptic* when its projective action has no real fixed point, that is when the
discriminant is negative. -/
def IsProjectiveElliptic (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := projectiveDiscriminant M < 0

/-- **Trichotomy of the projective classification.** Every `2 × 2` real matrix is hyperbolic,
parabolic or elliptic. -/
theorem isProjectiveHyperbolic_or_parabolic_or_elliptic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsProjectiveHyperbolic M ∨ IsProjectiveParabolic M ∨ IsProjectiveElliptic M := by
  rcases lt_trichotomy (projectiveDiscriminant M) 0 with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- The three cases of the classification are mutually exclusive. -/
theorem IsProjectiveHyperbolic.not_parabolic {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : IsProjectiveHyperbolic M) : ¬ IsProjectiveParabolic M := h.ne'

/-- A hyperbolic matrix is not elliptic. -/
theorem IsProjectiveHyperbolic.not_elliptic {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : IsProjectiveHyperbolic M) : ¬ IsProjectiveElliptic M := asymm h

/-- A parabolic matrix is not elliptic. -/
theorem IsProjectiveParabolic.not_elliptic {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : IsProjectiveParabolic M) : ¬ IsProjectiveElliptic M := by
  rw [IsProjectiveElliptic, h]
  exact lt_irrefl 0

/-- **The discriminant of an affine cycle is a square.** It is the square of the defect of the
slope product from `1`. -/
theorem projectiveDiscriminant_affineCycleMatrix (l : List (ℝ × ℝ)) :
    projectiveDiscriminant (affineCycleMatrix l) = (affineCycleSlope l - 1) ^ 2 := by
  rw [projectiveDiscriminant, trace_affineCycleMatrix, det_affineCycleMatrix]
  ring

/-- **An affine cycle is never elliptic.** The elliptic case of the projective classification is
unreachable by products of affine transfer matrices, whatever the number of phases: their
discriminant is a square. Ellipticity needs a matrix of negative determinant, such as
`inversionMatrix`. -/
theorem not_isProjectiveElliptic_affineCycleMatrix (l : List (ℝ × ℝ)) :
    ¬ IsProjectiveElliptic (affineCycleMatrix l) := by
  rw [IsProjectiveElliptic, projectiveDiscriminant_affineCycleMatrix]
  exact not_lt.2 (sq_nonneg _)

/-- **An affine cycle is hyperbolic exactly when its slope product differs from one.** -/
theorem isProjectiveHyperbolic_affineCycleMatrix_iff (l : List (ℝ × ℝ)) :
    IsProjectiveHyperbolic (affineCycleMatrix l) ↔ affineCycleSlope l ≠ 1 := by
  rw [IsProjectiveHyperbolic, projectiveDiscriminant_affineCycleMatrix]
  constructor
  · intro h hval
    rw [hval] at h
    norm_num at h
  · intro h
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr h)))

/-- **An affine cycle is parabolic exactly when its slope product is one.** -/
theorem isProjectiveParabolic_affineCycleMatrix_iff (l : List (ℝ × ℝ)) :
    IsProjectiveParabolic (affineCycleMatrix l) ↔ affineCycleSlope l = 1 := by
  rw [IsProjectiveParabolic, projectiveDiscriminant_affineCycleMatrix, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]

/-- **Periodic orbits of a hyperbolic affine cycle.** When the slope product is not `1` the cycle
returns a seed to itself exactly at the composite's unique fixed point. -/
theorem affineCycleStep_eq_self_iff_of_slope_ne_one {l : List (ℝ × ℝ)}
    (hs : affineCycleSlope l ≠ 1) (x : ℝ) :
    affineCycleStep l x = x ↔ x = affineFixedPoint (affineCycleSlope l) (affineCycleShift l) := by
  have hne : (1 : ℝ) - affineCycleSlope l ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [affineCycleStep_eq, affineStep_apply, affineFixedPoint]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Periodic orbits of a parabolic affine cycle.** When the slope product is `1` the cycle is a
translation: it returns every seed if the shift vanishes, and none otherwise. -/
theorem affineCycleStep_eq_self_iff_of_slope_one {l : List (ℝ × ℝ)}
    (hs : affineCycleSlope l = 1) (x : ℝ) :
    affineCycleStep l x = x ↔ affineCycleShift l = 0 := by
  rw [affineCycleStep_eq, affineStep_apply, hs, one_mul]
  constructor
  · intro h; linarith
  · intro h; rw [h, add_zero]

/-- **The periodic seed of a hyperbolic cycle is fixed by every iterate**, so the orbit of the
`n`-phase recurrence through it is genuinely periodic with period dividing the cycle length. -/
theorem affineCycleStep_iterate_affineFixedPoint {l : List (ℝ × ℝ)}
    (hs : affineCycleSlope l ≠ 1) (t : ℕ) :
    (affineCycleStep l)^[t] (affineFixedPoint (affineCycleSlope l) (affineCycleShift l)) =
      affineFixedPoint (affineCycleSlope l) (affineCycleShift l) :=
  Function.iterate_fixed ((affineCycleStep_eq_self_iff_of_slope_ne_one hs _).2 rfl) t

end DirectedTransport.InverseCoordinate

end
