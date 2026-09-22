/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.SensorNetwork
public import Maths.Multitubes.FiniteInequality.Quantitative
public import Maths.Multitubes.FiniteInequality.Parametric

import Mathlib.Topology.Order.Monotone
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin

/-!
# Optimal uniform sensor tolerance

Finite affine sensor comparisons admit a least nonnegative uniform tolerance, even when their
consistent readings are unbounded. Fixed-normal feasibility is closed in the tolerance, and
the zero reading is feasible at a sufficiently large tolerance. Normalized balanced combinations
of the signed measurement rows characterize feasibility and certify optimality.

The triangle with offsets zero, zero, and one has optimal uniform tolerance one third. A reading
attains this value, and a balanced combination of its three forward rows rules out every smaller
tolerance.

## Main definitions

* `CellularSheaves.RationalSensorNetwork.uniformToleranceLevels`: nonnegative tolerances that
  admit consistent real readings.
* `CellularSheaves.RationalSensorNetwork.minimumUniformTolerance`: the least such tolerance.

## Main results

* `CellularSheaves.RationalSensorNetwork.uniformTolerance_iff_normalizedDual`: exact dual
  characterization of uniform consistency.
* `CellularSheaves.RationalSensorNetwork.isLeast_minimumUniformTolerance`: the minimum is
  attained, including for networks without edges.
* `CellularSheaves.RationalSensorNetwork.isLeast_uniformTolerance_of_certificate`: matching
  primal and normalized dual witnesses certify the minimum.
* `CellularSheaves.minimumUniformTolerance_triangle`: the triangle's optimal tolerance is
  exactly one third.

## Tags

sensor consistency, uniform tolerance, optimization, Farkas certificate, graph sheaf
-/

@[expose] public section

noncomputable section

namespace CellularSheaves.RationalSensorNetwork

open Maths.FiniteInequality
open scoped BigOperators

variable {n m : ℕ}

/-- The signed sensor matrix interpreted over the real numbers. -/
def realMatrix (network : RationalSensorNetwork n m) : Fin (m + m) → Fin n → ℝ :=
  fun row coordinate => network.matrix row coordinate

/-- The signed measurement offsets interpreted over the real numbers. -/
def realOffset (network : RationalSensorNetwork n m) : Fin (m + m) → ℝ :=
  fun row => network.signedOffset row

/-- Nonnegative uniform tolerances that admit a consistent reading. -/
def uniformToleranceLevels (network : RationalSensorNetwork n m) : Set ℝ :=
  {level | 0 ≤ level ∧ ∃ reading, network.IsConsistent (fun _ => level) reading}

/-- Uniform consistency is the worst-residual problem for the two signed measurement rows. -/
theorem exists_uniformlyConsistent_iff_worstResidual (network : RationalSensorNetwork n m)
    (level : ℝ) :
    (∃ reading, network.IsConsistent (fun _ => level) reading) ↔
      WorstResidualAtMost network.realMatrix network.realOffset level := by
  constructor
  · rintro ⟨reading, hreading⟩
    have hrows := (network.isConsistent_iff_realRowInequalities _ _).mp hreading
    refine ⟨reading, fun row => ?_⟩
    have hrow := hrows row
    change network.realOffset row - level ≤ dotProduct (network.realMatrix row) reading at hrow
    linarith
  · rintro ⟨reading, hreading⟩
    refine ⟨reading, (network.isConsistent_iff_realRowInequalities _ _).mpr fun row => ?_⟩
    have hrow := hreading row
    change network.realOffset row - level ≤ dotProduct (network.realMatrix row) reading
    linarith

/-- Uniform consistency holds exactly when every normalized balanced row value is below the
proposed tolerance. -/
theorem uniformTolerance_iff_normalizedDual (network : RationalSensorNetwork n m)
    (level : ℝ) :
    level ∈ network.uniformToleranceLevels ↔
      0 ≤ level ∧ ∀ coefficient,
        IsNormalizedCertificate network.realMatrix coefficient →
          certificateValue network.realOffset coefficient ≤ level := by
  simp only [uniformToleranceLevels, Set.mem_ofPred_eq,
    network.exists_uniformlyConsistent_iff_worstResidual,
    worstResidualAtMost_iff_normalizedDual_le]

/-- Uniform tolerance feasibility is closed without a boundedness assumption on the readings. -/
theorem isClosed_uniformToleranceLevels (network : RationalSensorNetwork n m) :
    IsClosed network.uniformToleranceLevels := by
  have heq : network.uniformToleranceLevels = Set.Ici 0 ∩
      feasibleParameters network.realMatrix
        (fun level row => network.realOffset row - level) := by
    ext level
    constructor
    · rintro ⟨hnonneg, reading, hreading⟩
      exact ⟨hnonneg, reading,
        (network.isConsistent_iff_realRowInequalities _ _).mp hreading⟩
    · rintro ⟨hnonneg, reading, hreading⟩
      exact ⟨hnonneg, reading,
        (network.isConsistent_iff_realRowInequalities _ _).mpr hreading⟩
  rw [heq]
  exact isClosed_Ici.inter (isClosed_feasibleParameters _ _ fun _ =>
    continuous_const.sub continuous_id)

/-- The zero reading is consistent at the sum of the absolute measurement offsets. -/
theorem uniformToleranceLevels_nonempty (network : RationalSensorNetwork n m) :
    network.uniformToleranceLevels.Nonempty := by
  refine ⟨∑ edge, |(network.offset edge : ℝ)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), (fun _ => 0), fun edge => ?_⟩
  have hle : |(network.offset edge : ℝ)| ≤ ∑ other, |(network.offset other : ℝ)| :=
    Finset.single_le_sum (f := fun other : Fin m => |(network.offset other : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ edge)
  simpa [sheaf] using hle

/-- The infimum of feasible nonnegative uniform sensor tolerances. -/
def minimumUniformTolerance (network : RationalSensorNetwork n m) : ℝ :=
  sInf network.uniformToleranceLevels

/-- Every finite affine sensor network has an attained least nonnegative uniform tolerance. -/
theorem isLeast_minimumUniformTolerance (network : RationalSensorNetwork n m) :
    IsLeast network.uniformToleranceLevels network.minimumUniformTolerance :=
  network.isClosed_uniformToleranceLevels.isLeast_csInf
    network.uniformToleranceLevels_nonempty ⟨0, fun _ hlevel => hlevel.1⟩

/-- A real sensor reading attains the minimum tolerance. -/
theorem exists_isConsistent_minimumUniformTolerance (network : RationalSensorNetwork n m) :
    ∃ reading, network.IsConsistent (fun _ => network.minimumUniformTolerance) reading :=
  network.isLeast_minimumUniformTolerance.1.2

/-- Increasing the uniform tolerance preserves feasibility. -/
theorem mem_uniformToleranceLevels_of_le (network : RationalSensorNetwork n m)
    {level other : ℝ} (hlevel : level ∈ network.uniformToleranceLevels) (hle : level ≤ other) :
    other ∈ network.uniformToleranceLevels := by
  obtain ⟨hnonneg, reading, hreading⟩ := hlevel
  exact ⟨hnonneg.trans hle, reading, fun edge => (hreading edge).trans hle⟩

/-- Feasible nonnegative uniform tolerances form the closed ray beginning at the minimum. -/
theorem uniformToleranceLevels_eq_Ici (network : RationalSensorNetwork n m) :
    network.uniformToleranceLevels = Set.Ici network.minimumUniformTolerance := by
  ext level
  exact ⟨fun hlevel => network.isLeast_minimumUniformTolerance.2 hlevel, fun hlevel =>
    network.mem_uniformToleranceLevels_of_le network.isLeast_minimumUniformTolerance.1 hlevel⟩

/-- A consistent assignment and a normalized dual witness of the same value certify optimal
uniform tolerance. -/
theorem isLeast_uniformTolerance_of_certificate (network : RationalSensorNetwork n m)
    {level : ℝ} (hnonneg : 0 ≤ level) {reading : Fin n → ℝ}
    (hreading : network.IsConsistent (fun _ => level) reading)
    {coefficient : Fin (m + m) → ℝ}
    (hcertificate : IsNormalizedCertificate network.realMatrix coefficient)
    (hvalue : certificateValue network.realOffset coefficient = level) :
    IsLeast network.uniformToleranceLevels level := by
  refine ⟨⟨hnonneg, reading, hreading⟩, fun other hother => ?_⟩
  have hdual := (network.uniformTolerance_iff_normalizedDual other).mp hother
  simpa only [hvalue] using hdual.2 coefficient hcertificate

end CellularSheaves.RationalSensorNetwork

namespace CellularSheaves

open Maths.FiniteInequality
open scoped BigOperators

/-- The three forward triangle rows, each with normalized mass one third. -/
def triangleNormalizedCertificate (row : Fin 6) : ℝ := (triangleCertificate row : ℝ) / 3

/-- The normalized triangle weights are nonnegative, balanced, and have total mass one. -/
theorem triangleNormalizedCertificate_valid :
    IsNormalizedCertificate triangleNetwork.realMatrix triangleNormalizedCertificate := by
  have hcheck := (Maths.LinearProgramming.checkRationalCertificate_eq_true_iff
    triangleNetwork.matrix (triangleNetwork.base (fun _ => 0)) triangleCertificate).mp
      triangleCertificate_check
  have hmassQ : (∑ row, triangleCertificate row) = 3 := by
    rw [← Equiv.sum_comp (RationalSensorNetwork.rowEquiv (m := 3))]
    norm_num [triangleCertificate, RationalSensorNetwork.row, Fin.sum_univ_three]
  have hmassR : (∑ row, (triangleCertificate row : ℝ)) = 3 := by exact_mod_cast hmassQ
  refine ⟨fun row => div_nonneg (Rat.cast_nonneg.mpr (hcheck.1 row)) (by norm_num), ?_, ?_⟩
  · simp only [triangleNormalizedCertificate, ← Finset.sum_div, hmassR]
    norm_num
  · intro coordinate
    have hbalance :
        (∑ row, (triangleCertificate row : ℝ) * triangleNetwork.realMatrix row coordinate) = 0 := by
      have hcast := congrArg (fun value : ℚ => (value : ℝ)) (hcheck.2.1 coordinate)
      simpa only [RationalSensorNetwork.realMatrix, Rat.cast_sum, Rat.cast_mul,
        Rat.cast_zero] using hcast
    simp only [triangleNormalizedCertificate, div_mul_eq_mul_div, ← Finset.sum_div,
      hbalance, zero_div]

/-- The triangle's normalized obstruction has value one third. -/
theorem triangleNormalizedCertificate_value :
    certificateValue triangleNetwork.realOffset triangleNormalizedCertificate = 1 / 3 := by
  have hvalueQ : (∑ row, triangleCertificate row * triangleNetwork.signedOffset row) = 1 := by
    rw [← Equiv.sum_comp (RationalSensorNetwork.rowEquiv (m := 3))]
    norm_num [triangleCertificate, RationalSensorNetwork.signedOffset,
      RationalSensorNetwork.rowSign, RationalSensorNetwork.rowEdge, RationalSensorNetwork.row,
      triangleNetwork, Fin.sum_univ_three]
  have hvalueR :
      (∑ row, (triangleCertificate row : ℝ) * triangleNetwork.realOffset row) = 1 := by
    dsimp [RationalSensorNetwork.realOffset]
    exact_mod_cast hvalueQ
  simp only [certificateValue, triangleNormalizedCertificate, div_mul_eq_mul_div,
    ← Finset.sum_div, hvalueR]

/-- The triangle admits tolerance one third and no smaller nonnegative uniform tolerance. -/
theorem isLeast_uniformTolerance_triangle :
    IsLeast triangleNetwork.uniformToleranceLevels (1 / 3) := by
  obtain ⟨reading, hreading⟩ := exists_triangle_isConsistent_one_third
  exact triangleNetwork.isLeast_uniformTolerance_of_certificate (by norm_num) hreading
    triangleNormalizedCertificate_valid triangleNormalizedCertificate_value

/-- The optimal uniform tolerance for the inconsistent measurement triangle is one third. -/
theorem minimumUniformTolerance_triangle : triangleNetwork.minimumUniformTolerance = 1 / 3 :=
  triangleNetwork.isLeast_minimumUniformTolerance.unique isLeast_uniformTolerance_triangle

end CellularSheaves
