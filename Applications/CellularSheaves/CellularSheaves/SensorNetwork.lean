/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.GraphSheaf
public import Maths.Multitubes.FiniteInequality.CertificateCheck
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Rational sensor-network consistency

A sensor network compares affine calibrations at the endpoints of each directed edge.  Exact
agreement is a global section of a real graph sheaf.  Allowing an edgewise tolerance produces two
signed linear inequalities per edge, so rational assignments and Farkas certificates can be
checked by exact computation and transferred soundly to real consistency or inconsistency.

The signed rows are ordered as the positive residual rows followed by their negatives.  For an
edge `e`, the positive row is
`targetScale e * x(target e) - sourceScale e * x(source e) >= offset e - tolerance e`.

## Main definitions

* `CellularSheaves.RationalSensorNetwork`: rational affine sensor-comparison data.
* `CellularSheaves.RationalSensorNetwork.sheaf`: its real graph sheaf.
* `CellularSheaves.RationalSensorNetwork.IsConsistent`: edgewise tolerant consistency.
* `CellularSheaves.RationalSensorNetwork.matrix` and
  `CellularSheaves.RationalSensorNetwork.base`: the signed rational inequality system.
* `CellularSheaves.RationalSensorNetwork.checkAssignment` and
  `CellularSheaves.RationalSensorNetwork.checkCertificate`: executable witness checkers.

## Main results

* `CellularSheaves.RationalSensorNetwork.isConsistent_zero_iff_isCompatible`: zero tolerance is
  exact graph-sheaf compatibility.
* `CellularSheaves.RationalSensorNetwork.isConsistent_iff_realRowInequalities`: tolerant
  consistency is exactly the signed real inequality system.
* `CellularSheaves.RationalSensorNetwork.isConsistent_of_checkAssignment`: a checked rational
  assignment is a real consistent assignment.
* `CellularSheaves.RationalSensorNetwork.not_exists_isConsistent_of_checkCertificate`: a checked
  certificate proves real inconsistency.
* `CellularSheaves.triangleReading_check` and
  `CellularSheaves.triangleCertificate_check`: exact witnesses for the inconsistent triangle.

## Tags

cellular sheaf, sensor network, consistency, rational arithmetic, Farkas certificate
-/

@[expose] public section

namespace CellularSheaves

open Finset

/-- Rational affine comparisons on a finite directed sensor network. -/
structure RationalSensorNetwork (n m : ℕ) where
  /-- Source sensor of each comparison. -/
  source : Fin m → Fin n
  /-- Target sensor of each comparison. -/
  target : Fin m → Fin n
  /-- Scale applied to the source reading. -/
  sourceScale : Fin m → ℚ
  /-- Scale applied to the target reading. -/
  targetScale : Fin m → ℚ
  /-- Offset added to the scaled source reading. -/
  offset : Fin m → ℚ

namespace RationalSensorNetwork

variable {n m : ℕ}

/-! ## Main definitions -/

/-- The finite directed graph underlying a rational sensor network. -/
def graph (network : RationalSensorNetwork n m) : Maths.EdgeGraph (Fin n) (Fin m) where
  source := network.source
  target := network.target

/-- The real graph sheaf whose edge agreement is affine sensor consistency. -/
def sheaf (network : RationalSensorNetwork n m) : GraphSheaf network.graph where
  VertexStalk := fun _ => ℝ
  EdgeStalk := fun _ => ℝ
  sourceRestriction edge reading :=
    (network.sourceScale edge : ℝ) * reading + network.offset edge
  targetRestriction edge reading := (network.targetScale edge : ℝ) * reading

/-- A real reading is consistent within the specified nonuniform edge tolerances. -/
def IsConsistent (network : RationalSensorNetwork n m) (tolerance : Fin m → ℝ)
    (reading : Fin n → ℝ) : Prop :=
  ∀ edge, |(network.targetScale edge : ℝ) * reading (network.target edge) -
    ((network.sourceScale edge : ℝ) * reading (network.source edge) + network.offset edge)| ≤
      tolerance edge

/-- The two signs used to encode an absolute-value constraint as two linear rows. -/
def rowEquiv : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv

/-- Decode a row as a positive or negative copy of an edge constraint. -/
def row (index : Fin (m + m)) : Fin m ⊕ Fin m := rowEquiv.symm index

/-- The edge underlying either signed copy of a row. -/
def rowEdge (index : Fin (m + m)) : Fin m := Sum.elim id id (row index)

/-- The sign of a row: `1` on the first copy and `-1` on the second. -/
def rowSign (index : Fin (m + m)) : ℚ := Sum.elim (fun _ => 1) (fun _ => -1) (row index)

/-- Rational signed coefficient matrix of the tolerant consistency constraints. -/
def matrix (network : RationalSensorNetwork n m) : Fin (m + m) → Fin n → ℚ :=
  fun index coordinate => rowSign index *
    ((if coordinate = network.target (rowEdge index) then
        network.targetScale (rowEdge index) else 0) -
      if coordinate = network.source (rowEdge index) then
        network.sourceScale (rowEdge index) else 0)

/-- The signed offset before an edge tolerance is subtracted. -/
def signedOffset (network : RationalSensorNetwork n m) : Fin (m + m) → ℚ :=
  fun index => rowSign index * network.offset (rowEdge index)

/-- Rational right-hand side at the specified edge tolerances. -/
def base (network : RationalSensorNetwork n m) (tolerance : Fin m → ℚ) :
    Fin (m + m) → ℚ :=
  fun index => network.signedOffset index - tolerance (rowEdge index)

/-- The coefficientwise-real signed row inequalities. -/
def RealRowInequalities (network : RationalSensorNetwork n m) (tolerance : Fin m → ℝ)
    (reading : Fin n → ℝ) : Prop :=
  ∀ index, (network.signedOffset index : ℝ) - tolerance (rowEdge index) ≤
    dotProduct
      (fun coordinate => (network.matrix index coordinate : ℝ)) reading

/-- Check a proposed rational sensor assignment by exact arithmetic. -/
def checkAssignment (network : RationalSensorNetwork n m) (tolerance : Fin m → ℚ)
    (reading : Fin n → ℚ) : Bool :=
  Maths.LinearProgramming.checkRationalPoint network.matrix (network.base tolerance) reading

/-- Check proposed rational Farkas row weights by exact arithmetic. -/
def checkCertificate (network : RationalSensorNetwork n m) (tolerance : Fin m → ℚ)
    (coefficient : Fin (m + m) → ℚ) : Bool :=
  Maths.LinearProgramming.checkRationalCertificate network.matrix (network.base tolerance)
    coefficient

private theorem rowEquiv_apply (candidate : Fin m ⊕ Fin m) :
    row (rowEquiv candidate) = candidate := by
  simp [row]

private theorem rowEval (network : RationalSensorNetwork n m) (reading : Fin n → ℚ)
    (candidate : Fin m ⊕ Fin m) :
    Maths.LinearProgramming.rowEval network.matrix (rowEquiv candidate) reading =
      Sum.elim (fun edge =>
          network.targetScale edge * reading (network.target edge) -
            network.sourceScale edge * reading (network.source edge))
        (fun edge => -(
          network.targetScale edge * reading (network.target edge) -
            network.sourceScale edge * reading (network.source edge))) candidate := by
  classical
  obtain edge | edge := candidate <;>
    simp [Maths.LinearProgramming.rowEval, matrix, rowSign, rowEdge, rowEquiv_apply,
      sub_mul, Finset.sum_sub_distrib]

private theorem realRowEval (network : RationalSensorNetwork n m) (reading : Fin n → ℝ)
    (candidate : Fin m ⊕ Fin m) :
    dotProduct
        (fun coordinate => (network.matrix (rowEquiv candidate) coordinate : ℝ)) reading =
      Sum.elim (fun edge =>
          (network.targetScale edge : ℝ) * reading (network.target edge) -
            (network.sourceScale edge : ℝ) * reading (network.source edge))
        (fun edge => -(
          (network.targetScale edge : ℝ) * reading (network.target edge) -
            (network.sourceScale edge : ℝ) * reading (network.source edge))) candidate := by
  classical
  obtain edge | edge := candidate
  · have htarget (coordinate : Fin n) :
        ((if coordinate = network.target edge then network.targetScale edge else 0 : ℚ) : ℝ) =
          if coordinate = network.target edge then (network.targetScale edge : ℝ) else 0 := by
      by_cases h : coordinate = network.target edge <;> simp [h]
    have hsource (coordinate : Fin n) :
        ((if coordinate = network.source edge then network.sourceScale edge else 0 : ℚ) : ℝ) =
          if coordinate = network.source edge then (network.sourceScale edge : ℝ) else 0 := by
      by_cases h : coordinate = network.source edge <;> simp [h]
    simp [dotProduct, matrix, rowSign, rowEdge, rowEquiv_apply, htarget, hsource,
      one_mul, sub_mul, Finset.sum_sub_distrib]
  · have htarget (coordinate : Fin n) :
        ((if coordinate = network.target edge then network.targetScale edge else 0 : ℚ) : ℝ) =
          if coordinate = network.target edge then (network.targetScale edge : ℝ) else 0 := by
      by_cases h : coordinate = network.target edge <;> simp [h]
    have hsource (coordinate : Fin n) :
        ((if coordinate = network.source edge then network.sourceScale edge else 0 : ℚ) : ℝ) =
          if coordinate = network.source edge then (network.sourceScale edge : ℝ) else 0 := by
      by_cases h : coordinate = network.source edge <;> simp [h]
    simp [dotProduct, matrix, rowSign, rowEdge, rowEquiv_apply, htarget, hsource,
      neg_mul, sub_mul, Finset.sum_sub_distrib]

/-! ## Main results -/

/-- Zero-tolerance consistency is exactly compatibility of the associated graph sheaf. -/
theorem isConsistent_zero_iff_isCompatible (network : RationalSensorNetwork n m)
    (reading : Fin n → ℝ) :
    network.IsConsistent (fun _ => 0) reading ↔ network.sheaf.IsCompatible reading := by
  constructor
  · intro h edge
    have hedge := h edge
    have hzero : (network.targetScale edge : ℝ) * reading (network.target edge) -
        ((network.sourceScale edge : ℝ) * reading (network.source edge) +
          network.offset edge) = 0 :=
      abs_eq_zero.mp (le_antisymm hedge (abs_nonneg _))
    change (network.sourceScale edge : ℝ) * reading (network.source edge) +
      network.offset edge = (network.targetScale edge : ℝ) * reading (network.target edge)
    linarith
  · intro h edge
    have hedge := h edge
    dsimp [sheaf] at hedge
    simp [graph] at hedge
    change |(network.targetScale edge : ℝ) * reading (network.target edge) -
      ((network.sourceScale edge : ℝ) * reading (network.source edge) +
        network.offset edge)| ≤ 0
    rw [hedge]
    simp

/-- Tolerant consistency is exactly satisfaction of all signed real row inequalities. -/
theorem isConsistent_iff_realRowInequalities (network : RationalSensorNetwork n m)
    (tolerance : Fin m → ℝ) (reading : Fin n → ℝ) :
    network.IsConsistent tolerance reading ↔ network.RealRowInequalities tolerance reading := by
  constructor
  · intro h index
    obtain ⟨candidate, rfl⟩ := rowEquiv.surjective index
    obtain edge | edge := candidate
    · rw [realRowEval]
      have hedge := (abs_le.mp (h edge)).1
      simp only [signedOffset, rowEquiv_apply, rowSign, rowEdge, Sum.elim_inl,
        one_mul, id_eq]
      linarith
    · rw [realRowEval]
      have hedge := (abs_le.mp (h edge)).2
      simp only [signedOffset, rowEquiv_apply, rowSign, rowEdge, Sum.elim_inr,
        Rat.cast_neg, neg_mul, id_eq]
      norm_num at hedge ⊢
      linarith
  · intro h edge
    apply abs_le.mpr
    constructor
    · have hrow := h (rowEquiv (.inl edge))
      rw [realRowEval] at hrow
      simp only [signedOffset, rowEquiv_apply, rowSign, rowEdge, Sum.elim_inl,
        one_mul, id_eq] at hrow
      norm_num at hrow ⊢
      linarith
    · have hrow := h (rowEquiv (.inr edge))
      rw [realRowEval] at hrow
      simp only [signedOffset, rowEquiv_apply, rowSign, rowEdge, Sum.elim_inr,
        Rat.cast_neg, neg_mul, id_eq] at hrow
      norm_num at hrow ⊢
      linarith

/-- A checked rational assignment becomes a real consistent assignment after casting. -/
theorem isConsistent_of_checkAssignment (network : RationalSensorNetwork n m)
    (tolerance : Fin m → ℚ) (reading : Fin n → ℚ)
    (hcheck : network.checkAssignment tolerance reading = true) :
    network.IsConsistent (fun edge => (tolerance edge : ℝ))
      (fun vertex => (reading vertex : ℝ)) := by
  rw [network.isConsistent_iff_realRowInequalities]
  intro index
  have hrow := Maths.FiniteInequality.realPotential_of_checkRationalPoint
    network.matrix (network.base tolerance) reading hcheck index
  simpa [base, Rat.cast_sub] using hrow

/-- A checked Farkas certificate rules out every real assignment within the cast tolerances. -/
theorem not_exists_isConsistent_of_checkCertificate (network : RationalSensorNetwork n m)
    (tolerance : Fin m → ℚ) (coefficient : Fin (m + m) → ℚ)
    (hcheck : network.checkCertificate tolerance coefficient = true) :
    ¬∃ reading : Fin n → ℝ,
      network.IsConsistent (fun edge => (tolerance edge : ℝ)) reading := by
  intro hexists
  apply Maths.FiniteInequality.not_realPotential_of_checkRationalCertificate
    network.matrix (network.base tolerance) coefficient hcheck
  obtain ⟨reading, hreading⟩ := hexists
  refine ⟨reading, fun index => ?_⟩
  have hrow := (network.isConsistent_iff_realRowInequalities _ _).mp hreading index
  simpa [base, Rat.cast_sub] using hrow

end RationalSensorNetwork

/-! ## Main results -/

/-- Three unit-scale sensors on a directed triangle whose last comparison has offset one. -/
def triangleNetwork : RationalSensorNetwork 3 3 where
  source := ![0, 1, 2]
  target := ![1, 2, 0]
  sourceScale := fun _ => 1
  targetScale := fun _ => 1
  offset := ![0, 0, 1]

/-- A rational reading whose three residual magnitudes are all `1 / 3`. -/
def triangleReading : Fin 3 → ℚ := ![0, -1 / 3, -2 / 3]

/-- Unit weights on the three positive rows form the zero-tolerance contradiction certificate. -/
def triangleCertificate (index : Fin 6) : ℚ :=
  match RationalSensorNetwork.row (m := 3) index with
  | .inl _ => 1
  | .inr _ => 0

/-- The exact checker accepts the balanced reading at uniform tolerance `1 / 3`. -/
theorem triangleReading_check :
    triangleNetwork.checkAssignment (fun _ => 1 / 3) triangleReading = true := by
  apply (Maths.LinearProgramming.checkRationalPoint_eq_true_iff _ _ _).mpr
  intro index
  obtain ⟨candidate, rfl⟩ := RationalSensorNetwork.rowEquiv.surjective index
  obtain edge | edge := candidate <;> fin_cases edge <;>
    rw [RationalSensorNetwork.rowEval] <;>
    norm_num [RationalSensorNetwork.base, RationalSensorNetwork.signedOffset,
      RationalSensorNetwork.rowSign, RationalSensorNetwork.rowEdge,
      RationalSensorNetwork.rowEquiv_apply, triangleNetwork, triangleReading]

/-- The exact checker accepts the sparse certificate against zero tolerance. -/
theorem triangleCertificate_check :
    triangleNetwork.checkCertificate (fun _ => 0) triangleCertificate = true := by
  apply (Maths.LinearProgramming.checkRationalCertificate_eq_true_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro index
    generalize hrow : RationalSensorNetwork.row index = candidate
    obtain edge | edge := candidate <;> fin_cases edge <;>
      norm_num [triangleCertificate, hrow]
  · intro coordinate
    rw [← Equiv.sum_comp RationalSensorNetwork.rowEquiv]
    fin_cases coordinate <;>
      norm_num [RationalSensorNetwork.matrix, RationalSensorNetwork.rowSign,
        RationalSensorNetwork.rowEdge, RationalSensorNetwork.rowEquiv_apply,
        triangleCertificate, triangleNetwork, Fin.sum_univ_three]
  · rw [← Equiv.sum_comp RationalSensorNetwork.rowEquiv]
    norm_num [RationalSensorNetwork.base, RationalSensorNetwork.signedOffset,
      RationalSensorNetwork.rowSign, RationalSensorNetwork.rowEdge,
      RationalSensorNetwork.rowEquiv_apply, triangleCertificate, triangleNetwork,
      Fin.sum_univ_three]

/-- The triangle has a real reading consistent at uniform tolerance `1 / 3`. -/
theorem exists_triangle_isConsistent_one_third :
    ∃ reading : Fin 3 → ℝ, triangleNetwork.IsConsistent (fun _ => 1 / 3) reading := by
  refine ⟨fun vertex => (triangleReading vertex : ℝ), ?_⟩
  convert triangleNetwork.isConsistent_of_checkAssignment _ _ triangleReading_check using 1;
    norm_num

/-- The triangle has no exactly compatible real sensor reading. -/
theorem not_exists_triangle_isConsistent_zero :
    ¬∃ reading : Fin 3 → ℝ, triangleNetwork.IsConsistent (fun _ => 0) reading := by
  intro hexists
  apply triangleNetwork.not_exists_isConsistent_of_checkCertificate _ _
    triangleCertificate_check
  simpa using hexists

end CellularSheaves
