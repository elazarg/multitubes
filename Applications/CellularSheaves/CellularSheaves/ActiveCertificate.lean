/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.OptimalTolerance
public import Maths.Multitubes.FiniteInequality.OptimalCertificate

/-!
# Sparse active certificates for optimal sensor tolerance

A sensor network with at least one comparison has a normalized balanced combination of signed
comparison rows attaining its least uniform tolerance. The combination can be chosen with small
support. Every row receiving positive weight is an active signed sensor comparison at any supplied
optimal reading.

## Main definitions

* `CellularSheaves.RationalSensorNetwork.signedComparisonResidual`: the oriented residual of a
  signed comparison row.

## Main results

* `CellularSheaves.RationalSensorNetwork.exists_rankSparse_activeCertificate`: every optimal
  reading of a nonempty sensor network admits a normalized optimal certificate supported on at
  most the rank of the signed row normals plus one, and every positively weighted row is tight.

## Tags

sensor consistency, active constraint, sparse certificate, optimal tolerance
-/

@[expose] public section

noncomputable section

namespace CellularSheaves.RationalSensorNetwork

open Maths.FiniteInequality
open scoped BigOperators

variable {n m : ℕ}

/-- The signed residual of one comparison row at a real sensor reading. -/
def signedComparisonResidual (network : RationalSensorNetwork n m)
    (reading : Fin n → ℝ) (row : Fin (m + m)) : ℝ :=
  network.realOffset row - dotProduct (network.realMatrix row) reading

private theorem row_rowEquiv (candidate : Fin m ⊕ Fin m) :
    row (rowEquiv candidate) = candidate := by
  simp [row]

/-- A forward signed row measures source restriction minus target restriction. -/
@[simp] theorem signedComparisonResidual_forward (network : RationalSensorNetwork n m)
    (reading : Fin n → ℝ) (edge : Fin m) :
    network.signedComparisonResidual reading (rowEquiv (.inl edge)) =
      (network.sourceScale edge : ℝ) * reading (network.source edge) +
        network.offset edge -
          (network.targetScale edge : ℝ) * reading (network.target edge) := by
  classical
  have htarget (coordinate : Fin n) :
      ((if coordinate = network.target edge then network.targetScale edge else 0 : ℚ) : ℝ) =
        if coordinate = network.target edge then (network.targetScale edge : ℝ) else 0 := by
    by_cases h : coordinate = network.target edge <;> simp [h]
  have hsource (coordinate : Fin n) :
      ((if coordinate = network.source edge then network.sourceScale edge else 0 : ℚ) : ℝ) =
        if coordinate = network.source edge then (network.sourceScale edge : ℝ) else 0 := by
    by_cases h : coordinate = network.source edge <;> simp [h]
  simp [signedComparisonResidual, realOffset, realMatrix, signedOffset, matrix, rowSign,
    rowEdge, row_rowEquiv, dotProduct, htarget, hsource, sub_mul,
    Finset.sum_sub_distrib]
  ring

/-- A reverse signed row measures target restriction minus source restriction. -/
@[simp] theorem signedComparisonResidual_reverse (network : RationalSensorNetwork n m)
    (reading : Fin n → ℝ) (edge : Fin m) :
    network.signedComparisonResidual reading (rowEquiv (.inr edge)) =
      (network.targetScale edge : ℝ) * reading (network.target edge) -
        ((network.sourceScale edge : ℝ) * reading (network.source edge) +
          network.offset edge) := by
  classical
  have htarget (coordinate : Fin n) :
      ((if coordinate = network.target edge then network.targetScale edge else 0 : ℚ) : ℝ) =
        if coordinate = network.target edge then (network.targetScale edge : ℝ) else 0 := by
    by_cases h : coordinate = network.target edge <;> simp [h]
  have hsource (coordinate : Fin n) :
      ((if coordinate = network.source edge then network.sourceScale edge else 0 : ℚ) : ℝ) =
        if coordinate = network.source edge then (network.sourceScale edge : ℝ) else 0 := by
    by_cases h : coordinate = network.source edge <;> simp [h]
  simp [signedComparisonResidual, realOffset, realMatrix, signedOffset, matrix, rowSign,
    rowEdge, row_rowEquiv, dotProduct, htarget, hsource, sub_mul,
    Finset.sum_sub_distrib]
  ring

private theorem isLeast_worstResidual_minimumUniformTolerance
    (network : RationalSensorNetwork n m) [Nonempty (Fin m)] :
    IsLeast
      {level | WorstResidualAtMost network.realMatrix network.realOffset level}
      network.minimumUniformTolerance := by
  constructor
  · exact (network.exists_uniformlyConsistent_iff_worstResidual _).mp
      network.exists_isConsistent_minimumUniformTolerance
  · intro level hlevel
    obtain ⟨reading, hreading⟩ :=
      (network.exists_uniformlyConsistent_iff_worstResidual level).mpr hlevel
    let edge : Fin m := Classical.choice inferInstance
    have hnonneg : 0 ≤ level :=
      (abs_nonneg ((network.targetScale edge : ℝ) * reading (network.target edge) -
        ((network.sourceScale edge : ℝ) * reading (network.source edge) +
          network.offset edge))).trans (hreading edge)
    exact network.isLeast_minimumUniformTolerance.2 ⟨hnonneg, reading, hreading⟩

/-- Every optimal reading of a sensor network with a comparison admits a normalized optimal
certificate whose positive rows are active signed comparisons and whose support has size at most
the rank of the signed row normals plus one. -/
theorem exists_rankSparse_activeCertificate
    (network : RationalSensorNetwork n m) [Nonempty (Fin m)]
    (reading : Fin n → ℝ)
    (hreading : network.IsConsistent (fun _ => network.minimumUniformTolerance) reading) :
    ∃ coefficient : Fin (m + m) → ℝ,
      IsNormalizedCertificate network.realMatrix coefficient ∧
      certificateValue network.realOffset coefficient = network.minimumUniformTolerance ∧
      (∀ row, 0 < coefficient row →
        network.signedComparisonResidual reading row = network.minimumUniformTolerance) ∧
      Fintype.card {row : Fin (m + m) // coefficient row ≠ 0} ≤
        (Set.range network.realMatrix).finrank ℝ + 1 := by
  have hrows : ∀ row,
      network.realOffset row - dotProduct (network.realMatrix row) reading ≤
        network.minimumUniformTolerance := by
    have hrealRows :=
      (network.isConsistent_iff_realRowInequalities _ _).mp hreading
    intro row
    have hrow := hrealRows row
    change (network.signedOffset row : ℝ) -
      dotProduct (fun coordinate => (network.matrix row coordinate : ℝ)) reading ≤
        network.minimumUniformTolerance
    linarith
  obtain ⟨coefficient, hnormalized, hvalue, hactive, hsparse⟩ :=
    exists_rankSparse_normalizedCertificate_of_isLeast
      network.realMatrix network.realOffset
      (isLeast_worstResidual_minimumUniformTolerance network) hrows
  exact ⟨coefficient, hnormalized, hvalue,
    fun row hpos => by
      simpa only [signedComparisonResidual] using hactive row hpos,
    hsparse⟩

end CellularSheaves.RationalSensorNetwork

end
