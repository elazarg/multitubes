/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.FiniteInequality.Sparse

import Mathlib.Tactic.Linarith

/-!
# Optimal normalized certificates

An attained least worst-residual level has a matching normalized dual certificate.  The
certificate can be chosen on active rows of any supplied optimal potential, with support bounded
by the rank of the row vectors plus one.

## Main results

* `Maths.FiniteInequality.exists_normalizedCertificate_value_eq_of_isLeast`: an attained least
  residual level has a normalized certificate of the same value.
* `Maths.FiniteInequality.certificateValue_eq_iff_support_tight`: equality in weak duality is
  equivalent to tightness on the certificate support.
* `Maths.FiniteInequality.isLeast_worstResidualAtMost_of_certificate`: a matching feasible point
  and normalized certificate certify global optimality.
* `Maths.FiniteInequality.exists_rankSparse_normalizedCertificate_of_isLeast`: an optimal
  certificate can be chosen active at a supplied optimal point and rank-sparse.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace FiniteInequality

open scoped BigOperators

universe uS uR

variable {State : Type uS} {Row : Type uR}
variable [Fintype State] [Fintype Row]

omit [Fintype State] in
private theorem exists_maximizing_normalizedCertificate
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hexists : ∃ coefficient, IsNormalizedCertificate delta coefficient) :
    ∃ coefficient, IsNormalizedCertificate delta coefficient ∧
      ∀ candidate, IsNormalizedCertificate delta candidate →
        certificateValue base candidate ≤ certificateValue base coefficient := by
  classical
  let feasible := LinearProgramming.normalizedFarkasCertificateSet
    (balanceMatrix delta) (fun _ => 1)
  obtain ⟨initial, hinitial⟩ := hexists
  have hinitialMem : initial ∈ feasible :=
    (mem_normalizedFarkasCertificateSet_iff delta initial).mpr hinitial
  let objectiveMap := LinearProgramming.finiteDotContinuousLinearMap base
  obtain ⟨optimal, hoptimalMem, hoptimal⟩ :=
    (normalizedCertificateSet_isCompact delta).exists_isMaxOn
      ⟨initial, hinitialMem⟩ objectiveMap.continuous.continuousOn
  refine ⟨optimal, (mem_normalizedFarkasCertificateSet_iff delta optimal).mp hoptimalMem,
    fun candidate hcandidate => ?_⟩
  simpa [certificateValue, objectiveMap,
    LinearProgramming.finiteDotContinuousLinearMap_apply, mul_comm] using
      hoptimal ((mem_normalizedFarkasCertificateSet_iff delta candidate).mpr hcandidate)

/-- An attained least worst-residual level has a normalized certificate with matching value. -/
theorem exists_normalizedCertificate_value_eq_of_isLeast
    (delta : Row → State → ℝ) (base : Row → ℝ) {level : ℝ}
    (hleast : IsLeast {candidate | WorstResidualAtMost delta base candidate} level) :
    ∃ coefficient, IsNormalizedCertificate delta coefficient ∧
      certificateValue base coefficient = level := by
  classical
  have hexists : ∃ coefficient, IsNormalizedCertificate delta coefficient := by
    by_contra hnone
    have hall (candidate : ℝ) : WorstResidualAtMost delta base candidate :=
      (worstResidualAtMost_iff_normalizedDual_le delta base candidate).mpr fun coefficient hcert =>
        (hnone ⟨coefficient, hcert⟩).elim
    have := hleast.2 (hall (level - 1))
    linarith
  obtain ⟨coefficient, hcertificate, hmaximal⟩ :=
    exists_maximizing_normalizedCertificate delta base hexists
  refine ⟨coefficient, hcertificate, le_antisymm
    (certificateValue_le_of_worstResidualAtMost hleast.1 hcertificate) ?_⟩
  by_contra hnot
  have hstrict : certificateValue base coefficient < level := lt_of_not_ge hnot
  let intermediate := (certificateValue base coefficient + level) / 2
  have hintermediate : WorstResidualAtMost delta base intermediate :=
    (worstResidualAtMost_iff_normalizedDual_le delta base intermediate).mpr fun candidate hc => by
      exact (hmaximal candidate hc).trans (by dsimp [intermediate]; linarith)
  have := hleast.2 hintermediate
  dsimp [intermediate] at this
  linarith

private theorem weighted_residual_eq
    (delta : Row → State → ℝ) (base : Row → ℝ) (point : State → ℝ)
    {coefficient : Row → ℝ} (hcertificate : IsNormalizedCertificate delta coefficient) :
    (∑ row, coefficient row *
      (base row - dotProduct (delta row) point)) = certificateValue base coefficient := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib, certificateValue]
  suffices ∑ row, coefficient row * dotProduct (delta row) point = 0 by rw [this, sub_zero]
  calc
    (∑ row, coefficient row * dotProduct (delta row) point) =
        ∑ state, (∑ row, coefficient row * delta row state) * point state := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = 0 := by simp [hcertificate.2.2]

/-- Equality in weak duality holds exactly when every row in the positive certificate support is
tight at the feasible point. -/
theorem certificateValue_eq_iff_support_tight
    (delta : Row → State → ℝ) (base : Row → ℝ) (point : State → ℝ) (level : ℝ)
    {coefficient : Row → ℝ} (hcertificate : IsNormalizedCertificate delta coefficient)
    (hrows : ∀ row, base row - dotProduct (delta row) point ≤ level) :
    certificateValue base coefficient = level ↔
      ∀ row, 0 < coefficient row →
        base row - dotProduct (delta row) point = level := by
  classical
  let slack := fun row => level - (base row - dotProduct (delta row) point)
  have hslack (row) : 0 ≤ slack row := by dsimp [slack]; linarith [hrows row]
  have hsum : (∑ row, coefficient row * slack row) =
      level - certificateValue base coefficient := by
    dsimp [slack]
    rw [← weighted_residual_eq delta base point hcertificate]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcertificate.2.1, one_mul]
  constructor
  · intro hvalue row hpositive
    have hzero : ∑ row, coefficient row * slack row = 0 := by rw [hsum, hvalue, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (fun candidate _ => mul_nonneg (hcertificate.1 candidate) (hslack candidate))).mp
        hzero row (Finset.mem_univ row)
    have : slack row = 0 := (mul_eq_zero.mp hterm).resolve_left hpositive.ne'
    dsimp [slack] at this
    linarith
  · intro htight
    have hzero : ∑ row, coefficient row * slack row = 0 := by
      apply Finset.sum_eq_zero
      intro row _
      by_cases hcoefficient : coefficient row = 0
      · simp [hcoefficient]
      · have hpositive := lt_of_le_of_ne (hcertificate.1 row) (Ne.symm hcoefficient)
        simp [slack, htight row hpositive]
    rw [hsum] at hzero
    linarith

/-- A positive coefficient in a matching normalized certificate marks a tight row. -/
theorem eq_of_pos_of_certificateValue_eq
    (delta : Row → State → ℝ) (base : Row → ℝ) (point : State → ℝ) (level : ℝ)
    {coefficient : Row → ℝ} (hcertificate : IsNormalizedCertificate delta coefficient)
    (hrows : ∀ row, base row - dotProduct (delta row) point ≤ level)
    (hvalue : certificateValue base coefficient = level) {row : Row}
    (hpositive : 0 < coefficient row) :
    base row - dotProduct (delta row) point = level :=
  (certificateValue_eq_iff_support_tight delta base point level hcertificate hrows).mp
    hvalue row hpositive

/-- A feasible level and a normalized certificate of the same value certify that the level is
globally least. -/
theorem isLeast_worstResidualAtMost_of_certificate
    (delta : Row → State → ℝ) (base : Row → ℝ) {level : ℝ}
    (hlevel : WorstResidualAtMost delta base level)
    {coefficient : Row → ℝ} (hcertificate : IsNormalizedCertificate delta coefficient)
    (hvalue : certificateValue base coefficient = level) :
    IsLeast {candidate | WorstResidualAtMost delta base candidate} level := by
  refine ⟨hlevel, fun candidate hcandidate => ?_⟩
  rw [← hvalue]
  exact certificateValue_le_of_worstResidualAtMost hcandidate hcertificate

omit [Fintype State] in
private theorem exists_optimal_linearIndependent
    (delta : Row → State → ℝ) (base : Row → ℝ)
    {initial : Row → ℝ} (hinitial : IsNormalizedCertificate delta initial) :
    ∃ coefficient, IsNormalizedCertificate delta coefficient ∧
      certificateValue base initial ≤ certificateValue base coefficient ∧
      LinearIndependent ℝ
        (fun row : {row : Row // coefficient row ≠ 0} => augmentedColumn delta row.1) := by
  classical
  let feasible := LinearProgramming.normalizedFarkasCertificateSet
    (balanceMatrix delta) (fun _ => 1)
  have hinitialMem : initial ∈ feasible :=
    (mem_normalizedFarkasCertificateSet_iff delta initial).mpr hinitial
  let objectiveMap := LinearProgramming.finiteDotContinuousLinearMap base
  obtain ⟨optimal, hoptimalMem, hoptimal⟩ :=
    (normalizedCertificateSet_isCompact delta).exists_isMaxOn
      ⟨initial, hinitialMem⟩ objectiveMap.continuous.continuousOn
  have hstandard : LinearProgramming.IsStandardOptimal
      (LinearProgramming.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearProgramming.normalizedFarkasRhs base optimal := by
    refine ⟨hoptimalMem, fun candidate hcandidate => ?_⟩
    simpa [objectiveMap, LinearProgramming.finiteDotContinuousLinearMap_apply] using
      hoptimal hcandidate
  obtain ⟨extreme, hextreme, hextremeOptimal, hvalue⟩ :=
    LinearProgramming.exists_extreme_standardOptimal_of_standardOptimal
      (LinearProgramming.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearProgramming.normalizedFarkasRhs base hstandard
  refine ⟨extreme, (mem_normalizedFarkasCertificateSet_iff delta extreme).mp
    hextremeOptimal.1, ?_, ?_⟩
  · calc
      certificateValue base initial ≤ certificateValue base optimal := by
        simpa [certificateValue, objectiveMap,
          LinearProgramming.finiteDotContinuousLinearMap_apply, mul_comm] using
            hoptimal hinitialMem
      _ = certificateValue base extreme := by
        simpa [certificateValue, mul_comm] using hvalue.symm
  · exact LinearProgramming.linearIndependent_supportColumns_of_extreme_standardFeasible
      (LinearProgramming.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearProgramming.normalizedFarkasRhs hextreme

/-- At an attained least level, an optimal certificate can be chosen on tight rows of any supplied
optimal point, with support at most the row-vector rank plus one. -/
theorem exists_rankSparse_normalizedCertificate_of_isLeast
    (delta : Row → State → ℝ) (base : Row → ℝ) {level : ℝ}
    (hleast : IsLeast {candidate | WorstResidualAtMost delta base candidate} level)
    {point : State → ℝ}
    (hpoint : ∀ row, base row - dotProduct (delta row) point ≤ level) :
    ∃ coefficient, IsNormalizedCertificate delta coefficient ∧
      certificateValue base coefficient = level ∧
      (∀ row, 0 < coefficient row →
        base row - dotProduct (delta row) point = level) ∧
      Fintype.card {row : Row // coefficient row ≠ 0} ≤
        (Set.range delta).finrank ℝ + 1 := by
  obtain ⟨initial, hinitial, hinitialValue⟩ :=
    exists_normalizedCertificate_value_eq_of_isLeast delta base hleast
  obtain ⟨coefficient, hcertificate, hinitialLe, hlinear⟩ :=
    exists_optimal_linearIndependent delta base hinitial
  have hvalueLe := certificateValue_le_of_worstResidualAtMost hleast.1 hcertificate
  have hvalue : certificateValue base coefficient = level := by linarith
  refine ⟨coefficient, hcertificate, hvalue,
    (certificateValue_eq_iff_support_tight delta base point level hcertificate hpoint).mp hvalue,
    ?_⟩
  exact support_card_le_rank_add_one_of_linearIndependent delta coefficient hlinear

end FiniteInequality

end

end Maths
