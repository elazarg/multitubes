/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.FiniteInequality.Quantitative
public import DirectedTransport.LinearAlgebra.NormalizedFarkas
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

import DirectedTransport.FiniteInequality.Arithmetic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Rank-sparse normalized finite-inequality certificates

An infeasible finite inequality system has a positive normalized certificate
whose augmented balance columns on the positive support are linearly
independent.  Its support is therefore bounded by the rank of all augmented
columns, which is at most the coordinate rank plus one.

## Main definitions

* `DirectedTransport.FiniteInequality.balanceMatrix`: the row data read as a matrix of balance
  columns indexed by rows.
* `DirectedTransport.FiniteInequality.augmentedColumn`: a balance column extended by the
  mass-one coordinate, so that normalization becomes one more linear condition.
* `DirectedTransport.FiniteInequality.IsPositiveCircuit`: a normalized certificate whose
  positive-support row vectors are affinely independent.  Support coefficients are nonzero and
  nonnegative, hence strictly positive.

## Main results

* `DirectedTransport.FiniteInequality.exists_positive_normalizedCertificate_of_infeasible`:
  infeasibility produces a normalized certificate of positive objective.
* `DirectedTransport.FiniteInequality.exists_positive_normalizedCertificate_linearIndependent`:
  that certificate can be chosen with linearly independent augmented support columns.  This is
  the engine for every sparsity bound below.
* `DirectedTransport.FiniteInequality.exists_positiveCircuit_of_infeasible`: the same witness
  packaged as a minimal affine row configuration around the origin.
* `DirectedTransport.FiniteInequality.exists_positive_normalizedCertificate_support_card_le_rank`
  and `exists_positive_normalizedCertificate_support_card_le_rank_add_one`: the support size is
  bounded by the rank of the augmented columns, and hence by the coordinate rank plus one.
* `DirectedTransport.FiniteInequality.exists_rankSparse_rationalCertificate_of_real_infeasible`:
  for rational data, sparsity and rationality hold simultaneously.  The rank bounding the
  support is still computed after extending the row normals to `ℝ`.  Its integral companion
  `exists_rankSparse_integralCoefficientCertificate_of_real_infeasible` clears only the
  certificate denominators, stating balance and objective over `ℚ`.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace FiniteInequality

open scoped BigOperators

universe uS uR

variable {State : Type uS} {Row : Type uR}
variable [Fintype State] [Fintype Row]

private theorem sum_supportSubtype (coefficient value : Row → ℝ) :
    (∑ row : {row : Row // row ∈
        Finset.univ.filter fun candidate => coefficient candidate ≠ 0},
      coefficient row.1 * value row.1) =
        ∑ row, coefficient row * value row := by
  classical
  let selected := Finset.univ.filter fun row => coefficient row ≠ 0
  change (∑ row : {row : Row // row ∈ selected},
    coefficient row.1 * value row.1) = _
  calc
    (∑ row : {row // row ∈ selected},
        coefficient row.1 * value row.1) =
        ∑ row ∈ selected.attach,
          coefficient row.1 * value row.1 := by
            rw [Finset.attach_eq_univ]
    _ = ∑ row ∈ selected, coefficient row * value row := by
      simpa using Finset.sum_attach selected
        (fun row => coefficient row * value row)
    _ = ∑ row ∈ Finset.univ, coefficient row * value row := by
      apply Finset.sum_filter_of_ne
      intro row _ hproduct
      contrapose! hproduct
      simp [hproduct]
    _ = ∑ row, coefficient row * value row := by rfl

/-- Balance matrix with states as rows and inequalities as columns. -/
def balanceMatrix (delta : Row → State → ℝ) : Matrix State Row ℝ :=
  fun state row => delta row state

/-- The balance column augmented by the mass-one coordinate. -/
def augmentedColumn (delta : Row → State → ℝ) (row : Row) :
    Sum State Unit → ℝ :=
  (LinearAlgebra.normalizedFarkasMatrix
    (balanceMatrix delta) (fun _ => 1)).col row

/-- A normalized positive circuit: the origin is expressed by nonnegative
coefficients of total mass one, and the row vectors on the positive support
are affinely independent.  Since support coefficients are nonzero and
nonnegative, they are strictly positive. -/
def IsPositiveCircuit (delta : Row → State → ℝ)
    (coefficient : Row → ℝ) : Prop :=
  IsNormalizedCertificate delta coefficient ∧
    AffineIndependent ℝ
      (fun row : {row : Row // coefficient row ≠ 0} => delta row.1)

omit [Fintype State] in
/-- The standard normalized-Farkas polytope is exactly the normalized
certificate predicate. -/
theorem mem_normalizedFarkasCertificateSet_iff
    (delta : Row → State → ℝ) (coefficient : Row → ℝ) :
    coefficient ∈ LinearAlgebra.normalizedFarkasCertificateSet
        (balanceMatrix delta) (fun _ => 1) ↔
      IsNormalizedCertificate delta coefficient := by
  classical
  constructor
  · intro hmem
    refine ⟨hmem.1, ?_, ?_⟩
    · have hmass := congrFun hmem.2 (Sum.inr ())
      change (∑ row, 1 * coefficient row) = 1 at hmass
      simpa using hmass
    · intro state
      have hbalance := congrFun hmem.2 (Sum.inl state)
      change (∑ row, delta row state * coefficient row) = 0 at hbalance
      simpa only [mul_comm] using hbalance
  · intro hcertificate
    refine ⟨hcertificate.1, funext fun index => ?_⟩
    cases index with
    | inl state =>
        change (∑ row, delta row state * coefficient row) = 0
        simpa only [mul_comm] using hcertificate.2.2 state
    | inr _ =>
        change (∑ row, 1 * coefficient row) = 1
        simpa using hcertificate.2.1

private theorem coefficient_eq_zero_of_sum_eq_zero
    (coefficient : Row → ℝ) (hnonneg : ∀ row, 0 ≤ coefficient row)
    (hsum : ∑ row, coefficient row = 0) :
    ∀ row, coefficient row = 0 := by
  intro row
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun index _ => hnonneg index)).mp hsum
  exact hall row (Finset.mem_univ row)

/-- Infeasibility produces a normalized certificate with positive objective. -/
theorem exists_positive_normalizedCertificate_of_infeasible
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsNormalizedCertificate delta coefficient ∧
        0 < certificateValue base coefficient := by
  classical
  rcases exists_potential_or_nonnegative_incompatibility delta base with
    hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
  · exact (hinfeasible hpotential).elim
  · have hmassNonneg : 0 ≤ ∑ row, coefficient row :=
      Finset.sum_nonneg fun row _ => hnonneg row
    have hmassPos : 0 < ∑ row, coefficient row := by
      by_contra hnot
      have hmassZero : ∑ row, coefficient row = 0 :=
        le_antisymm (le_of_not_gt hnot) hmassNonneg
      have hzero := coefficient_eq_zero_of_sum_eq_zero
        coefficient hnonneg hmassZero
      have : ∑ row, coefficient row * base row = 0 := by simp [hzero]
      linarith
    let mass := ∑ row, coefficient row
    let normalized : Row → ℝ := fun row => coefficient row / mass
    refine ⟨normalized, ⟨fun row => div_nonneg (hnonneg row) hmassNonneg,
      ?_, ?_⟩, ?_⟩
    · dsimp [normalized, mass]
      rw [← Finset.sum_div, div_self hmassPos.ne']
    · intro state
      dsimp [normalized, mass]
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hbalance state, zero_div]
    · dsimp [certificateValue, normalized, mass]
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, div_pos_iff]
      exact Or.inl ⟨hpositive, hmassPos⟩

omit [Fintype State] in
private theorem normalizedCertificateSet_isCompact
    (delta : Row → State → ℝ) :
    IsCompact (LinearAlgebra.normalizedFarkasCertificateSet
      (balanceMatrix delta) (fun _ => 1)) := by
  classical
  let feasible := LinearAlgebra.normalizedFarkasCertificateSet
    (balanceMatrix delta) (fun _ => 1)
  have hclosed : IsClosed feasible :=
    LinearAlgebra.isClosed_standardFeasibleSet _ _
  have hsubset : feasible ⊆ Set.Icc (0 : Row → ℝ) 1 := by
    intro coefficient hcoefficient
    have hnormalized :=
      (mem_normalizedFarkasCertificateSet_iff delta coefficient).mp hcoefficient
    constructor
    · exact hnormalized.1
    · intro row
      have hsingle := Finset.single_le_sum
        (fun candidate _ => hnormalized.1 candidate)
        (Finset.mem_univ row)
      simpa [hnormalized.2.1] using hsingle
  have heq : feasible = feasible ∩ Set.Icc (0 : Row → ℝ) 1 := by
    ext coefficient
    constructor
    · intro hmem
      exact ⟨hmem, hsubset hmem⟩
    · exact fun hmem => hmem.1
  change IsCompact feasible
  rw [heq]
  simpa [Set.inter_comm] using isCompact_Icc.inter_right hclosed

/-- **Rank-sparse positive certificate.**  The positive support columns can be
chosen linearly independent in the augmented balance system. -/
theorem exists_positive_normalizedCertificate_linearIndependent
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsNormalizedCertificate delta coefficient ∧
      0 < certificateValue base coefficient ∧
      LinearIndependent ℝ
        (fun row : {row : Row // coefficient row ≠ 0} =>
          augmentedColumn delta row.1) := by
  classical
  obtain ⟨initial, hinitial, hinitialPositive⟩ :=
    exists_positive_normalizedCertificate_of_infeasible delta base hinfeasible
  let feasible := LinearAlgebra.normalizedFarkasCertificateSet
    (balanceMatrix delta) (fun _ => 1)
  have hinitialMem : initial ∈ feasible :=
    (mem_normalizedFarkasCertificateSet_iff delta initial).mpr hinitial
  let objectiveMap := LinearAlgebra.finiteDotContinuousLinearMap base
  obtain ⟨optimal, hoptimalMem, hoptimal⟩ :=
    (normalizedCertificateSet_isCompact delta).exists_isMaxOn
      ⟨initial, hinitialMem⟩ objectiveMap.continuous.continuousOn
  have hstandardOptimal : LinearAlgebra.IsStandardOptimal
      (LinearAlgebra.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearAlgebra.normalizedFarkasRhs base optimal := by
    refine ⟨hoptimalMem, fun candidate hcandidate => ?_⟩
    simpa [objectiveMap, LinearAlgebra.finiteDotContinuousLinearMap_apply] using
      hoptimal hcandidate
  obtain ⟨extreme, hextreme, hextremeOptimal, hvalue⟩ :=
    LinearAlgebra.exists_extreme_standardOptimal_of_standardOptimal
      (LinearAlgebra.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearAlgebra.normalizedFarkasRhs base hstandardOptimal
  have hextremeNormalized : IsNormalizedCertificate delta extreme :=
    (mem_normalizedFarkasCertificateSet_iff delta extreme).mp
      hextremeOptimal.1
  have hinitialLe : certificateValue base initial ≤
      certificateValue base optimal := by
    simpa [certificateValue, objectiveMap,
      LinearAlgebra.finiteDotContinuousLinearMap_apply, mul_comm] using
      hoptimal hinitialMem
  have hextremePositive : 0 < certificateValue base extreme := by
    have hvalue' : certificateValue base extreme =
        certificateValue base optimal := by
      simpa [certificateValue, mul_comm] using hvalue
    rw [hvalue']
    exact hinitialPositive.trans_le hinitialLe
  have hlinear :=
    LinearAlgebra.linearIndependent_supportColumns_of_extreme_standardFeasible
      (LinearAlgebra.normalizedFarkasMatrix
        (balanceMatrix delta) (fun _ => 1))
      LinearAlgebra.normalizedFarkasRhs hextreme
  exact ⟨extreme, hextremeNormalized, hextremePositive, hlinear⟩

omit [Fintype State] in
private theorem affineIndependent_of_linearIndependent_augmented
    (delta : Row → State → ℝ) (coefficient : Row → ℝ)
    (hlinear : LinearIndependent ℝ
      (fun row : {row : Row // coefficient row ≠ 0} =>
        augmentedColumn delta row.1)) :
    AffineIndependent ℝ
      (fun row : {row : Row // coefficient row ≠ 0} => delta row.1) := by
  classical
  rw [affineIndependent_iff]
  intro selected weight hsum hdelta row hrow
  let extended : {row : Row // coefficient row ≠ 0} → ℝ :=
    fun candidate => if candidate ∈ selected then weight candidate else 0
  have haugmented :
      (∑ candidate, extended candidate •
        augmentedColumn delta candidate.1) = 0 := by
    funext coordinate
    cases coordinate with
    | inl state =>
        have hstate := congrFun hdelta state
        simpa [Finset.sum_apply, Pi.smul_apply, ite_apply, augmentedColumn,
          Matrix.col_apply, LinearAlgebra.normalizedFarkasMatrix,
          balanceMatrix, extended] using hstate
    | inr _ =>
        simpa [Finset.sum_apply, Pi.smul_apply, ite_apply, augmentedColumn,
          Matrix.col_apply, LinearAlgebra.normalizedFarkasMatrix,
          extended] using hsum
  have hzero := Fintype.linearIndependent_iff.mp
    hlinear extended haugmented row
  simpa [extended, hrow] using hzero

/-- Every infeasible finite system has a positive-objective circuit
certificate.  This packages the extreme normalized Farkas witness as a
minimal affine row configuration around the origin. -/
theorem exists_positiveCircuit_of_infeasible
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsPositiveCircuit delta coefficient ∧
        0 < certificateValue base coefficient := by
  obtain ⟨coefficient, hcertificate, hpositive, hlinear⟩ :=
    exists_positive_normalizedCertificate_linearIndependent
      delta base hinfeasible
  exact ⟨coefficient,
    ⟨hcertificate,
      affineIndependent_of_linearIndependent_augmented
        delta coefficient hlinear⟩,
    hpositive⟩

omit [Fintype State] [Fintype Row] in
private theorem vectorSpan_range_le_span_range
    (family : Row → State → ℝ) :
    vectorSpan ℝ (Set.range family) ≤
      Submodule.span ℝ (Set.range family) := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro value ⟨first, ⟨firstRow, rfl⟩,
    second, ⟨secondRow, rfl⟩, rfl⟩
  exact Submodule.sub_mem _
    (Submodule.subset_span ⟨firstRow, rfl⟩)
    (Submodule.subset_span ⟨secondRow, rfl⟩)

/-- **Rank plus one support bound.**  If the balance columns have rank `r`,
an infeasibility certificate can be chosen with at most `r + 1` positive
coordinates. -/
theorem exists_positive_normalizedCertificate_support_card_le_rank_add_one
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsNormalizedCertificate delta coefficient ∧
      0 < certificateValue base coefficient ∧
      Fintype.card {row : Row // coefficient row ≠ 0} ≤
        (Set.range delta).finrank ℝ + 1 := by
  obtain ⟨coefficient, hcertificate, hpositive, hlinear⟩ :=
    exists_positive_normalizedCertificate_linearIndependent
      delta base hinfeasible
  refine ⟨coefficient, hcertificate, hpositive, ?_⟩
  have haffine := affineIndependent_of_linearIndependent_augmented
    delta coefficient hlinear
  have hcard := haffine.card_le_finrank_succ
  apply hcard.trans
  apply Nat.add_le_add_right
  apply Submodule.finrank_mono
  exact (vectorSpan_mono ℝ <| by
    rintro _ ⟨row, rfl⟩
    exact ⟨row.1, rfl⟩).trans (vectorSpan_range_le_span_range delta)

/-- **Rank-sparse rational certificate.**  For rational row data, the
rank-plus-one support bound and rationality can be achieved simultaneously.
The rank is computed after extending the row normals to `ℝ`. -/
theorem exists_rankSparse_rationalCertificate_of_real_infeasible
    (delta : Row → State → ℚ) (base : Row → ℚ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        ∑ state, (delta row state : ℝ) * potential state) :
    ∃ (selected : Finset Row)
        (coefficient : {row // row ∈ selected} → ℚ),
      selected.card ≤
        (Set.range (fun row state => (delta row state : ℝ))).finrank ℝ + 1 ∧
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state,
        ∑ row, coefficient row * delta row.1 state = 0) ∧
      0 < ∑ row, coefficient row * base row.1 := by
  classical
  let deltaR : Row → State → ℝ :=
    fun row state => delta row state
  let baseR : Row → ℝ := fun row => base row
  have hinfeasibleR : ¬∃ potential : State → ℝ,
      ∀ row, baseR row ≤ dotProduct (deltaR row) potential := by
    simpa only [deltaR, baseR, dotProduct] using hinfeasible
  obtain ⟨realCoefficient, hreal, hpositive, hcard⟩ :=
    exists_positive_normalizedCertificate_support_card_le_rank_add_one
      deltaR baseR hinfeasibleR
  let selected := Finset.univ.filter fun row => realCoefficient row ≠ 0
  have hselectedCard : selected.card ≤
      (Set.range deltaR).finrank ℝ + 1 := by
    apply le_trans ?_ hcard
    rw [← Fintype.card_coe]
    apply Nat.le_of_eq
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (by intro row; simp [selected])
  let selectedDelta : {row // row ∈ selected} → State → ℚ :=
    fun row => delta row.1
  let selectedBase : {row // row ∈ selected} → ℚ :=
    fun row => base row.1
  have hselectedInfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (selectedBase row : ℝ) ≤
        ∑ state, (selectedDelta row state : ℝ) * potential state := by
    rintro ⟨potential, hpotential⟩
    let restricted : {row // row ∈ selected} → ℝ :=
      fun row => realCoefficient row.1
    have hnonnegative (row) : 0 ≤ restricted row := hreal.1 row.1
    have hbalance (state) :
        ∑ row, restricted row * (selectedDelta row state : ℝ) = 0 := by
      calc
        (∑ row, restricted row * (selectedDelta row state : ℝ)) =
            ∑ row, realCoefficient row * deltaR row state := by
          simpa only [selected, restricted, selectedDelta, deltaR] using
            sum_supportSubtype realCoefficient
              (fun row => deltaR row state)
        _ = 0 := hreal.2.2 state
    have hvalue : 0 <
        ∑ row, restricted row * (selectedBase row : ℝ) := by
      rw [show (∑ row, restricted row * (selectedBase row : ℝ)) =
          ∑ row, realCoefficient row * baseR row by
        simpa only [selected, restricted, selectedBase, baseR] using
          sum_supportSubtype realCoefficient baseR]
      exact hpositive
    have hweak := DirectedTransport.not_nonnegative_incompatibility_of_potential
      (fun row => by simpa only [dotProduct] using hpotential row)
      hnonnegative hbalance
    linarith
  obtain ⟨coefficient, hnonnegative, hbalance, hpositiveQ⟩ :=
    exists_rationalCertificate_of_real_infeasible
      selectedDelta selectedBase hselectedInfeasible
  refine ⟨selected, coefficient, ?_, hnonnegative, ?_, ?_⟩
  · simpa only [deltaR] using hselectedCard
  · simpa only [selectedDelta] using hbalance
  · simpa only [selectedBase] using hpositiveQ

/-- **Rank-sparse integer-valued certificate.**  A rational infeasible system
has an integer coefficient certificate with the same rank-plus-one support
bound.  Its balance and objective are evaluated over `ℚ`; only certificate
denominators are cleared. -/
theorem exists_rankSparse_integralCoefficientCertificate_of_real_infeasible
    (delta : Row → State → ℚ) (base : Row → ℚ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        ∑ state, (delta row state : ℝ) * potential state) :
    ∃ (selected : Finset Row)
        (coefficient : {row // row ∈ selected} → ℤ),
      selected.card ≤
        (Set.range (fun row state => (delta row state : ℝ))).finrank ℝ + 1 ∧
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state,
        ∑ row, (coefficient row : ℚ) * delta row.1 state = 0) ∧
      0 < ∑ row, (coefficient row : ℚ) * base row.1 := by
  classical
  obtain ⟨selected, rational, hcard, hnonnegative, hbalance, hpositive⟩ :=
    exists_rankSparse_rationalCertificate_of_real_infeasible
      delta base hinfeasible
  let selectedDelta : {row // row ∈ selected} → State → ℚ :=
    fun row => delta row.1
  let selectedBase : {row // row ∈ selected} → ℚ :=
    fun row => base row.1
  have hselectedInfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (selectedBase row : ℝ) ≤
        ∑ state, (selectedDelta row state : ℝ) * potential state := by
    rintro ⟨potential, hpotential⟩
    let coefficientR : {row // row ∈ selected} → ℝ :=
      fun row => rational row
    have hnonnegativeR (row) : 0 ≤ coefficientR row :=
      Rat.cast_nonneg.mpr (hnonnegative row)
    have hbalanceR (state) :
        ∑ row, coefficientR row * (selectedDelta row state : ℝ) = 0 := by
      have hcast := congrArg (fun value : ℚ => (value : ℝ))
        (hbalance state)
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero,
        coefficientR, selectedDelta] using hcast
    have hpositiveR : 0 <
        ∑ row, coefficientR row * (selectedBase row : ℝ) := by
      have hcast : (0 : ℝ) <
          ((∑ row, rational row * base row.1 : ℚ) : ℝ) :=
        Rat.cast_pos.mpr hpositive
      simpa only [Rat.cast_sum, Rat.cast_mul, coefficientR,
        selectedBase] using hcast
    have hweak := DirectedTransport.not_nonnegative_incompatibility_of_potential
      (fun row => by simpa only [dotProduct] using hpotential row)
      hnonnegativeR hbalanceR
    linarith
  obtain ⟨coefficient, hnonnegativeZ, hbalanceZ, hpositiveZ⟩ :=
    exists_integralCoefficientCertificate_of_real_infeasible
      selectedDelta selectedBase hselectedInfeasible
  exact ⟨selected, coefficient, hcard, hnonnegativeZ,
    hbalanceZ, hpositiveZ⟩

/-- The support size is bounded by the rank of the augmented balance columns. -/
theorem exists_positive_normalizedCertificate_support_card_le_rank
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsNormalizedCertificate delta coefficient ∧
      0 < certificateValue base coefficient ∧
      Fintype.card {row : Row // coefficient row ≠ 0} ≤
        (Set.range (augmentedColumn delta)).finrank ℝ := by
  obtain ⟨coefficient, hcertificate, hpositive, hlinear⟩ :=
    exists_positive_normalizedCertificate_linearIndependent
      delta base hinfeasible
  refine ⟨coefficient, hcertificate, hpositive, ?_⟩
  have hsupportRank :=
    (linearIndependent_iff_card_le_finrank_span.mp hlinear)
  exact hsupportRank.trans <| Submodule.finrank_mono <|
    Submodule.span_mono <| by
      rintro _ ⟨row, rfl⟩
      exact ⟨row.1, rfl⟩

end FiniteInequality

end

end DirectedTransport
