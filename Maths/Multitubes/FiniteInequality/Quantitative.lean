/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.FiniteInequality.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative normalized duality for finite inequalities

This is the threshold form of finite-dimensional Farkas duality.  It avoids
naming an extended-real infimum: a worst residual threshold is attainable
exactly when every balanced nonnegative certificate of mass one has objective
at most that threshold.  If no normalized certificate exists, every real
threshold is attainable, which is precisely the unbounded-below case.

## Main definitions

* `Maths.FiniteInequality.IsNormalizedCertificate`: a balanced nonnegative row
  combination of total mass one.
* `Maths.FiniteInequality.certificateValue`: its objective value against lower
  bounds.
* `Maths.FiniteInequality.WorstResidualAtMost`: existence of a potential whose
  worst row residual is at most a given level.
* `Maths.FiniteInequality.Recession.IsBalancedNonnegative` and
  `Maths.FiniteInequality.Recession.IsCritical`: a balanced nonnegative combination
  without the mass-one normalization, and the rows whose coefficient vector pairs to zero with a
  recession direction.

## Main results

* `Maths.FiniteInequality.worstResidualAtMost_iff_normalizedDual_le`: the exact
  threshold duality - a worst-residual threshold is attainable exactly when every normalized
  certificate has objective at most that threshold.  It is stated level by level, not
  through an extended-real infimum, which keeps the certificate-free case meaningful.
* `Maths.FiniteInequality.exists_positive_normalizedCertificate_of_infeasible`:
  infeasibility produces a normalized certificate of positive objective, by dividing a Farkas
  certificate by its mass.
* `Maths.FiniteInequality.certificateValue_le_of_worstResidualAtMost`: the easy
  direction, usable on its own.
* `Maths.FiniteInequality.Recession.coefficient_eq_zero_of_not_critical`: every
  balanced nonnegative certificate is supported on rows critical for any common recession
  direction.
* `Maths.FiniteInequality.Recession.exists_potential_iff_exists_critical_potential`:
  feasibility of the whole system reduces to feasibility of that critical subsystem.

## Tags

Farkas lemma, strong duality, worst residual, recession direction, minimax, normalized certificate
-/

@[expose] public section

namespace Maths

noncomputable section

namespace FiniteInequality

open scoped BigOperators

universe uS uR

variable {State : Type uS} {Row : Type uR}
variable [Fintype State] [Fintype Row]

/-- A balanced nonnegative row combination with total mass one. -/
def IsNormalizedCertificate (delta : Row → State → ℝ)
    (coefficient : Row → ℝ) : Prop :=
  (∀ row, 0 ≤ coefficient row) ∧
    (∑ row, coefficient row = 1) ∧
    ∀ state, ∑ row, coefficient row * delta row state = 0

/-- Objective value of a normalized certificate. -/
def certificateValue (base : Row → ℝ) (coefficient : Row → ℝ) : ℝ :=
  ∑ row, coefficient row * base row

/-- A potential whose worst row residual is at most `level`. -/
def WorstResidualAtMost (delta : Row → State → ℝ) (base : Row → ℝ)
    (level : ℝ) : Prop :=
  ∃ potential : State → ℝ,
    ∀ row, base row - dotProduct (delta row) potential ≤ level

private theorem weighted_shiftedBase_eq (base : Row → ℝ)
    (coefficient : Row → ℝ) (level : ℝ) :
    (∑ row, coefficient row * (base row - level)) =
      certificateValue base coefficient -
        level * ∑ row, coefficient row := by
  rw [certificateValue]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Infeasibility produces a normalized certificate with positive objective. -/
theorem exists_positive_normalizedCertificate_of_infeasible
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) :
    ∃ coefficient : Row → ℝ,
      IsNormalizedCertificate delta coefficient ∧
        0 < certificateValue base coefficient := by
  classical
  rcases exists_potential_or_farkasCertificate delta base with
    hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
  · exact (hinfeasible hpotential).elim
  · have hmassNonneg : 0 ≤ ∑ row, coefficient row :=
      Finset.sum_nonneg fun row _ => hnonneg row
    have hmassPos : 0 < ∑ row, coefficient row := by
      by_contra hnot
      have hmassZero : ∑ row, coefficient row = 0 :=
        le_antisymm (le_of_not_gt hnot) hmassNonneg
      have hzero := (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).1 hmassZero
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

/-- Weak normalized duality. -/
theorem certificateValue_le_of_worstResidualAtMost
    {delta : Row → State → ℝ} {base : Row → ℝ} {level : ℝ}
    (hlevel : WorstResidualAtMost delta base level)
    {coefficient : Row → ℝ}
    (hcertificate : IsNormalizedCertificate delta coefficient) :
    certificateValue base coefficient ≤ level := by
  classical
  rcases hlevel with ⟨potential, hpotential⟩
  have hrows (row) : base row - level ≤ dotProduct (delta row) potential := by
    have := hpotential row
    linarith
  have hweak := sum_mul_base_nonpos_of_potential
    hrows hcertificate.1 hcertificate.2.2
  rw [weighted_shiftedBase_eq, hcertificate.2.1] at hweak
  linarith

/-- **Exact normalized threshold duality.** -/
theorem worstResidualAtMost_iff_normalizedDual_le
    (delta : Row → State → ℝ) (base : Row → ℝ) (level : ℝ) :
    WorstResidualAtMost delta base level ↔
      ∀ coefficient : Row → ℝ,
        IsNormalizedCertificate delta coefficient →
          certificateValue base coefficient ≤ level := by
  classical
  constructor
  · intro hlevel coefficient hcertificate
    exact certificateValue_le_of_worstResidualAtMost hlevel hcertificate
  · intro hdual
    by_contra hlevel
    obtain ⟨coefficient, hcertificate, hpositive⟩ :=
      exists_positive_normalizedCertificate_of_infeasible delta (fun row => base row - level)
        fun ⟨potential, hpotential⟩ =>
          hlevel ⟨potential, fun row => by linarith [hpotential row]⟩
    simp only [certificateValue] at hpositive
    rw [weighted_shiftedBase_eq, hcertificate.2.1] at hpositive
    linarith [hdual coefficient hcertificate]

/-! ## Recession reduction -/

namespace Recession

/-- A nonnegative balanced combination of row vectors. -/
def IsBalancedNonnegative
    (delta : Row → State → ℝ) (coefficient : Row → ℝ) : Prop :=
  (∀ row, 0 ≤ coefficient row) ∧
    ∀ state, ∑ row, coefficient row * delta row state = 0

/-- Rows whose coefficient vector pairs to zero with a recession direction. -/
def IsCritical (delta : Row → State → ℝ) (direction : State → ℝ)
    (row : Row) : Prop :=
  dotProduct (delta row) direction = 0

/-- Every balanced nonnegative certificate is supported on rows critical for
any common recession direction. -/
theorem coefficient_eq_zero_of_not_critical
    (delta : Row → State → ℝ) (direction : State → ℝ)
    (hrecession : ∀ row, 0 ≤ dotProduct (delta row) direction)
    {coefficient : Row → ℝ}
    (hcertificate : IsBalancedNonnegative delta coefficient)
    {row : Row} (hnoncritical : ¬IsCritical delta direction row) :
    coefficient row = 0 := by
  classical
  have hsum : ∑ candidate,
      coefficient candidate * dotProduct (delta candidate) direction = 0 := by
    rw [sum_mul_dotProduct]
    simp [hcertificate.2]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ)
    (fun candidate _ => mul_nonneg (hcertificate.1 candidate)
      (hrecession candidate))).mp hsum row (Finset.mem_univ row)
  have hcriticalPos : 0 < dotProduct (delta row) direction :=
    lt_of_le_of_ne (hrecession row) (Ne.symm hnoncritical)
  exact (mul_eq_zero.mp hterm).resolve_right hcriticalPos.ne'

/-- A finite inequality system is feasible exactly when the subsystem
critical for a common nonnegative recession direction is feasible. -/
theorem exists_potential_iff_exists_critical_potential
    (delta : Row → State → ℝ) (base : Row → ℝ)
    (direction : State → ℝ)
    (hrecession : ∀ row, 0 ≤ dotProduct (delta row) direction) :
    (∃ potential : State → ℝ,
      ∀ row, base row ≤ dotProduct (delta row) potential) ↔
      ∃ potential : State → ℝ,
        ∀ row, IsCritical delta direction row →
          base row ≤ dotProduct (delta row) potential := by
  classical
  constructor
  · rintro ⟨potential, hpotential⟩
    exact ⟨potential, fun row _ => hpotential row⟩
  · rintro ⟨criticalPotential, hcriticalPotential⟩
    rcases exists_potential_or_farkasCertificate delta base with
      hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
    · exact hpotential
    · have hcertificate : IsBalancedNonnegative delta coefficient :=
        ⟨hnonneg, hbalance⟩
      have hweighted : ∑ row, coefficient row * base row ≤
          ∑ row,
            coefficient row * dotProduct (delta row) criticalPotential := by
        apply Finset.sum_le_sum
        intro row _
        by_cases hcritical : IsCritical delta direction row
        · exact mul_le_mul_of_nonneg_left
            (hcriticalPotential row hcritical) (hnonneg row)
        · rw [coefficient_eq_zero_of_not_critical delta direction
            hrecession hcertificate hcritical]
          simp
      have hzero :
          ∑ row,
              coefficient row * dotProduct (delta row) criticalPotential = 0 := by
        rw [sum_mul_dotProduct]
        simp [hbalance]
      rw [hzero] at hweighted
      exact (not_lt_of_ge hweighted hpositive).elim

end Recession

end FiniteInequality

end

end Maths
