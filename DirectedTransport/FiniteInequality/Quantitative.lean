/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.FiniteInequality.Basic

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

* `DirectedTransport.FiniteInequality.IsNormalizedCertificate`: a balanced nonnegative row
  combination of total mass one.
* `DirectedTransport.FiniteInequality.certificateValue`: its objective value against lower
  bounds.
* `DirectedTransport.FiniteInequality.WorstResidualAtMost`: existence of a potential whose
  worst row residual is at most a given level.
* `DirectedTransport.FiniteInequality.Recession.IsBalancedNonnegative` and
  `DirectedTransport.FiniteInequality.Recession.IsCritical`: a balanced nonnegative combination
  without the mass-one normalization, and the rows on which a recession direction has zero
  gain.

## Main results

* `DirectedTransport.FiniteInequality.worstResidualAtMost_iff_normalizedDual_le`: the exact
  threshold duality - a worst-residual threshold is attainable exactly when every normalized
  certificate has objective at most that threshold.  It is stated level by level rather than
  through an extended-real infimum, which is what keeps the certificate-free case meaningful.
* `DirectedTransport.FiniteInequality.certificateValue_le_of_worstResidualAtMost`: the easy
  direction, usable on its own.
* `DirectedTransport.FiniteInequality.Recession.coefficient_eq_zero_of_not_critical`: every
  balanced nonnegative certificate is supported on rows critical for any common recession
  direction.
* `DirectedTransport.FiniteInequality.Recession.exists_potential_iff_exists_critical_potential`:
  feasibility of the whole system reduces to feasibility of that critical subsystem.
-/

@[expose] public section

namespace DirectedTransport

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

private theorem coefficient_eq_zero_of_sum_eq_zero
    (coefficient : Row → ℝ) (hnonneg : ∀ row, 0 ≤ coefficient row)
    (hsum : ∑ row, coefficient row = 0) :
    ∀ row, coefficient row = 0 := by
  intro row
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun index _ => hnonneg index)).mp hsum
  exact hall row (Finset.mem_univ row)

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
  have hweak := not_nonnegative_incompatibility_of_potential
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
    rcases exists_potential_or_nonnegative_incompatibility delta
      (fun row => base row - level) with
      hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
    · exact ⟨hpotential.choose, fun row => by
        have := hpotential.choose_spec row
        linarith⟩
    · have hmassNonneg : 0 ≤ ∑ row, coefficient row :=
        Finset.sum_nonneg fun row _ => hnonneg row
      have hmassPos : 0 < ∑ row, coefficient row := by
        by_contra hnot
        have hmassZero : ∑ row, coefficient row = 0 :=
          le_antisymm (le_of_not_gt hnot) hmassNonneg
        have hzero := coefficient_eq_zero_of_sum_eq_zero
          coefficient hnonneg hmassZero
        have : ∑ row, coefficient row * (base row - level) = 0 := by
          simp [hzero]
        linarith
      let mass := ∑ row, coefficient row
      let normalized : Row → ℝ := fun row => coefficient row / mass
      have hnormalized : IsNormalizedCertificate delta normalized := by
        refine ⟨fun row => div_nonneg (hnonneg row) hmassNonneg, ?_, ?_⟩
        · dsimp [normalized, mass]
          rw [← Finset.sum_div, div_self hmassPos.ne']
        · intro state
          dsimp [normalized, mass]
          simp only [div_mul_eq_mul_div]
          rw [← Finset.sum_div, hbalance state, zero_div]
      have hvalue : level < certificateValue base normalized := by
        dsimp [certificateValue, normalized, mass]
        simp only [div_mul_eq_mul_div]
        rw [← Finset.sum_div]
        rw [weighted_shiftedBase_eq] at hpositive
        simp only [certificateValue] at hpositive
        rw [lt_div_iff₀ hmassPos]
        nlinarith
      exact (not_lt_of_ge (hdual normalized hnormalized) hvalue).elim

/-! ## Recession reduction -/

namespace Recession

/-- A nonnegative balanced combination of row vectors. -/
def IsBalancedNonnegative
    (delta : Row → State → ℝ) (coefficient : Row → ℝ) : Prop :=
  (∀ row, 0 ≤ coefficient row) ∧
    ∀ state, ∑ row, coefficient row * delta row state = 0

/-- Rows on which a recession direction has zero gain. -/
def IsCritical (delta : Row → State → ℝ) (direction : State → ℝ)
    (row : Row) : Prop :=
  dotProduct (delta row) direction = 0

private theorem weighted_dot_eq
    (delta : Row → State → ℝ) (coefficient : Row → ℝ)
    (direction : State → ℝ) :
    (∑ row, coefficient row * dotProduct (delta row) direction) =
      ∑ state, (∑ row, coefficient row * delta row state) * direction state := by
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro row _
  ring

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
    rw [weighted_dot_eq]
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
    rcases exists_potential_or_nonnegative_incompatibility delta base with
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
        rw [weighted_dot_eq]
        simp [hbalance]
      rw [hzero] at hweighted
      exact (not_lt_of_ge hweighted hpositive).elim

end Recession

end FiniteInequality

end

end DirectedTransport
