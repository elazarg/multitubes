/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.FiniteInequality.Basic
public import Mathlib.Basic.Real.Basic

import Maths.LinearProgramming.FourierMotzkin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rational and integral finite-inequality certificates

Fourier--Motzkin elimination over `ℚ` gives rational incompatibility
certificates for rational finite systems.  For integral data, clearing the
finitely many coefficient denominators gives an integral certificate.

## Main definitions

* `Maths.FiniteInequality.commonDenominator` and `integralMultiple`: the scaling
  used to clear denominators, and the resulting integer coefficient.

## Main results

* `Maths.FiniteInequality.exists_rationalPotential_or_rationalCertificate`: the
  theorem of the alternative entirely over `ℚ`, as an instance of the ordered-field statement.
* `Maths.FiniteInequality.exists_rationalPotential_iff_exists_realPotential`: a
  rational system is feasible over `ℚ` exactly when it is feasible over `ℝ`, so passing to the
  reals gains nothing.
* `Maths.FiniteInequality.exists_rationalCertificate_of_real_infeasible`: real
  infeasibility of a rational system is witnessed by a rational certificate.
* `Maths.FiniteInequality.exists_integralCoefficientCertificate_of_rationalCertificate`:
  clearing the denominators of a rational certificate gives an integer-valued one.
* `Maths.FiniteInequality.exists_integralCertificate_of_real_infeasible`: for
  integral data the certificate can be taken integer-valued.  Note only the certificate's
  denominators are cleared - the intermediate
  `exists_integralCoefficientCertificate_of_real_infeasible` still states its balance and
  objective over `ℚ`.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace FiniteInequality

open scoped BigOperators

universe uS uR

variable {State : Type uS} {Row : Type uR}
variable [Fintype State] [Fintype Row]

/-- The finite theorem of the alternative directly over the rational field: the instance `𝕜 = ℚ`
of `Maths.exists_potential_or_nonnegative_incompatibility`. -/
theorem exists_rationalPotential_or_rationalCertificate
    (delta : Row → State → ℚ) (base : Row → ℚ) :
    (∃ potential : State → ℚ,
      ∀ row, base row ≤ dotProduct (delta row) potential) ∨
    (∃ coefficient : Row → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state = 0) ∧
      0 < ∑ row, coefficient row * base row) :=
  exists_potential_or_nonnegative_incompatibility delta base

/-- Rational finite inequalities have a rational feasible point whenever they
have a real feasible point.  Thus extending scalars from `ℚ` to `ℝ` does not
create feasibility for a rational polyhedron. -/
theorem exists_rationalPotential_iff_exists_realPotential
    (delta : Row → State → ℚ) (base : Row → ℚ) :
    (∃ potential : State → ℚ,
      ∀ row, base row ≤ dotProduct (delta row) potential) ↔
    ∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        dotProduct (fun state => (delta row state : ℝ)) potential := by
  classical
  constructor
  · rintro ⟨potential, hpotential⟩
    refine ⟨fun state => (potential state : ℝ), fun row => ?_⟩
    have hcast := Rat.cast_mono (K := ℝ) (hpotential row)
    simpa only [Rat.cast_sum, Rat.cast_mul, dotProduct] using hcast
  · rintro ⟨realPotential, hrealPotential⟩
    rcases exists_rationalPotential_or_rationalCertificate delta base with
      hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
    · exact hpotential
    · exfalso
      let coefficientR : Row → ℝ := fun row => coefficient row
      have hnonnegR (row) : 0 ≤ coefficientR row := by
        dsimp [coefficientR]
        exact Rat.cast_nonneg.mpr (hnonneg row)
      have hbalanceR (state) :
          ∑ row, coefficientR row * (delta row state : ℝ) = 0 := by
        have hcast := congrArg (fun value : ℚ => (value : ℝ))
          (hbalance state)
        simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero,
          coefficientR] using hcast
      have hweak := not_nonnegative_incompatibility_of_potential
        hrealPotential hnonnegR hbalanceR
      have hpositiveR : (0 : ℝ) <
          ∑ row, coefficientR row * (base row : ℝ) := by
        have hcast : (0 : ℝ) <
            ((∑ row, coefficient row * base row : ℚ) : ℝ) :=
          Rat.cast_pos.mpr hpositive
        simpa only [Rat.cast_sum, Rat.cast_mul, coefficientR] using hcast
      linarith

/-- Real infeasibility of a rational system has a rational certificate. -/
theorem exists_rationalCertificate_of_real_infeasible
    (delta : Row → State → ℚ) (base : Row → ℚ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        ∑ state, (delta row state : ℝ) * potential state) :
    ∃ coefficient : Row → ℚ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state = 0) ∧
      0 < ∑ row, coefficient row * base row := by
  rcases exists_rationalPotential_or_rationalCertificate delta base with
    ⟨potential, hpotential⟩ | hcertificate
  · exfalso
    apply hinfeasible
    refine ⟨fun state => (potential state : ℝ), fun row => ?_⟩
    have hrow := hpotential row
    simp only [dotProduct] at hrow
    have hcast := Rat.cast_mono (K := ℝ) hrow
    simpa only [Rat.cast_sum, Rat.cast_mul] using hcast
  · exact hcertificate

/-- The product of all coefficient denominators: a common denominator that clears every
entry of a rational coefficient vector at once. -/
def commonDenominator (coefficient : Row → ℚ) : ℕ :=
  ∏ row, (coefficient row).den

private theorem commonDenominator_pos (coefficient : Row → ℚ) :
    0 < commonDenominator coefficient := by
  classical
  unfold commonDenominator
  exact Finset.prod_pos fun row _ => (coefficient row).pos

private theorem den_dvd_commonDenominator (coefficient : Row → ℚ)
    (row : Row) :
    (coefficient row).den ∣ commonDenominator coefficient := by
  classical
  exact Finset.dvd_prod_of_mem (fun candidate => (coefficient candidate).den)
    (Finset.mem_univ row)

/-- Integral coefficient obtained by clearing all rational denominators. -/
def integralMultiple (coefficient : Row → ℚ) (row : Row) : ℤ :=
  (coefficient row).num *
    (commonDenominator coefficient / (coefficient row).den : ℕ)

private theorem cast_integralMultiple (coefficient : Row → ℚ) (row : Row) :
    (integralMultiple coefficient row : ℚ) =
      commonDenominator coefficient * coefficient row := by
  have hdiv := den_dvd_commonDenominator coefficient row
  have hden : (coefficient row).den *
      (commonDenominator coefficient / (coefficient row).den) =
        commonDenominator coefficient := Nat.mul_div_cancel' hdiv
  have hdenQ : ((coefficient row).den : ℚ) *
      (commonDenominator coefficient / (coefficient row).den : ℕ) =
        commonDenominator coefficient := by
    exact_mod_cast hden
  calc
    (integralMultiple coefficient row : ℚ) =
        ((coefficient row).num : ℚ) *
          ((commonDenominator coefficient /
            (coefficient row).den : ℕ) : ℚ) := by
      simp only [integralMultiple, Int.cast_mul, Int.cast_natCast]
    _ = (coefficient row * ((coefficient row).den : ℚ)) *
          ((commonDenominator coefficient /
            (coefficient row).den : ℕ) : ℚ) := by
      rw [Rat.mul_den_eq_num]
    _ = (((coefficient row).den : ℚ) *
          ((commonDenominator coefficient /
            (coefficient row).den : ℕ) : ℚ)) *
            coefficient row := by ring
    _ = commonDenominator coefficient * coefficient row := by rw [hdenQ]

omit [Fintype State] in
/-- **Clearing denominators.**  Scaling a rational certificate by the common denominator of its
coefficients gives an integer-valued certificate of the same system.  Only the certificate
denominators are cleared; the balance and objective remain statements over `ℚ`. -/
theorem exists_integralCoefficientCertificate_of_rationalCertificate
    {delta : Row → State → ℚ} {base : Row → ℚ} {rational : Row → ℚ}
    (hnonneg : ∀ row, 0 ≤ rational row)
    (hbalance : ∀ state, ∑ row, rational row * delta row state = 0)
    (hpositive : 0 < ∑ row, rational row * base row) :
    ∃ coefficient : Row → ℤ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state,
        ∑ row, (coefficient row : ℚ) * delta row state = 0) ∧
      0 < ∑ row, (coefficient row : ℚ) * base row := by
  have hscalePos : (0 : ℚ) < commonDenominator rational := by
    exact_mod_cast commonDenominator_pos rational
  have hsum (value : Row → ℚ) :
      ∑ row, (integralMultiple rational row : ℚ) * value row =
        commonDenominator rational * ∑ row, rational row * value row := by
    simp_rw [cast_integralMultiple, Finset.mul_sum, mul_assoc]
  refine ⟨integralMultiple rational, fun row => ?_, fun state => ?_, ?_⟩
  · have hnonnegQ : (0 : ℚ) ≤ integralMultiple rational row := by
      rw [cast_integralMultiple]
      exact mul_nonneg hscalePos.le (hnonneg row)
    exact_mod_cast hnonnegQ
  · rw [hsum, hbalance state, mul_zero]
  · rw [hsum]
    exact mul_pos hscalePos hpositive

/-- Rational row data admit an integer-valued certificate whenever they are
real-infeasible.  Only the certificate denominators are cleared; the balance
and objective remain equalities and inequalities over `ℚ`. -/
theorem exists_integralCoefficientCertificate_of_real_infeasible
    (delta : Row → State → ℚ) (base : Row → ℚ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        ∑ state, (delta row state : ℝ) * potential state) :
    ∃ coefficient : Row → ℤ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state,
        ∑ row, (coefficient row : ℚ) * delta row state = 0) ∧
      0 < ∑ row, (coefficient row : ℚ) * base row := by
  obtain ⟨rational, hnonneg, hbalance, hpositive⟩ :=
    exists_rationalCertificate_of_real_infeasible delta base hinfeasible
  exact exists_integralCoefficientCertificate_of_rationalCertificate hnonneg hbalance hpositive

/-- Integral data with no real feasible potential admit a nonnegative integral
Farkas certificate with strictly positive objective. -/
theorem exists_integralCertificate_of_real_infeasible
    (delta : Row → State → ℤ) (base : Row → ℤ)
    (hinfeasible : ¬∃ potential : State → ℝ,
      ∀ row, (base row : ℝ) ≤
        ∑ state, (delta row state : ℝ) * potential state) :
    ∃ coefficient : Row → ℤ,
      (∀ row, 0 ≤ coefficient row) ∧
      (∀ state, ∑ row, coefficient row * delta row state = 0) ∧
      0 < ∑ row, coefficient row * base row := by
  obtain ⟨coefficient, hnonneg, hbalance, hpositive⟩ :=
    exists_integralCoefficientCertificate_of_real_infeasible
      (fun row state => (delta row state : ℚ)) (fun row => (base row : ℚ))
      (by simpa using hinfeasible)
  exact ⟨coefficient, hnonneg, fun state => by exact_mod_cast hbalance state,
    by exact_mod_cast hpositive⟩

end FiniteInequality

end

end Maths
