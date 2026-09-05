/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.LinearProgramming.CertificateCheck
public import Maths.Multitubes.FiniteInequality.Basic

import Mathlib.Data.Rat.BigOperators

/-!
# Checked rational witnesses for finite inequalities

The executable rational checks for a `Fin`-indexed matrix directly certify the real potential
predicates used by finite-inequality applications.  The input includes an externally supplied
point or certificate; these declarations verify witnesses but do not search for them.

## Main results

* `Maths.FiniteInequality.realPotential_of_checkRationalPoint`: a checked rational point gives
  a real potential satisfying every finite inequality.
* `Maths.FiniteInequality.not_realPotential_of_checkRationalCertificate`: a checked rational
  Farkas certificate proves that no real potential satisfies every finite inequality.

## Tags

rational arithmetic, executable verification, finite inequalities, Farkas certificate
-/

@[expose] public section

namespace Maths
namespace FiniteInequality

/-- A checked rational point, cast coordinatewise, satisfies the corresponding real finite
inequalities. -/
theorem realPotential_of_checkRationalPoint {m n : ℕ}
    (delta : Fin m → Fin n → ℚ) (base : Fin m → ℚ) (point : Fin n → ℚ)
    (hcheck : LinearProgramming.checkRationalPoint delta base point = true) :
    ∀ row, (base row : ℝ) ≤
      dotProduct (fun state => (delta row state : ℝ))
        (fun state => (point state : ℝ)) := by
  intro row
  have hrow :=
    (LinearProgramming.checkRationalPoint_eq_true_iff delta base point).mp hcheck row
  have hcast := Rat.cast_mono (K := ℝ) hrow
  simpa only [LinearProgramming.rowEval, Rat.cast_sum, Rat.cast_mul, dotProduct] using hcast

/-- A checked rational Farkas certificate rules out every real potential for the corresponding
finite inequalities. -/
theorem not_realPotential_of_checkRationalCertificate {m n : ℕ}
    (delta : Fin m → Fin n → ℚ) (base : Fin m → ℚ) (coefficient : Fin m → ℚ)
    (hcheck :
      LinearProgramming.checkRationalCertificate delta base coefficient = true) :
    ¬ ∃ potential : Fin n → ℝ,
      ∀ row, (base row : ℝ) ≤
        dotProduct (fun state => (delta row state : ℝ)) potential := by
  intro hpotential
  apply LinearProgramming.not_realFeasible_of_checkRationalCertificate
    delta base coefficient hcheck
  obtain ⟨potential, hpotential⟩ := hpotential
  refine ⟨potential, fun row => ?_⟩
  simpa only [LinearProgramming.rowEval, dotProduct] using hpotential row

end FiniteInequality
end Maths
