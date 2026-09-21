/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.LinearProgramming.FourierMotzkin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic

import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable checks for rational linear-inequality witnesses

Finite rational arithmetic is decidable, so proposed points and Farkas certificates for a
system `A x ≥ b` can be checked by computation.  The checks in this file consume externally
supplied witnesses; they do not search for a point or certificate.

The row and column dimensions occur in the types, so malformed witness shapes cannot be passed
to either checker.  A checker can still reject a correctly shaped witness whose arithmetic does
not establish the requested conclusion.

## Main definitions

* `Maths.LinearProgramming.checkRationalPoint`: check a proposed rational feasible point.
* `Maths.LinearProgramming.checkRationalCertificate`: check a proposed rational Farkas
  certificate.

## Main results

* `Maths.LinearProgramming.checkRationalPoint_eq_true_iff`: the point check is equivalent to
  satisfaction of every row, and hence witnesses primal feasibility.
* `Maths.LinearProgramming.checkRationalCertificate_eq_true_iff`: the certificate check is
  equivalent to `Maths.LinearProgramming.IsCertificate`.
* `Maths.LinearProgramming.realFeasible_of_checkRationalPoint`: a checked rational point also
  supplies a feasible point after extending the system to the reals.
* `Maths.LinearProgramming.not_realFeasible_of_checkRationalCertificate`: a checked rational
  certificate also proves infeasibility after extending the system to the reals.

## Tags

rational arithmetic, executable verification, linear inequalities, Farkas certificate
-/

open Finset

@[expose] public section

namespace Maths
namespace LinearProgramming

/-- A list fold over all elements of `Fin n` agrees with the corresponding finite sum. -/
theorem list_sum_ofFn {n : ℕ} (f : Fin n → ℚ) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih]

/-- Evaluate a rational row using a list fold.  This computational presentation agrees with
`Maths.LinearProgramming.rowEval` but does not require compiled multiset internals. -/
def rationalRowEval {m n : ℕ} (A : Fin m → Fin n → ℚ) (i : Fin m)
    (x : Fin n → ℚ) : ℚ :=
  (List.ofFn fun j => A i j * x j).sum

/-- The list-based rational row evaluator agrees with the mathematical finite sum. -/
@[simp] theorem rationalRowEval_eq_rowEval {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (i : Fin m) (x : Fin n → ℚ) : rationalRowEval A i x = rowEval A i x := by
  exact list_sum_ofFn _

/-- Check whether a proposed rational point satisfies every row of `A x ≥ b`. -/
def checkRationalPoint {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Bool :=
  decide (∀ i, b i ≤ rationalRowEval A i x)

/-- Check whether proposed rational weights form a Farkas certificate for `A x ≥ b`. -/
def checkRationalCertificate {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (u : Fin m → ℚ) : Bool :=
  decide ((∀ i, 0 ≤ u i) ∧
    (∀ j : Fin n, (List.ofFn fun i => u i * A i j).sum = 0) ∧
    (0 < (List.ofFn fun i => u i * b i).sum))

/-- The executable point check succeeds exactly when the proposed point satisfies every row. -/
theorem checkRationalPoint_eq_true_iff {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x : Fin n → ℚ) :
    checkRationalPoint A b x = true ↔ ∀ i, b i ≤ rowEval A i x := by
  constructor
  · intro h
    simpa using (of_decide_eq_true h)
  · intro h
    apply decide_eq_true
    simpa using h

/-- A successful point check supplies a witness of primal feasibility. -/
theorem isFeasible_of_checkRationalPoint {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x : Fin n → ℚ) (hcheck : checkRationalPoint A b x = true) :
    IsFeasible A b :=
  ⟨x, (checkRationalPoint_eq_true_iff A b x).mp hcheck⟩

/-- A successful rational point check supplies a feasible point for the coefficientwise cast
system over the real numbers. -/
theorem realFeasible_of_checkRationalPoint {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ)
    (hcheck : checkRationalPoint A b x = true) :
    @IsFeasible ℝ _ _ (Fin m) n _
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) := by
  refine ⟨fun j => (x j : ℝ), fun i => ?_⟩
  have hrow := (checkRationalPoint_eq_true_iff A b x).mp hcheck i
  have hcast := Rat.cast_mono (K := ℝ) hrow
  simpa only [rowEval, Rat.cast_sum, Rat.cast_mul] using hcast

/-- The executable certificate check succeeds exactly for a Farkas certificate. -/
theorem checkRationalCertificate_eq_true_iff {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (u : Fin m → ℚ) :
    checkRationalCertificate A b u = true ↔ IsCertificate A b u := by
  change decide ((∀ i, 0 ≤ u i) ∧
    (∀ j : Fin n, (List.ofFn fun i => u i * A i j).sum = 0) ∧
    (0 < (List.ofFn fun i => u i * b i).sum)) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [IsCertificate, list_sum_ofFn]

/-- A successful rational certificate check rules out rational primal feasibility. -/
theorem not_isFeasible_of_checkRationalCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (u : Fin m → ℚ)
    (hcheck : checkRationalCertificate A b u = true) :
    ¬ IsFeasible A b := by
  intro hfeasible
  exact feas_cert_disjoint A b hfeasible
    ⟨u, (checkRationalCertificate_eq_true_iff A b u).mp hcheck⟩

/-- A successful rational certificate check rules out feasibility of the coefficientwise
cast system over the real numbers. -/
theorem not_realFeasible_of_checkRationalCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (u : Fin m → ℚ)
    (hcheck : checkRationalCertificate A b u = true) :
    ¬ @IsFeasible ℝ _ _ (Fin m) n _
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) := by
  intro hfeasible
  have hcertificateQ := (checkRationalCertificate_eq_true_iff A b u).mp hcheck
  have hcertificateR : @IsCertificate ℝ _ _ (Fin m) n _
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) (fun i => (u i : ℝ)) := by
    refine ⟨fun i => Rat.cast_nonneg.mpr (hcertificateQ.1 i), ?_, ?_⟩
    · intro j
      have hcast := congrArg (fun value : ℚ => (value : ℝ)) (hcertificateQ.2.1 j)
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] using hcast
    · have hcast : (0 : ℝ) < ((∑ i, u i * b i : ℚ) : ℝ) :=
        Rat.cast_pos.mpr hcertificateQ.2.2
      simpa only [Rat.cast_sum, Rat.cast_mul] using hcast
  exact feas_cert_disjoint _ _ hfeasible ⟨_, hcertificateR⟩

end LinearProgramming
end Maths

private def feasibleExampleMatrix : Fin 2 → Fin 1 → ℚ
  | 0, _ => 1
  | 1, _ => -1

private def feasibleExampleBound : Fin 2 → ℚ
  | 0 => 1
  | 1 => -2

private def infeasibleExampleBound : Fin 2 → ℚ
  | 0 => 1
  | 1 => 0

#guard Maths.LinearProgramming.checkRationalPoint feasibleExampleMatrix feasibleExampleBound
  (fun _ => 1) == true

#guard Maths.LinearProgramming.checkRationalPoint feasibleExampleMatrix feasibleExampleBound
  (fun _ => 0) == false

#guard Maths.LinearProgramming.checkRationalCertificate feasibleExampleMatrix
  infeasibleExampleBound (fun _ => 1) == true

#guard Maths.LinearProgramming.checkRationalCertificate feasibleExampleMatrix
  infeasibleExampleBound (fun _ => -1) == false

#guard Maths.LinearProgramming.checkRationalCertificate feasibleExampleMatrix
  infeasibleExampleBound (fun i => if i = 0 then 1 else 0) == false

#guard Maths.LinearProgramming.checkRationalCertificate feasibleExampleMatrix
  (fun _ => 0) (fun _ => 1) == false
