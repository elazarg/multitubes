/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.LinearAlgebra.StandardForm

/-!
# Normalized Farkas certificates

A homogeneous Farkas system `balance *ᵥ z = 0` with `0 ≤ z` is a cone: it is invariant under
positive scaling, so it has no extreme point other than the origin and no bounded optimum. It
is *normalized* here by appending one extra row, a mass functional `mass`, constrained to take
the value `1`. The result is a standard-form polyhedron in the sense of
`DirectedTransport.LinearAlgebra.StandardForm`: a bounded slice of the certificate cone that
meets every ray of it on which the mass is positive.

This file is only the change of coordinates. Everything proved about the resulting set -
closedness, Farkas duality, extreme points and their sparsity, attainment of linear optima -
comes from `DirectedTransport.LinearAlgebra.StandardForm`, which this file re-exports.

## Main definitions

* `DirectedTransport.LinearAlgebra.normalizedFarkasMatrix`: a homogeneous balance matrix with
  a mass row appended.
* `DirectedTransport.LinearAlgebra.normalizedFarkasRhs`: the matching right-hand side, zero on
  the balance rows and one on the mass row.
* `DirectedTransport.LinearAlgebra.normalizedFarkasCertificateSet`: the set of nonnegative
  vectors that balance and have unit mass, as a standard-form fiber.

## Main results

* `DirectedTransport.LinearAlgebra.mem_normalizedFarkasCertificateSet`: membership, unpacked
  into the balance and unit-mass conditions.
* `DirectedTransport.LinearAlgebra.isClosed_normalizedFarkasCertificateSet`: the certificate
  set is closed.
-/

open Finset Matrix Set

@[expose] public section

namespace DirectedTransport
namespace LinearAlgebra

/-! ### The normalized Farkas system

A homogeneous Farkas system `balance *ᵥ z = 0`, `0 ≤ z`, is a cone: it is invariant under
positive scaling. Appending a mass row and demanding unit mass cuts that cone down to a
standard-form polyhedron. -/

/-- Add a normalizing mass row to a homogeneous Farkas balance matrix. -/
def normalizedFarkasMatrix
    {Row Col : Type*}
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) :
    Matrix (Row ⊕ Unit) Col ℝ
  | Sum.inl i, j => balance i j
  | Sum.inr _, j => mass j

/-- The balance rows of the normalized Farkas matrix are the rows of `balance`. -/
@[simp] theorem normalizedFarkasMatrix_inl
    {Row Col : Type*} (balance : Matrix Row Col ℝ) (mass : Col → ℝ)
    (i : Row) (j : Col) :
    normalizedFarkasMatrix balance mass (Sum.inl i) j = balance i j := rfl

/-- The extra row of the normalized Farkas matrix is the mass functional. -/
@[simp] theorem normalizedFarkasMatrix_inr
    {Row Col : Type*} (balance : Matrix Row Col ℝ) (mass : Col → ℝ)
    (u : Unit) (j : Col) :
    normalizedFarkasMatrix balance mass (Sum.inr u) j = mass j := rfl

/-- The right-hand side for a normalized homogeneous Farkas certificate: zero on the balance
rows and one on the mass row. -/
def normalizedFarkasRhs
    {Row : Type*} : Row ⊕ Unit → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The normalized Farkas right-hand side vanishes on the balance rows. -/
@[simp] theorem normalizedFarkasRhs_inl {Row : Type*} (i : Row) :
    (normalizedFarkasRhs : Row ⊕ Unit → ℝ) (Sum.inl i) = 0 := rfl

/-- The normalized Farkas right-hand side is one on the mass row. -/
@[simp] theorem normalizedFarkasRhs_inr {Row : Type*} (u : Unit) :
    (normalizedFarkasRhs : Row ⊕ Unit → ℝ) (Sum.inr u) = 1 := rfl

/-- The nonnegative normalized Farkas certificates of a homogeneous balance system: the
standard-form fiber of the mass-augmented matrix. -/
def normalizedFarkasCertificateSet
    {Row Col : Type*} [Fintype Col]
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) :
    Set (Col → ℝ) :=
  standardFeasibleSet
    (normalizedFarkasMatrix balance mass)
    normalizedFarkasRhs

/-- A normalized Farkas certificate is a nonnegative vector that balances and has unit mass. -/
theorem mem_normalizedFarkasCertificateSet
    {Row Col : Type*} [Fintype Col]
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) (z : Col → ℝ) :
    z ∈ normalizedFarkasCertificateSet balance mass ↔
      (∀ j, 0 ≤ z j) ∧ balance *ᵥ z = 0 ∧ ∑ j, mass j * z j = 1 := by
  simp only [normalizedFarkasCertificateSet, mem_standardFeasibleSet]
  constructor
  · rintro ⟨hz, heq⟩
    refine ⟨hz, funext fun i => ?_, ?_⟩
    · simpa [Matrix.mulVec, dotProduct] using congrFun heq (Sum.inl i)
    · simpa [Matrix.mulVec, dotProduct] using congrFun heq (Sum.inr ())
  · rintro ⟨hz, hbal, hmass⟩
    refine ⟨hz, funext fun i => ?_⟩
    rcases i with i | u
    · simpa [Matrix.mulVec, dotProduct] using congrFun hbal i
    · simpa [Matrix.mulVec, dotProduct] using hmass

/-- The set of normalized Farkas certificates is closed. -/
theorem isClosed_normalizedFarkasCertificateSet
    {Row Col : Type*} [Fintype Col]
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) :
    IsClosed (normalizedFarkasCertificateSet balance mass) :=
  isClosed_standardFeasibleSet _ _

end LinearAlgebra
end DirectedTransport
