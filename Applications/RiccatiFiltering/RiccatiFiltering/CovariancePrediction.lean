/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Mixed.Order
public import Mathlib.Analysis.Matrix.Order

/-!
# Covariance prediction as Löwner transport

A linear state transition with process covariance `Q` sends a covariance matrix `P` to
`A * P * Aᴴ + Q`. This map preserves positive semidefiniteness and is monotone in the Löwner
order. Edge matrices may be rectangular, so the covariance dimension can change along a typed
walk.

The positive semidefinite cone is only used as an ordered fiber. No lattice operations or matrix
inverses are required. Consequently exact, lax, oplax, and mixed-section path results apply
directly to mode-dependent covariance bounds.

## Main definitions

* `RiccatiFiltering.CovarianceMatrix` - positive semidefinite complex covariance matrices.
* `RiccatiFiltering.covariancePrediction` - the update `P ↦ A * P * Aᴴ + Q`.
* `RiccatiFiltering.predictionTransport` - edgewise heterogeneous covariance prediction.

## Main results

* `RiccatiFiltering.monotone_covariancePrediction` - covariance prediction is
  Löwner-monotone.
* `RiccatiFiltering.monotone_predictionTransport_edgeMap` - every prediction edge is
  monotone.
* `RiccatiFiltering.prediction_walkMap_le_of_lax_or_exact` - propagation of upper covariance
  bounds.
* `RiccatiFiltering.prediction_le_walkMap_of_oplax_or_exact` - propagation of lower covariance
  bounds.

## Tags

covariance prediction, positive semidefinite matrix, Löwner order, transport
-/

@[expose] public section

namespace RiccatiFiltering

open Maths Matrix
open scoped ComplexOrder MatrixOrder

universe uI uO uV uE uW

/-- Positive semidefinite covariance matrices with their inherited Löwner order. -/
abbrev CovarianceMatrix (index : Type*) [Fintype index] :=
  {P : Matrix index index ℂ // P.PosSemidef}

/-- Covariance prediction through a linear transition with additive process covariance. -/
def covariancePrediction {I : Type uI} {O : Type uO} [Fintype I] [Fintype O]
    (dynamics : Matrix O I ℂ) (processNoise : CovarianceMatrix O)
    (prior : CovarianceMatrix I) : CovarianceMatrix O :=
  ⟨dynamics * prior.1 * dynamicsᴴ + processNoise.1,
    (prior.2.mul_mul_conjTranspose_same dynamics).add processNoise.2⟩

/-- Covariance prediction is monotone in the Löwner order. -/
theorem monotone_covariancePrediction {I : Type uI} {O : Type uO}
    [Fintype I] [Fintype O] (dynamics : Matrix O I ℂ)
    (processNoise : CovarianceMatrix O) :
    Monotone (covariancePrediction dynamics processNoise) := by
  intro first second hle
  change first.1 ≤ second.1 at hle
  change dynamics * first.1 * dynamicsᴴ + processNoise.1 ≤
    dynamics * second.1 * dynamicsᴴ + processNoise.1
  rw [Matrix.le_iff] at hle ⊢
  rw [add_sub_add_right_eq_sub, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact hle.mul_mul_conjTranspose_same dynamics

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)
variable (W : V → Type uW) [∀ vertex, Fintype (W vertex)]

/-- Transport by mode-dependent covariance prediction maps. -/
def predictionTransport
    (dynamics : (edge : E) →
      Matrix (W (G.target edge)) (W (G.source edge)) ℂ)
    (processNoise : (edge : E) → CovarianceMatrix (W (G.target edge))) :
    Transport G (fun vertex ↦ CovarianceMatrix (W vertex)) where
  edgeMap edge := covariancePrediction (dynamics edge) (processNoise edge)

/-- Every covariance prediction edge is Löwner-monotone. -/
theorem monotone_predictionTransport_edgeMap
    (dynamics : (edge : E) →
      Matrix (W (G.target edge)) (W (G.source edge)) ℂ)
    (processNoise : (edge : E) → CovarianceMatrix (W (G.target edge))) :
    ∀ edge, Monotone ((predictionTransport G W dynamics processNoise).edgeMap edge) := by
  intro edge
  exact monotone_covariancePrediction (dynamics edge) (processNoise edge)

variable {G W}
variable {dynamics : (edge : E) →
  Matrix (W (G.target edge)) (W (G.source edge)) ℂ}
variable {processNoise : (edge : E) → CovarianceMatrix (W (G.target edge))}
variable {mode : E → EdgeMode}
variable {family : ∀ vertex, CovarianceMatrix (W vertex)}
variable {start finish : V}

/-- Mixed local prediction constraints give an upper covariance bound along every path whose
edges are lax or exact. -/
theorem prediction_walkMap_le_of_lax_or_exact
    (hfamily : (predictionTransport G W dynamics processNoise).IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    (predictionTransport G W dynamics processNoise).walkMap walk (family start) ≤
      family finish := by
  exact hfamily.walkMap_le_of_lax_or_exact
    (monotone_predictionTransport_edgeMap G W dynamics processNoise) walk hmode

/-- Mixed local prediction constraints give a lower covariance bound along every path whose
edges are oplax or exact. -/
theorem prediction_le_walkMap_of_oplax_or_exact
    (hfamily : (predictionTransport G W dynamics processNoise).IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    family finish ≤
      (predictionTransport G W dynamics processNoise).walkMap walk (family start) := by
  exact hfamily.le_walkMap_of_oplax_or_exact
    (monotone_predictionTransport_edgeMap G W dynamics processNoise) walk hmode

end RiccatiFiltering
