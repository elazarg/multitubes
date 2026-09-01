/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import RiccatiFiltering.CovariancePrediction
public import RiccatiFiltering.ScalarRiccati

/-!
# Covariance and Riccati transport

Covariance prediction is a heterogeneous Löwner-monotone transport on positive semidefinite
matrices. Scalar observation adds a nonlinear monotone Riccati step. Exact, lax, and oplax
sections give consistent, upper-bounding, and lower-bounding covariance families.

## Main definitions

* `RiccatiFiltering.CovarianceMatrix` - the positive semidefinite covariance cone.
* `RiccatiFiltering.covariancePrediction` - the matrix update `P ↦ A P Aᴴ + Q`.
* `RiccatiFiltering.predictionTransport` - heterogeneous covariance prediction transport.
* `RiccatiFiltering.scalarObservation` - the scalar covariance observation update.
* `RiccatiFiltering.scalarRiccati` - scalar prediction followed by observation.
* `RiccatiFiltering.scalarRiccatiTransport` - graph transport by scalar Riccati maps.

## Main results

* `RiccatiFiltering.monotone_covariancePrediction` - matrix prediction is Löwner-monotone.
* `RiccatiFiltering.prediction_walkMap_le_of_lax_or_exact` and
  `RiccatiFiltering.prediction_le_walkMap_of_oplax_or_exact` - matrix path bounds.
* `RiccatiFiltering.monotone_scalarObservation` and
  `RiccatiFiltering.scalarObservation_le` - scalar observation is monotone and reduces
  covariance.
* `RiccatiFiltering.monotone_scalarRiccati` - the scalar Riccati map is monotone.
* `RiccatiFiltering.scalar_walkMap_le_of_lax_or_exact` and
  `RiccatiFiltering.scalar_le_walkMap_of_oplax_or_exact` - nonlinear scalar path bounds.

## Tags

Riccati equation, covariance, filtering, Löwner order, positive semidefinite matrix
-/

@[expose] public section

namespace RiccatiFiltering

end RiccatiFiltering
