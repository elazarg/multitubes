/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Order
public import Mathlib.Data.NNReal.Defs

import Mathlib.Tactic.Linarith

/-!
# Scalar Riccati transport

For a nonnegative prior covariance `p` and observation-noise covariance `r`, the scalar
observation update is `p * r / (p + r)`. It is monotone in the prior and never exceeds it.
Composing it with the affine prediction `p ↦ gain * p + processNoise` gives a nonlinear scalar
Riccati map.

Edgewise scalar Riccati maps form a monotone directed transport. Mixed local covariance bounds
therefore propagate along every typed walk of a compatible polarity without requiring a closed
form for the composite nonlinear recurrence.

## Main definitions

* `RiccatiFiltering.scalarObservation` - scalar conditioning by observation noise.
* `RiccatiFiltering.scalarRiccati` - scalar prediction followed by observation.
* `RiccatiFiltering.scalarRiccatiTransport` - edgewise scalar Riccati transport.

## Main results

* `RiccatiFiltering.monotone_scalarObservation` - observation is monotone in the prior.
* `RiccatiFiltering.scalarObservation_le` - observation does not increase covariance.
* `RiccatiFiltering.monotone_scalarRiccati` - the full scalar update is monotone.
* `RiccatiFiltering.scalarRiccati_le_prediction` - the observation update is below prediction.
* `RiccatiFiltering.scalar_walkMap_le_of_lax_or_exact` - propagation of upper covariance bounds.
* `RiccatiFiltering.scalar_le_walkMap_of_oplax_or_exact` - propagation of lower covariance bounds.

## Tags

scalar Riccati equation, covariance, filtering, nonlinear transport
-/

@[expose] public section

noncomputable section

namespace RiccatiFiltering

open Maths
open scoped NNReal

universe uV uE

/-- Scalar posterior covariance after an observation with noise covariance `noise`. -/
def scalarObservation (noise prior : ℝ≥0) : ℝ≥0 :=
  prior * noise / (prior + noise)

/-- Scalar observation is monotone in the prior covariance. -/
theorem monotone_scalarObservation (noise : ℝ≥0) :
    Monotone (scalarObservation noise) := by
  intro first second hle
  by_cases hnoise : noise = 0
  · simp [scalarObservation, hnoise]
  · have hnoisePos : 0 < noise := pos_iff_ne_zero.mpr hnoise
    have hfirstPos : 0 < first + noise :=
      lt_of_le_of_lt bot_le (lt_add_of_pos_right first hnoisePos)
    have hsecondPos : 0 < second + noise :=
      lt_of_le_of_lt bot_le (lt_add_of_pos_right second hnoisePos)
    rw [scalarObservation, scalarObservation, div_le_div_iff₀ hfirstPos hsecondPos]
    calc
      first * noise * (second + noise) =
          first * second * noise + first * noise * noise := by ring
      _ ≤ first * second * noise + second * noise * noise := by
        gcongr
      _ = second * noise * (first + noise) := by ring

/-- Conditioning by an observation never increases scalar covariance. -/
theorem scalarObservation_le (noise prior : ℝ≥0) :
    scalarObservation noise prior ≤ prior := by
  by_cases hdenominator : prior + noise = 0
  · simp [scalarObservation, hdenominator]
  · have hpositive : 0 < prior + noise := pos_iff_ne_zero.mpr hdenominator
    rw [scalarObservation, div_le_iff₀ hpositive]
    calc
      prior * noise ≤ prior * prior + prior * noise := le_add_of_nonneg_left bot_le
      _ = prior * (prior + noise) := by ring

/-- Scalar affine prediction followed by the nonlinear observation update. -/
def scalarRiccati (gain processNoise observationNoise prior : ℝ≥0) : ℝ≥0 :=
  scalarObservation observationNoise (gain * prior + processNoise)

/-- The scalar Riccati update is monotone in the prior covariance. -/
theorem monotone_scalarRiccati (gain processNoise observationNoise : ℝ≥0) :
    Monotone (scalarRiccati gain processNoise observationNoise) := by
  intro first second hle
  apply monotone_scalarObservation observationNoise
  exact add_le_add_left (mul_le_mul_of_nonneg_left hle bot_le) processNoise

/-- The posterior scalar covariance is below its predicted covariance. -/
theorem scalarRiccati_le_prediction (gain processNoise observationNoise prior : ℝ≥0) :
    scalarRiccati gain processNoise observationNoise prior ≤ gain * prior + processNoise :=
  scalarObservation_le observationNoise (gain * prior + processNoise)

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-- Directed transport by edgewise nonlinear scalar Riccati updates. -/
def scalarRiccatiTransport (gain processNoise observationNoise : E → ℝ≥0) :
    Transport G (fun _vertex ↦ ℝ≥0) where
  edgeMap edge := scalarRiccati (gain edge) (processNoise edge) (observationNoise edge)

/-- Every scalar Riccati transport edge is monotone. -/
theorem monotone_scalarRiccatiTransport_edgeMap
    (gain processNoise observationNoise : E → ℝ≥0) :
    ∀ edge, Monotone ((scalarRiccatiTransport G gain processNoise observationNoise).edgeMap edge) :=
  fun edge ↦ monotone_scalarRiccati (gain edge) (processNoise edge) (observationNoise edge)

variable {G}
variable {gain processNoise observationNoise : E → ℝ≥0}
variable {mode : E → EdgeMode} {family : V → ℝ≥0}
variable {start finish : V}

/-- Mixed local scalar Riccati constraints give an upper covariance bound along every path whose
edges are lax or exact. -/
theorem scalar_walkMap_le_of_lax_or_exact
    (hfamily : (scalarRiccatiTransport G gain processNoise observationNoise).IsMixedSection
      mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    (scalarRiccatiTransport G gain processNoise observationNoise).walkMap
        walk (family start) ≤ family finish := by
  exact hfamily.walkMap_le_of_lax_or_exact
    (monotone_scalarRiccatiTransport_edgeMap G gain processNoise observationNoise) walk hmode

/-- Mixed local scalar Riccati constraints give a lower covariance bound along every path whose
edges are oplax or exact. -/
theorem scalar_le_walkMap_of_oplax_or_exact
    (hfamily : (scalarRiccatiTransport G gain processNoise observationNoise).IsMixedSection
      mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    family finish ≤
      (scalarRiccatiTransport G gain processNoise observationNoise).walkMap
        walk (family start) := by
  exact hfamily.le_walkMap_of_oplax_or_exact
    (monotone_scalarRiccatiTransport_edgeMap G gain processNoise observationNoise) walk hmode

end RiccatiFiltering
