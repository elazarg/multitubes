/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Worklist
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases

/-!
# Threshold endorsement by fair relaxation

A threshold policy may combine evidence that arrived along different endorsement paths.  The
four-context example has two seed tokens, both transported to an aggregation context.  A nonlinear
edge releases a third token only after both seeds are present.  Processing that threshold edge
before its inputs requires a second sweep.

The threshold transfer is monotone but does not preserve binary joins.  It therefore lies beyond
the union-preserving path-closure interface: joining the results of individual paths cannot model
the intermediate combination of evidence.  Finite sweep relaxation nevertheless computes the
least sound assignment, and the generic stopping theorem certifies the observed fixed point.

The example models only the logical shape of a two-endorsement policy.  It makes no claim about
cryptographic validity, independence of endorsers, probability, or truth.

## Main definitions

* `WebOfTrust.thresholdTransfer` - release token `2` exactly when tokens `0` and `1` are present.
* `WebOfTrust.thresholdTransport` - the four-context endorsement transport.
* `WebOfTrust.thresholdSeed` and `WebOfTrust.thresholdExpected` - the input and final families.
* `WebOfTrust.thresholdSweep` - the deliberately reverse-ordered sweep.

## Main results

* `WebOfTrust.thresholdTransfer_not_map_sup` - the threshold transfer does not preserve joins.
* `WebOfTrust.thresholdSweep_one` and `WebOfTrust.thresholdSweep_two` - one sweep accumulates the
  two inputs, while the second releases the threshold token.
* `WebOfTrust.thresholdExpected_isLax` - the computed family satisfies every endorsement rule.
* `WebOfTrust.thresholdSweep_two_isLeast` - the generic sweep stopping theorem proves that the
  two-pass result is the least sound assignment above the seeds.

## Tags

web of trust, threshold policy, worklist, chaotic iteration, nonlinear evidence
-/

@[expose] public section

namespace WebOfTrust

open Maths

/-- Release token `2` when both prerequisite tokens `0` and `1` are present. -/
def thresholdTransfer (facts : Finset (Fin 3)) : Finset (Fin 3) :=
  if 0 ∈ facts ∧ 1 ∈ facts then {2} else ∅

/-- The threshold transfer is monotone in the available evidence. -/
theorem monotone_thresholdTransfer : Monotone thresholdTransfer := by
  intro first second hle
  by_cases hfirst : 0 ∈ first ∧ 1 ∈ first
  · have hsecond : 0 ∈ second ∧ 1 ∈ second := ⟨hle hfirst.1, hle hfirst.2⟩
    simp [thresholdTransfer, hfirst, hsecond]
  · simp [thresholdTransfer, hfirst]

/-- Combining two insufficient evidence sets can trigger the threshold, so the transfer does not
preserve binary joins. -/
theorem thresholdTransfer_not_map_sup :
    thresholdTransfer ({0} ⊔ {1}) ≠ thresholdTransfer {0} ⊔ thresholdTransfer {1} := by
  decide

/-- Three endorsement edges: two inputs into context `2`, followed by its threshold output. -/
def thresholdGraph : EdgeGraph (Fin 4) (Fin 3) where
  source := ![0, 1, 2]
  target := ![2, 2, 3]

/-- The first two edges copy evidence; the last applies the threshold rule. -/
def thresholdEdgeMap (edge : Fin 3) : Finset (Fin 3) → Finset (Fin 3) :=
  ![id, id, thresholdTransfer] edge

/-- Transport for the finite threshold-endorsement example. -/
def thresholdTransport : Transport thresholdGraph (fun _ ↦ Finset (Fin 3)) where
  edgeMap := thresholdEdgeMap

/-- Every edge transfer in the threshold example is monotone. -/
theorem monotone_thresholdEdgeMap :
    ∀ edge, Monotone (thresholdTransport.edgeMap edge) := by
  intro edge
  fin_cases edge
  · exact fun _ _ hle ↦ hle
  · exact fun _ _ hle ↦ hle
  · exact monotone_thresholdTransfer

/-- Seed token `0` at context `0` and token `1` at context `1`. -/
def thresholdSeed : Fin 4 → Finset (Fin 3) :=
  ![{0}, {1}, ∅, ∅]

/-- The least sound result: both inputs accumulate at context `2`, releasing token `2` at `3`. -/
def thresholdExpected : Fin 4 → Finset (Fin 3) :=
  ![{0}, {1}, {0, 1}, {2}]

/-- Process the threshold edge before the two edges supplying its prerequisites. -/
def thresholdSweep : List (Fin 3) := [2, 1, 0]

/-- The threshold sweep contains every edge of the example. -/
theorem mem_thresholdSweep (edge : Fin 3) : edge ∈ thresholdSweep := by
  fin_cases edge <;> simp [thresholdSweep]

/-- After one reverse-ordered sweep, the prerequisite tokens have accumulated but the output has
not yet been revisited. -/
theorem thresholdSweep_one :
    thresholdTransport.sweepRelaxation thresholdSweep thresholdSeed 1 =
      ![{0}, {1}, {0, 1}, ∅] := by
  decide

/-- The second sweep revisits the nonlinear edge and releases token `2`. -/
theorem thresholdSweep_two :
    thresholdTransport.sweepRelaxation thresholdSweep thresholdSeed 2 =
      thresholdExpected := by
  decide

/-- Once the expected family is reached, another sweep makes no change. -/
theorem thresholdExpected_fixed :
    thresholdTransport.relaxSweep thresholdSweep thresholdExpected = thresholdExpected := by
  decide

/-- The computed threshold family satisfies every local endorsement rule. -/
theorem thresholdExpected_isLax : thresholdTransport.IsLaxSection thresholdExpected := by
  apply thresholdTransport.isLaxSection_of_relaxSweep_eq mem_thresholdSweep
  exact thresholdExpected_fixed

/-- Two reverse-ordered sweeps compute the least sound assignment containing the seeds. -/
theorem thresholdSweep_two_isLeast :
    thresholdSeed ≤ thresholdTransport.sweepRelaxation thresholdSweep thresholdSeed 2 ∧
      thresholdTransport.IsLaxSection
        (thresholdTransport.sweepRelaxation thresholdSweep thresholdSeed 2) ∧
      ∀ majorant : Fin 4 → Finset (Fin 3),
        thresholdSeed ≤ majorant → thresholdTransport.IsLaxSection majorant →
          thresholdTransport.sweepRelaxation thresholdSweep thresholdSeed 2 ≤ majorant := by
  apply thresholdTransport.sweepRelaxation_isLeast_of_relaxSweep_eq
    monotone_thresholdEdgeMap mem_thresholdSweep
  rw [thresholdSweep_two]
  exact thresholdExpected_fixed

end WebOfTrust

end
