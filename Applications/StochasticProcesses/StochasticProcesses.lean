/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import StochasticProcesses.KernelTransport
public import StochasticProcesses.HittingBarrier

/-!
# Nonnegative stochastic transport

This client reads a forward probability kernel contravariantly on nonnegative
extended-real observables. The resulting expectation pullback is a
deterministic edge map on the reversed graph, so the ordinary exact, lax, and
oplax section rules give harmonic, superharmonic, and subharmonic path bounds.

## Main definitions

* `StochasticProcesses.expect` - weighted expectation of a PMF.
* `StochasticProcesses.kernelStar` - expectation pullback of a state kernel.
* `StochasticProcesses.kernelPullbackTransport` - dependent pullback transport
  on a reversed graph.
* `StochasticProcesses.pathKernel` - PMF composition along a typed forward walk.
* `StochasticProcesses.kernelTransport` - the one-loop specialization of the
  pullback transport.
* `StochasticProcesses.hitBy` and `StochasticProcesses.eventuallyHit` - finite-horizon
  hitting probabilities and their supremum.
* `StochasticProcesses.stoppedKernel` - the absorbing-on-target kernel used to express finite
  hitting as an endpoint event.

## Main results

* `StochasticProcesses.expect_mono` - pointwise order is preserved by
  expectation.
* `StochasticProcesses.expect_bind` - expectation through one kernel bind.
* `StochasticProcesses.kernelStar_monotone` - expectation pullback is
  monotone.
* `StochasticProcesses.kernelPullbackTransport_edgeMap_monotone` - dependent
  pullback edges are monotone.
* `StochasticProcesses.isSection_iff_harmonic`,
  `StochasticProcesses.isLaxSection_iff_superharmonic`, and
  `StochasticProcesses.isOplaxSection_iff_subharmonic` - the three section
  polarities as pointwise kernel inequalities.
* `StochasticProcesses.walkMap_reverse_eq_expect_pathKernel` - reversed pullback as
  expectation under the forward path kernel.
* `StochasticProcesses.pathKernel_append` - kernel composition respects walk
  concatenation.
* `StochasticProcesses.expect_pathKernel_eq_of_harmonic`,
  `StochasticProcesses.expect_pathKernel_le_of_superharmonic`, and
  `StochasticProcesses.le_expect_pathKernel_of_subharmonic` - generic path bounds.
* `StochasticProcesses.walkMap_loopWalk_eq_iterate` - the transport walk map
  is the expectation of the corresponding iterated kernel.
* `StochasticProcesses.superharmonic_iterate_le` and
  `StochasticProcesses.subharmonic_iterate_ge` - one-sided path bounds.
* `StochasticProcesses.hitBy_le_barrier` and
  `StochasticProcesses.eventuallyHit_le_barrier` - superharmonic barrier certificates.
* `StochasticProcesses.hitBy_eq_expect_stopped` - finite-horizon hitting as the target endpoint
  probability for the stopped kernel.
* `StochasticProcesses.hitBy_le_one` and `StochasticProcesses.eventuallyHit_le_one` - probability
  normalization bounds.
* `StochasticProcesses.eventuallyHit_trial_start` - a sharp fair-trial example.

## Tags

stochastic processes, Markov kernel, expectation, harmonic, superharmonic,
subharmonic, transport
-/

@[expose] public section

namespace StochasticProcesses

end StochasticProcesses
