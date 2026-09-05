/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import SwitchedHybridControl.Control
public import SwitchedHybridControl.ErrorBounds

/-!
# Switched and hybrid control

This application reads a transport as a switched or hybrid certificate graph.  A
physical transition is oriented from its pre-state mode to its post-state mode, while the
certificate graph reverses that edge so that a target energy is pulled back to the source.
The concrete example has two heterogeneous state spaces and a noninjective reset.

## Main definitions

* `SwitchedHybridControl.storageTransport` - charged value transport on the reversed graph.
* `SwitchedHybridControl.IsStorageCertificate` - the pointwise storage inequality on a family
  of mode-dependent energies.
* `SwitchedHybridControl.IsLyapunovFamily` - the zero-cost specialization of storage
  certification.
* `SwitchedHybridControl.pullbackTransport` - the uncharged pullback value transport.
* `SwitchedHybridControl.examplePhysicalGraph` - the two-mode physical transition graph.
* `SwitchedHybridControl.exampleEnergy` - the concrete energy family.
* `SwitchedHybridControl.ErrorComparison` and `SwitchedHybridControl.IsRadiusFamily` - local
  affine error propagation and compatible mode-dependent radii.

## Main results

* `SwitchedHybridControl.storageCertificate_iff_isLaxSection` - pointwise certification is the
  lax-section condition on the reversed certificate graph.
* `SwitchedHybridControl.isLyapunovFamily_iff_isLaxSection` - the zero-cost specialization of
  that lax-section characterization.
* `SwitchedHybridControl.walk_storage_nonincrease` and
  `SwitchedHybridControl.closedWalk_storage_nonincrease` - local certificate inequalities
  propagate along walks and closed walks.
* `SwitchedHybridControl.not_exists_fixedPoint_holonomy_of_pos_walkSum` - a positive-cost
  closed walk cannot fix a state under physical holonomy.
* `SwitchedHybridControl.exampleEnergy_certified` - the concrete family is certified.
* `SwitchedHybridControl.exampleReset_noninjective` - the reset merges two states.
* `SwitchedHybridControl.exampleCycle_strict_decrease` - the closed physical cycle strictly
  decreases the energy at state `1` of `Fin 3`.
* `SwitchedHybridControl.ErrorComparison.walk_error_le` - affine local error estimates imply
  mode-dependent error bounds along every shared execution.
* `SwitchedHybridControl.radius_feasible_iff` - bounded comparison radii are exactly a finite
  linear-inequality feasibility problem.

## Tags

switched systems, hybrid systems, Lyapunov function, storage function, pullback, reset,
transport
-/

@[expose] public section

namespace SwitchedHybridControl

end SwitchedHybridControl
