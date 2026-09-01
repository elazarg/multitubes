/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CoalgebraicRefinement.Deterministic

/-!
# Coalgebraic refinement by relation transport

A deterministic labeled coalgebra lifts relations by comparing observations and equally labeled
successors. Simulations are post-fixed relations, the greatest simulation is a Knaster–Tarski
fixed point, and finite unfoldings are walks of a one-loop directed transport.

## Main definitions

* `CoalgebraicRefinement.DeterministicSystem` - a labeled deterministic coalgebra.
* `CoalgebraicRefinement.simulationOperator` - its relation lifting.
* `CoalgebraicRefinement.IsSimulation` - the post-fixed-point simulation predicate.
* `CoalgebraicRefinement.TraceRelated` - observation agreement after every finite word.
* `CoalgebraicRefinement.greatestSimulation` - the greatest simulation relation.
* `CoalgebraicRefinement.refinementTransport` - relation lifting as one-loop transport.

## Main results

* `CoalgebraicRefinement.monotone_simulationOperator` - relation lifting is monotone.
* `CoalgebraicRefinement.greatestSimulation_isGreatest` - the greatest fixed point contains
  every simulation.
* `CoalgebraicRefinement.greatestSimulation_iff_traceRelated` - greatest simulation coincides
  with finite trace agreement.
* `CoalgebraicRefinement.isOplaxSection_iff_isSimulation` - simulations are oplax sections.
* `CoalgebraicRefinement.simulation_le_walkMap` - simulations survive every finite unfolding.
* `CoalgebraicRefinement.greatestSimulation_walkMap_eq` - the greatest simulation is exact
  under every finite unfolding.

## Tags

coalgebra, simulation, bisimulation, relation lifting, greatest fixed point, directed transport
-/

@[expose] public section

namespace CoalgebraicRefinement

end CoalgebraicRefinement
