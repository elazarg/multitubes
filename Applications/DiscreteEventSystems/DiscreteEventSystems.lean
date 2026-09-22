/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DiscreteEventSystems.Synchronization

/-!
# Discrete-event systems

This application models synchronization networks by a max-plus event-time recurrence. Edge
shifts are processing or transfer delays, while the maximum over incoming edges records that an
event waits for every prerequisite represented by the incoming alternatives.

## Main definitions

* `DiscreteEventSystems.TimedNetwork`: a floorless unit-slope max-plus network.
* `DiscreteEventSystems.TimedNetwork.step`: one update of all event times.
* `DiscreteEventSystems.exampleNetwork`: a two-event synchronization network.

## Main results

* `DiscreteEventSystems.TimedNetwork.iterate_eigenschedule`: an eigen-schedule grows linearly
  under every iterate.
* `DiscreteEventSystems.TimedNetwork.iterate_between_schedule`: bounded initial timing error
  remains bounded around the linear schedule.
* `DiscreteEventSystems.TimedNetwork.exists_uniform_deviation_bound`: every initial timing vector
  on a finite event set stays uniformly close to the linear schedule.
* `DiscreteEventSystems.example_step`: the verified recurrence for the example.
* `DiscreteEventSystems.example_schedule`: the example has cycle time three.
* `DiscreteEventSystems.example_linear_growth`: its event times grow by three per firing.
* `DiscreteEventSystems.example_delayed_schedule`: increasing one delay changes the certified
  cycle time from three to four.

## Tags

discrete-event system, synchronization, timed event graph, max-plus, throughput
-/

@[expose] public section

namespace DiscreteEventSystems

end DiscreteEventSystems
