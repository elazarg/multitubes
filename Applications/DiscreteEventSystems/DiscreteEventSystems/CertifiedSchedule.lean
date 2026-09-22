/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DiscreteEventSystems.Synchronization
public import Maths.Multitubes.Additive.CriticalGraph
public import Maths.Multitubes.Additive.ShortCycles

/-!
# Certified schedules from critical cycles

A timed network admits a schedule at a proposed cycle time when that time bounds every closed
walk mean, is attained by a nonempty cycle, and the attaining vertex reaches every event.  The
phase is constructed as the greatest shifted walk weight from the attaining vertex.  Only outward
reachability from that vertex is used; strong connectivity is unnecessary.

The attaining cycle also certifies optimality: every schedule, and more generally every phase
satisfying all edge demands at a proposed upper cycle time, has cycle time at least its mean.
The construction is mathematical rather than an executable search procedure.

## Main definitions

* `DiscreteEventSystems.TimedNetwork.rootedPhase`: the critical rooted-weight phase.
* `DiscreteEventSystems.exampleBottleneckCycle`: a maximizing cycle in the two-event example.

## Main results

* `DiscreteEventSystems.TimedNetwork.rootedPhase_isSchedule`: a reachable maximizing cycle
  constructs a schedule.
* `DiscreteEventSystems.TimedNetwork.exists_optimalSchedule`: finite global reachability selects
  a maximizing cycle, constructs its schedule, and proves optimality among all feasible bounds.
* `DiscreteEventSystems.TimedNetwork.cycleMean_le_of_feasibleCycleTime`: every nonempty cycle
  lower-bounds any feasible cycle time.
* `DiscreteEventSystems.TimedNetwork.cycleMean_le_of_isSchedule`: every schedule is bounded
  below by every cycle mean.
* `DiscreteEventSystems.example_rootedPhase_eq`: the constructed example phase is `(-2, 0)`.
* `DiscreteEventSystems.example_certified_schedule`: the construction gives cycle time `3`.
* `DiscreteEventSystems.example_feasibleCycleTime_optimal`: the bottleneck proves every feasible
  upper cycle-time bound is at least `3`.
* `DiscreteEventSystems.example_cycleTime_optimal`: every competing schedule has cycle time at
  least `3`.

## Tags

timed event graph, max-plus, critical cycle, cycle mean, certified schedule
-/

@[expose] public section

namespace DiscreteEventSystems

open Maths
open Maths.MaxPlusPotential
open Maths.MaxAffineTransport

universe uV uE

namespace TimedNetwork

variable {V : Type uV} {E : Type uE}

/-- The phase obtained from greatest walk weights after subtracting the proposed cycle time. -/
noncomputable def rootedPhase [Finite E] (network : TimedNetwork V E)
    (cycleTime : ℝ) (base : V) : V → ℝ :=
  maxRootedWeight network.graph (fun edge => network.delay edge - cycleTime) base

/-- Edge feasibility at a proposed upper cycle time. -/
def IsFeasibleCycleTime (network : TimedNetwork V E) (cycleTime : ℝ)
    (phase : V → ℝ) : Prop :=
  ∀ edge, phase (network.graph.source edge) + network.delay edge ≤
    cycleTime + phase (network.graph.target edge)

/-- A critical rooted-weight phase is a schedule.  The assumptions say exactly that the proposed
cycle time bounds all closed-walk means, is attained at `base`, and `base` reaches every event. -/
theorem rootedPhase_isSchedule [Fintype E] [DecidableEq V] (network : TimedNetwork V E)
    {cycleTime : ℝ} {base : V}
    (hcycles : ∀ (vertex : V) (cycle : network.graph.Walk vertex vertex),
      walkWeight network.delay cycle ≤ cycle.length * cycleTime)
    (hcritical : IsCriticalVertex network.graph network.delay cycleTime base)
    (hreach : ∀ vertex : V, Nonempty (network.graph.Walk base vertex)) :
    network.IsSchedule cycleTime (network.rootedPhase cycleTime base) := by
  have heigen := isGraphEigenvector_maxRootedWeight hcycles hcritical hreach
  have hin (vertex : V) : (incoming network.graph vertex).Nonempty := by
    obtain ⟨edge, htarget, -⟩ := heigen.2 vertex
    exact ⟨edge, mem_incoming.2 htarget⟩
  rw [IsSchedule, isEigenvector_iff network.graph network.label cycleTime
    (network.rootedPhase cycleTime base) hin]
  constructor
  · intro edge
    have hedge := heigen.1 edge
    simp only [label, rootedPhase, Label.apply_of_floor_bot, Label.affinePart, one_mul]
    linarith [hedge]
  · intro vertex
    obtain ⟨edge, htarget, htight⟩ := heigen.2 vertex
    refine ⟨edge, htarget, ?_⟩
    simp only [label, rootedPhase, Label.apply_of_floor_bot, Label.affinePart, one_mul]
    rw [add_comm (network.delay edge)]
    exact htight

/-- Every nonempty cycle lower-bounds any cycle time satisfying all edge demands. -/
theorem cycleMean_le_of_feasibleCycleTime (network : TimedNetwork V E)
    {cycleTime : ℝ} {phase : V → ℝ}
    (hfeasible : network.IsFeasibleCycleTime cycleTime phase)
    {base : V} (cycle : network.graph.Walk base base) (hcycle : 0 < cycle.length) :
    walkWeight network.delay cycle / cycle.length ≤ cycleTime := by
  have hpotential : IsPotential network.graph
      (fun edge => network.delay edge - cycleTime) phase := by
    intro edge
    dsimp [MaxPlusPotential.defect]
    linarith [hfeasible edge]
  have hclosed := hpotential.closedWalk_nonpos cycle
  rw [walkWeight_sub_const, nsmul_eq_mul] at hclosed
  rw [div_le_iff₀ (by exact_mod_cast hcycle)]
  linarith

/-- Every schedule has cycle time at least the mean delay of every nonempty closed walk. -/
theorem cycleMean_le_of_isSchedule [Fintype E] [DecidableEq V]
    (network : TimedNetwork V E) {cycleTime : ℝ} {phase : V → ℝ}
    (hschedule : network.IsSchedule cycleTime phase)
    {base : V} (cycle : network.graph.Walk base base) (hcycle : 0 < cycle.length) :
    walkWeight network.delay cycle / cycle.length ≤ cycleTime := by
  apply network.cycleMean_le_of_feasibleCycleTime (phase := phase) _ cycle hcycle
  intro edge
  have hedge : (network.label edge).apply (phase (network.graph.source edge)) ≤
      network.step phase (network.graph.target edge) := le_vertexOperator rfl
  rw [show network.step phase (network.graph.target edge) =
      cycleTime + phase (network.graph.target edge) from hschedule _] at hedge
  simpa [label, Label.apply_of_floor_bot, Label.affinePart, add_comm] using hedge

/-- On a finite graph with a nonempty cycle and global directed reachability, a maximizing cycle
exists and its rooted phase is an optimal schedule.  The returned closed walk is an explicit
bottleneck certificate, of length at most the number of events. -/
theorem exists_optimalSchedule [Fintype V] [Fintype E] [DecidableEq V]
    (network : TimedNetwork V E)
    (hexists : ∃ (vertex : V) (cycle : network.graph.Walk vertex vertex), 0 < cycle.length)
    (hreach : ∀ base vertex : V, Nonempty (network.graph.Walk base vertex)) :
    ∃ (cycleTime : ℝ) (base : V) (best : network.graph.Walk base base),
      0 < best.length ∧ best.length ≤ Fintype.card V ∧
        walkWeight network.delay best = best.length * cycleTime ∧
        IsCriticalVertex network.graph network.delay cycleTime base ∧
        network.IsSchedule cycleTime (network.rootedPhase cycleTime base) ∧
        (∀ (vertex : V) (cycle : network.graph.Walk vertex vertex), 0 < cycle.length →
          walkWeight network.delay cycle / cycle.length ≤ cycleTime) ∧
        ∀ (otherTime : ℝ) (phase : V → ℝ),
          network.IsFeasibleCycleTime otherTime phase → cycleTime ≤ otherTime := by
  obtain ⟨base, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean
      network.graph network.delay hexists
  let cycleTime := walkWeight network.delay best / best.length
  have hcycles (vertex : V) (cycle : network.graph.Walk vertex vertex) :
      walkWeight network.delay cycle ≤ cycle.length * cycleTime := by
    rcases Nat.eq_zero_or_pos cycle.length with hzero | hcycle
    · have hedges : cycle.edges = [] :=
        List.length_eq_zero_iff.mp (by rw [EdgeGraph.Walk.edges_length, hzero])
      simp [walkWeight, hedges, hzero]
    · have hlen : (0 : ℝ) < cycle.length := by exact_mod_cast hcycle
      simpa [cycleTime, mul_comm] using (div_le_iff₀ hlen).mp (hmax vertex cycle hcycle)
  have hbest : walkWeight network.delay best = best.length * cycleTime := by
    dsimp [cycleTime]
    have hne : (best.length : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  have hcritical : IsCriticalVertex network.graph network.delay cycleTime base :=
    ⟨best, hpos, hbest⟩
  have hschedule := network.rootedPhase_isSchedule hcycles hcritical (hreach base)
  refine ⟨cycleTime, base, best, hpos, hcard, hbest, hcritical, hschedule,
    fun vertex cycle hcycle => hmax vertex cycle hcycle, ?_⟩
  intro otherTime phase hother
  have hbound := network.cycleMean_le_of_feasibleCycleTime hother best hpos
  exact hbound

end TimedNetwork

/-! The two-event certified schedule. -/

/-- The second event's self-dependency, viewed as a one-edge closed walk. -/
def exampleBottleneckCycle : exampleNetwork.graph.Walk .second .second :=
  (.nil : exampleNetwork.graph.Walk .second .second).concat .secondSelf rfl

/-- The bottleneck cycle has length one. -/
@[simp] theorem exampleBottleneckCycle_length : exampleBottleneckCycle.length = 1 := rfl

/-- The bottleneck cycle has total delay three. -/
@[simp] theorem exampleBottleneckCycle_weight :
    walkWeight exampleNetwork.delay exampleBottleneckCycle = 3 := by
  calc
    _ = walkWeight exampleNetwork.delay
          (.nil : exampleNetwork.graph.Walk .second .second) +
        exampleNetwork.delay .secondSelf := walkWeight_concat
          exampleNetwork.delay (.nil : exampleNetwork.graph.Walk .second .second)
            .secondSelf rfl
    _ = 3 := by norm_num [walkWeight, exampleNetwork]

/-- Every event is reachable from the bottleneck event. -/
theorem example_reachable_from_second (vertex : ExampleEvent) :
    Nonempty (exampleNetwork.graph.Walk .second vertex) := by
  cases vertex with
  | first =>
      exact ⟨(.nil : exampleNetwork.graph.Walk .second .second).concat .secondToFirst rfl⟩
  | second => exact ⟨.nil⟩

/-- The explicit shifted phase used to calculate the rooted construction. -/
def exampleShiftedPhase : ExampleEvent → ℝ
  | .first => -2
  | .second => 0

/-- The shifted example delays admit `exampleShiftedPhase` as a potential. -/
theorem exampleShiftedPhase_isPotential :
    IsPotential exampleNetwork.graph (fun edge => exampleNetwork.delay edge - 3)
      exampleShiftedPhase := by
  intro edge
  cases edge <;>
    norm_num [MaxPlusPotential.defect, exampleGraph, exampleNetwork, exampleShiftedPhase]

/-- Every example cycle has mean at most three. -/
theorem example_cycle_bound (vertex : ExampleEvent)
    (cycle : exampleNetwork.graph.Walk vertex vertex) :
    walkWeight exampleNetwork.delay cycle ≤ cycle.length * 3 := by
  have hclosed := exampleShiftedPhase_isPotential.closedWalk_nonpos cycle
  rw [walkWeight_sub_const, nsmul_eq_mul] at hclosed
  linarith

/-- The bottleneck event is critical at cycle time three. -/
theorem example_second_critical :
    IsCriticalVertex exampleNetwork.graph exampleNetwork.delay 3 .second := by
  exact ⟨exampleBottleneckCycle, by simp, by simp⟩

/-- The critical rooted-weight construction evaluates to phase offsets `(-2, 0)`. -/
theorem example_rootedPhase_eq :
    exampleNetwork.rootedPhase 3 .second = exampleShiftedPhase := by
  funext vertex
  cases vertex with
  | second =>
      change maxRootedWeight exampleNetwork.graph
        (fun edge => exampleNetwork.delay edge - 3) .second .second = 0
      exact maxRootedWeight_self
        (fun v cycle => exampleShiftedPhase_isPotential.closedWalk_nonpos cycle) .second
  | first =>
      apply le_antisymm
      · obtain ⟨walk, -, hwalk⟩ := maxRootedWeight_mem
          (fun v cycle => exampleShiftedPhase_isPotential.closedWalk_nonpos cycle)
          (example_reachable_from_second .first)
        rw [TimedNetwork.rootedPhase, ← hwalk]
        simpa [exampleShiftedPhase] using exampleShiftedPhase_isPotential.walkWeight_le walk
      · refine le_maxRootedWeight ⟨
          (.nil : exampleNetwork.graph.Walk .second .second).concat .secondToFirst rfl, ?_, ?_⟩
        · change [ExampleDependency.secondToFirst].Nodup
          simp
        · calc
            _ = walkWeight (fun edge => exampleNetwork.delay edge - 3)
                  (.nil : exampleNetwork.graph.Walk .second .second) +
                (exampleNetwork.delay .secondToFirst - 3) := walkWeight_concat
                  (fun edge => exampleNetwork.delay edge - 3)
                  (.nil : exampleNetwork.graph.Walk .second .second) .secondToFirst rfl
            _ = -2 := by norm_num [walkWeight, exampleNetwork]

/-- The maximizing-cycle construction produces a schedule of cycle time three. -/
theorem example_certified_schedule :
    exampleNetwork.IsSchedule 3 (exampleNetwork.rootedPhase 3 .second) :=
  exampleNetwork.rootedPhase_isSchedule example_cycle_bound example_second_critical
    example_reachable_from_second

/-- The constructed phase is the displayed phase translated by `-2`. -/
theorem example_rootedPhase_eq_examplePhase_sub_two :
    exampleNetwork.rootedPhase 3 .second = fun vertex => examplePhase vertex - 2 := by
  rw [example_rootedPhase_eq]
  funext vertex
  cases vertex <;> norm_num [exampleShiftedPhase, examplePhase]

/-- The bottleneck cycle proves that every feasible upper cycle time is at least three. -/
theorem example_feasibleCycleTime_optimal {cycleTime : ℝ} {phase : ExampleEvent → ℝ}
    (hfeasible : exampleNetwork.IsFeasibleCycleTime cycleTime phase) : 3 ≤ cycleTime := by
  simpa using exampleNetwork.cycleMean_le_of_feasibleCycleTime hfeasible
    exampleBottleneckCycle (by simp)

/-- The bottleneck cycle proves that every competing schedule has cycle time at least three. -/
theorem example_cycleTime_optimal {cycleTime : ℝ} {phase : ExampleEvent → ℝ}
    (hschedule : exampleNetwork.IsSchedule cycleTime phase) : 3 ≤ cycleTime := by
  simpa using exampleNetwork.cycleMean_le_of_isSchedule hschedule exampleBottleneckCycle (by simp)

end DiscreteEventSystems
