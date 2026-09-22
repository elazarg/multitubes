/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.FixedPoint

/-!
# Max-plus synchronization networks

A timed network has a finite event graph and one real delay per dependency edge. Its next event
times are the max-plus vertex operator: an edge from `u` to `v` demands time
`x u + delay`, and event `v` occurs at the greatest incoming demand. Labels are explicitly
floorless and have slope one. This additive homogeneity is what turns an eigen-schedule into a
linear orbit and, when the cycle time is positive, gives its reciprocal a throughput meaning.

The worked two-event network has recurrence
`a' = max (a + 2) (b + 1)` and `b' = max (a + 4) (b + 3)`. Starting from `(0, 2)`, each
firing adds three to both event times. Raising the self-delay of the first event from two to four
gives a second checkable network whose synchronized schedule `(0, 0)` grows by four per firing.

## Main definitions

* `DiscreteEventSystems.TimedNetwork`: a graph equipped with max-plus delays.
* `DiscreteEventSystems.TimedNetwork.step`: the simultaneous event-time update.
* `DiscreteEventSystems.TimedNetwork.IsSchedule`: the cycle-time eigen-equation.
* `DiscreteEventSystems.exampleNetwork` and `DiscreteEventSystems.delayedNetwork`: the example
  and its delay perturbation.

## Main results

* `DiscreteEventSystems.TimedNetwork.step_add_const`: timed updates are additively homogeneous.
* `DiscreteEventSystems.TimedNetwork.iterate_eigenschedule`: a schedule of cycle time `c` has
  exact event times `x + n * c` after `n` firings.
* `DiscreteEventSystems.TimedNetwork.iterate_between_schedule`: initial timings between two
  translates of a schedule remain between the corresponding translates of its linear orbit.
* `DiscreteEventSystems.TimedNetwork.exists_uniform_deviation_bound`: on a finite event set,
  every initial timing vector stays a bounded distance from the linear schedule.
* `DiscreteEventSystems.example_step`: the graph operator is the stated recurrence.
* `DiscreteEventSystems.example_schedule` and
  `DiscreteEventSystems.example_linear_growth`: cycle time three and its exact orbit.
* `DiscreteEventSystems.example_delayed_schedule`: the perturbed cycle time is four.

## Implementation notes

The throughput certificate is deliberately restricted to translation labels. General max-affine
labels need not be additively homogeneous, so an eigenvalue there does not justify a linear-growth
or reciprocal-throughput claim.

## Tags

timed event graph, synchronization, max-plus, eigen-schedule, throughput, sensitivity
-/

@[expose] public section

namespace DiscreteEventSystems

open Maths
open Maths.MaxAffineTransport

universe uV uE

/-- A max-plus timed network: a dependency graph and a delay on each edge. -/
structure TimedNetwork (V : Type uV) (E : Type uE) where
  /-- The directed dependency graph. -/
  graph : EdgeGraph V E
  /-- The processing or transfer delay carried by each dependency. -/
  delay : E → ℝ

namespace TimedNetwork

variable {V : Type uV} {E : Type uE}

/-- The floorless unit-slope labels associated to a timed network. -/
def label (network : TimedNetwork V E) (edge : E) : Label :=
  ⟨⊥, network.delay edge, 1⟩

/-- One simultaneous update of all event times. -/
def step [Fintype E] [DecidableEq V] (network : TimedNetwork V E) :
    (V → ℝ) → V → ℝ :=
  vertexOperator network.graph network.label

/-- An event schedule with cycle time `cycleTime`: one update translates every event time by the
same amount. -/
def IsSchedule [Fintype E] [DecidableEq V] (network : TimedNetwork V E)
    (cycleTime : ℝ) (schedule : V → ℝ) : Prop :=
  IsEigenvector network.graph network.label cycleTime schedule

@[simp] theorem label_floor (network : TimedNetwork V E) (edge : E) :
    (network.label edge).floor = ⊥ := rfl

@[simp] theorem label_shift (network : TimedNetwork V E) (edge : E) :
    (network.label edge).shift = network.delay edge := rfl

@[simp] theorem label_slope (network : TimedNetwork V E) (edge : E) :
    (network.label edge).slope = 1 := rfl

/-- Timed-network updates commute with translating all event times, provided every event has an
incoming dependency. -/
theorem step_add_const [Fintype E] [DecidableEq V] (network : TimedNetwork V E)
    (hin : ∀ vertex : V, (incoming network.graph vertex).Nonempty) (x : V → ℝ) (c : ℝ) :
    network.step (fun vertex => x vertex + c) = fun vertex => network.step x vertex + c := by
  funext vertex
  exact vertexOperator_add_const network.graph (fun _ => rfl) (fun _ => rfl) x c (hin vertex)

/-- An eigen-schedule grows exactly linearly: after `n` firings, every event time is translated by
`n * cycleTime`. Additive homogeneity is the essential hypothesis behind this conclusion. -/
theorem iterate_eigenschedule [Fintype E] [DecidableEq V] (network : TimedNetwork V E)
    (hin : ∀ vertex : V, (incoming network.graph vertex).Nonempty) {cycleTime : ℝ}
    {schedule : V → ℝ} (hschedule : network.IsSchedule cycleTime schedule) (n : ℕ) :
    (network.step^[n]) schedule = fun vertex => schedule vertex + n * cycleTime := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, network.step_add_const hin,
        show network.step schedule = fun vertex => cycleTime + schedule vertex by
          funext vertex
          exact hschedule vertex]
      funext vertex
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Every initial timing vector trapped between two translates of an eigen-schedule remains between
the corresponding translates of its linear orbit. -/
theorem iterate_between_schedule [Fintype E] [DecidableEq V] (network : TimedNetwork V E)
    (hin : ∀ vertex : V, (incoming network.graph vertex).Nonempty) {cycleTime : ℝ}
    {schedule initial : V → ℝ} (hschedule : network.IsSchedule cycleTime schedule)
    {lower upper : ℝ} (hlower : (fun vertex => schedule vertex + lower) ≤ initial)
    (hupper : initial ≤ fun vertex => schedule vertex + upper) (n : ℕ) :
    (fun vertex => schedule vertex + n * cycleTime + lower) ≤
        (network.step^[n]) initial ∧
      (network.step^[n]) initial ≤ fun vertex => schedule vertex + n * cycleTime + upper := by
  have hmono : Monotone network.step :=
    monotone_vertexOperator network.graph fun edge => by rw [network.label_slope]; exact zero_le_one
  have hiterate : Monotone (network.step^[n]) := hmono.iterate n
  have hl := hiterate hlower
  have hu := hiterate hupper
  have htranslate (c : ℝ) : ∀ m : ℕ,
      (network.step^[m]) (fun vertex => schedule vertex + c) =
        fun vertex => (network.step^[m]) schedule vertex + c := by
    intro m
    induction m with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          network.step_add_const hin]
  rw [htranslate lower n, network.iterate_eigenschedule hin hschedule] at hl
  rw [htranslate upper n, network.iterate_eigenschedule hin hschedule] at hu
  constructor
  · intro vertex
    simpa only [Pi.add_apply] using hl vertex
  · intro vertex
    simpa only [Pi.add_apply] using hu vertex

/-- On a finite event set, every initial timing vector remains within a uniform constant of the
linear eigen-schedule. The bound is independent of the firing count and of the event. -/
theorem exists_uniform_deviation_bound [Fintype E] [Fintype V] [DecidableEq V]
    (network : TimedNetwork V E)
    (hin : ∀ vertex : V, (incoming network.graph vertex).Nonempty) {cycleTime : ℝ}
    {schedule : V → ℝ} (hschedule : network.IsSchedule cycleTime schedule)
    (initial : V → ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (n : ℕ) (vertex : V),
      |(network.step^[n]) initial vertex - (schedule vertex + n * cycleTime)| ≤ bound := by
  obtain ⟨rawBound, hrawBound⟩ :=
    Finite.exists_le fun vertex : V => |initial vertex - schedule vertex|
  let bound := max 0 rawBound
  have hbound_nonneg : 0 ≤ bound := le_max_left _ _
  have hdeviation (vertex : V) : |initial vertex - schedule vertex| ≤ bound :=
    le_trans (hrawBound vertex) (le_max_right _ _)
  have hlower : (fun vertex => schedule vertex - bound) ≤ initial := by
    intro vertex
    have := (abs_le.mp (hdeviation vertex)).1
    linarith [hdeviation vertex]
  have hupper : initial ≤ fun vertex => schedule vertex + bound := by
    intro vertex
    linarith [(abs_le.mp (hdeviation vertex)).2]
  refine ⟨bound, hbound_nonneg, fun n vertex => ?_⟩
  obtain ⟨hl, hu⟩ := network.iterate_between_schedule hin hschedule hlower hupper n
  rw [abs_le]
  constructor
  · have := hl vertex
    linarith
  · have := hu vertex
    linarith

end TimedNetwork

/-- The two event types in the synchronization example. -/
inductive ExampleEvent
  | first
  | second
  deriving DecidableEq

/-- The four dependencies in the synchronization example. -/
inductive ExampleDependency
  | firstSelf
  | secondToFirst
  | firstToSecond
  | secondSelf
  deriving DecidableEq

/-- The four example dependencies form a finite edge type. -/
instance exampleDependencyFintype : Fintype ExampleDependency where
  elems := {.firstSelf, .secondToFirst, .firstToSecond, .secondSelf}
  complete edge := by cases edge <;> simp

/-- The complete dependency graph on the two example events. -/
def exampleGraph : EdgeGraph ExampleEvent ExampleDependency where
  source
    | .firstSelf => .first
    | .secondToFirst => .second
    | .firstToSecond => .first
    | .secondSelf => .second
  target
    | .firstSelf => .first
    | .secondToFirst => .first
    | .firstToSecond => .second
    | .secondSelf => .second

/-- The example network, with delays `2`, `1`, `4`, and `3`. -/
def exampleNetwork : TimedNetwork ExampleEvent ExampleDependency where
  graph := exampleGraph
  delay
    | .firstSelf => 2
    | .secondToFirst => 1
    | .firstToSecond => 4
    | .secondSelf => 3

/-- Every event in the example has an incoming dependency. -/
theorem example_incoming (vertex : ExampleEvent) :
    (incoming exampleGraph vertex).Nonempty := by
  cases vertex
  · exact ⟨.firstSelf, mem_incoming.2 rfl⟩
  · exact ⟨.firstToSecond, mem_incoming.2 rfl⟩

/-- The graph operator computes the advertised max-plus recurrence. -/
theorem example_step (x : ExampleEvent → ℝ) :
    exampleNetwork.step x = fun
      | ExampleEvent.first => max (x ExampleEvent.first + 2) (x ExampleEvent.second + 1)
      | ExampleEvent.second => max (x ExampleEvent.first + 4) (x ExampleEvent.second + 3) := by
  funext vertex
  cases vertex
  · change vertexOperator exampleGraph exampleNetwork.label x .first = _
    rw [vertexOperator_eq_sup' (example_incoming .first)]
    apply le_antisymm
    · apply Finset.sup'_le
      intro edge hedge
      have htarget := mem_incoming.1 hedge
      cases edge with
      | firstSelf =>
          simp only [TimedNetwork.label, exampleNetwork, exampleGraph, Label.apply_mk_bot,
            one_mul]
          calc
            2 + x .first = x .first + 2 := add_comm _ _
            _ ≤ max (x .first + 2) (x .second + 1) := le_max_left _ _
      | secondToFirst =>
          simp only [TimedNetwork.label, exampleNetwork, exampleGraph, Label.apply_mk_bot,
            one_mul]
          calc
            1 + x .second = x .second + 1 := add_comm _ _
            _ ≤ max (x .first + 2) (x .second + 1) := le_max_right _ _
      | firstToSecond => simp [exampleGraph] at htarget
      | secondSelf => simp [exampleGraph] at htarget
    · apply max_le
      · simpa [TimedNetwork.label, exampleNetwork, exampleGraph, add_comm] using
          (Finset.le_sup' (fun edge => (exampleNetwork.label edge).apply
            (x (exampleGraph.source edge)))
            (mem_incoming.2 (rfl : exampleGraph.target ExampleDependency.firstSelf = .first)))
      · simpa [TimedNetwork.label, exampleNetwork, exampleGraph, add_comm] using
          (Finset.le_sup' (fun edge => (exampleNetwork.label edge).apply
            (x (exampleGraph.source edge)))
            (mem_incoming.2 (rfl : exampleGraph.target ExampleDependency.secondToFirst = .first)))
  · change vertexOperator exampleGraph exampleNetwork.label x .second = _
    rw [vertexOperator_eq_sup' (example_incoming .second)]
    apply le_antisymm
    · apply Finset.sup'_le
      intro edge hedge
      have htarget := mem_incoming.1 hedge
      cases edge with
      | firstSelf => simp [exampleGraph] at htarget
      | secondToFirst => simp [exampleGraph] at htarget
      | firstToSecond =>
          simp only [TimedNetwork.label, exampleNetwork, exampleGraph, Label.apply_mk_bot,
            one_mul]
          calc
            4 + x .first = x .first + 4 := add_comm _ _
            _ ≤ max (x .first + 4) (x .second + 3) := le_max_left _ _
      | secondSelf =>
          simp only [TimedNetwork.label, exampleNetwork, exampleGraph, Label.apply_mk_bot,
            one_mul]
          calc
            3 + x .second = x .second + 3 := add_comm _ _
            _ ≤ max (x .first + 4) (x .second + 3) := le_max_right _ _
    · apply max_le
      · simpa [TimedNetwork.label, exampleNetwork, exampleGraph, add_comm] using
          (Finset.le_sup' (fun edge => (exampleNetwork.label edge).apply
            (x (exampleGraph.source edge)))
            (mem_incoming.2 (rfl : exampleGraph.target ExampleDependency.firstToSecond = .second)))
      · simpa [TimedNetwork.label, exampleNetwork, exampleGraph, add_comm] using
          (Finset.le_sup' (fun edge => (exampleNetwork.label edge).apply
            (x (exampleGraph.source edge)))
            (mem_incoming.2 (rfl : exampleGraph.target ExampleDependency.secondSelf = .second)))

/-- The phase offsets `(0, 2)` of the steady example schedule. -/
def examplePhase : ExampleEvent → ℝ
  | .first => 0
  | .second => 2

/-- The example phase is an eigen-schedule with cycle time three. -/
theorem example_schedule : exampleNetwork.IsSchedule 3 examplePhase := by
  intro vertex
  change exampleNetwork.step examplePhase vertex = _
  rw [example_step]
  cases vertex <;> norm_num [examplePhase]

/-- After `n` firings, the example schedule is translated by exactly `3n`. -/
theorem example_linear_growth (n : ℕ) :
    (exampleNetwork.step^[n]) examplePhase = fun vertex => examplePhase vertex + n * 3 :=
  TimedNetwork.iterate_eigenschedule exampleNetwork example_incoming example_schedule n

/-- The network obtained by raising the first self-delay from two to four. -/
def delayedNetwork : TimedNetwork ExampleEvent ExampleDependency where
  graph := exampleGraph
  delay
    | .firstSelf => 4
    | .secondToFirst => 1
    | .firstToSecond => 4
    | .secondSelf => 3

/-- The synchronized phase offsets `(0, 0)` for the delayed network. -/
def delayedPhase : ExampleEvent → ℝ
  | .first => 0
  | .second => 0

/-- Raising one delay produces a certified cycle time of four. -/
theorem example_delayed_schedule : delayedNetwork.IsSchedule 4 delayedPhase := by
  change IsEigenvector exampleGraph delayedNetwork.label 4 delayedPhase
  rw [isEigenvector_iff exampleGraph delayedNetwork.label 4 delayedPhase example_incoming]
  constructor
  · intro edge
    cases edge <;>
      norm_num [TimedNetwork.label, delayedNetwork, exampleGraph, delayedPhase]
  · intro vertex
    cases vertex
    · exact ⟨.firstSelf, rfl,
        by norm_num [TimedNetwork.label, delayedNetwork, exampleGraph, delayedPhase]⟩
    · exact ⟨.firstToSecond, rfl,
        by norm_num [TimedNetwork.label, delayedNetwork, exampleGraph, delayedPhase]⟩

end DiscreteEventSystems
