/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Basic
public import Mathlib.Order.FixedPoints

/-!
# Deterministic coalgebraic simulation

A deterministic labeled system supplies an observation and one successor for each label. Given
two such systems and a relation on their observations, the one-step simulation operator lifts a
state relation by requiring related current observations and related equally labeled successors.

The lifting is monotone. Its post-fixed points are simulations, and Knaster–Tarski supplies their
greatest member. The same lifting labels a one-loop transport on the relation lattice. Under this
translation simulations are oplax sections, so directed-transport walk induction gives every
finite unfolding theorem. The greatest simulation is a fixed point and hence an exact section.

## Main definitions

* `CoalgebraicRefinement.DeterministicSystem` - a deterministic labeled coalgebra.
* `CoalgebraicRefinement.DeterministicSystem.run` - execution along a finite label word.
* `CoalgebraicRefinement.simulationOperator` - the observation-and-successor relation lifting.
* `CoalgebraicRefinement.IsSimulation` - a post-fixed point of the lifting.
* `CoalgebraicRefinement.TraceRelated` - observation agreement after every finite word.
* `CoalgebraicRefinement.simulationOrderHom` - the bundled monotone lifting.
* `CoalgebraicRefinement.greatestSimulation` - the greatest fixed point of the lifting.
* `CoalgebraicRefinement.refinementGraph` - the one-loop unfolding graph.
* `CoalgebraicRefinement.refinementTransport` - the lifting as transport on relations.
* `CoalgebraicRefinement.refinementWalk` - a prescribed number of unfoldings.

## Main results

* `CoalgebraicRefinement.monotone_simulationOperator` - the lifting is monotone.
* `CoalgebraicRefinement.DeterministicSystem.run_append` - consecutive words compose.
* `CoalgebraicRefinement.IsSimulation.observe_run` - simulations preserve every finite trace.
* `CoalgebraicRefinement.traceRelated_isSimulation` - finite trace agreement is a simulation.
* `CoalgebraicRefinement.isSimulation_iff` - the pointwise simulation condition.
* `CoalgebraicRefinement.greatestSimulation_isFixedPoint` - the greatest simulation is fixed.
* `CoalgebraicRefinement.greatestSimulation_isGreatest` - every simulation is contained in it.
* `CoalgebraicRefinement.greatestSimulation_iff_traceRelated` - greatest simulation is finite
  trace agreement.
* `CoalgebraicRefinement.isOplaxSection_iff_isSimulation` - simulations are oplax sections.
* `CoalgebraicRefinement.simulation_le_walkMap` - finite unfoldings preserve simulations.
* `CoalgebraicRefinement.greatestSimulation_walkMap_eq` - finite unfoldings fix the greatest
  simulation.

## Tags

coalgebra, deterministic transition system, simulation, relation lifting, greatest fixed point
-/

@[expose] public section

namespace CoalgebraicRefinement

open Maths

universe uA uL uOL uOR uSL uSR

/-- A deterministic labeled coalgebra with observations. -/
structure DeterministicSystem (Label : Type uA) (Output : Type uOL) (State : Type uSL) where
  /-- The observation exposed by a state. -/
  observe : State → Output
  /-- The successor selected by a label. -/
  step : Label → State → State

variable {Label : Type uL} {LeftOutput : Type uOL} {RightOutput : Type uOR}
variable {LeftState : Type uSL} {RightState : Type uSR}

/-- Execute a deterministic system along a finite word, from left to right. -/
def DeterministicSystem.run (system : DeterministicSystem Label LeftOutput LeftState) :
    List Label → LeftState → LeftState
  | [], state => state
  | label :: labels, state => system.run labels (system.step label state)

/-- Running two consecutive words is the composite of their executions. -/
theorem DeterministicSystem.run_append
    (system : DeterministicSystem Label LeftOutput LeftState)
    (first second : List Label) (state : LeftState) :
    system.run (first ++ second) state = system.run second (system.run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons label labels ih => exact ih (state := system.step label state)

/-- Lift a state relation through one observation and one transition layer. -/
def simulationOperator
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop) :
    LeftState → RightState → Prop :=
  fun first second =>
    outputRel (left.observe first) (right.observe second) ∧
      ∀ label, relation (left.step label first) (right.step label second)

/-- The one-step simulation operator is monotone in its state relation. -/
theorem monotone_simulationOperator
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    Monotone (simulationOperator left right outputRel) := by
  intro first second hle leftState rightState hfirst
  exact ⟨hfirst.1, fun label ↦ hle _ _ (hfirst.2 label)⟩

/-- A simulation is a state relation contained in its one-step lifting. -/
def IsSimulation
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop) : Prop :=
  relation ≤ simulationOperator left right outputRel relation

/-- A simulation relates the states reached after every finite label word. -/
theorem IsSimulation.run
    {left : DeterministicSystem Label LeftOutput LeftState}
    {right : DeterministicSystem Label RightOutput RightState}
    {outputRel : LeftOutput → RightOutput → Prop}
    {relation : LeftState → RightState → Prop}
    (hsimulation : IsSimulation left right outputRel relation)
    {leftState : LeftState} {rightState : RightState}
    (hrelated : relation leftState rightState) (labels : List Label) :
    relation (left.run labels leftState) (right.run labels rightState) := by
  induction labels generalizing leftState rightState with
  | nil => exact hrelated
  | cons label labels ih =>
      exact ih ((hsimulation leftState rightState hrelated).2 label)

/-- A simulation relates the observations reached after every finite label word. -/
theorem IsSimulation.observe_run
    {left : DeterministicSystem Label LeftOutput LeftState}
    {right : DeterministicSystem Label RightOutput RightState}
    {outputRel : LeftOutput → RightOutput → Prop}
    {relation : LeftState → RightState → Prop}
    (hsimulation : IsSimulation left right outputRel relation)
    {leftState : LeftState} {rightState : RightState}
    (hrelated : relation leftState rightState) (labels : List Label) :
    outputRel (left.observe (left.run labels leftState))
      (right.observe (right.run labels rightState)) :=
  (hsimulation _ _ (hsimulation.run hrelated labels)).1

/-- Two states are trace-related when their observations are related after every finite word. -/
def TraceRelated
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    LeftState → RightState → Prop :=
  fun leftState rightState =>
    ∀ labels, outputRel (left.observe (left.run labels leftState))
      (right.observe (right.run labels rightState))

/-- Finite trace agreement is closed under one-step relation lifting. -/
theorem traceRelated_isSimulation
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    IsSimulation left right outputRel (TraceRelated left right outputRel) := by
  intro leftState rightState htrace
  refine ⟨htrace [], fun label labels ↦ ?_⟩
  exact htrace (label :: labels)

/-- The simulation predicate in pointwise observation-and-successor form. -/
theorem isSimulation_iff
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop) :
    IsSimulation left right outputRel relation ↔
      ∀ leftState rightState, relation leftState rightState →
        outputRel (left.observe leftState) (right.observe rightState) ∧
          ∀ label, relation (left.step label leftState) (right.step label rightState) :=
  Iff.rfl

/-- The relation lifting bundled as an order homomorphism. -/
def simulationOrderHom
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    (LeftState → RightState → Prop) →o (LeftState → RightState → Prop) where
  toFun := simulationOperator left right outputRel
  monotone' := monotone_simulationOperator left right outputRel

/-- The greatest simulation relation supplied by Knaster–Tarski. -/
def greatestSimulation
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    LeftState → RightState → Prop :=
  (simulationOrderHom left right outputRel).gfp

/-- The greatest simulation is a fixed point of the relation lifting. -/
theorem greatestSimulation_isFixedPoint
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    simulationOperator left right outputRel (greatestSimulation left right outputRel) =
      greatestSimulation left right outputRel :=
  (simulationOrderHom left right outputRel).map_gfp

/-- The greatest fixed point is itself a simulation. -/
theorem greatestSimulation_isSimulation
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    IsSimulation left right outputRel (greatestSimulation left right outputRel) :=
  (greatestSimulation_isFixedPoint left right outputRel).ge

/-- Every simulation relation is contained in the greatest simulation. -/
theorem greatestSimulation_isGreatest
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop)
    (hsimulation : IsSimulation left right outputRel relation) :
    relation ≤ greatestSimulation left right outputRel :=
  (simulationOrderHom left right outputRel).le_gfp hsimulation

/-- For deterministic systems, greatest simulation is exactly finite trace agreement. -/
theorem greatestSimulation_iff_traceRelated
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (leftState : LeftState) (rightState : RightState) :
    greatestSimulation left right outputRel leftState rightState ↔
      TraceRelated left right outputRel leftState rightState := by
  constructor
  · intro hgreat labels
    exact (greatestSimulation_isSimulation left right outputRel).observe_run hgreat labels
  · intro htrace
    exact greatestSimulation_isGreatest left right outputRel
      (TraceRelated left right outputRel) (traceRelated_isSimulation left right outputRel)
      leftState rightState htrace

/-- The one-vertex, one-edge graph whose walks count finite unfoldings. -/
def refinementGraph : EdgeGraph Unit Unit where
  source := fun _ => ()
  target := fun _ => ()

/-- The relation lifting as a one-loop directed transport. -/
def refinementTransport
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    Transport refinementGraph (fun _ => LeftState → RightState → Prop) where
  edgeMap _ := simulationOperator left right outputRel

/-- A simulation is exactly a constant-family oplax section of refinement transport. -/
theorem isOplaxSection_iff_isSimulation
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop) :
    (refinementTransport left right outputRel).IsOplaxSection (fun _ => relation) ↔
      IsSimulation left right outputRel relation := by
  constructor
  · intro hsection
    exact hsection ()
  · intro hsimulation _edge
    exact hsimulation

/-- Every refinement-transport edge is monotone. -/
theorem monotone_refinementTransport_edgeMap
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    ∀ edge, Monotone ((refinementTransport left right outputRel).edgeMap edge) :=
  fun _edge ↦ monotone_simulationOperator left right outputRel

/-- The loop walk representing `steps` finite relation unfoldings. -/
def refinementWalk : ℕ → refinementGraph.Walk () ()
  | 0 => .nil
  | steps + 1 => (refinementWalk steps).concat () rfl

/-- Every simulation is contained in each of its finite relation unfoldings. -/
theorem simulation_le_walkMap
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop)
    (relation : LeftState → RightState → Prop)
    (hsimulation : IsSimulation left right outputRel relation) (steps : ℕ) :
    relation ≤
      (refinementTransport left right outputRel).walkMap (refinementWalk steps) relation := by
  have hsection :=
    (isOplaxSection_iff_isSimulation left right outputRel relation).2 hsimulation
  exact hsection.le_walkMap
    (monotone_refinementTransport_edgeMap left right outputRel) (refinementWalk steps)

/-- The greatest simulation is an exact section of refinement transport. -/
theorem greatestSimulation_isSection
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) :
    (refinementTransport left right outputRel).IsSection
      (fun _ => greatestSimulation left right outputRel) := by
  intro _edge
  exact greatestSimulation_isFixedPoint left right outputRel

/-- Every finite relation unfolding fixes the greatest simulation. -/
theorem greatestSimulation_walkMap_eq
    (left : DeterministicSystem Label LeftOutput LeftState)
    (right : DeterministicSystem Label RightOutput RightState)
    (outputRel : LeftOutput → RightOutput → Prop) (steps : ℕ) :
    (refinementTransport left right outputRel).walkMap (refinementWalk steps)
        (greatestSimulation left right outputRel) =
      greatestSimulation left right outputRel := by
  exact (greatestSimulation_isSection left right outputRel).walkMap_eq (refinementWalk steps)

end CoalgebraicRefinement
