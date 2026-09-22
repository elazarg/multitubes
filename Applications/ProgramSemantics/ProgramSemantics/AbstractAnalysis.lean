/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import ProgramSemantics.FiniteReachability
public import Maths.Multitubes.Morphism

import Mathlib.Tactic.FinCases

/-!
# Executable abstract reachability analysis

A finite abstract state space can analyze an infinite concrete state space when concretization
forms an upper simulation of forward predicate transports. The general least-lax-majorant
comparison theorem then turns local transition soundness into global reachability soundness.

The worked analyzer tracks parity for natural-number states. Its two instructions add two and
reset every input to zero. Finite saturation computes only the even abstract cell, which proves
that no odd concrete state is reachable. The reset is deliberately noninjective.

## Main definitions

* `ProgramSemantics.AbstractDomain.concretizeSet`: concretization of abstract-state sets.
* `ProgramSemantics.AbstractDomain.upperSimulation`: the generic predicate simulation.
* `ProgramSemantics.parityReachable`: executable saturation of the parity abstraction.

## Main results

* `ProgramSemantics.AbstractDomain.leastLaxMajorant_sound`: abstract least closure soundly
  contains concrete least closure.
* `ProgramSemantics.AbstractDomain.computedReachability_sound`: executable abstract saturation
  contains concrete least closure after concretization.
* `ProgramSemantics.parityReachable_eq`: the analyzer computes only the even cell.
* `ProgramSemantics.parity_walk_even`: every concrete execution from zero ends even.
* `ProgramSemantics.parity_odd_not_reachable`: the unsafe odd cell is excluded.
* `ProgramSemantics.parity_initial_abstraction_imprecise`: the finite abstraction deliberately
  represents more states than the concrete initial singleton.

## Tags

abstract interpretation, finite-state analysis, reachability, upper simulation, parity
-/

@[expose] public section

namespace ProgramSemantics

open Maths

universe uV uE uC uA

/-- A finite-state abstraction of dependent concrete transition systems. -/
structure AbstractDomain {V : Type uV} {E : Type uE} (G : EdgeGraph V E)
    (Concrete : V → Type uC) (Abstract : Type uA)
    (concreteStep : (edge : E) → Concrete (G.source edge) → Concrete (G.target edge))
    (abstractStep : E → Abstract → Abstract) where
  /-- Concrete states represented by one abstract state at each control location. -/
  concretize : (vertex : V) → Abstract → Set (Concrete vertex)
  /-- Each concrete step is represented by the corresponding abstract step. -/
  step_mem : ∀ (edge : E) (abstract : Abstract) (state : Concrete (G.source edge)),
    state ∈ concretize (G.source edge) abstract →
      concreteStep edge state ∈ concretize (G.target edge) (abstractStep edge abstract)

namespace AbstractDomain

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Concrete : V → Type uC} {Abstract : Type uA}
variable {concreteStep : (edge : E) →
  Concrete (G.source edge) → Concrete (G.target edge)}
variable {abstractStep : E → Abstract → Abstract}

/-- Direct-image predicate transport is monotone on every edge. -/
theorem monotone_forwardPredicateTransport
    (step : (edge : E) → Concrete (G.source edge) → Concrete (G.target edge))
    (edge : E) : Monotone ((forwardPredicateTransport G step).edgeMap edge) := by
  change Monotone (Set.image (step edge))
  intro first second hsubset
  exact Set.image_mono hsubset

private theorem walkMap_le_leastLaxMajorant
    (step : (edge : E) → Concrete (G.source edge) → Concrete (G.target edge))
    (lower : ∀ vertex, Set (Concrete vertex)) {start finish : V}
    (walk : G.Walk start finish) :
    (forwardPredicateTransport G step).walkMap walk (lower start) ⊆
      (forwardPredicateTransport G step).leastLaxMajorant
        (monotone_forwardPredicateTransport step) lower finish := by
  have hlower := ((forwardPredicateTransport G step).leastLaxMajorant_isLeast
    (monotone_forwardPredicateTransport step) lower).1
  have hlax := ((forwardPredicateTransport G step).leastLaxMajorant_isLeast
    (monotone_forwardPredicateTransport step) lower).2.1
  induction walk with
  | nil => exact hlower _
  | concat walk edge legal ih =>
      rw [Transport.walkMap_concat]
      rintro target ⟨middle, hmiddle, rfl⟩
      cases legal
      apply hlax edge
      exact ⟨middle, ih hmiddle, rfl⟩

/-- Concretization of a set of abstract states. -/
def concretizeSet (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep)
    (vertex : V) (states : Set Abstract) : Set (Concrete vertex) :=
  {state | ∃ abstract ∈ states, state ∈ domain.concretize vertex abstract}

/-- A sound abstract domain induces an upper simulation between forward predicate transports. -/
def upperSimulation (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep) :
    Transport.UpperSimulation
      (forwardPredicateTransport (State := fun _ : V => Abstract) G abstractStep)
      (forwardPredicateTransport G concreteStep) where
  app := domain.concretizeSet
  edge_le edge states := by
    rintro state ⟨source, ⟨abstract, habstract, hsource⟩, rfl⟩
    exact ⟨abstractStep edge abstract, ⟨abstract, habstract, rfl⟩,
      domain.step_mem edge abstract source hsource⟩

/-- Concretization is monotone in the represented abstract-state set. -/
theorem monotone_concretizeSet
    (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep) (vertex : V) :
    Monotone (domain.concretizeSet vertex) := by
  intro first second hsubset state
  rintro ⟨abstract, habstract, hstate⟩
  exact ⟨abstract, hsubset habstract, hstate⟩

/-- Abstract least closure soundly contains concrete least closure. -/
theorem leastLaxMajorant_sound
    (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep)
    (abstractLower : V → Set Abstract) (concreteLower : ∀ vertex, Set (Concrete vertex))
    (hlower : ∀ vertex, concreteLower vertex ⊆
      domain.concretizeSet vertex (abstractLower vertex)) :
    (forwardPredicateTransport G concreteStep).leastLaxMajorant
        (monotone_forwardPredicateTransport concreteStep) concreteLower ≤
      (domain.upperSimulation.mapFamily
        ((forwardPredicateTransport (State := fun _ : V => Abstract) G
          abstractStep).leastLaxMajorant
          (monotone_forwardPredicateTransport (G := G) (Concrete := fun _ => Abstract)
            abstractStep) abstractLower)) := by
  exact domain.upperSimulation.leastLaxMajorant_le_map
    (domain.monotone_concretizeSet)
      (monotone_forwardPredicateTransport (G := G) (Concrete := fun _ => Abstract)
        abstractStep)
      (monotone_forwardPredicateTransport (G := G) concreteStep)
      abstractLower concreteLower hlower

section Finite

variable [Fintype V] [DecidableEq V] [Fintype E]
variable [Fintype Abstract] [DecidableEq Abstract]

/-- Finite abstract saturation is the abstract least lax majorant. -/
theorem reachableStates_eq_leastLaxMajorant
    (abstractStep : E → Abstract → Abstract) (initial : V → Finset Abstract) :
    (fun vertex => (reachableStates G abstractStep initial vertex : Set Abstract)) =
      (forwardPredicateTransport G abstractStep).leastLaxMajorant
        (monotone_forwardPredicateTransport (G := G) (Concrete := fun _ => Abstract)
          abstractStep)
        (fun vertex => (initial vertex : Set Abstract)) := by
  let transport := forwardPredicateTransport (State := fun _ : V => Abstract) G abstractStep
  let lower := fun vertex => (initial vertex : Set Abstract)
  have hpath := leastReachablePredicate (State := fun _ : V => Abstract) G abstractStep lower
  have hleast := transport.leastLaxMajorant_isLeast
    (monotone_forwardPredicateTransport (G := G) (Concrete := fun _ => Abstract)
      abstractStep) lower
  have heq : transport.pathClosure lower =
      transport.leastLaxMajorant
        (monotone_forwardPredicateTransport (G := G) (Concrete := fun _ => Abstract)
          abstractStep) lower := by
    apply le_antisymm
    · exact hpath.2.2 _ hleast.2.1 hleast.1
    · exact hleast.2.2 _ hpath.2.1 hpath.1
  funext vertex
  ext abstract
  change abstract ∈ reachableStates G abstractStep initial vertex ↔ _
  rw [mem_reachableStates_iff_pathClosure]
  exact Set.ext_iff.mp (congrFun heq vertex) abstract

/-- Executable finite abstract reachability contains concrete least closure after
concretization. -/
theorem computedReachability_sound
    (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep)
    (abstractInitial : V → Finset Abstract)
    (concreteLower : ∀ vertex, Set (Concrete vertex))
    (hlower : ∀ vertex, concreteLower vertex ⊆
      domain.concretizeSet vertex (abstractInitial vertex : Set Abstract)) :
    (forwardPredicateTransport G concreteStep).leastLaxMajorant
        (monotone_forwardPredicateTransport concreteStep) concreteLower ≤
      fun vertex => domain.concretizeSet vertex
        (reachableStates G abstractStep abstractInitial vertex : Set Abstract) := by
  have hsound := domain.leastLaxMajorant_sound
    (fun vertex => (abstractInitial vertex : Set Abstract)) concreteLower hlower
  intro vertex state hstate
  have heq := congrFun (reachableStates_eq_leastLaxMajorant
    (G := G) abstractStep abstractInitial) vertex
  change ∃ abstract ∈ (reachableStates G abstractStep abstractInitial vertex : Set Abstract),
    state ∈ domain.concretize vertex abstract
  rw [heq]
  exact hsound vertex hstate

/-- Every finite concrete execution from the concrete lower set is contained in the
concretization computed by finite abstract saturation. -/
theorem walkMap_le_computedReachability
    (domain : AbstractDomain G Concrete Abstract concreteStep abstractStep)
    (abstractInitial : V → Finset Abstract)
    (concreteLower : ∀ vertex, Set (Concrete vertex))
    (hlower : ∀ vertex, concreteLower vertex ⊆
      domain.concretizeSet vertex (abstractInitial vertex : Set Abstract))
    {start finish : V} (walk : G.Walk start finish) :
    (forwardPredicateTransport G concreteStep).walkMap walk (concreteLower start) ⊆
      domain.concretizeSet finish
        (reachableStates G abstractStep abstractInitial finish : Set Abstract) := by
  exact (walkMap_le_leastLaxMajorant concreteStep concreteLower walk).trans
    (domain.computedReachability_sound abstractInitial concreteLower hlower finish)

end Finite

end AbstractDomain

/-! ## Main results -/

/-- One-location graph with an increment instruction and a reset instruction. -/
def parityGraph : EdgeGraph Unit Bool where
  source _ := ()
  target _ := ()

/-- Infinite-state concrete instructions: add two, or reset noninjectively to zero. -/
def parityConcreteStep : Bool → Nat → Nat
  | false, _ => 0
  | true, state => state + 2

/-- Abstract instructions on parity: preserve parity, or reset to even. -/
def parityAbstractStep : Bool → Bool → Bool
  | false, _ => false
  | true, parity => parity

/-- The parity abstraction, with `false` representing even and `true` representing odd. -/
def parityDomain : AbstractDomain parityGraph (fun _ => Nat) Bool
    parityConcreteStep parityAbstractStep where
  concretize _ parity := {state | state % 2 = parity.toNat}
  step_mem edge parity state hstate := by
    cases edge <;> simp_all [parityConcreteStep, parityAbstractStep]

/-- Executable finite saturation from the even abstract cell. -/
def parityReachable : Finset Bool :=
  reachableStates parityGraph parityAbstractStep (fun _ => {false}) ()

/-- Saturation computes only the even cell. -/
theorem parityReachable_eq : parityReachable = {false} := by
  decide

/-- The odd abstract cell is rejected by the executable analyzer. -/
theorem parity_odd_not_reachable : true ∉ parityReachable := by
  decide

/-- The even abstract cell already represents `2`, although the concrete initial set is `{0}`.
This records the expected loss of precision without compromising soundness. -/
theorem parity_initial_abstraction_imprecise :
    2 ∈ parityDomain.concretize () false ∧ 2 ∉ ({0} : Set Nat) := by
  constructor
  · change 2 % 2 = 0
    decide
  · decide

/-- Every concrete execution from zero ends in the concretization of the computed even cell.
The computed finite abstract saturation soundly bounds the infinite concrete state space. -/
theorem parity_walk_even (walk : parityGraph.Walk () ()) :
    (forwardPredicateTransport (State := fun _ : Unit => Nat)
      parityGraph parityConcreteStep).walkMap walk ({0} : Set Nat) ⊆
      {state | state % 2 = 0} := by
  intro state hstate
  have hsound := AbstractDomain.walkMap_le_computedReachability parityDomain
    (fun _ => {false}) (fun _ => ({0} : Set Nat))
    (fun _ source hsource => by
      subst source
      refine ⟨false, by simp, ?_⟩
      change 0 % 2 = 0
      decide) walk
  obtain ⟨parity, hparity, hconcrete⟩ := hsound hstate
  have hfalse : parity = false := by
    have hmem : parity ∈ parityReachable := hparity
    simpa [parityReachable_eq] using hmem
  subst parity
  exact hconcrete

end ProgramSemantics
