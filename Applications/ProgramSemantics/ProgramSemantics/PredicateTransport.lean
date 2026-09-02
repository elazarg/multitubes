/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure
public import Maths.Multitubes.Mixed.AdjointOrder
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Predicate transformers for transport

A state transition acts on predicates by inverse image.  The direct image of a predicate is
its existential postcondition, and Mathlib's `Set.image_preimage` theorem makes direct image
left adjoint to inverse image.  Consequently an oplax inverse-image constraint becomes a lax
direct-image constraint on the reversed edge.  No injectivity or inverse state transition is
needed.

The inverse-image transport is deliberately read on an edge oriented from a postcondition
vertex to a precondition vertex: inverse image is contravariant for a forward state step.  The
reversed laxification then carries the direct-image postcondition in the forward direction.

The forward transport also preserves arbitrary joins, so the general path-closure theorem
computes the least inductive predicate family above prescribed lower data.

## Main definitions

* `ProgramSemantics.predicateTransport` - edgewise inverse-image transport.
* `ProgramSemantics.forwardPredicateTransport` - edgewise direct-image transport.
* `ProgramSemantics.StateSaturated` - predicates constant on transition kernel classes.
* `ProgramSemantics.collapse` - the constant Boolean transition used for the concrete
  noninjective example.

## Main results

* `ProgramSemantics.mixedPredicateLaxification_iff` - an ordered mixed section for inverse
  image is equivalent to an all-lax section for direct image on the laxification graph.
* `ProgramSemantics.backward_obligation_iff_forward_postcondition` - the elementary
  weakest-precondition/strongest-postcondition adjunction.
* `ProgramSemantics.leastReachablePredicate` - the least lax direct-image family above
  prescribed lower predicates.
* `ProgramSemantics.preimage_image_eq_self_iff` - exact recovery by inverse-after-direct
  image is equivalent to kernel saturation.
* `ProgramSemantics.collapse_merges_predicates` and
  `ProgramSemantics.collapse_preimage_image_singleton` - the Boolean transition is not
  invertible on states or predicates.

## Tags

program semantics, predicate transformer, weakest precondition, strongest postcondition,
transport, Galois connection, path closure
-/

@[expose] public section

noncomputable section

namespace ProgramSemantics

open Maths

universe uV uE uS uX uY

variable {V : Type uV} {E : Type uE} {State : V → Type uS}

/-- Inverse-image transport of predicates along edge-indexed state transitions.

The edge orientation is from a postcondition vertex to a precondition vertex, so this is the
backward transformer for the corresponding forward state step. -/
def predicateTransport (G : EdgeGraph V E)
    (step : (edge : E) → State (G.source edge) → State (G.target edge)) :
    Transport G.reverse (fun vertex => Set (State vertex)) where
  edgeMap edge := Set.preimage (step edge)

/-- Direct-image transport of predicates along edge-indexed state transitions.

This is the forward postcondition transformer on the original edge orientation. -/
def forwardPredicateTransport (G : EdgeGraph V E)
    (step : (edge : E) → State (G.source edge) → State (G.target edge)) :
    Transport G (fun vertex => Set (State vertex)) where
  edgeMap edge := Set.image (step edge)

variable {G : EdgeGraph V E}
variable {step : (edge : E) → State (G.source edge) → State (G.target edge)}
variable {mode : E → EdgeMode}
variable {family : ∀ vertex, Set (State vertex)}

/-- Direct image is the residual for inverse-image transport on every reversed edge. -/
def directImageResidual (G : EdgeGraph V E)
    (step : (edge : E) → State (G.source edge) → State (G.target edge))
    (mode : E → EdgeMode) :
    ∀ _edge : Transport.LaxificationReverseEdge mode,
      Set (State (G.source _edge.1)) → Set (State (G.target _edge.1)) :=
  fun edge => Set.image (step edge.1)

/-- Mixed inverse-image predicate constraints become all-lax direct-image constraints after
edge reversal.  This is the weakest-precondition/strongest-postcondition adjunction at the
level of entire transports.  Thus the source graph is read in the backward
orientation described by `predicateTransport`. -/
theorem mixedPredicateLaxification_iff
    (G : EdgeGraph V E)
    (step : (edge : E) → State (G.source edge) → State (G.target edge))
    (mode : E → EdgeMode) (family : ∀ vertex, Set (State vertex)) :
    (predicateTransport G step).IsMixedSection mode family ↔
      ((predicateTransport G step).laxification mode
        (directImageResidual G step mode)).IsLaxSection family := by
  apply Transport.isMixedSection_iff_laxification_of_galoisConnection
  intro edge
  exact Set.image_preimage

/-- A direct-image postcondition is contained in `Q` exactly when `P` is contained in the
inverse-image weakest precondition of `Q`. -/
theorem backward_obligation_iff_forward_postcondition
    {X : Type uX} {Y : Type uY} (step : X → Y) (P : Set X) (Q : Set Y) :
    P ⊆ Set.preimage step Q ↔ Set.image step P ⊆ Q := by
  exact Set.image_subset_iff.symm

/-- A predicate is saturated when it is constant on every kernel class of a state step. -/
def StateSaturated {X : Type uX} {Y : Type uY} (step : X → Y) (P : Set X) : Prop :=
  ∀ ⦃x y⦄, step x = step y → (x ∈ P ↔ y ∈ P)

/-- Inverse image after direct image is exactly the original predicate when the predicate is
saturated under the kernel relation of the state step. -/
theorem preimage_image_eq_self_iff
    {X : Type uX} {Y : Type uY} (step : X → Y) (P : Set X) :
    step ⁻¹' (step '' P) = P ↔ StateSaturated step P := by
  constructor
  · intro h x y hxy
    constructor
    · intro hx
      have hy : y ∈ step ⁻¹' (step '' P) := by
        change step y ∈ step '' P
        exact ⟨x, hx, hxy⟩
      rwa [h] at hy
    · intro hy
      have hx : x ∈ step ⁻¹' (step '' P) := by
        change step x ∈ step '' P
        exact ⟨y, hy, hxy.symm⟩
      rwa [h] at hx
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      change step x ∈ step '' P at hx
      rcases hx with ⟨y, hy, hxy⟩
      exact (h hxy.symm).mpr hy
    · exact Set.subset_preimage_image step P

/-- The forward predicate transport has the arbitrary-supremum homomorphisms needed by path
closure. -/
def forwardPredicateSupHom (step : (edge : E) →
    State (G.source edge) → State (G.target edge)) (edge : E) :
    sSupHom (Set (State (G.source edge))) (Set (State (G.target edge))) :=
  sSupHom.setImage (step edge)

/-- The path closure of lower predicates is the least inductive family containing them. -/
theorem leastReachablePredicate
    (G : EdgeGraph V E)
    (step : (edge : E) → State (G.source edge) → State (G.target edge))
    (lower : ∀ vertex, Set (State vertex)) :
    (forwardPredicateTransport G step).IsLaxSection
        ((forwardPredicateTransport G step).pathClosure lower) ∧
      (∀ vertex, lower vertex ≤
        (forwardPredicateTransport G step).pathClosure lower vertex) ∧
      ∀ family : ∀ vertex, Set (State vertex),
        (forwardPredicateTransport G step).IsLaxSection family →
        (∀ vertex, lower vertex ≤ family vertex) →
        ∀ vertex,
          (forwardPredicateTransport G step).pathClosure lower vertex ≤ family vertex := by
  apply (forwardPredicateTransport G step).pathClosure_isLeast_of_sSupHom
    (fun edge => forwardPredicateSupHom step edge)
  intro edge point
  rfl

/-! ## A noninjective state transition -/

/-- The Boolean transition that forgets the input state. -/
def collapse : Bool → Bool := fun _ => false

/-- The collapse transition gives the same direct-image predicate for both Boolean states. -/
theorem collapse_merges_predicates :
    collapse '' ({true} : Set Bool) = collapse '' ({false} : Set Bool) := by
  ext point
  simp [collapse]

/-- Inverse image after direct image saturates the singleton under the collapse transition. -/
theorem collapse_preimage_image_singleton :
    collapse ⁻¹' (collapse '' ({true} : Set Bool)) = Set.univ := by
  ext point
  simp [collapse]

end ProgramSemantics

end
