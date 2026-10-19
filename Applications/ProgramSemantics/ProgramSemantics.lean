/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import ProgramSemantics.PredicateTransport
public import ProgramSemantics.FiniteReachability
public import ProgramSemantics.AbstractAnalysis
public import ProgramSemantics.Octagon

/-!
# Program semantics and transport

Predicate transformers give a small program-semantics client for transport.  A
state transition acts contravariantly on predicates by inverse image.  Its direct image is
the lower adjoint supplied when an oplax predicate constraint is reversed.  This works for
noninjective transitions, where the two predicate transformers are not inverse functions.

## Main definitions

* `ProgramSemantics.predicateTransport` - inverse-image transport of predicates.
* `ProgramSemantics.forwardPredicateTransport` - direct-image transport of predicates.
* `Maths.EdgeGraph.reverse` - the edge-reversed control-flow graph.
* `ProgramSemantics.StateSaturated` - predicates constant on transition kernel classes.
* `ProgramSemantics.collapse` - a noninjective Boolean state transition.
* `ProgramSemantics.reachableConfigurations` - terminating finite-state saturation.
* `ProgramSemantics.reachableStates` - saturation projected to control locations.
* `ProgramSemantics.AbstractDomain` - a sound finite abstraction of concrete transitions.
* `ProgramSemantics.Octagon.doubledGraph` - the skew-symmetric doubled graph of an octagon
  constraint system.

## Main results

* `ProgramSemantics.mixedPredicateLaxification_iff` - mixed inverse-image constraints
  are equivalent to lax direct-image constraints after edge reversal.
* `ProgramSemantics.leastReachablePredicate` - path closure is the least inductive
  predicate family containing given lower data.
* `ProgramSemantics.preimage_image_eq_self_iff` - exact recovery by inverse-after-direct
  image is equivalent to kernel saturation.
* `ProgramSemantics.collapse_preimage_image_singleton` - inverse image after direct
  image saturates a predicate for a collapsing transition.
* `ProgramSemantics.mem_reachableConfigurations_iff` - finite saturation agrees with
  typed-walk execution.
* `ProgramSemantics.mem_reachableStates_iff_pathClosure` - finite saturation agrees with
  the least predicate closure.
* `ProgramSemantics.reset_reachableStates` - a checked noninjective safety example.
* `ProgramSemantics.AbstractDomain.computedReachability_sound` - finite abstract saturation
  contains concrete least closure after concretization.
* `ProgramSemantics.parity_walk_even` - computed parity reachability proves all-walk safety for
  an infinite natural-number state space.
* `ProgramSemantics.Octagon.feasible_iff_forall_closedWalk_nonneg` - octagon constraints over a
  linearly ordered field are feasible exactly when every closed walk of the doubled graph has
  nonnegative total bound.
* `ProgramSemantics.Octagon.integer_gap` - the same test is not sufficient over the integers.

## Tags

program semantics, predicate transformer, weakest precondition, strongest postcondition,
transport, Galois connection, noninjective, finite-state reachability, abstract interpretation,
octagon
-/

@[expose] public section

namespace ProgramSemantics

export Maths (EdgeGraph EdgeMode Transport)

end ProgramSemantics
