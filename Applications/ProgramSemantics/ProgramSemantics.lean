/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import ProgramSemantics.PredicateTransport

/-!
# Program semantics and transport

Predicate transformers give a small program-semantics client for transport.  A
state transition acts contravariantly on predicates by inverse image.  Its direct image is
the residual supplied when an oplax predicate constraint is reversed.  This works for
noninjective transitions, where the two predicate transformers are not inverse functions.

## Main definitions

* `ProgramSemantics.predicateTransport` - inverse-image transport of predicates.
* `ProgramSemantics.forwardPredicateTransport` - direct-image transport of predicates.
* `ProgramSemantics.reverseGraph` - the edge-reversed control-flow graph.
* `ProgramSemantics.StateSaturated` - predicates constant on transition kernel classes.
* `ProgramSemantics.collapse` - a noninjective Boolean state transition.

## Main results

* `ProgramSemantics.mixedPredicateLaxification_iff` - mixed inverse-image constraints
  are equivalent to lax direct-image constraints after edge reversal.
* `ProgramSemantics.leastReachablePredicate` - path closure is the least inductive
  predicate family containing given lower data.
* `ProgramSemantics.preimage_image_eq_self_iff` - exact recovery by inverse-after-direct
  image is equivalent to kernel saturation.
* `ProgramSemantics.collapse_preimage_image_singleton` - inverse image after direct
  image saturates a predicate for a collapsing transition.

## Tags

program semantics, predicate transformer, weakest precondition, strongest postcondition,
transport, Galois connection, noninjective
-/

@[expose] public section

namespace ProgramSemantics

export Maths (EdgeGraph EdgeMode Transport)

end ProgramSemantics
