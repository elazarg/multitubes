/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import ConicFinance.TransactionCosts

/-!
# Deterministic conic finance

Transaction sets label the edges of a market graph. Their native relational semantics composes
along walks by Minkowski addition, while existential image embeds the same semantics into
transport on powersets. Serial composition preserves convexity, but aggregation over alternative
paths need not do so.

## Main definitions

* `ConicFinance.SolvencyLE` - the preorder relation induced by an additive solvency cone.
* `ConicFinance.TransactionMarket` - feasible portfolio increments attached to graph edges.
* `ConicFinance.TransactionMarket.walkIncrement` - the Minkowski sum along a walk.
* `ConicFinance.TransactionMarket.relationTransport` - the relation-labelled market graph.

## Main results

* `ConicFinance.TransactionMarket.walkRelation_iff_sub_mem_walkIncrement` - path feasibility is
  membership of the net portfolio change in the pathwise Minkowski sum.
* `ConicFinance.TransactionMarket.walkIncrement_append` - serial paths add their attainable
  increment sets.
* `Maths.RelationTransport.walkMap_eq_image_walkRelation` - powerset transport agrees exactly
  with native relational composition.
* `ConicFinance.TransactionMarket.convex_walkIncrement` - serial composition preserves
  convexity.
* `ConicFinance.not_convex_alternativeReachable` - alternative-path aggregation need not
  preserve convexity.

## Tags

transaction costs, solvency cone, Minkowski sum, relation, convexity, path transport
-/

@[expose] public section

namespace ConicFinance

end ConicFinance
