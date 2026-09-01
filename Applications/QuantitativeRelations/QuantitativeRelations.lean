/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantitativeRelations.GradedTransport

/-!
# Quantitative relations and directed transport

Graded mixed relations attach an additive edge cost to dependent directed transport.

## Main definitions

* `QuantitativeRelations.IsGradedMixedSectionFor` - a graded mixed section.

## Main results

* `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_lax_or_exact` and
  `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_oplax_or_exact` - propagation
  with one compatible polarity.
* `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_symmetric` - propagation
  along an arbitrary mixed walk under symmetry.
* `QuantitativeRelations.walkMap_nndist_le` - the pseudometric nonexpansiveness sanity test.
* `QuantitativeRelations.closedWalk_nndist_le` - its closed-walk specialization.

## Tags

graded relation, dependent transport, mixed polarity, walk sum, pseudometric
-/

@[expose] public section

namespace QuantitativeRelations

end QuantitativeRelations
