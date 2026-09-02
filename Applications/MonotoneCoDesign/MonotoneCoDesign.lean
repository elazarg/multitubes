/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.RelationalClosure
public import MonotoneCoDesign.MonotoneFeasibility

/-!
# Monotone co-design by relational transport

Co-design feasibility relations compose along typed graph walks. Existential image embeds the
native relational semantics into transport on powersets, where feasible assignments are
oplax sections and path closure constructs least attainable families.

## Main definitions

* `Maths.RelationTransport` - relations attached to typed graph edges.
* `Maths.RelationTransport.walkRelation` - relational composition along a walk.
* `Maths.RelationTransport.powersetTransport` - the existential-image adapter.
* `Maths.RelationTransport.ofTransport` - ordinary transport embedded by function graphs.
* `MonotoneCoDesign.IsMonotoneFeasibility` - co-design monotonicity for a feasibility relation.
* `MonotoneCoDesign.orderFeasibility` - the identity monotone feasibility relation.

## Main results

* `Maths.RelationTransport.walkMap_eq_image_walkRelation` - powerset walk transport agrees with
  native relational composition.
* `Maths.RelationTransport.walkRelation_ofTransport` - the relational extension recovers ordinary
  walk transport on functions.
* `Maths.RelationTransport.isOplaxSection_singleton_iff` - native compatible assignments are
  singleton-valued oplax sections.
* `Maths.RelationTransport.IsSection.walkRelation` - local compatibility propagates along every
  walk.
* `Maths.RelationTransport.mem_pathClosure_iff` - closure is existential path attainability.
* `MonotoneCoDesign.IsMonotoneFeasibility.comp` - serial composition preserves co-design
  monotonicity.
* `MonotoneCoDesign.RelationTransport.HasMonotoneFeasibility.walkRelation_of_pos` - nonempty
  paths preserve monotone feasibility.

## Tags

monotone co-design, feasibility relation, relational composition, transport, powerset
-/

@[expose] public section

namespace MonotoneCoDesign

end MonotoneCoDesign
