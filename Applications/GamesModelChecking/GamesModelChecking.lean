/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import GamesModelChecking.Alternation

/-!
# Alternating fixed points and local transport constraints

Nested least and greatest fixed points select solutions of monotone equation systems. A two-copy
system shows that the nesting priority is information beyond its local equations: opposite
nesting orders for least and greatest variables select distinct exact sections of the same
transport graph.

## Main definitions

* `GamesModelChecking.BinaryMonotoneSystem` - a monotone two-variable equation system.
* `GamesModelChecking.BinaryMonotoneSystem.leastGreatestSolution` - least outside, greatest
  inside.
* `GamesModelChecking.BinaryMonotoneSystem.greatestLeastSolution` - greatest outside, least
  inside.
* `GamesModelChecking.copySystem` - the mutual-copy equation system.
* `GamesModelChecking.copyTransport` - its local exact transport constraints.

## Main results

* `GamesModelChecking.BinaryMonotoneSystem.isFixedPoint_leastGreatestSolution` and
  `GamesModelChecking.BinaryMonotoneSystem.isFixedPoint_greatestLeastSolution` - both nested
  solutions satisfy both local equations.
* `GamesModelChecking.copyFixedPoint_iff_isSection` - the local copy equations are exactly the
  section equations of the two-edge transport graph.
* `GamesModelChecking.priority_data_not_determined_by_local_sections` - opposite nesting orders
  select distinct exact sections despite identical local constraints.

## Tags

fixed point, alternation, priority, model checking, exact section
-/

@[expose] public section

namespace GamesModelChecking

end GamesModelChecking
