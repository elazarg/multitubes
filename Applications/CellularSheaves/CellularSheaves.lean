/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.GraphSheaf

/-!
# Graph sheaves as exact and relational transport

A graph sheaf has vertex and edge stalks with two restriction maps for each graph edge. Its global
sections admit two equivalent transport descriptions: exact sections on the bipartite incidence
graph, and relational sections on the original graph using the pullback relation of the two
restrictions.

## Main definitions

* `CellularSheaves.GraphSheaf` - stalks and restriction maps on a directed graph.
* `CellularSheaves.GraphSheaf.IsCompatible` - compatible vertex-stalk assignments.
* `CellularSheaves.GraphSheaf.incidenceTransport` - exact transport on the incidence graph.
* `CellularSheaves.GraphSheaf.relationTransport` - pullback relations on the original graph.

## Main results

* `CellularSheaves.GraphSheaf.compatibleSectionEquiv` - compatible assignments are exact sections
  of incidence transport.
* `CellularSheaves.GraphSheaf.isRelationSection_iff` - the same assignments are relational
  sections on the original graph.
* `CellularSheaves.erasedSheaf_not_functional` - noninjective restrictions can produce a relation
  that is not the graph of any function.

## Tags

cellular sheaf, incidence graph, exact section, pullback relation, heterogeneous fiber
-/

@[expose] public section

namespace CellularSheaves

end CellularSheaves
