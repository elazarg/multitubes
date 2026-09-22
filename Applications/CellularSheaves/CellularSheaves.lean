/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.GraphSheaf
public import CellularSheaves.OptimalTolerance
public import CellularSheaves.CycleConsistency
public import CellularSheaves.ActiveCertificate

/-!
# Graph sheaves as exact and relational transport

A graph sheaf has vertex and edge stalks with two restriction maps for each graph edge. Its global
sections admit two equivalent transport descriptions: exact sections on the bipartite incidence
graph, and relational sections on the original graph using the pullback relation of the two
restrictions.  For finite real sensor networks, affine endpoint restrictions additionally give an
exact signed linear-inequality model of approximate consistency, executable rational witnesses,
and an attained optimal uniform tolerance.

## Main definitions

* `CellularSheaves.GraphSheaf` - stalks and restriction maps on a directed graph.
* `CellularSheaves.GraphSheaf.IsCompatible` - compatible vertex-stalk assignments.
* `CellularSheaves.GraphSheaf.incidenceTransport` - exact transport on the incidence graph.
* `CellularSheaves.GraphSheaf.relationTransport` - pullback relations on the original graph.
* `CellularSheaves.RationalSensorNetwork` - finite affine sensor comparisons with rational data.
* `CellularSheaves.RationalSensorNetwork.minimumUniformTolerance` - the least nonnegative
  uniform consistency tolerance.
* `CellularSheaves.RationalSensorNetwork.signedComparisonGraph` - the doubled graph for
  unit-scale comparison residuals.

## Main results

* `CellularSheaves.GraphSheaf.compatibleSectionEquiv` - compatible assignments are exact sections
  of incidence transport.
* `CellularSheaves.GraphSheaf.isRelationSection_iff` - the same assignments are relational
  sections on the original graph.
* `CellularSheaves.erasedSheaf_not_functional` - noninjective restrictions can produce a relation
  that is not the graph of any function.
* `CellularSheaves.RationalSensorNetwork.isConsistent_zero_iff_isCompatible` - exact sensor
  consistency is graph-sheaf compatibility.
* `CellularSheaves.RationalSensorNetwork.not_exists_isConsistent_of_checkCertificate` - an exact
  rational Farkas check certifies real inconsistency.
* `CellularSheaves.RationalSensorNetwork.isLeast_minimumUniformTolerance` - every finite affine
  network has an attained least nonnegative uniform tolerance.
* `CellularSheaves.minimumUniformTolerance_triangle` - the inconsistent triangle has optimal
  tolerance `1 / 3`.
* `CellularSheaves.RationalSensorNetwork.exists_isConsistent_uniform_iff_closedWalk_le` -
  unit-scale uniform consistency is exactly a signed closed-walk mean bound.
* `CellularSheaves.RationalSensorNetwork.exists_rankSparse_activeCertificate` - an optimal
  reading has a rank-sparse normalized certificate supported on active signed comparisons.

## Tags

cellular sheaf, sensor consistency, optimal tolerance, exact section, rational certificate
-/

@[expose] public section

namespace CellularSheaves

end CellularSheaves
