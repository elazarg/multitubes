/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Relational

/-!
# Graph sheaves and incidence transport

A graph sheaf assigns a stalk to each vertex and edge, together with restriction maps from the
stalks at both endpoints into the edge stalk. A vertex assignment is compatible when its two
restrictions agree on every edge.

Subdivision gives a bipartite incidence graph whose exact transport sections contain both vertex
and edge values. Alternatively, equality after restriction defines a relation directly between
the two endpoint stalks. Compatible assignments are exactly the relational sections, and are in
bijection with the exact incidence sections. The compatibility space is also the equalizer of the
two global restriction maps.

The final example uses constant restrictions from `Bool` to `Unit`. Every pair of endpoint values
is compatible, so the induced relation is not functional. Thus incidence maps express global
compatibility, while neither they nor the resulting relation justify reconstruction without an
additional injectivity or splitting hypothesis.

## Main definitions

* `CellularSheaves.GraphSheaf` - vertex and edge stalks with endpoint restrictions.
* `CellularSheaves.GraphSheaf.IsCompatible` - compatible vertex-stalk assignments.
* `CellularSheaves.GraphSheaf.incidenceGraph` - the bipartite subdivision graph.
* `CellularSheaves.GraphSheaf.incidenceTransport` - restriction maps on the incidence graph.
* `CellularSheaves.GraphSheaf.relationTransport` - endpoint compatibility as a pullback relation.
* `CellularSheaves.erasedSheaf` - a one-edge sheaf with noninjective restrictions.

## Main results

* `CellularSheaves.GraphSheaf.isCompatible_iff_restriction_eq` - compatibility is a global
  equalizer condition.
* `CellularSheaves.GraphSheaf.compatibleSectionEquiv` - compatible vertex assignments are exact
  incidence sections.
* `CellularSheaves.GraphSheaf.isRelationSection_iff` - compatible assignments are relational
  sections on the original graph.
* `CellularSheaves.erasedSheaf_relation_iff` - the noninjective example induces the universal
  endpoint relation.
* `CellularSheaves.erasedSheaf_not_functional` - this relation is not a function graph.

## Tags

cellular sheaf, incidence graph, exact section, equalizer, pullback relation
-/

@[expose] public section

namespace CellularSheaves

open Maths
open scoped SetRel

universe uV uE uS

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- A graph sheaf consists of vertex and edge stalks and the two endpoint restriction maps of each
edge. -/
structure GraphSheaf (G : EdgeGraph V E) where
  /-- The stalk over a graph vertex. -/
  VertexStalk : V → Type uS
  /-- The stalk over a graph edge. -/
  EdgeStalk : E → Type uS
  /-- Restriction from the source-vertex stalk to an edge stalk. -/
  sourceRestriction : (edge : E) → VertexStalk (G.source edge) → EdgeStalk edge
  /-- Restriction from the target-vertex stalk to an edge stalk. -/
  targetRestriction : (edge : E) → VertexStalk (G.target edge) → EdgeStalk edge

namespace GraphSheaf

variable (F : GraphSheaf G)

/-- A vertex assignment is compatible when its two endpoint restrictions agree on every edge. -/
def IsCompatible (value : ∀ vertex, F.VertexStalk vertex) : Prop :=
  ∀ edge, F.sourceRestriction edge (value (G.source edge)) =
    F.targetRestriction edge (value (G.target edge))

/-- Apply all source-endpoint restrictions to a vertex assignment. -/
def sourceRestrictionMap (value : ∀ vertex, F.VertexStalk vertex) :
    ∀ edge, F.EdgeStalk edge :=
  fun edge ↦ F.sourceRestriction edge (value (G.source edge))

/-- Apply all target-endpoint restrictions to a vertex assignment. -/
def targetRestrictionMap (value : ∀ vertex, F.VertexStalk vertex) :
    ∀ edge, F.EdgeStalk edge :=
  fun edge ↦ F.targetRestriction edge (value (G.target edge))

/-- Compatibility is the equalizer of the two global restriction maps. -/
theorem isCompatible_iff_restriction_eq (value : ∀ vertex, F.VertexStalk vertex) :
    F.IsCompatible value ↔ F.sourceRestrictionMap value = F.targetRestrictionMap value := by
  constructor
  · intro hcompatible
    funext edge
    exact hcompatible edge
  · intro heq edge
    exact congrArg (fun restriction ↦ restriction edge) heq

/-- The bipartite graph obtained by replacing each original edge by its two incidences. -/
def incidenceGraph : EdgeGraph (V ⊕ E) (E ⊕ E) where
  source
    | .inl edge => .inl (G.source edge)
    | .inr edge => .inl (G.target edge)
  target
    | .inl edge => .inr edge
    | .inr edge => .inr edge

/-- The stalk family on the bipartite incidence graph. -/
def incidenceFiber : V ⊕ E → Type uS
  | .inl vertex => F.VertexStalk vertex
  | .inr edge => F.EdgeStalk edge

/-- The two endpoint restrictions regarded as maps on the incidence graph. -/
def incidenceTransport : Transport (incidenceGraph (G := G)) F.incidenceFiber where
  edgeMap
    | .inl edge => F.sourceRestriction edge
    | .inr edge => F.targetRestriction edge

/-- Combine vertex-stalk and edge-stalk values into one incidence-graph family. -/
def incidenceFamily (vertexValue : ∀ vertex, F.VertexStalk vertex)
    (edgeValue : ∀ edge, F.EdgeStalk edge) : ∀ cell, F.incidenceFiber cell
  | .inl vertex => vertexValue vertex
  | .inr edge => edgeValue edge

/-- A compatible vertex assignment extended by its common values in the edge stalks. -/
def compatibleFamily (value : ∀ vertex, F.VertexStalk vertex) :
    ∀ cell, F.incidenceFiber cell :=
  F.incidenceFamily value (F.sourceRestrictionMap value)

/-- A compatible assignment extends to an exact section of the incidence transport. -/
theorem isSection_compatibleFamily {value : ∀ vertex, F.VertexStalk vertex}
    (hvalue : F.IsCompatible value) :
    F.incidenceTransport.IsSection (F.compatibleFamily value) := by
  intro incidence
  cases incidence with
  | inl edge => rfl
  | inr edge => exact (hvalue edge).symm

/-- Read the vertex-stalk values from an incidence-graph family. -/
def vertexValue (family : ∀ cell, F.incidenceFiber cell) :
    ∀ vertex, F.VertexStalk vertex :=
  fun vertex ↦ family (.inl vertex)

/-- The vertex values of an exact incidence section are compatible. -/
theorem isCompatible_vertexValue {family : ∀ cell, F.incidenceFiber cell}
    (hfamily : F.incidenceTransport.IsSection family) :
    F.IsCompatible (F.vertexValue family) := by
  intro edge
  have hsource :
      F.sourceRestriction edge (family (.inl (G.source edge))) = family (.inr edge) :=
    hfamily (.inl edge)
  have htarget :
      F.targetRestriction edge (family (.inl (G.target edge))) = family (.inr edge) :=
    hfamily (.inr edge)
  exact hsource.trans htarget.symm

/-- Compatible vertex assignments are equivalent to exact sections on the incidence graph. -/
def compatibleSectionEquiv :
    {value : ∀ vertex, F.VertexStalk vertex // F.IsCompatible value} ≃
      {family : ∀ cell, F.incidenceFiber cell // F.incidenceTransport.IsSection family} where
  toFun value := ⟨F.compatibleFamily value, F.isSection_compatibleFamily value.property⟩
  invFun family := ⟨F.vertexValue family, F.isCompatible_vertexValue family.property⟩
  left_inv value := by
    apply Subtype.ext
    funext vertex
    rfl
  right_inv family := by
    apply Subtype.ext
    funext cell
    cases cell with
    | inl vertex => rfl
    | inr edge => exact family.property (.inl edge)

/-- Endpoint compatibility as a relation on each original graph edge. -/
def relationTransport : RelationTransport G F.VertexStalk where
  edgeRelation edge :=
    {(source, target) |
      F.sourceRestriction edge source = F.targetRestriction edge target}

/-- Relational sections on the original graph are precisely compatible vertex assignments. -/
theorem isRelationSection_iff (value : ∀ vertex, F.VertexStalk vertex) :
    F.relationTransport.IsSection value ↔ F.IsCompatible value :=
  Iff.rfl

end GraphSheaf

/-! ## A nonfunctional compatibility span -/

/-- A graph with one edge from `false` to `true`. -/
def oneEdgeGraph : EdgeGraph Bool Unit where
  source _edge := false
  target _edge := true

/-- A graph sheaf whose endpoint restrictions erase all Boolean information. -/
def erasedSheaf : GraphSheaf oneEdgeGraph where
  VertexStalk _vertex := Bool
  EdgeStalk _edge := Unit
  sourceRestriction _edge _value := ()
  targetRestriction _edge _value := ()

/-- Every pair of endpoint values is related by the erased sheaf. -/
theorem erasedSheaf_relation_iff (source target : Bool) :
    source ~[erasedSheaf.relationTransport.edgeRelation ()] target :=
  rfl

/-- The compatibility relation of the erased sheaf is not the graph of a function. -/
theorem erasedSheaf_not_functional :
    ¬ ∃ function : Bool → Bool,
      erasedSheaf.relationTransport.edgeRelation () = Function.graph function := by
  rintro ⟨function, hfunction⟩
  have hfalse : (false, false) ∈ Function.graph function := by
    rw [← hfunction]
    exact erasedSheaf_relation_iff false false
  have htrue : (false, true) ∈ Function.graph function := by
    rw [← hfunction]
    exact erasedSheaf_relation_iff false true
  rw [Function.mem_graph] at hfalse htrue
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

end CellularSheaves
