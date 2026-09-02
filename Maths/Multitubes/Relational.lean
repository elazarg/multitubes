/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Mathlib.Data.Rel

/-!
# Relation-labelled transport

A relation-labelled graph assigns a relation between the endpoint fibers of every edge. Two
fiber elements are related along a walk when intermediate elements can be chosen at every edge.
This gives the free path-category composition of the edge relations.

Existential image embeds relation-labelled transport into ordinary map-labelled transport on
powersets. The native composite relation and the induced walk map agree exactly. Function graphs
embed ordinary transport in the other direction, and this embedding also commutes with walks.

## Main definitions

* `Maths.RelationTransport` - relations attached to the edges of a typed graph.
* `Maths.RelationTransport.walkRelation` - existential composition along a typed walk.
* `Maths.RelationTransport.powersetTransport` - transport by existential image.
* `Maths.RelationTransport.ofTransport` - ordinary transport embedded by function graphs.
* `Maths.RelationTransport.IsSection` - a point assignment satisfying every edge relation.

## Main results

* `Maths.RelationTransport.walkRelation_append` - native walk relations compose under append.
* `Maths.RelationTransport.walkMap_eq_image_walkRelation` - powerset walk transport is native
  relational image.
* `Maths.RelationTransport.walkRelation_ofTransport` - function-graph relations recover ordinary
  walk transport.
* `Maths.RelationTransport.isOplaxSection_singleton_iff` - relational sections are singleton
  oplax sections after the powerset embedding.
* `Maths.RelationTransport.IsSection.walkRelation` - edgewise compatibility propagates along
  walks.

## Tags

relation, quiver, transport, relational composition, powerset
-/

@[expose] public section

namespace Maths

open scoped SetRel

universe uV uE uF

variable {V : Type uV} {E : Type uE}
variable {G : EdgeGraph V E} {Fiber : V → Type uF}

/-- Relations between the endpoint fibers of the edges of a directed graph. -/
structure RelationTransport (G : EdgeGraph V E) (Fiber : V → Type uF) where
  /-- The relation carried by an edge. -/
  edgeRelation : (edge : E) → SetRel (Fiber (G.source edge)) (Fiber (G.target edge))

namespace RelationTransport

variable (T : RelationTransport G Fiber)

/-- Regard the maps of an ordinary transport as their function-graph relations. -/
def ofTransport (transport : Transport G Fiber) : RelationTransport G Fiber where
  edgeRelation edge := Function.graph (transport.edgeMap edge)

/-- Compose edge relations existentially along a typed walk. -/
def walkRelation {start : V} :
    {finish : V} → G.Walk start finish → SetRel (Fiber start) (Fiber finish)
  | _, .nil => SetRel.id
  | _, .concat walk edge legal =>
      walkRelation walk ○
        {(source, target) |
          fiberCast Fiber legal.symm source ~[T.edgeRelation edge] target}

/-- Existential image embeds relation-labelled edges into transport on powersets. -/
def powersetTransport : Transport G (fun vertex ↦ Set (Fiber vertex)) where
  edgeMap edge := (T.edgeRelation edge).image

variable {T}

/-- On function-graph edges, the native walk relation is the graph of ordinary walk transport. -/
theorem walkRelation_ofTransport {start finish : V} (transport : Transport G Fiber)
    (walk : G.Walk start finish) :
    (ofTransport transport).walkRelation walk = Function.graph (transport.walkMap walk) := by
  induction walk with
  | nil => exact Function.graph_id.symm
  | @concat middle walk edge legal ih =>
      subst middle
      rw [walkRelation, ih]
      exact (Function.graph_comp (transport.edgeMap edge) (transport.walkMap walk)).symm

/-- Function-graph path feasibility is equality with the ordinary transported value. -/
theorem walkRelation_ofTransport_iff {start finish : V} (transport : Transport G Fiber)
    (walk : G.Walk start finish) (source : Fiber start) (target : Fiber finish) :
    source ~[(ofTransport transport).walkRelation walk] target ↔
      transport.walkMap walk source = target := by
  rw [walkRelation_ofTransport]
  exact Function.mem_graph

/-- Powerset walk transport is exactly image under the composite native walk relation. -/
theorem walkMap_eq_image_walkRelation {start finish : V}
    (walk : G.Walk start finish) (set : Set (Fiber start)) :
    T.powersetTransport.walkMap walk set = (T.walkRelation walk).image set := by
  induction walk with
  | nil => simp [powersetTransport, walkRelation]
  | @concat middle walk edge legal ih =>
      subst middle
      rw [Transport.walkMap_concat, fiberCast_rfl, ih]
      simp only [powersetTransport, walkRelation]
      exact (SetRel.image_comp (T.walkRelation walk) (T.edgeRelation edge) set).symm

/-- Native relation semantics composes in the same order as walk concatenation. -/
theorem walkRelation_append {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    T.walkRelation (first.append second) = T.walkRelation first ○ T.walkRelation second := by
  induction second with
  | nil => simp [walkRelation]
  | concat walk edge legal ih =>
      rw [EdgeGraph.Walk.append_concat]
      simp only [walkRelation, ih, SetRel.comp_assoc]

/-- A relational section assigns one fiber element to every vertex and satisfies every edge
relation. -/
def IsSection (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge, family (G.source edge) ~[T.edgeRelation edge] family (G.target edge)

/-- Relational sections are exactly singleton-valued oplax sections after the powerset
embedding. -/
theorem isOplaxSection_singleton_iff (family : ∀ vertex, Fiber vertex) :
    T.powersetTransport.IsOplaxSection (fun vertex ↦ {family vertex}) ↔
      T.IsSection family := by
  constructor
  · intro hsection edge
    have htarget := hsection edge (Set.mem_singleton (family (G.target edge)))
    change family (G.target edge) ∈
      (T.edgeRelation edge).image {family (G.source edge)} at htarget
    simpa only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left] using htarget
  · intro hfamily edge target htarget
    rw [Set.mem_singleton_iff] at htarget
    subst target
    exact ⟨family (G.source edge), Set.mem_singleton _, hfamily edge⟩

/-- Every existential-image edge map is monotone. -/
theorem monotone_powersetTransport_edgeMap :
    ∀ edge, Monotone (T.powersetTransport.edgeMap edge) :=
  fun edge ↦ (T.edgeRelation edge).image_mono

/-- Edgewise compatibility propagates through the composite relation of every walk. -/
theorem IsSection.walkRelation {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsSection family) {start finish : V} (walk : G.Walk start finish) :
    family start ~[T.walkRelation walk] family finish := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      refine ⟨family _, ih, ?_⟩
      simpa only [Set.mem_ofPred_eq, fiberCast_family] using hfamily edge

end RelationTransport

end Maths
