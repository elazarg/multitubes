/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Closure
public import Mathlib.Data.Rel
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Relation-labelled transport for co-design feasibility

A relation-labelled graph gives native existential path semantics: two interface values are
related along a walk when intermediate values can be chosen at every component boundary.
Existential image turns each edge relation into an ordinary map between powersets. The native
walk relation and the resulting transport agree exactly.

A feasible assignment chooses one interface value at each vertex and satisfies every edge
relation. Such assignments correspond to singleton-valued oplax sections of the powerset
transport. This exposes the existing walk and closure theorems without making
relations primitive in the general library.

## Main definitions

* `MonotoneCoDesign.RelationTransport` - a relation between the endpoint fibers of every edge.
* `MonotoneCoDesign.RelationTransport.walkRelation` - relational composition along a typed walk.
* `MonotoneCoDesign.RelationTransport.powersetTransport` - transport by existential image.
* `MonotoneCoDesign.RelationTransport.IsFeasibleAssignment` - an edgewise feasible family.
* `MonotoneCoDesign.RelationTransport.ofTransport` - a map-labelled transport as function graphs.

## Main results

* `MonotoneCoDesign.RelationTransport.walkMap_eq_image_walkRelation` - powerset transport along a
  walk is the image under its native composite relation.
* `MonotoneCoDesign.RelationTransport.walkRelation_append` - native walk relations compose.
* `MonotoneCoDesign.RelationTransport.walkRelation_ofTransport` - relation transport recovers the
  graph of ordinary walk transport on function-labelled edges.
* `MonotoneCoDesign.RelationTransport.isOplaxSection_singleton_iff` - feasible assignments are
  singleton-valued oplax sections.
* `MonotoneCoDesign.RelationTransport.IsFeasibleAssignment.walkRelation` - edgewise feasibility
  propagates along walks.
* `MonotoneCoDesign.RelationTransport.mem_pathClosure_iff` - path closure contains exactly the
  values attainable from the lower family.
* `MonotoneCoDesign.RelationTransport.pathClosure_isLeast` - path closure is the least attainable
  family containing prescribed interface values.

## Tags

co-design, feasibility relation, relation-labelled graph, relational composition, powerset
-/

@[expose] public section

noncomputable section

namespace MonotoneCoDesign

open Maths
open scoped SetRel

universe uV uE uF

variable {V : Type uV} {E : Type uE}
variable {G : EdgeGraph V E} {Fiber : V → Type uF}

/-- Relations between the endpoint fibers of the edges of a directed graph. -/
structure RelationTransport (G : EdgeGraph V E) (Fiber : V → Type uF) where
  /-- The feasibility relation carried by an edge. -/
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

/-- An assignment is feasible when every adjacent pair satisfies its component relation. -/
def IsFeasibleAssignment (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge, family (G.source edge) ~[T.edgeRelation edge] family (G.target edge)

/-- Native feasible assignments are exactly singleton-valued oplax sections after the powerset
embedding. -/
theorem isOplaxSection_singleton_iff (family : ∀ vertex, Fiber vertex) :
    T.powersetTransport.IsOplaxSection (fun vertex ↦ {family vertex}) ↔
      T.IsFeasibleAssignment family := by
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

/-- Edgewise feasibility propagates through the native composite relation of every walk. -/
theorem IsFeasibleAssignment.walkRelation {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsFeasibleAssignment family) {start finish : V}
    (walk : G.Walk start finish) :
    family start ~[T.walkRelation walk] family finish := by
  have hsection := (T.isOplaxSection_singleton_iff family).2 hfamily
  have hwalk := hsection.le_walkMap T.monotone_powersetTransport_edgeMap walk
  have htarget := hwalk (Set.mem_singleton (family finish))
  rw [T.walkMap_eq_image_walkRelation] at htarget
  change (family start, family finish) ∈ T.walkRelation walk
  simpa only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left] using htarget

/-- The existential-image edge maps preserve arbitrary suprema. -/
def edgeImageSupHom (edge : E) :
    sSupHom (Set (Fiber (G.source edge))) (Set (Fiber (G.target edge))) where
  toFun := (T.edgeRelation edge).image
  map_sSup' := by
    intro sets
    change (T.edgeRelation edge).image (⋃₀ sets) =
      ⋃₀ ((T.edgeRelation edge).image '' sets)
    rw [SetRel.image_sUnion]
    simp only [Set.sUnion_image]

/-- Path closure contains exactly the values related to lower data along some typed walk. -/
theorem mem_pathClosure_iff (lower : ∀ vertex, Set (Fiber vertex))
    {finish : V} (target : Fiber finish) :
    target ∈ T.powersetTransport.pathClosure lower finish ↔
      ∃ (start : V) (walk : G.Walk start finish) (source : Fiber start),
        source ∈ lower start ∧ source ~[T.walkRelation walk] target := by
  change
    (target ∈ ⋃ (start : V) (walk : G.Walk start finish),
      T.powersetTransport.walkMap walk (lower start)) ↔ _
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨start, walk, htarget⟩
    rw [T.walkMap_eq_image_walkRelation] at htarget
    obtain ⟨source, hsource, hrelation⟩ := htarget
    exact ⟨start, walk, source, hsource, hrelation⟩
  · rintro ⟨start, walk, source, hsource, hrelation⟩
    refine ⟨start, walk, ?_⟩
    rw [T.walkMap_eq_image_walkRelation]
    exact ⟨source, hsource, hrelation⟩

/-- Path closure is the least attainable family containing prescribed interface values. -/
theorem pathClosure_isLeast (lower : ∀ vertex, Set (Fiber vertex)) :
    T.powersetTransport.IsLaxSection (T.powersetTransport.pathClosure lower) ∧
      (∀ vertex, lower vertex ⊆ T.powersetTransport.pathClosure lower vertex) ∧
      ∀ family : ∀ vertex, Set (Fiber vertex),
        T.powersetTransport.IsLaxSection family →
        (∀ vertex, lower vertex ⊆ family vertex) →
        ∀ vertex, T.powersetTransport.pathClosure lower vertex ⊆ family vertex := by
  apply T.powersetTransport.pathClosure_isLeast_of_sSupHom
    (fun edge ↦ T.edgeImageSupHom edge)
  intro edge point
  rfl

end RelationTransport

end MonotoneCoDesign

end
