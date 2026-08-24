/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The path-category presentation of directed transport

The typed walks of an edge graph form a path category: vertices are objects,
walks are morphisms, and walk append is categorical composition.
Directed transport is a functor from this category to types, while a monoid
labelling is a functor to the associated one-object category.

The category interface is an adapter.  The inductive walk and transport
definitions form the computational interface for walk recursion, endpoint
typing, and ordered lax-section arguments.  No universal property of this
presentation is asserted here.

## Main definitions

* `DirectedTransport.PathCategory`: the objects of the path category of an edge graph,
  together with `DirectedTransport.PathCategory.ofVertex` and
  `DirectedTransport.PathCategory.vertex` translating between vertices and objects.
* `DirectedTransport.PathCategory.instCategory`: walks as morphisms, with append as
  composition, and `DirectedTransport.PathCategory.edge` for the generating morphisms.
* `DirectedTransport.Transport.toPathFunctor` and
  `DirectedTransport.pathFunctorToTransport`: the translation between directed transport
  and type-valued functors on the path category.
* `DirectedTransport.Transport.IsLaxPathSection`: ordered naturality along every walk.
* `DirectedTransport.labelFunctor`: a monoid edge labelling as a functor to the associated
  one-object category.

## Main results

* `DirectedTransport.Transport.toPathFunctor_toTransport` and
  `DirectedTransport.pathFunctorToTransport_toPathFunctor`: the two interfaces carry the
  same data.
* `DirectedTransport.Transport.isSection_iff_pathFunctor_section`: exact sections are
  exactly sections of the associated functor.
* `DirectedTransport.Transport.isLaxSection_iff_isLaxPathSection`: edgewise and pathwise
  lax sections agree for monotone transport.
* `DirectedTransport.hasTrivialCycleLabels_iff_labelFunctor_end_eq_id`: flat labels are
  exactly those whose label functor kills every endomorphism.
-/

@[expose] public section

noncomputable section

namespace DirectedTransport

open CategoryTheory

universe uV uE uF uM

variable {V : Type uV} {E : Type uE}

/-- Objects of the path category of `G`.  The graph parameter keeps category
instances for different edge graphs on the same vertex type distinct. -/
def PathCategory (_G : EdgeGraph V E) := V

namespace PathCategory

variable {G : EdgeGraph V E}

/-- Regard a vertex as an object of the path category. -/
@[reducible] def ofVertex (G : EdgeGraph V E) (vertex : V) : PathCategory G := vertex

/-- The vertex underlying a path-category object. -/
@[reducible] def vertex (object : PathCategory G) : V := object

/-- Appending a walk to the empty walk returns the walk. -/
theorem nil_append {start finish : V}
    (walk : G.Walk start finish) :
    (EdgeGraph.Walk.nil : G.Walk start start).append walk = walk := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, ih]

/-- Walk append is associative. -/
theorem append_assoc {first second third fourth : V}
    (front : G.Walk first second) (middle : G.Walk second third)
    (back : G.Walk third fourth) :
    (front.append middle).append back = front.append (middle.append back) := by
  induction back with
  | nil => rfl
  | concat back edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, EdgeGraph.Walk.append_concat,
        EdgeGraph.Walk.append_concat, ih]

/-- The category of typed walks in the directed multigraph `G`. -/
instance instCategory : Category (PathCategory G) where
  Hom start finish := G.Walk start.vertex finish.vertex
  id _ := .nil
  comp front back := front.append back
  comp_id front := EdgeGraph.Walk.append_nil front
  id_comp back := nil_append back
  assoc front middle back := append_assoc front middle back

@[simp] theorem id_eq_nil (object : PathCategory G) :
    (𝟙 object : G.Walk object.vertex object.vertex) = .nil := rfl

@[simp] theorem comp_eq_append {first second third : PathCategory G}
    (front : first ⟶ second) (back : second ⟶ third) :
    front ≫ back = front.append back := rfl

/-- The generating morphism represented by one edge. -/
def edge (candidate : E) :
    ofVertex G (G.source candidate) ⟶ ofVertex G (G.target candidate) :=
  EdgeGraph.Walk.singleton candidate

end PathCategory

variable {G : EdgeGraph V E} {Fiber : V → Type uF}

/-- A directed transport viewed as a representation of the path category in
types. -/
def Transport.toPathFunctor (T : Transport G Fiber) :
    PathCategory G ⥤ Type uF where
  obj object := Fiber object.vertex
  map walk := ↾(T.walkMap walk)
  map_id _ := rfl
  map_comp front back := by
    ext point
    change T.walkMap (front.append back) point =
      T.walkMap back (T.walkMap front point)
    exact T.walkMap_append front back point

@[simp] theorem Transport.toPathFunctor_map_apply (T : Transport G Fiber)
    {start finish : PathCategory G} (walk : start ⟶ finish)
    (point : Fiber start.vertex) :
    T.toPathFunctor.map walk point = T.walkMap walk point := rfl

/-- Recover edge transport from a type-valued functor on the path category by
restricting it to the generating edge morphisms. -/
def pathFunctorToTransport (F : PathCategory G ⥤ Type uF) :
    Transport G
      (fun vertex => F.obj (PathCategory.ofVertex G vertex)) where
  edgeMap edge := F.map (PathCategory.edge (G := G) edge)

/-- Transport reconstructed from a path functor agrees with the functor map
on every typed walk. -/
@[simp] theorem pathFunctorToTransport_walkMap
    (F : PathCategory G ⥤ Type uF) {start finish : V}
    (walk : G.Walk start finish)
    (point : F.obj (PathCategory.ofVertex G start)) :
    (pathFunctorToTransport F).walkMap walk point = F.map walk point := by
  induction walk with
  | nil =>
      change point = F.map (.nil : G.Walk start start) point
      have hmap := F.map_id (PathCategory.ofVertex G start)
      have hnil :
          (𝟙 (PathCategory.ofVertex G start) :
              PathCategory.ofVertex G start ⟶
                PathCategory.ofVertex G start) =
            (.nil : G.Walk start start) := rfl
      rw [hnil] at hmap
      exact (ConcreteCategory.congr_hom hmap point).symm
  | @concat finish walk edge legal ih =>
      subst legal
      change F.map (PathCategory.edge (G := G) edge)
          ((pathFunctorToTransport F).walkMap walk point) =
        F.map (walk.concat edge rfl) point
      rw [ih]
      exact (F.map_comp_apply walk
        (PathCategory.edge (G := G) edge) point).symm

/-- Restricting the path functor of a transport back to edges recovers the
original transport definitionally. -/
@[simp] theorem Transport.toPathFunctor_toTransport (T : Transport G Fiber) :
    pathFunctorToTransport T.toPathFunctor = T := rfl

/-- Extending reconstructed edge transport along walks recovers the original
path functor.  Thus the two interfaces carry the same data. -/
@[simp] theorem pathFunctorToTransport_toPathFunctor
    (F : PathCategory G ⥤ Type uF) :
    (pathFunctorToTransport F).toPathFunctor = F := by
  fapply CategoryTheory.Functor.ext
  · intro object
    rfl
  · intro start finish walk
    ext point
    exact pathFunctorToTransport_walkMap F walk point

/-- A vertex-indexed family regarded as a family over path-category objects. -/
def pathFunctorFamily (T : Transport G Fiber)
    (family : ∀ vertex, Fiber vertex) :
    ∀ object : PathCategory G, (T.toPathFunctor).obj object := by
  intro object
  change Fiber object.vertex
  exact family object.vertex

/-- Exact edge sections are exactly sections of the path-category functor,
meaning families natural with respect to every walk. -/
theorem Transport.isSection_iff_pathFunctor_section
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) :
    T.IsSection family ↔
      pathFunctorFamily T family ∈ T.toPathFunctor.sections := by
  change T.IsSection family ↔
    ∀ {start finish : PathCategory G} (walk : start ⟶ finish),
      T.walkMap walk (family start.vertex) = family finish.vertex
  constructor
  · intro hsection start finish walk
    exact hsection.walkMap_eq walk
  · intro hsection candidate
    have hwalk := hsection (PathCategory.edge (G := G) candidate)
    simpa [PathCategory.edge, PathCategory.ofVertex,
      PathCategory.vertex] using hwalk

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- Ordered naturality along every path.  This is the path-category form of a
lax section; it is deliberately separate from ordinary natural
transformations. -/
def Transport.IsLaxPathSection (T : Transport G Fiber)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ {start finish : PathCategory G} (walk : start ⟶ finish),
    T.walkMap walk (family start.vertex) ≤ family finish.vertex

/-- Under monotone edge maps, edgewise lax sections are equivalent to ordered
naturality along every morphism of the path category. -/
theorem Transport.isLaxSection_iff_isLaxPathSection
    (T : Transport G Fiber) (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (family : ∀ vertex, Fiber vertex) :
    T.IsLaxSection family ↔ T.IsLaxPathSection family := by
  constructor
  · intro hsection start finish walk
    exact hsection.walkMap_le hmono walk
  · intro hsection candidate
    have hwalk := hsection (PathCategory.edge (G := G) candidate)
    change T.edgeMap candidate (family (G.source candidate)) ≤
      family (G.target candidate) at hwalk
    simpa only using hwalk

end Ordered

variable {M : Type uM}

/-- A monoid edge labelling extended functorially to the path category. -/
def labelFunctor [Monoid M] (label : E → M) :
    PathCategory G ⥤ SingleObj M where
  obj _ := SingleObj.star M
  map walk := walkLabel label walk
  map_id _ := walkLabel_nil
  map_comp front back := by
    rw [SingleObj.comp_as_mul]
    rw [PathCategory.comp_eq_append, walkLabel_append]

@[simp] theorem labelFunctor_map [Monoid M] (label : E → M)
    {start finish : PathCategory G} (walk : start ⟶ finish) :
    (labelFunctor (G := G) label).map walk = walkLabel label walk := rfl

/-- Trivial cycle labels say exactly that the label functor sends every
endomorphism to the identity of the one-object category. -/
theorem hasTrivialCycleLabels_iff_labelFunctor_end_eq_id [Monoid M]
    (label : E → M) :
    HasTrivialCycleLabels G label ↔
      ∀ (object : PathCategory G) (cycle : object ⟶ object),
        (labelFunctor (G := G) label).map cycle = 𝟙 (SingleObj.star M) := by
  rfl

end DirectedTransport

end
