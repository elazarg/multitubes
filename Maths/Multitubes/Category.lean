/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Maths.Graph.FlatPathFunctor
public import Maths.Multitubes.Relational
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Transport as a representation of the path category

The typed walks of an edge graph form its path category `Maths.PathCategory`, the free
category on the graph.  A transport is a functor from the path category to types, and a monoid
labelling is a functor to the one-object category of the monoid, and a relation-labelled
transport is a functor to the category of types and relations.  By the universal property of
the path category each is the unique extension of its values on edges
(`Maths.Transport.toPathFunctor_eq_lift` and `Maths.labelFunctor_eq_lift`), and conversely every
type-valued functor on the path category is the walk transport of its edge maps.

The inductive walk and transport definitions remain the computational interface for walk
recursion, endpoint typing, and ordered lax-section arguments; this file identifies them with
the categorical ones.

## Main definitions

* `Maths.Transport.toPathFunctor` and
  `Maths.pathFunctorToTransport`: the translation between transport
  and type-valued functors on the path category.
* `Maths.Transport.IsLaxPathSection`: ordered naturality along every walk.
* `Maths.labelFunctor`: a monoid edge labelling as a functor to the associated
  one-object category.
* `Maths.unitOfLabelIso`: an isomorphism of the label functor read as a unit of the monoid.
* `Maths.RelationTransport.toPathFunctor`: a relation-labelled transport as a functor to the
  category of types and relations.

## Main results

* `Maths.Transport.toPathFunctor_eq_lift`, `Maths.labelFunctor_eq_lift`, and
  `Maths.RelationTransport.toPathFunctor_eq_lift`: walk transport, walk labels, and walk
  relations are the extensions of edge data along the universal property.
* `Maths.RelationTransport.ofTransport_toPathFunctor`: function-graph transport is ordinary
  transport followed by the embedding of functions into relations.
* `Maths.Transport.toPathFunctor_toTransport` and
  `Maths.pathFunctorToTransport_toPathFunctor`: the two interfaces carry the
  same data.
* `Maths.Transport.isSection_iff_pathFunctor_section`: exact sections are
  exactly sections of the associated functor.
* `Maths.Transport.isLaxSection_iff_isLaxPathSection`: edgewise and pathwise
  lax sections agree for monotone transport.
* `Maths.hasTrivialCycleLabels_iff_labelFunctor_end_eq_id`: flat labels are
  exactly those whose label functor kills every endomorphism.
* `Maths.Transport.isFlatAt_toPathFunctor_iff` and `Maths.isFlatAt_labelFunctor_iff`: one-base
  flatness of a transport or of a labelling is flatness of its path functor, in the sense of
  `Maths.IsFlatAt`.
-/

@[expose] public section

noncomputable section

namespace Maths

open CategoryTheory

universe uV uE uF uM

variable {V : Type uV} {E : Type uE}

variable {G : EdgeGraph V E} {Fiber : V → Type uF}

/-- A transport viewed as a representation of the path category in
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

/-- **Walk transport is the extension of the edge maps.**  The path functor of a transport is
the unique functor out of the path category taking each edge to its edge map. -/
theorem Transport.toPathFunctor_eq_lift (T : Transport G Fiber) :
    T.toPathFunctor = PathCategory.lift Fiber fun edge => ↾(T.edgeMap edge) :=
  PathCategory.eq_lift_of_map_edge _ fun _ => rfl

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
  | concat edge walk ih =>
      change F.map (PathCategory.edge (G := G) edge)
          ((pathFunctorToTransport F).walkMap walk point) =
        F.map (walk.concat edge) point
      rw [ih]
      exact (F.map_comp_apply walk
        (PathCategory.edge (G := G) edge) point).symm

/-- Restricting the path functor of a transport back to edges recovers the
original transport definitionally. -/
@[simp] theorem Transport.toPathFunctor_toTransport (T : Transport G Fiber) :
    pathFunctorToTransport T.toPathFunctor = T := rfl

/-- Extending reconstructed edge transport along walks recovers the original
path functor: both are the extension of the same edge data.  Thus the two interfaces carry the
same data. -/
@[simp] theorem pathFunctorToTransport_toPathFunctor
    (F : PathCategory G ⥤ Type uF) :
    (pathFunctorToTransport F).toPathFunctor = F :=
  (pathFunctorToTransport F).toPathFunctor_eq_lift.trans (PathCategory.eq_lift F).symm

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
    (T : Transport G Fiber) (hmono : T.IsMonotone)
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

/-- An isomorphism between two objects of a label functor is a unit of the monoid: both objects
are the single object, whose automorphisms are the units. -/
def unitOfLabelIso [Monoid M] {label : E → M} {first second : PathCategory G}
    (iso : (labelFunctor (G := G) label).obj first ≅ (labelFunctor label).obj second) : Mˣ where
  val := iso.hom
  inv := iso.inv
  val_inv := iso.inv_hom_id
  inv_val := iso.hom_inv_id

@[simp] theorem val_unitOfLabelIso [Monoid M] {label : E → M} {first second : PathCategory G}
    (iso : (labelFunctor (G := G) label).obj first ≅ (labelFunctor label).obj second) :
    (unitOfLabelIso iso : M) = iso.hom :=
  rfl

/-- **Walk labels are the extension of the edge labels.**  The label functor is the unique
functor into the one-object category of the monoid taking each edge to its label. -/
theorem labelFunctor_eq_lift [Monoid M] (label : E → M) :
    labelFunctor (G := G) label =
      PathCategory.lift (fun _ => SingleObj.star M)
        fun edge => (label edge : SingleObj.star M ⟶ SingleObj.star M) :=
  PathCategory.eq_lift_of_map_edge _ fun _ => walkLabel_singleton _

/-- Trivial cycle labels say exactly that the label functor sends every
endomorphism to the identity of the one-object category. -/
theorem hasTrivialCycleLabels_iff_labelFunctor_end_eq_id [Monoid M]
    (label : E → M) :
    HasTrivialCycleLabels G label ↔
      ∀ (object : PathCategory G) (cycle : object ⟶ object),
        (labelFunctor (G := G) label).map cycle = 𝟙 (SingleObj.star M) := by
  rfl

/-! ### Flatness -/

/-- One-base flatness of a transport is flatness of its path functor. -/
theorem Transport.isFlatAt_toPathFunctor_iff {Fiber : V → Type uF} (T : Transport G Fiber)
    {base : V} :
    IsFlatAt T.toPathFunctor base ↔ T.HasTrivialHolonomyAt base :=
  forall_congr' fun _ => ⟨fun h => funext (ConcreteCategory.congr_hom h),
    fun h => ConcreteCategory.hom_ext _ _ (congrFun h)⟩

/-- One-base flatness of a monoid labelling is flatness of its label functor. -/
theorem isFlatAt_labelFunctor_iff {M : Type uM} [Monoid M] (label : E → M) {base : V} :
    IsFlatAt (labelFunctor (G := G) label) base ↔ HasTrivialCycleLabelsAt G label base :=
  Iff.rfl

/-! ### Relation-labelled transport -/

namespace RelationTransport

variable (R : RelationTransport G Fiber)

/-- A relation-labelled transport viewed as a functor from the path category to the category
of types and relations. -/
def toPathFunctor : PathCategory G ⥤ RelCat.{uF} where
  obj object := Fiber object.vertex
  map walk := .ofRel (R.walkRelation walk)
  map_id _ := rfl
  map_comp front back := RelCat.Hom.ext _ _ (R.walkRelation_append front back)

/-- **Walk relations are the extension of the edge relations.** -/
theorem toPathFunctor_eq_lift :
    R.toPathFunctor = PathCategory.lift (C := RelCat.{uF}) Fiber
      fun edge => RelCat.Hom.ofRel (R.edgeRelation edge) :=
  PathCategory.eq_lift_of_map_edge _ fun edge => RelCat.Hom.ext _ _ <| by
    ext ⟨source, target⟩
    simp [toPathFunctor, PathCategory.edge, EdgeGraph.Walk.singleton, walkRelation]

/-- **Function-graph transport is ordinary transport followed by the graph embedding.**  The
relational path functor of the function graphs of a transport is its type-valued path functor
composed with the embedding of functions into relations. -/
theorem ofTransport_toPathFunctor (T : Transport G Fiber) :
    (ofTransport T).toPathFunctor = T.toPathFunctor ⋙ RelCat.graphFunctor := by
  rw [toPathFunctor_eq_lift]
  exact (PathCategory.eq_lift_of_map_edge (T.toPathFunctor ⋙ RelCat.graphFunctor)
    fun _ => rfl).symm

end RelationTransport

end Maths

end
