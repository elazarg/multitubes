/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.PathCategory
public import Mathlib.CategoryTheory.Retract

/-!
# Flat functors on the path category

A functor out of the path category of a directed multigraph is flat at a vertex when it sends
every closed walk there to the identity.  Flatness at both endpoints makes parallel walks with a
return walk agree, and makes each such walk an isomorphism inverted by its return.

Flatness at one base object alone makes the base a retract of every vertex object along chosen
walks to and from the base.  Compressing any path by its endpoint idempotents gives the same
morphism, and the compressed morphisms are mutually inverse relative to those idempotents.  This
is the concrete retract-groupoid statement usually described through the Karoubi envelope.

## Main definitions

* `Maths.IsFlatAt`: a path functor sends every endomorphism at one object to the identity.
* `Maths.isoOfIsFlatAt`: the isomorphism carried by a walk with a return between flat objects.
* `Maths.categoricalIngress` and `Maths.categoricalReturn`: the morphisms to and from the base
  object determined by chosen path families.
* `Maths.categoricalRetract`: the base object as a retract of each vertex object.
* `Maths.categoricalRetractProjector`: the resulting idempotent at each vertex object.

## Main results

* `Maths.map_eq_of_isFlatAt_of_return`: a path functor flat at both endpoints of two parallel
  walks with a return walk sends them to the same morphism.
* `Maths.categoricalIngress_comp_return`: ingress followed by return is the identity, so the
  projectors split.
* `Maths.categoricalRetractProjector_idempotent`: the projectors are idempotent.
* `Maths.categorical_compressed_map_eq`: compressing a path by its endpoint projectors gives a
  path-independent core morphism.
* `Maths.categorical_coreMap_comp_reverse` and `Maths.categorical_reverse_comp_coreMap`: the
  core morphisms are mutually inverse relative to the projectors.

## Tags

path category, flat functor, holonomy, retract, idempotent, Karoubi envelope
-/

@[expose] public section

namespace Maths

open CategoryTheory

universe uV uE uC

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {C : Type uC} [Category C]

section

variable (F : PathCategory G ⥤ C) {base : V}

/-- Every endomorphism at one path-category object is sent to the identity. -/
def IsFlatAt (F : PathCategory G ⥤ C) (base : V) : Prop :=
  ∀ cycle : PathCategory.ofVertex G base ⟶ PathCategory.ofVertex G base,
    F.map cycle = 𝟙 _

private theorem map_append {start middle finish : V}
    (front : G.Walk start middle) (back : G.Walk middle finish) :
    F.map (front.append back) = F.map front ≫ F.map back :=
  F.map_comp front back

/-- **Flat path functors invert walks with a return.**  A walk between objects at which the functor
is flat, together with any return walk, is sent to an isomorphism whose inverse is the image of
the return walk.  In types this is an equivalence of fibers and in the one-object category of a
monoid it is a unit. -/
@[simps]
def isoOfIsFlatAt {start finish : V} (hstart : IsFlatAt F start) (hfinish : IsFlatAt F finish)
    (walk : G.Walk start finish) (back : G.Walk finish start) :
    F.obj (PathCategory.ofVertex G start) ≅ F.obj (PathCategory.ofVertex G finish) where
  hom := F.map walk
  inv := F.map back
  hom_inv_id := by
    rw [← map_append]
    exact hstart _
  inv_hom_id := by
    rw [← map_append]
    exact hfinish _

/-- **Path independence of flat path functors.**  A path functor flat at both endpoints of two
parallel walks sends them to the same morphism, as soon as a return walk exists: both are
inverse to the image of the return walk. -/
theorem map_eq_of_isFlatAt_of_return {start finish : V} (hstart : IsFlatAt F start)
    (hfinish : IsFlatAt F finish) (first second : G.Walk start finish)
    (back : G.Walk finish start) : F.map first = F.map second :=
  (Iso.inv_eq_inv (isoOfIsFlatAt F hstart hfinish first back)
    (isoOfIsFlatAt F hstart hfinish second back)).1 rfl

/-- The chosen morphism from the base object to one vertex object. -/
def categoricalIngress (paths : ∀ vertex, G.Walk base vertex)
    (vertex : V) :
    F.obj (PathCategory.ofVertex G base) ⟶
      F.obj (PathCategory.ofVertex G vertex) :=
  F.map (paths vertex)

/-- The chosen morphism from one vertex object back to the base object. -/
def categoricalReturn (returns : ∀ vertex, G.Walk vertex base)
    (vertex : V) :
    F.obj (PathCategory.ofVertex G vertex) ⟶
      F.obj (PathCategory.ofVertex G base) :=
  F.map (returns vertex)

/-- The split idempotent on a vertex object determined by chosen ingress and
return paths. -/
def categoricalRetractProjector
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) :
    F.obj (PathCategory.ofVertex G vertex) ⟶
      F.obj (PathCategory.ofVertex G vertex) :=
  categoricalReturn F returns vertex ≫ categoricalIngress F paths vertex

theorem categoricalIngress_comp_return
    (hflat : IsFlatAt F base)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) :
    categoricalIngress F paths vertex ≫
        categoricalReturn F returns vertex = 𝟙 _ := by
  rw [categoricalIngress, categoricalReturn, ← map_append]
  exact hflat ((paths vertex).append (returns vertex))

/-- The base object as a retract of a vertex object, along the chosen ingress and return
morphisms.  Its idempotent `r ≫ i` is `Maths.categoricalRetractProjector`. -/
def categoricalRetract (hflat : IsFlatAt F base) (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) :
    Retract (F.obj (PathCategory.ofVertex G base)) (F.obj (PathCategory.ofVertex G vertex)) where
  i := categoricalIngress F paths vertex
  r := categoricalReturn F returns vertex
  retract := categoricalIngress_comp_return F hflat paths returns vertex

theorem categoricalRetractProjector_idempotent
    (hflat : IsFlatAt F base)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) :
    categoricalRetractProjector F paths returns vertex ≫
        categoricalRetractProjector F paths returns vertex =
      categoricalRetractProjector F paths returns vertex := by
  simp only [categoricalRetractProjector]
  slice_lhs 2 3 =>
    rw [categoricalIngress_comp_return F hflat paths returns vertex]
  simp

/-- **Categorical retract-flatness.**  Compressing a path by its endpoint
projectors gives the path-independent core morphism from return at the source
to ingress at the target. -/
theorem categorical_compressed_map_eq
    (hflat : IsFlatAt F base)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    {source target : V} (walk : G.Walk source target) :
    categoricalRetractProjector F paths returns source ≫ F.map walk ≫
        categoricalRetractProjector F paths returns target =
      categoricalReturn F returns source ≫
        categoricalIngress F paths target := by
  have hmiddle :
      categoricalIngress F paths source ≫ F.map walk ≫
          categoricalReturn F returns target = 𝟙 _ := by
    unfold categoricalIngress categoricalReturn
    rw [← map_append, ← map_append]
    exact hflat _
  simp only [categoricalRetractProjector]
  slice_lhs 2 4 => rw [hmiddle]
  simp

/-- The two path-independent core morphisms compose to the source
projector. -/
theorem categorical_coreMap_comp_reverse
    (hflat : IsFlatAt F base)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (source target : V) :
    (categoricalReturn F returns source ≫
        categoricalIngress F paths target) ≫
      (categoricalReturn F returns target ≫
        categoricalIngress F paths source) =
      categoricalRetractProjector F paths returns source := by
  simp only [categoricalRetractProjector]
  slice_lhs 2 3 =>
    rw [categoricalIngress_comp_return F hflat paths returns target]
  simp

/-- The reverse core morphism composed with the forward one gives the target
projector. -/
theorem categorical_reverse_comp_coreMap
    (hflat : IsFlatAt F base)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (source target : V) :
    (categoricalReturn F returns target ≫
        categoricalIngress F paths source) ≫
      (categoricalReturn F returns source ≫
        categoricalIngress F paths target) =
      categoricalRetractProjector F paths returns target :=
  categorical_coreMap_comp_reverse F hflat paths returns target source

end

end Maths
