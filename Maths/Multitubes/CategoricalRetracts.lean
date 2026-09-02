/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Category

/-!
# Categorical retract normal forms for transport

For a functor from a directed path category to an arbitrary category,
flatness at one base object produces split idempotents at every vertex.
Compressing any path by its endpoint idempotents gives the same morphism,
and the compressed morphisms are mutually inverse relative to those
idempotents.  This is the concrete retract-groupoid statement usually
described via the Karoubi envelope.

## Main definitions

* `Maths.IsFlatAt`: a path functor sends every endomorphism at one object to
  the identity.
* `Maths.categoricalIngress` and `Maths.categoricalReturn`: the
  morphisms to and from the base object determined by chosen path families.
* `Maths.categoricalRetractProjector`: the resulting endomorphism at each
  vertex object.

## Main results

* `Maths.categoricalIngress_comp_return`: ingress followed by return is the
  identity, so the projectors split.
* `Maths.categoricalRetractProjector_idempotent`: the projectors are
  idempotent.
* `Maths.categorical_compressed_map_eq`: compressing a path by its endpoint
  projectors gives a path-independent core morphism.
* `Maths.categorical_coreMap_comp_reverse` and
  `Maths.categorical_reverse_comp_coreMap`: the core morphisms are mutually
  inverse relative to the projectors.
-/

@[expose] public section

noncomputable section

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
    calc
      F.map (paths source) ≫ F.map walk ≫ F.map (returns target) =
          (F.map (paths source) ≫ F.map walk) ≫
            F.map (returns target) := by rw [Category.assoc]
      _ =
          F.map ((paths source).append walk) ≫
            F.map (returns target) := by rw [map_append]
      _ = F.map
          (((paths source).append walk).append (returns target)) :=
            (map_append F _ _).symm
      _ = 𝟙 _ := hflat _
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

end
