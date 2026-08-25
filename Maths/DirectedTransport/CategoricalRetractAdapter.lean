/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.CategoricalRetracts
public import Maths.DirectedTransport.Exact
public import Mathlib.CategoryTheory.Retract

/-!
# Categorical retract adapter for directed transport

One-base-flat path functors supply explicit ingress and return morphisms.  They
form Mathlib categorical retracts, connecting retract-flat transport to generic
results about split monomorphisms, split epimorphisms, and retracts.

This file also states the bridge between the concrete and the categorical
retract theories: one-base flatness of a transport (`Maths.DirectedTransport.Exact`)
coincides with flatness of its path functor, and across that dictionary the
concrete compression theorem is definitionally an instance of the categorical
one, so the path-functor translation of `Maths.DirectedTransport.Category` carries an
actual theorem rather than only data.

## Main definitions

* `Maths.categoricalRetract`: the `CategoryTheory.Retract` exhibiting
  the base object as a retract of each vertex object, built from the chosen ingress and return
  morphisms.

## Main results

* `Maths.categoricalRetract_i`, `Maths.categoricalRetract_r`, and
  `Maths.categoricalRetract_r_comp_i`: the retract's data unfolds to the
  ingress and return morphisms.
* `Maths.categorical_compressed_map_eq_retract_r_comp_i`: the compressed core
  morphism is the retract's return followed by the retract's ingress.
* `Maths.Transport.isFlatAt_toPathFunctor_iff`: one-base flatness of a
  transport is flatness of its path functor.
* `Maths.Transport.compressed_walkMap_eq_via_category`: the concrete retract
  normal form of `Maths.DirectedTransport.Exact`, rederived through the path-functor dictionary.
-/

@[expose] public section

noncomputable section

namespace Maths

open CategoryTheory

universe uV uE uF uC vC

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {C : Type uC} [Category.{vC} C]

section

variable (F : PathCategory G ⥤ C) {base : V}
variable (paths : ∀ vertex, G.Walk base vertex)
variable (returns : ∀ vertex, G.Walk vertex base)

/-- The base object as an actual categorical retract of a vertex object. -/
def categoricalRetract (hflat : IsFlatAt F base) (vertex : V) :
    Retract (F.obj (PathCategory.ofVertex G base))
      (F.obj (PathCategory.ofVertex G vertex)) where
  i := categoricalIngress F paths vertex
  r := categoricalReturn F returns vertex
  retract := categoricalIngress_comp_return F hflat paths returns vertex

@[simp] theorem categoricalRetract_i
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).i =
      categoricalIngress F paths vertex := rfl

@[simp] theorem categoricalRetract_r
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).r =
      categoricalReturn F returns vertex := rfl

/-- The idempotent induced by the packaged retract is exactly the transport
projector used by categorical retract-flatness. -/
@[simp] theorem categoricalRetract_r_comp_i
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).r ≫
        (categoricalRetract F paths returns hflat vertex).i =
      categoricalRetractProjector F paths returns vertex := rfl

/-- The path-independent core map is the canonical return-ingress morphism
between the packaged endpoint retracts. -/
theorem categorical_compressed_map_eq_retract_r_comp_i
    (hflat : IsFlatAt F base) {source target : V}
    (walk : G.Walk source target) :
    categoricalRetractProjector F paths returns source ≫ F.map walk ≫
        categoricalRetractProjector F paths returns target =
      (categoricalRetract F paths returns hflat source).r ≫
        (categoricalRetract F paths returns hflat target).i :=
  categorical_compressed_map_eq F hflat paths returns walk

end

/-! ### The bridge to the concrete retract development

`Maths.DirectedTransport.Exact` proves the retract normal form concretely, by walk
induction, and `Maths.DirectedTransport.CategoricalRetracts` proves it categorically.
The two developments meet along `Maths.Transport.toPathFunctor`:
one-base flatness of a transport is flatness of its path functor, and under
that dictionary the concrete compression theorem is definitionally an instance
of the categorical one.  The lemmas below prove the bridge, so the dictionary
is itself a theorem. -/

section ConcreteBridge

variable {Fiber : V → Type uF} (T : Transport G Fiber) {base : V}

/-- One-base flatness of a transport is flatness of its path functor:
`Maths.IsFlatAt` transfers across the path-functor dictionary. -/
theorem Transport.isFlatAt_toPathFunctor_iff :
    IsFlatAt T.toPathFunctor base ↔
      ∀ cycle : G.Walk base base, T.holonomy cycle = id := by
  constructor
  · intro hflat cycle
    funext point
    have h := ConcreteCategory.congr_hom (hflat cycle) point
    exact h
  · intro hbaseFlat cycle
    ext point
    have h := congrFun (hbaseFlat cycle) point
    exact h

/-- `Maths.Transport.compressed_walkMap_eq`, rederived from the
categorical retract theorem through the path-functor dictionary.  The proof
transfers by definitional equality: the concrete compression theorem is
literally the categorical one instantiated at `T.toPathFunctor`. -/
theorem Transport.compressed_walkMap_eq_via_category
    (ingress : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    {start finish : V} (walk : G.Walk start finish) :
    T.retractProjector ingress returns finish ∘ T.walkMap walk ∘
        T.retractProjector ingress returns start =
      T.ingressMap ingress finish ∘ T.returnMap returns start := by
  have hflat : IsFlatAt T.toPathFunctor base :=
    T.isFlatAt_toPathFunctor_iff.mpr hbaseFlat
  have h := categorical_compressed_map_eq T.toPathFunctor hflat ingress returns walk
  funext point
  have hpoint := ConcreteCategory.congr_hom h point
  exact hpoint

end ConcreteBridge

end Maths

end
