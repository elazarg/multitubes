/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.CategoryTheory.EqToHom

/-!
# The path category of a directed multigraph

The typed walks of a directed multigraph form a category: vertices are objects, walks are
morphisms, and walk concatenation is composition.  It is the free category on the graph.  An
assignment of an object of a category `C` to every vertex and of a morphism to every edge
extends uniquely to a functor out of the path category (`Maths.PathCategory.lift`), and every
functor out of the path category is the extension of its values on edges
(`Maths.PathCategory.eq_lift`).

Every composite of edge data along walks is such an extension: transport along walks is the
extension into types, the label of a walk is the extension into a one-object category, and the
composite relation of a walk is the extension into relations.

## Main definitions

* `Maths.PathCategory`: the objects of the path category, with
  `Maths.PathCategory.ofVertex` and `Maths.PathCategory.vertex` translating between vertices
  and objects.
* `Maths.PathCategory.instCategory`: walks as morphisms, with concatenation as composition, and
  `Maths.PathCategory.edge` for the generating morphisms.
* `Maths.PathCategory.lift`: the functor extending an assignment of objects to vertices and
  morphisms to edges.

## Main results

* `Maths.PathCategory.lift_map_edge`: the extension takes the prescribed value on edges.
* `Maths.PathCategory.eq_lift` and `Maths.PathCategory.eq_lift_of_map_edge`: every functor out
  of the path category is the extension of its values on edges.

## Tags

path category, free category, quiver, walk, universal property
-/

@[expose] public section

namespace Maths

open CategoryTheory

universe uV uE v u

variable {V : Type uV} {E : Type uE}

/-- Objects of the path category of `G`.  The graph parameter keeps category instances for
different edge graphs on the same vertex type distinct. -/
def PathCategory (_G : EdgeGraph V E) := V

namespace PathCategory

variable {G : EdgeGraph V E}

/-- Regard a vertex as an object of the path category. -/
@[reducible] def ofVertex (G : EdgeGraph V E) (vertex : V) : PathCategory G := vertex

/-- The vertex underlying a path-category object. -/
@[reducible] def vertex (object : PathCategory G) : V := object

/-- The category of typed walks in the directed multigraph `G`. -/
instance instCategory : Category (PathCategory G) where
  Hom start finish := G.Walk start.vertex finish.vertex
  id _ := .nil
  comp front back := front.append back
  comp_id front := EdgeGraph.Walk.append_nil front
  id_comp back := EdgeGraph.Walk.nil_append back
  assoc front middle back := EdgeGraph.Walk.append_assoc front middle back

@[simp] theorem id_eq_nil (object : PathCategory G) :
    (𝟙 object : G.Walk object.vertex object.vertex) = .nil := rfl

@[simp] theorem comp_eq_append {first second third : PathCategory G}
    (front : first ⟶ second) (back : second ⟶ third) :
    front ≫ back = front.append back := rfl

/-- The generating morphism represented by one edge. -/
def edge (candidate : E) :
    ofVertex G (G.source candidate) ⟶ ofVertex G (G.target candidate) :=
  EdgeGraph.Walk.singleton candidate

/-- Extending a walk by an edge is composing with that edge. -/
theorem concat_eq_comp_edge {start : V} {candidate : E} (walk : G.Walk start (G.source candidate)) :
    (walk.concat candidate : (ofVertex G start ⟶ ofVertex G (G.target candidate))) =
      (walk : ofVertex G start ⟶ ofVertex G (G.source candidate)) ≫ edge candidate :=
  rfl

/-! ### The universal property -/

variable {C : Type u} [Category.{v} C]

/-- The composite in `C` of the morphisms assigned to the edges of a walk. -/
def liftMap (obj : V → C) (map : ∀ edge : E, obj (G.source edge) ⟶ obj (G.target edge))
    {start : V} : {finish : V} → G.Walk start finish → (obj start ⟶ obj finish)
  | _, .nil => 𝟙 _
  | _, .concat edge walk => liftMap obj map walk ≫ map edge

variable (obj : V → C) (map : ∀ edge : E, obj (G.source edge) ⟶ obj (G.target edge))

@[simp] theorem liftMap_nil (start : V) : liftMap obj map (.nil : G.Walk start start) = 𝟙 _ :=
  rfl

@[simp] theorem liftMap_concat {start : V} (candidate : E)
    (walk : G.Walk start (G.source candidate)) :
    liftMap obj map (walk.concat candidate) = liftMap obj map walk ≫ map candidate :=
  rfl

theorem liftMap_append {start middle finish : V} (front : G.Walk start middle)
    (back : G.Walk middle finish) :
    liftMap obj map (front.append back) = liftMap obj map front ≫ liftMap obj map back := by
  induction back with
  | nil => exact (Category.comp_id _).symm
  | concat edge back ih =>
      rw [EdgeGraph.Walk.append_concat, liftMap_concat, liftMap_concat, ih, Category.assoc]

/-- The functor out of the path category extending an assignment of objects to vertices and
morphisms to edges. -/
def lift : PathCategory G ⥤ C where
  obj object := obj object.vertex
  map walk := liftMap obj map walk
  map_id _ := rfl
  map_comp front back := liftMap_append obj map front back

@[simp] theorem lift_obj (vertex : V) : (lift obj map).obj (ofVertex G vertex) = obj vertex :=
  rfl

/-- The extension takes the prescribed value on every edge. -/
@[simp] theorem lift_map_edge (candidate : E) :
    (lift obj map).map (edge candidate) = map candidate :=
  Category.id_comp _

/-- A functor out of the path category maps every walk to the composite of its values on the
edges of the walk. -/
theorem map_eq_liftMap (F : PathCategory G ⥤ C) {start finish : V}
    (walk : G.Walk start finish) :
    F.map (X := ofVertex G start) (Y := ofVertex G finish) walk =
      liftMap (fun vertex => F.obj (ofVertex G vertex)) (fun candidate => F.map (edge candidate))
        walk := by
  induction walk with
  | nil => exact F.map_id _
  | concat candidate walk ih =>
      rw [concat_eq_comp_edge, F.map_comp, ih]
      rfl

/-- **Universal property.**  Every functor out of the path category is the extension of its
values on vertices and edges. -/
theorem eq_lift (F : PathCategory G ⥤ C) :
    F = lift (fun vertex => F.obj (ofVertex G vertex))
      (fun candidate => F.map (edge candidate)) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ walk => by
    change F.map walk = eqToHom rfl ≫ liftMap _ _ walk ≫ eqToHom rfl
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact map_eq_liftMap F walk

/-- **Uniqueness of the extension.**  A functor taking prescribed values on edges is the
extension of those values. -/
theorem eq_lift_of_map_edge (F : PathCategory G ⥤ C)
    {map : ∀ edge : E, F.obj (ofVertex G (G.source edge)) ⟶ F.obj (ofVertex G (G.target edge))}
    (hmap : ∀ candidate, F.map (edge candidate) = map candidate) :
    F = lift (fun vertex => F.obj (ofVertex G vertex)) map := by
  rw [← funext hmap]
  exact eq_lift F

end PathCategory

end Maths
