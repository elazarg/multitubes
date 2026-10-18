/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.Logic.Equiv.Defs

/-!
# Morphisms and isomorphisms of directed multigraphs

A morphism of edge graphs sends vertices to vertices and edges to edges, commuting with
`source` and `target`.  It carries typed walks to typed walks edge by edge, preserving length
and mapping the edge list.  An isomorphism is a pair of bijections with the same commutation
property.

## Main definitions

* `Maths.EdgeGraph.Hom`: a morphism of edge graphs.
* `Maths.EdgeGraph.Hom.id` and `Maths.EdgeGraph.Hom.comp`: identity and composition.
* `Maths.EdgeGraph.Walk.map`: the image of a typed walk under a morphism.
* `Maths.EdgeGraph.Iso`: an isomorphism of edge graphs.

## Main results

* `Maths.EdgeGraph.Walk.length_map` and `Maths.EdgeGraph.Walk.edges_map`: mapping
  preserves length and maps the edge list.
* `Maths.EdgeGraph.Walk.map_append`: mapping distributes over concatenation.
* `Maths.EdgeGraph.Walk.map_id` and `Maths.EdgeGraph.Walk.map_comp`: mapping is functorial.

## Tags

directed multigraph, quiver, graph homomorphism, prefunctor, walk
-/

@[expose] public section

namespace Maths

namespace EdgeGraph

universe uV uE uV' uE' uV'' uE''

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {V'' : Type uV''} {E'' : Type uE''}

/-- A morphism of edge graphs: maps on vertices and edges commuting with the endpoint maps. -/
@[ext] structure Hom (G : EdgeGraph V E) (H : EdgeGraph V' E') where
  /-- The vertex map. -/
  vertexMap : V → V'
  /-- The edge map. -/
  edgeMap : E → E'
  /-- The edge map preserves sources. -/
  source_edgeMap : ∀ edge, H.source (edgeMap edge) = vertexMap (G.source edge)
  /-- The edge map preserves targets. -/
  target_edgeMap : ∀ edge, H.target (edgeMap edge) = vertexMap (G.target edge)

namespace Hom

variable {G : EdgeGraph V E} {H : EdgeGraph V' E'} {K : EdgeGraph V'' E''}

/-- The identity morphism. -/
def id (G : EdgeGraph V E) : Hom G G where
  vertexMap := fun vertex => vertex
  edgeMap := fun edge => edge
  source_edgeMap _ := rfl
  target_edgeMap _ := rfl

/-- Composition of morphisms, applying `f` first. -/
def comp (g : Hom H K) (f : Hom G H) : Hom G K where
  vertexMap := g.vertexMap ∘ f.vertexMap
  edgeMap := g.edgeMap ∘ f.edgeMap
  source_edgeMap edge := by
    simp only [Function.comp_apply, g.source_edgeMap, f.source_edgeMap]
  target_edgeMap edge := by
    simp only [Function.comp_apply, g.target_edgeMap, f.target_edgeMap]

@[simp] theorem id_vertexMap (vertex : V) : (Hom.id G).vertexMap vertex = vertex := rfl

@[simp] theorem id_edgeMap (edge : E) : (Hom.id G).edgeMap edge = edge := rfl

@[simp] theorem comp_vertexMap (g : Hom H K) (f : Hom G H) (vertex : V) :
    (g.comp f).vertexMap vertex = g.vertexMap (f.vertexMap vertex) := rfl

@[simp] theorem comp_edgeMap (g : Hom H K) (f : Hom G H) (edge : E) :
    (g.comp f).edgeMap edge = g.edgeMap (f.edgeMap edge) := rfl

end Hom

namespace Walk

variable {G : EdgeGraph V E} {H : EdgeGraph V' E'} {K : EdgeGraph V'' E''}
  {start middle finish : V}

/-- The image of a typed walk under a morphism, edge by edge. -/
def map (f : Hom G H) {start : V} :
    {finish : V} → G.Walk start finish → H.Walk (f.vertexMap start) (f.vertexMap finish)
  | _, .nil => .nil
  | _, .concat walkSoFar edge legal =>
      (Walk.concat (map f walkSoFar) (f.edgeMap edge)
        ((f.source_edgeMap edge).trans (congrArg f.vertexMap legal))).castFinish
        (f.target_edgeMap edge)

@[simp] theorem map_nil (f : Hom G H) :
    (Walk.nil : G.Walk start start).map f = .nil := rfl

theorem map_concat (f : Hom G H) (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (walkSoFar.concat edge legal).map f =
      ((walkSoFar.map f).concat (f.edgeMap edge)
        ((f.source_edgeMap edge).trans (congrArg f.vertexMap legal))).castFinish
        (f.target_edgeMap edge) := rfl

/-- The image of a walk extended by an edge, up to the retyping of its endpoint. -/
theorem map_concat_heq (f : Hom G H) (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (walkSoFar.concat edge legal).map f ≍
      (walkSoFar.map f).concat (f.edgeMap edge)
        ((f.source_edgeMap edge).trans (congrArg f.vertexMap legal)) := by
  rw [map_concat]
  exact castFinish_heq _ _

/-- Mapping preserves the number of edges. -/
@[simp] theorem length_map (f : Hom G H) (walk : G.Walk start finish) :
    (walk.map f).length = walk.length := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [map_concat, ih]

/-- Mapping applies the edge map to the chronological edge list. -/
@[simp] theorem edges_map (f : Hom G H) (walk : G.Walk start finish) :
    (walk.map f).edges = walk.edges.map f.edgeMap := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [map_concat, ih]

private theorem castFinish_append {start middle finish finish' : V}
    (first : G.Walk start middle) (second : G.Walk middle finish)
    (hfinish : finish = finish') :
    first.append (second.castFinish hfinish) = (first.append second).castFinish hfinish := by
  subst hfinish
  rfl

private theorem castFinish_castFinish {start finish finish' finish'' : V}
    (walk : G.Walk start finish) (h₁ : finish = finish') (h₂ : finish' = finish'') :
    (walk.castFinish h₁).castFinish h₂ = walk.castFinish (h₁.trans h₂) := by
  subst h₁ h₂
  rfl

/-- Mapping commutes with a change of terminal index. -/
theorem map_castFinish (f : Hom G H) {finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    (walk.castFinish hfinish).map f =
      (walk.map f).castFinish (congrArg f.vertexMap hfinish) := by
  subst hfinish
  rfl

/-- Mapping distributes over concatenation. -/
theorem map_append (f : Hom G H) (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    (first.append second).map f = (first.map f).append (second.map f) := by
  induction second with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [append_concat, map_concat, map_concat, ih, castFinish_append]
      rfl

/-- Mapping along the identity morphism is the identity. -/
@[simp] theorem map_id (walk : G.Walk start finish) : walk.map (Hom.id G) = walk := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [map_concat, ih]
      rfl

/-- Mapping along a composite is the composite of the mappings. -/
theorem map_comp (g : Hom H K) (f : Hom G H) (walk : G.Walk start finish) :
    walk.map (g.comp f) = (walk.map f).map g := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [map_concat, map_concat, ih, map_castFinish, map_concat, castFinish_castFinish]
      rfl

end Walk

/-- An isomorphism of edge graphs: bijections on vertices and edges commuting with the
endpoint maps. -/
structure Iso (G : EdgeGraph V E) (H : EdgeGraph V' E') where
  /-- The bijection on vertices. -/
  vertexEquiv : V ≃ V'
  /-- The bijection on edges. -/
  edgeEquiv : E ≃ E'
  /-- The edge bijection preserves sources. -/
  source_edgeEquiv : ∀ edge, H.source (edgeEquiv edge) = vertexEquiv (G.source edge)
  /-- The edge bijection preserves targets. -/
  target_edgeEquiv : ∀ edge, H.target (edgeEquiv edge) = vertexEquiv (G.target edge)

namespace Iso

variable {G : EdgeGraph V E} {H : EdgeGraph V' E'}

/-- The forward morphism of an isomorphism. -/
def toHom (e : Iso G H) : Hom G H where
  vertexMap := e.vertexEquiv
  edgeMap := e.edgeEquiv
  source_edgeMap := e.source_edgeEquiv
  target_edgeMap := e.target_edgeEquiv

/-- The inverse isomorphism. -/
def symm (e : Iso G H) : Iso H G where
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  source_edgeEquiv edge := by
    rw [Equiv.eq_symm_apply, ← e.source_edgeEquiv, Equiv.apply_symm_apply]
  target_edgeEquiv edge := by
    rw [Equiv.eq_symm_apply, ← e.target_edgeEquiv, Equiv.apply_symm_apply]

end Iso

end EdgeGraph

end Maths
