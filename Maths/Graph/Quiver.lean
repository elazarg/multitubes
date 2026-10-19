/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.Morphism
public import Maths.Graph.PathCategory
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Edge graphs as quivers

An edge graph presents a quiver: its arrows from `u` to `v` are the edges with source `u` and
target `v`.  The presentation keeps a global type of edges, which the sums over edges,
circulations, and edge multiplicities of this file's importers need, while mathlib's quivers
index arrows by their endpoints.  This file identifies the two.

Typed walks are exactly mathlib's quiver paths (`Maths.EdgeGraph.Walk.equivPath`), with
concatenation corresponding to path composition, so the path category of an edge graph is
equivalent to mathlib's path category of its quiver (`Maths.PathCategory.equivPaths`).
Morphisms of edge graphs are prefunctors, and their action on walks is `Prefunctor.mapPath`.

## Main definitions

* `Maths.EdgeGraph.Vertex`: the vertices of an edge graph, carrying its quiver.
* `Maths.EdgeGraph.Walk.toPath` and `Maths.EdgeGraph.Walk.ofPath`: walks as quiver paths and
  back, packaged as `Maths.EdgeGraph.Walk.equivPath`.
* `Maths.EdgeGraph.Hom.toPrefunctor`: an edge-graph morphism as a prefunctor.
* `Maths.PathCategory.toPaths` and `Maths.PathCategory.ofPaths`: the functors between the path
  category and mathlib's path category of the quiver, packaged as
  `Maths.PathCategory.equivPaths`.

## Main results

* `Maths.EdgeGraph.Walk.toPath_append`: concatenation is path composition.
* `Maths.EdgeGraph.Walk.length_toPath`: the correspondence preserves length.
* `Maths.EdgeGraph.Walk.toPath_map`: mapping a walk is mapping its path.
* `Maths.EdgeGraph.isStronglyConnected_iff_quiver`: strong connectivity is mathlib's
  `Quiver.IsStronglyConnected` of the quiver.
* `Maths.PathCategory.toPaths_comp_ofPaths` and `Maths.PathCategory.ofPaths_comp_toPaths`: the
  two path categories are isomorphic.

## Tags

quiver, path, prefunctor, path category, free category
-/

@[expose] public section

namespace Maths

open CategoryTheory

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}

namespace EdgeGraph

/-- The vertices of an edge graph, carrying the quiver whose arrows are its edges.  The wrapper
keeps the quivers of different edge graphs on one vertex type distinct. -/
@[ext] structure Vertex (G : EdgeGraph V E) where
  /-- The underlying vertex. -/
  vertex : V

/-- The quiver presented by an edge graph: an arrow is an edge with prescribed endpoints. -/
instance (G : EdgeGraph V E) : Quiver G.Vertex where
  Hom source target := {edge : E // G.source edge = source.vertex ∧ G.target edge = target.vertex}

variable {G : EdgeGraph V E} {H : EdgeGraph V' E'}

/-- An edge as an arrow between its own endpoints. -/
def arrow (edge : E) : (⟨G.source edge⟩ : G.Vertex) ⟶ ⟨G.target edge⟩ :=
  ⟨edge, rfl, rfl⟩

namespace Walk

variable {start middle finish : V}

/-- A typed walk as a quiver path. -/
def toPath {start : V} :
    {finish : V} → G.Walk start finish → Quiver.Path (⟨start⟩ : G.Vertex) ⟨finish⟩
  | _, .nil => .nil
  | _, .concat edge walk => walk.toPath.cons (arrow edge)

/-- A quiver path as a typed walk. -/
def ofPath {start : G.Vertex} :
    {finish : G.Vertex} → Quiver.Path start finish → G.Walk start.vertex finish.vertex
  | _, .nil => .nil
  | _, .cons path arrow =>
      (((ofPath path).castFinish arrow.2.1.symm).concat arrow.1).castFinish arrow.2.2

@[simp] theorem toPath_nil : (Walk.nil : G.Walk start start).toPath = .nil := rfl

@[simp] theorem toPath_concat (edge : E) (walk : G.Walk start (G.source edge)) :
    (walk.concat edge).toPath = walk.toPath.cons (arrow edge) := rfl

@[simp] theorem ofPath_nil {vertex : G.Vertex} :
    ofPath (.nil : Quiver.Path vertex vertex) = .nil := rfl

/-- The edges of a path read as a walk. -/
@[simp] theorem edges_ofPath_cons {source middle target : G.Vertex}
    (path : Quiver.Path source middle) (arrow : middle ⟶ target) :
    (ofPath (path.cons arrow)).edges = (ofPath path).edges ++ [arrow.1] := by
  rw [ofPath, edges_castFinish, edges_concat, edges_castFinish]

@[simp] theorem ofPath_toPath (walk : G.Walk start finish) : ofPath walk.toPath = walk := by
  induction walk with
  | nil => rfl
  | concat edge walk ih =>
      exact Walk.ext ((edges_ofPath_cons walk.toPath (arrow edge)).trans (by rw [ih]; rfl))

@[simp] theorem toPath_ofPath {source target : G.Vertex} (path : Quiver.Path source target) :
    (ofPath path).toPath = path := by
  induction path with
  | nil => rfl
  | @cons middle last path arrow ih =>
      obtain ⟨middle⟩ := middle
      obtain ⟨last⟩ := last
      obtain ⟨edge, hsource, htarget⟩ := arrow
      cases hsource
      cases htarget
      exact congrArg (Quiver.Path.cons · (arrow edge)) ih

/-- **Walks are quiver paths.** -/
def equivPath : G.Walk start finish ≃ Quiver.Path (⟨start⟩ : G.Vertex) ⟨finish⟩ where
  toFun := toPath
  invFun := ofPath
  left_inv := ofPath_toPath
  right_inv := toPath_ofPath

/-- Concatenation of walks is composition of paths. -/
theorem toPath_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).toPath = first.toPath.comp second.toPath := by
  induction second with
  | nil => rfl
  | concat edge second ih => exact congrArg (Quiver.Path.cons · (arrow edge)) ih

/-- Composition of paths is concatenation of walks. -/
theorem ofPath_comp {source middle target : G.Vertex} (first : Quiver.Path source middle)
    (second : Quiver.Path middle target) :
    ofPath (first.comp second) = (ofPath first).append (ofPath second) := by
  rw [← toPath_ofPath first, ← toPath_ofPath second, ← toPath_append, ofPath_toPath,
    ofPath_toPath, ofPath_toPath]

/-- The correspondence preserves length. -/
@[simp] theorem length_toPath (walk : G.Walk start finish) :
    walk.toPath.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat edge walk ih => exact congrArg (· + 1) ih

end Walk

/-- Strong connectivity of an edge graph is mathlib's strong connectivity of its quiver. -/
theorem isStronglyConnected_iff_quiver :
    G.IsStronglyConnected ↔ Quiver.IsStronglyConnected G.Vertex :=
  ⟨fun hconnected start finish => (hconnected start.vertex finish.vertex).map Walk.toPath,
    fun hconnected start finish => (hconnected ⟨start⟩ ⟨finish⟩).map Walk.ofPath⟩

/-- A morphism of edge graphs as a prefunctor of their quivers. -/
def Hom.toPrefunctor (f : G.Hom H) : G.Vertex ⥤q H.Vertex where
  obj vertex := ⟨f.vertexMap vertex.vertex⟩
  map arrow := ⟨f.edgeMap arrow.1, (f.source_edgeMap _).trans (congrArg _ arrow.2.1),
    (f.target_edgeMap _).trans (congrArg _ arrow.2.2)⟩

namespace Walk

variable {start finish : V}

/-- The edges of the image of a path are the images of its edges. -/
theorem edges_ofPath_mapPath (f : G.Hom H) {source target : G.Vertex}
    (path : Quiver.Path source target) :
    (ofPath (f.toPrefunctor.mapPath path)).edges = (ofPath path).edges.map f.edgeMap := by
  induction path with
  | nil => rfl
  | cons path arrow ih =>
      rw [Prefunctor.mapPath_cons, edges_ofPath_cons, ih, edges_ofPath_cons, List.map_append,
        List.map_singleton]
      rfl

/-- Reading the image of a path as a walk maps the walk it reads as. -/
theorem ofPath_mapPath (f : G.Hom H) {source target : G.Vertex}
    (path : Quiver.Path source target) :
    ofPath (f.toPrefunctor.mapPath path) = (ofPath path).map f :=
  Walk.ext ((edges_ofPath_mapPath f path).trans (edges_map f _).symm)

/-- **Mapping a walk is mapping its path.** -/
theorem toPath_map (f : G.Hom H) (walk : G.Walk start finish) :
    (walk.map f).toPath = f.toPrefunctor.mapPath walk.toPath := by
  have h := congrArg toPath (ofPath_mapPath f walk.toPath)
  rw [toPath_ofPath, ofPath_toPath] at h
  exact h.symm

end Walk

end EdgeGraph

namespace PathCategory

variable {G : EdgeGraph V E}

/-- Walks as paths, functorially. -/
def toPaths : PathCategory G ⥤ Paths G.Vertex where
  obj object := ⟨object.vertex⟩
  map walk := EdgeGraph.Walk.toPath walk
  map_id _ := rfl
  map_comp first second := EdgeGraph.Walk.toPath_append first second

/-- Paths as walks, functorially. -/
def ofPaths : Paths G.Vertex ⥤ PathCategory G where
  obj vertex := ofVertex G vertex.vertex
  map path := EdgeGraph.Walk.ofPath path
  map_id _ := rfl
  map_comp first second := EdgeGraph.Walk.ofPath_comp first second

/-- Reading walks as paths and back is the identity. -/
theorem toPaths_comp_ofPaths : toPaths ⋙ ofPaths = 𝟭 (PathCategory G) :=
  Functor.hext (fun _ => rfl) fun _ _ walk => heq_of_eq (EdgeGraph.Walk.ofPath_toPath walk)

/-- Reading paths as walks and back is the identity. -/
theorem ofPaths_comp_toPaths : ofPaths ⋙ toPaths = 𝟭 (Paths G.Vertex) :=
  Functor.hext (fun _ => rfl) fun _ _ path => heq_of_eq (EdgeGraph.Walk.toPath_ofPath path)

/-- **The path category of an edge graph is mathlib's path category of its quiver.**  The
equivalence is an isomorphism of categories: both composites are identity functors
(`Maths.PathCategory.toPaths_comp_ofPaths` and `Maths.PathCategory.ofPaths_comp_toPaths`). -/
def equivPaths : PathCategory G ≌ Paths G.Vertex :=
  CategoryTheory.Equivalence.mk toPaths ofPaths (eqToIso toPaths_comp_ofPaths.symm)
    (eqToIso ofPaths_comp_toPaths)

end PathCategory

end Maths
