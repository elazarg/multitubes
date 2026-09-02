/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure
public import Maths.Multitubes.Relational
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Path closure for relation-labelled transport

Existential image preserves arbitrary unions. Consequently the powerset embedding of a
relation-labelled transport admits path closure: starting from prescribed subsets of the fibers,
it collects exactly the elements reachable along some typed walk. This closure is the least lax
section containing the prescribed subsets.

## Main definitions

* `Maths.RelationTransport.edgeImageSupHom` - existential image as a supremum-preserving map.

## Main results

* `Maths.RelationTransport.mem_pathClosure_iff` - membership in path closure is relational
  reachability along some walk.
* `Maths.RelationTransport.pathClosure_isLeast` - relational path closure is the least attainable
  family containing the initial subsets.

## Tags

relation, quiver, transport, reachability, closure, powerset
-/

@[expose] public section

noncomputable section

namespace Maths.RelationTransport

open scoped SetRel

universe uV uE uF

variable {V : Type uV} {E : Type uE}
variable {G : EdgeGraph V E} {Fiber : V → Type uF}
variable (T : RelationTransport G Fiber)

/-- An existential-image edge map regarded as a map preserving arbitrary suprema. -/
def edgeImageSupHom (edge : E) :
    sSupHom (Set (Fiber (G.source edge))) (Set (Fiber (G.target edge))) where
  toFun := (T.edgeRelation edge).image
  map_sSup' := by
    intro sets
    change (T.edgeRelation edge).image (⋃₀ sets) =
      ⋃₀ ((T.edgeRelation edge).image '' sets)
    rw [SetRel.image_sUnion]
    simp only [Set.sUnion_image]

/-- Path closure contains exactly the values related to initial data along some typed walk. -/
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

/-- Path closure is the least lax section containing the prescribed fiber subsets. -/
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

end Maths.RelationTransport
