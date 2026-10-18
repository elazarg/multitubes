/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.Morphism
public import Maths.Multitubes.Relational
public import Maths.Multitubes.Switching
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# The graph of elements of a transport

A transport unfolds into a directed multigraph over its base.  Its vertices are the fiber
points `⟨vertex, point⟩`; above each base edge `e` and each point `x` of the source fiber lies
one edge from `⟨source e, x⟩` to `⟨target e, edgeMap e x⟩`.  Projection to the base is a
graph morphism.  The construction is the graph analogue of mathlib's
`CategoryTheory.Functor.Elements`.

With a group acting on itself by left multiplication through the gains of an edge graph this
is the derived graph of a voltage graph; with a permutation action on `k` letters it is a
`k`-lift; with signs it is the double cover of a signed graph.  For a relation-labelled
transport the same construction is the state graph explored by reachability analyses.

Walks lift uniquely: a base walk and a starting point determine a walk in the graph of
elements, ending at the transported point, and every walk upstairs is the lift of its
projection.  Holonomy is therefore monodromy: a closed walk lifts to a closed walk exactly at
the points its holonomy fixes.  Balance of a monoid-valued gain says that every closed walk
lifts to a closed walk from the identity, without any group hypothesis.  Sections are sheets,
sets of points closed under lifted edges and meeting each fiber once, and switching a gain
gives an isomorphic graph of elements.  For relations, lifting exists but is not unique, and
walk relations are reachability upstairs.

## Main definitions

* `Maths.Transport.elementsGraph`: the graph of elements of a transport.
* `Maths.Transport.elementsProjection`: its projection to the base.
* `Maths.Transport.liftWalk`: the lift of a base walk from a fiber point.
* `Maths.Transport.sheet`: the embedding of the base given by a section.
* `Maths.switchElementsIso`: the isomorphism of graphs of elements induced by switching.
* `Maths.RelationTransport.elementsGraph`: the graph of elements of a relation-labelled
  transport.

## Main results

* `Maths.Transport.map_liftWalk`: a lift projects to the walk it lifts.
* `Maths.Transport.finish_eq_of_walk` and `Maths.Transport.heq_liftWalk`: unique path
  lifting; every walk upstairs is the lift of its projection.
* `Maths.Transport.holonomy_eq_iff_exists_closed_lift`: holonomy fixes a point exactly when
  the closed walk lifts to a closed walk there.
* `Maths.hasTrivialCycleLabels_iff_forall_closed_lift`: balance is triviality of the cover at
  the identity.
* `Maths.Transport.isSection_iff_target_elementsGraph`: sections are sheets.
* `Maths.RelationTransport.mem_walkRelation_iff_exists_walk`: walk relations are reachability
  in the graph of elements.

## References

* J. L. Gross and T. W. Tucker, *Topological Graph Theory*, Wiley (1987), chapter 2.

## Tags

graph of elements, derived graph, voltage graph, covering graph, lift, monodromy, holonomy
-/

@[expose] public section

namespace Maths

universe uV uE uF uM

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

namespace Transport

variable {Fiber : V → Type uF} (T : Transport G Fiber)

/-- The graph of elements: a vertex is a fiber point, and an edge is a base edge together
with a point of its source fiber, running to the transported point. -/
abbrev elementsGraph : EdgeGraph (Σ vertex, Fiber vertex) (Σ edge, Fiber (G.source edge)) where
  source edge := ⟨G.source edge.1, edge.2⟩
  target edge := ⟨G.target edge.1, T.edgeMap edge.1 edge.2⟩

@[simp] theorem elementsGraph_source (edge : Σ edge, Fiber (G.source edge)) :
    T.elementsGraph.source edge = ⟨G.source edge.1, edge.2⟩ := rfl

@[simp] theorem elementsGraph_target (edge : Σ edge, Fiber (G.source edge)) :
    T.elementsGraph.target edge = ⟨G.target edge.1, T.edgeMap edge.1 edge.2⟩ := rfl

/-- The projection of the graph of elements to the base. -/
abbrev elementsProjection : EdgeGraph.Hom T.elementsGraph G where
  vertexMap := Sigma.fst
  edgeMap := Sigma.fst
  source_edgeMap _ := rfl
  target_edgeMap _ := rfl

/-- The lift of a base walk from a point of its initial fiber.  It ends at the transported
point. -/
def liftWalk {start : V} (point : Fiber start) :
    {finish : V} → (walk : G.Walk start finish) →
      T.elementsGraph.Walk ⟨start, point⟩ ⟨finish, T.walkMap walk point⟩
  | _, .nil => .nil
  | _, .concat edge walkSoFar =>
      .concat (G := T.elementsGraph) ⟨edge, T.walkMap walkSoFar point⟩ (liftWalk point walkSoFar)

variable {T}

/-- **Existence of lifts.**  A lift projects to the walk it lifts. -/
@[simp] theorem map_liftWalk {start finish : V} (point : Fiber start)
    (walk : G.Walk start finish) :
    (T.liftWalk point walk).map T.elementsProjection = walk := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      change (((T.liftWalk point walkSoFar).map T.elementsProjection).concat edge) = _
      rw [ih]

/-- **Unique lifting of endpoints.**  A walk upstairs ends at the point obtained by
transporting its initial point along its projection. -/
theorem finish_eq_of_walk {start : V} {point : Fiber start} {finish : Σ vertex, Fiber vertex}
    (walk : T.elementsGraph.Walk ⟨start, point⟩ finish) :
    finish = ⟨finish.1, T.walkMap (walk.map T.elementsProjection) point⟩ := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      obtain ⟨edge, value⟩ := edge
      have hvalue : value = T.walkMap (walkSoFar.map T.elementsProjection) point :=
        eq_of_heq (Sigma.mk.inj ih).2
      change (⟨G.target edge, T.edgeMap edge value⟩ : Σ vertex, Fiber vertex) =
        ⟨G.target edge, T.edgeMap edge (T.walkMap (walkSoFar.map T.elementsProjection) point)⟩
      exact congrArg (fun value => (⟨G.target edge, T.edgeMap edge value⟩ :
        Σ vertex, Fiber vertex)) hvalue

/-- **Unique path lifting.**  Every walk upstairs is the lift of its projection. -/
theorem heq_liftWalk {start : V} {point : Fiber start} {finish : Σ vertex, Fiber vertex}
    (walk : T.elementsGraph.Walk ⟨start, point⟩ finish) :
    walk ≍ T.liftWalk point (walk.map T.elementsProjection) := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      obtain ⟨edge, value⟩ := edge
      have hvalue : value = T.walkMap (walkSoFar.map T.elementsProjection) point :=
        eq_of_heq (Sigma.mk.inj (finish_eq_of_walk walkSoFar)).2
      exact EdgeGraph.Walk.concat_heq_concat (G := T.elementsGraph)
        (edge := ⟨edge, value⟩)
        (edge' := ⟨edge, T.walkMap (walkSoFar.map T.elementsProjection) point⟩)
        (Sigma.ext rfl (heq_of_eq hvalue)) ih

/-- **Holonomy is monodromy.**  The holonomy of a closed walk fixes a point exactly when the
walk lifts to a closed walk at that point. -/
theorem holonomy_eq_iff_exists_closed_lift {base : V} (cycle : G.Walk base base)
    (point : Fiber base) :
    T.holonomy cycle point = point ↔
      ∃ lift : T.elementsGraph.Walk ⟨base, point⟩ ⟨base, point⟩,
        lift.map T.elementsProjection = cycle := by
  constructor
  · intro hfixed
    refine ⟨(T.liftWalk point cycle).castFinish (congrArg (Sigma.mk base) hfixed), ?_⟩
    rw [EdgeGraph.Walk.map_castFinish, map_liftWalk]
    rfl
  · rintro ⟨lift, hlift⟩
    have hfinish := finish_eq_of_walk lift
    rw [hlift] at hfinish
    exact (eq_of_heq (Sigma.mk.inj hfinish).2).symm

/-- The embedding of the base into the graph of elements given by a section. -/
def sheet {family : ∀ vertex, Fiber vertex} (hfamily : T.IsSection family) :
    EdgeGraph.Hom G T.elementsGraph where
  vertexMap vertex := ⟨vertex, family vertex⟩
  edgeMap edge := ⟨edge, family (G.source edge)⟩
  source_edgeMap _ := rfl
  target_edgeMap edge := by rw [elementsGraph_target, hfamily edge]

/-- A sheet is a section of the projection. -/
@[simp] theorem elementsProjection_comp_sheet {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsSection family) :
    T.elementsProjection.comp (sheet hfamily) = EdgeGraph.Hom.id G :=
  rfl

/-- **Sections are sheets.**  A family of points is a section exactly when the lift of every
edge from the family's point at its source lands on the family's point at its target. -/
theorem isSection_iff_target_elementsGraph (family : ∀ vertex, Fiber vertex) :
    T.IsSection family ↔
      ∀ edge, T.elementsGraph.target ⟨edge, family (G.source edge)⟩ =
        ⟨G.target edge, family (G.target edge)⟩ := by
  refine forall_congr' fun edge => ?_
  rw [elementsGraph_target]
  exact ⟨fun h => by rw [h], fun h => eq_of_heq (Sigma.mk.inj h).2⟩

end Transport

/-! ### Gains -/

section Gain

variable {M : Type uM} [Monoid M]

/-- **Balance is triviality of the cover.**  A monoid-valued gain is balanced exactly when
every closed walk lifts to a closed walk from the identity in the graph of elements of the
left-multiplication transport.  No inverses are needed. -/
theorem hasTrivialCycleLabels_iff_forall_closed_lift (label : E → M) :
    HasTrivialCycleLabels G label ↔
      ∀ (base : V) (cycle : G.Walk base base),
        ∃ lift : (ofSMul G M label).elementsGraph.Walk ⟨base, 1⟩ ⟨base, 1⟩,
          lift.map (ofSMul G M label).elementsProjection = cycle := by
  refine forall_congr' fun base => forall_congr' fun cycle => ?_
  rw [← Transport.holonomy_eq_iff_exists_closed_lift, Transport.holonomy,
    walkMap_ofSMul_eq_walkLabel_smul, smul_eq_mul, mul_one]

/-- **Switching acts by isomorphism.**  Multiplying the point over each vertex by the
switching unit there identifies the graph of elements of a gain with that of its switching. -/
def switchElementsIso (η : V → Mˣ) (label : E → M) :
    EdgeGraph.Iso (ofSMul G M label).elementsGraph
      (ofSMul G M (switch G η label)).elementsGraph where
  vertexEquiv := Equiv.sigmaCongrRight fun vertex => Units.mulLeft (η vertex)
  edgeEquiv := Equiv.sigmaCongrRight fun edge => Units.mulLeft (η (G.source edge))
  source_edgeEquiv _ := rfl
  target_edgeEquiv edge := by
    obtain ⟨edge, point⟩ := edge
    change (⟨G.target edge, switch G η label edge * (η (G.source edge) * point)⟩ :
        Σ _ : V, M) = ⟨G.target edge, η (G.target edge) * (label edge * point)⟩
    simp [switch_apply, mul_assoc]

end Gain

/-! ### Relations -/

namespace RelationTransport

variable {Fiber : V → Type uF} (T : RelationTransport G Fiber)

/-- The graph of elements of a relation-labelled transport: an edge is a base edge together
with a related pair of endpoint values. -/
abbrev elementsGraph :
    EdgeGraph (Σ vertex, Fiber vertex)
      (Σ edge, {pair : Fiber (G.source edge) × Fiber (G.target edge) //
        pair ∈ T.edgeRelation edge}) where
  source edge := ⟨G.source edge.1, edge.2.1.1⟩
  target edge := ⟨G.target edge.1, edge.2.1.2⟩

/-- The projection of the relational graph of elements to the base. -/
abbrev elementsProjection : EdgeGraph.Hom T.elementsGraph G where
  vertexMap := Sigma.fst
  edgeMap := Sigma.fst
  source_edgeMap _ := rfl
  target_edgeMap _ := rfl

variable {T}

/-- A walk upstairs relates its endpoint values along its projection. -/
theorem mem_walkRelation_of_walk {start : V} {point : Fiber start}
    {finish : Σ vertex, Fiber vertex} (walk : T.elementsGraph.Walk ⟨start, point⟩ finish) :
    (point, finish.2) ∈ T.walkRelation (walk.map T.elementsProjection) := by
  induction walk with
  | nil => exact SetRel.mem_id.mpr rfl
  | concat edge walkSoFar ih =>
      obtain ⟨edge, ⟨first, second⟩, hpair⟩ := edge
      exact ⟨first, ih, hpair⟩

/-- **Walk relations are reachability upstairs.**  Two values are related along a base walk
exactly when some walk in the graph of elements joins them and projects to it. -/
theorem mem_walkRelation_iff_exists_walk {start finish : V} (walk : G.Walk start finish)
    (first : Fiber start) (last : Fiber finish) :
    (first, last) ∈ T.walkRelation walk ↔
      ∃ lift : T.elementsGraph.Walk ⟨start, first⟩ ⟨finish, last⟩,
        lift.map T.elementsProjection = walk := by
  constructor
  · intro hrelated
    induction walk with
    | nil =>
        have hlast : first = last := SetRel.mem_id.mp hrelated
        subst hlast
        exact ⟨.nil, rfl⟩
    | concat edge walkSoFar ih =>
        obtain ⟨middle, hmiddle, hedge⟩ := hrelated
        obtain ⟨lift, hlift⟩ := ih middle hmiddle
        refine ⟨lift.concat (G := T.elementsGraph) ⟨edge, ⟨(middle, last), hedge⟩⟩, ?_⟩
        subst hlift
        rfl
  · rintro ⟨lift, rfl⟩
    exact mem_walkRelation_of_walk lift

end RelationTransport

end Maths
