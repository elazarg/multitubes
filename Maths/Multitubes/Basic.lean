/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.WalkLabel
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Monotone.Defs

/-!
# Transport on operator-labelled transition graphs

A directed multigraph supplies the control-flow skeleton.  Each vertex carries a
state space (its **fiber**), and each edge carries a map from the fiber at its
source to the fiber at its target.  A walk denotes the chronological composite
of its edge maps; a closed walk denotes an endomorphism of the fiber over its
base vertex.

The phrase **operator-labelled transition graph** names the carrier.  The phrase
**transport** names the compositional semantics and its proof tools:
walk maps, holonomy, sections, lax and oplax sections, and monoid-valued walk
labels.

The same structure can be read in several ways.

* It is a representation of the free path category of a quiver, stated without
  importing category theory.
* Geometrically it is a discrete connection; `walkMap` is parallel transport
  and `holonomy` is holonomy or monodromy.
* With one common fiber and group labels it is the action carried by a gain or
  voltage graph in the sense of Zaslavsky.  General monoid labels are
  one-directional and need not support the label inversion under edge reversal
  that the classical notion carries.
* A section is a flat or equivariant section; in the gain-graph case with the
  group acting simply transitively on the fiber, a trivialization or switching
  function.  Lax and oplax sections are respectively subsolutions and
  supersolutions, or pre-invariants and post-invariants, according to the
  application.
* Computationally it is a labelled transition system transforming a per-state
  value, and `walkMap` is the denotational semantics of paths: a walk denotes
  the composite of its edge maps, and concatenation denotes composition
  (`Transport.walkMap_append`).

`Maths.EdgeGraph` supplies the directed multigraph and its typed walks, and
`Maths.Graph.WalkLabel` the monoid labels of walks.
`Maths.Multitubes.Additive.Exact` specializes this file to translation maps,
where cycle sums are translation holonomy and coboundaries are sections, and
`Maths.Multitubes.MaxAffine.Basic` specializes it to monotone max-affine
self-maps of `ℝ`, where the non-additive defect telescope is weighted by suffix
products of slopes.

## Main definitions

* `Maths.Transport` - vertex-indexed fibers with edge maps.
* `Maths.Transport.walkMap` - transport along a typed walk.
* `Maths.Transport.holonomy` - transport around a closed walk.
* `Maths.Transport.restrictEdges` - the restriction to an edge subgraph.
* `Maths.Transport.HasTrivialHolonomyAt` and `Maths.Transport.HasTrivialHolonomy` - every
  closed-walk map at one base, or at every base, is the identity.
* `Maths.Transport.unit` - the terminal transport, with one-point fibers.
* `Maths.Transport.Simulation` - a fiberwise map comparing the edge maps of two transports
  through an edge-indexed relation.
* `Maths.Transport.IsSectionFor` - a family related along every edge, by an
  edge-indexed relation, from the transported source value to the target value: a simulation
  out of the terminal transport.
* `Maths.Transport.IsSection`, `Maths.Transport.IsLaxSection`, and
  `Maths.Transport.IsOplaxSection` - the cases `=`, `≤`, and `≥`.
* `Maths.Transport.IsMonotone` - every edge map is monotone.
* `Maths.ofEdgeAct` - the constant-fiber case.
* `Maths.ofSMul` - the constant-fiber transport of a monoid labelling acting
  on a common fiber, whose walk maps are the actions of the walk labels
  `Maths.walkLabel`.

## Main results

* `Maths.Transport.walkMap_castStart` and `Maths.Transport.walkMap_castFinish` -
  endpoint reindexing commutes with transport.
* `Maths.Transport.walkMap_append` - path composition.
* `Maths.Transport.walkMap_injective` - walks of injective edge maps transport injectively.
* `Maths.Transport.Simulation.walkMap_rel_of_forall_mem_edges` - walk propagation of a
  simulation, for a transitive relation preserved by the target edge maps.
* `Maths.Transport.isSectionFor_iff_exists_simulation` - sections are simulations out of the
  terminal transport.
* `Maths.Transport.walkMap_rel_of_forall_mem_edges` and
  `Maths.Transport.IsSectionFor.walkMap_rel` - walk propagation for sections, its instance.
* `Maths.Transport.IsSection.walkMap_eq`, `Maths.Transport.IsLaxSection.walkMap_le`, and
  `Maths.Transport.IsOplaxSection.le_walkMap` - its exact, lax, and oplax instances.
* `Maths.Transport.IsSection.isLaxSection` and `Maths.Transport.IsSection.isOplaxSection` -
  exact sections are lax and oplax.
* `Maths.walkMap_ofSMul_eq_walkLabel_smul` - a monoid-labelled walk acts by its composite
  label.
* `Maths.hasTrivialHolonomy_ofSMul` - trivial cycle labels
  imply trivial holonomy of the induced transport.
* `Maths.hasTrivialCycleLabels_iff_hasTrivialHolonomy_ofSMul` - for the regular
  representation, by left multiplication on the monoid itself, the converse holds.

## Implementation notes

This file proves only the structural walk-induction lemmas.  Existence of
sections, lax sections, or oplax sections is label-specific potential theory
and belongs in the specialization that supplies the label algebra.

The development is stratified by how much order structure the fibers carry, and
the strata are worth naming because they behave differently under a change of
order.  Transport itself -- `walkMap`, `holonomy`, `IsSection`, and the exact
theory built on them -- assumes no order at all; edge maps are arbitrary
functions between fibers.  `IsLaxSection` and `IsOplaxSection` assume only a
fiberwise `LE`.  Turning equalities into inequalities and transporting lax or
oplax sections along walks require a `Preorder`.  Aggregation results beyond
the walk calculus need a *join*: the least lax majorant of
`Maths.Multitubes.Closure` is an
indexed supremum over all walks and assumes a `CompleteLattice`, the labels of
`Maths.Algebra.JoinSemidirect` act through `⊔` and assume a `SemilatticeSup`,
and a max-affine label is defined by a join against its floor.

So exact transport requires no relation, and the lax and oplax predicates
require only a fiberwise `LE`, while their walk propagation and the Bellman and
max-affine layers require progressively more structure.  The latter are
unavailable exactly when the fiber order has no binary joins.  The standard
example is the Löwner order on positive semidefinite operators, which is an
anti-lattice -- a supremum exists only for a comparable pair (Kadison) -- so
those layers have no operator-valued analogue, while the layers below them do.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory
  Ser. B 47 (1989), 32-52, for gain and voltage graphs.
* R. V. Kadison, *Order properties of bounded self-adjoint operators*, Proc.
  Amer. Math. Soc. 2 (1951), 505-510, for the anti-lattice property of the
  Löwner order referred to in the implementation notes.

## Tags

transport, quiver, gain graph, voltage graph, holonomy, parallel transport,
labelled transition system
-/

@[expose] public section


namespace Maths

universe uV uE uF uH uX uM

variable {V : Type uV} {E : Type uE}

/-- Move a fiber point along an equality of vertices. -/
def fiberCast (Fiber : V → Type uF) {first second : V} (hvertex : first = second)
    (point : Fiber first) : Fiber second :=
  cast (congrArg Fiber hvertex) point

variable {Fiber : V → Type uF}

@[simp] theorem fiberCast_rfl {vertex : V} (point : Fiber vertex) :
    fiberCast Fiber rfl point = point := rfl

@[simp] theorem fiberCast_family {first second : V}
    (family : ∀ vertex, Fiber vertex) (hvertex : first = second) :
    fiberCast Fiber hvertex (family first) = family second := by
  subst hvertex
  rfl

/-- `fiberCast` on a constant fiber family is the identity. -/
@[simp] theorem fiberCast_const {X : Type uX} {first second : V}
    (hvertex : first = second) (point : X) :
    fiberCast (fun _ : V => X) hvertex point = point := rfl

/-- Retyping both sides of a fiberwise comparison preserves the comparison. -/
theorem fiberCast_le_fiberCast [∀ vertex : V, LE (Fiber vertex)]
    {first second : V} (hvertex : first = second) {point other : Fiber first}
    (hle : point ≤ other) :
    fiberCast Fiber hvertex point ≤ fiberCast Fiber hvertex other := by
  subst hvertex
  exact hle

/-- Maps between the fibers at the endpoints of each edge of a directed
multigraph. -/
structure Transport (G : EdgeGraph V E) (Fiber : V → Type uF) where
  /-- The map from the fiber at an edge's source to the fiber at its target. -/
  edgeMap : (edge : E) → Fiber (G.source edge) → Fiber (G.target edge)

namespace Transport

variable {G : EdgeGraph V E} (T : Transport G Fiber)

/-- Transport a fiber point along a walk, applying edge maps in chronological
order. -/
def walkMap {start : V} :
    {finish : V} → G.Walk start finish → Fiber start → Fiber finish
  | _, .nil => id
  | _, .concat edge walkSoFar => fun point => T.edgeMap edge (walkMap walkSoFar point)

variable {T}

variable {start finish middle finish' base : V}

@[simp] theorem walkMap_nil (point : Fiber start) :
    T.walkMap (.nil : G.Walk start start) point = point := rfl

@[simp] theorem walkMap_concat (edge : E) (walk : G.Walk start (G.source edge))
    (point : Fiber start) :
    T.walkMap (walk.concat edge) point =
      T.edgeMap edge (T.walkMap walk point) := rfl

@[simp] theorem walkMap_singleton (edge : E) (point : Fiber (G.source edge)) :
    T.walkMap (EdgeGraph.Walk.singleton (G := G) edge) point = T.edgeMap edge point := rfl

/-- Retyping the start of a walk retypes its transported input. -/
@[simp] theorem walkMap_castStart {start' : V} (walk : G.Walk start finish)
    (hstart : start = start') (point : Fiber start') :
    T.walkMap (walk.castStart hstart) point =
      T.walkMap walk (fiberCast Fiber hstart.symm point) := by
  subst start'
  rfl

/-- Retyping the endpoint of a walk retypes its transported value. -/
@[simp] theorem walkMap_castFinish (walk : G.Walk start finish)
    (hfinish : finish = finish') (point : Fiber start) :
    T.walkMap (walk.castFinish hfinish) point =
      fiberCast Fiber hfinish (T.walkMap walk point) := by
  subst hfinish
  rfl

/-- Transport along a concatenation is the chronological composite of the two
walk transports. -/
theorem walkMap_append (first : G.Walk start middle) (second : G.Walk middle finish)
    (point : Fiber start) :
    T.walkMap (first.append second) point = T.walkMap second (T.walkMap first point) := by
  induction second with
  | nil => rfl
  | concat edge walkSoFar ih =>
      rw [EdgeGraph.Walk.append_concat, walkMap_concat, walkMap_concat, ih]

/-- Transport along a walk is injective when every edge map is. -/
theorem walkMap_injective (hinjective : ∀ edge, Function.Injective (T.edgeMap edge))
    (walk : G.Walk start finish) : Function.Injective (T.walkMap walk) := by
  induction walk with
  | nil => exact Function.injective_id
  | concat edge walkSoFar ih =>
      intro first second hequal
      simp only [walkMap_concat] at hequal
      exact ih (hinjective edge hequal)

/-- The restriction of a transport to the edge subgraph on a set of edges. -/
def restrictEdges (T : Transport G Fiber) (S : Set E) : Transport (G.restrictEdges S) Fiber where
  edgeMap edge := T.edgeMap edge.1

@[simp] theorem restrictEdges_edgeMap (S : Set E) (edge : S) :
    (T.restrictEdges S).edgeMap edge = T.edgeMap edge.1 := rfl

/-- Transport along a walk of an edge subgraph is transport along the same walk read in the
ambient graph. -/
@[simp] theorem walkMap_restrictEdges {S : Set E} (walk : (G.restrictEdges S).Walk start finish)
    (point : Fiber start) :
    (T.restrictEdges S).walkMap walk point = T.walkMap walk.ofRestrictEdges point := by
  induction walk with
  | nil => rfl
  | concat edge walk ih => exact congrArg (T.edgeMap edge.1) ih

/-- Transport around a closed walk, an endomorphism of the fiber over its base
vertex. -/
def holonomy (T : Transport G Fiber) {base : V} (cycle : G.Walk base base) :
    Fiber base → Fiber base :=
  T.walkMap cycle

@[simp] theorem holonomy_nil (point : Fiber base) :
    T.holonomy (.nil : G.Walk base base) point = point := rfl

/-- Traversing two closed walks at one base vertex composes their holonomies. -/
theorem holonomy_append (first second : G.Walk base base) (point : Fiber base) :
    T.holonomy (first.append second) point = T.holonomy second (T.holonomy first point) :=
  walkMap_append first second point

/-- Every closed-walk holonomy at one base vertex is the identity map on its fiber. -/
def HasTrivialHolonomyAt (T : Transport G Fiber) (base : V) : Prop :=
  ∀ cycle : G.Walk base base, T.holonomy cycle = id

/-- Every closed-walk holonomy is the identity map on its base fiber. -/
def HasTrivialHolonomy (T : Transport G Fiber) : Prop :=
  ∀ base : V, T.HasTrivialHolonomyAt base

/-- Trivial holonomy at a base fixes every point of the base fiber. -/
theorem HasTrivialHolonomyAt.holonomy_eq_self (hflat : T.HasTrivialHolonomyAt base)
    (cycle : G.Walk base base) (point : Fiber base) :
    T.holonomy cycle point = point := by
  rw [hflat cycle]
  rfl

/-- Trivial holonomy fixes every point of every base fiber. -/
theorem HasTrivialHolonomy.holonomy_eq_self (hflat : T.HasTrivialHolonomy)
    (cycle : G.Walk base base) (point : Fiber base) :
    T.holonomy cycle point = point :=
  (hflat base).holonomy_eq_self cycle point

/-! ### Simulations -/

variable {Other : V → Type uH}

/-- The **terminal transport**: a one-point fiber over every vertex.  A section of a transport
is a simulation out of it (`Maths.Transport.IsSectionFor.toSimulation`). -/
def unit (G : EdgeGraph V E) : Transport G (fun _ : V => Unit) where
  edgeMap _ := id

/-- A fiberwise map comparing the edge maps of two transports through an edge-indexed relation
on the target fiber: along every edge, transport in `S` after mapping is `relation`-related to
mapping after transport in `T`.  A morphism, `Maths.Transport.Hom`, is the case of equality;
lax and oplax morphisms are the cases `≤` and `≥`; a section is a simulation out of the
terminal transport `Maths.Transport.unit`. -/
structure Simulation (T : Transport G Fiber) (S : Transport G Other)
    (relation : ∀ edge : E, Other (G.target edge) → Other (G.target edge) → Prop) where
  /-- The map on the fiber over each vertex. -/
  app : (vertex : V) → Fiber vertex → Other vertex
  /-- The edgewise comparison of the two transports. -/
  edge_rel : ∀ (edge : E) (point : Fiber (G.source edge)),
    relation edge (S.edgeMap edge (app (G.source edge) point))
      (app (G.target edge) (T.edgeMap edge point))

namespace Simulation

variable {S : Transport G Other}
variable {relation : ∀ edge : E, Other (G.target edge) → Other (G.target edge) → Prop}

/-- Apply a simulation to a vertex-indexed family. -/
def mapFamily (f : Simulation T S relation) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Other vertex :=
  fun vertex => f.app vertex (family vertex)

/-- **Walk propagation.**  Let `R` be a fiberwise relation, transitive, reflexive on the image
of a simulation, and preserved by the edge maps of `S` along a walk.  If on every edge of the
walk `relation` implies `R` against the image of the simulation, then transport in `S` after
mapping is `R`-related to mapping after transport in `T` along the whole walk.  Only the edges
of the walk are consulted. -/
theorem walkMap_rel_of_forall_mem_edges (f : Simulation T S relation)
    {R : ∀ vertex, Other vertex → Other vertex → Prop}
    (hrefl : ∀ vertex point, R vertex (f.app vertex point) (f.app vertex point))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (walk : G.Walk start finish)
    (hpreserve : ∀ edge ∈ walk.edges, ∀ {x y}, R (G.source edge) x y →
      R (G.target edge) (S.edgeMap edge x) (S.edgeMap edge y))
    (hedge : ∀ edge ∈ walk.edges, ∀ x point, relation edge x (f.app (G.target edge) point) →
      R (G.target edge) x (f.app (G.target edge) point))
    (point : Fiber start) :
    R finish (S.walkMap walk (f.app start point)) (f.app finish (T.walkMap walk point)) := by
  induction walk with
  | nil => exact hrefl start point
  | concat edge walk ih =>
      have hprefix := ih (fun edge' hedge' => hpreserve edge' (by simp [hedge']))
        fun edge' hedge' => hedge edge' (by simp [hedge'])
      exact htrans _ (hpreserve edge (by simp) hprefix)
        (hedge edge (by simp) _ _ (f.edge_rel edge _))

/-- A simulation extends from edges to walks when `relation` implies a fiberwise relation that
is reflexive on its image, transitive, and preserved by the edge maps of `S`. -/
theorem walkMap_rel (f : Simulation T S relation)
    {R : ∀ vertex, Other vertex → Other vertex → Prop}
    (hrefl : ∀ vertex point, R vertex (f.app vertex point) (f.app vertex point))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (hpreserve : ∀ edge {x y}, R (G.source edge) x y →
      R (G.target edge) (S.edgeMap edge x) (S.edgeMap edge y))
    (hedge : ∀ edge x point, relation edge x (f.app (G.target edge) point) →
      R (G.target edge) x (f.app (G.target edge) point))
    (walk : G.Walk start finish) (point : Fiber start) :
    R finish (S.walkMap walk (f.app start point)) (f.app finish (T.walkMap walk point)) :=
  f.walkMap_rel_of_forall_mem_edges hrefl htrans walk (fun edge _ => hpreserve edge)
    (fun edge _ => hedge edge) point

/-- Weaken the comparison relation of a simulation. -/
def mono (f : Simulation T S relation)
    {relation' : ∀ edge : E, Other (G.target edge) → Other (G.target edge) → Prop}
    (hrelation : ∀ edge {x y}, relation edge x y → relation' edge x y) :
    Simulation T S relation' where
  app := f.app
  edge_rel edge point := hrelation edge (f.edge_rel edge point)

@[simp] theorem mono_app (f : Simulation T S relation)
    {relation' : ∀ edge : E, Other (G.target edge) → Other (G.target edge) → Prop}
    (hrelation : ∀ edge {x y}, relation edge x y → relation' edge x y) :
    (f.mono hrelation).app = f.app :=
  rfl

end Simulation

/-! ### Sections -/

/-- A family of fiber points related along every edge, by an edge-indexed relation on the
target fiber, from the transported source value to the target value.  Exact, lax, and oplax
sections are the cases `=`, `≤`, and `≥`; a mixed section chooses among them edge by edge.
Equivalently, a simulation out of the terminal transport
(`Maths.Transport.isSectionFor_iff_exists_simulation`). -/
def IsSectionFor (T : Transport G Fiber)
    (relation : ∀ edge : E, Fiber (G.target edge) → Fiber (G.target edge) → Prop)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, relation edge (T.edgeMap edge (family (G.source edge))) (family (G.target edge))

variable {family : ∀ vertex, Fiber vertex}
variable {relation : ∀ edge : E, Fiber (G.target edge) → Fiber (G.target edge) → Prop}

/-- A section, read as the simulation out of the terminal transport constant at the family. -/
def IsSectionFor.toSimulation (hfamily : T.IsSectionFor relation family) :
    Simulation (unit G) T relation where
  app vertex _ := family vertex
  edge_rel edge _ := hfamily edge

/-- A simulation out of the terminal transport is a section. -/
theorem Simulation.isSectionFor (f : Simulation (unit G) T relation) :
    T.IsSectionFor relation fun vertex => f.app vertex () :=
  fun edge => f.edge_rel edge ()

/-- **Sections are simulations out of the terminal transport.** -/
theorem isSectionFor_iff_exists_simulation :
    T.IsSectionFor relation family ↔
      ∃ f : Simulation (unit G) T relation, ∀ vertex, f.app vertex () = family vertex :=
  ⟨fun hfamily => ⟨hfamily.toSimulation, fun _ => rfl⟩, fun ⟨f, hf⟩ => by
    simpa only [hf] using f.isSectionFor⟩

/-- **Walk propagation of an edgewise relation.**  Let `R` be a fiberwise relation, transitive,
reflexive at a family, and preserved by the edge maps along a walk.  If every edge of the walk
relates the transported source value to the target value, then so does the whole walk.  Only
the edges of the walk are consulted. -/
theorem walkMap_rel_of_forall_mem_edges {R : ∀ vertex, Fiber vertex → Fiber vertex → Prop}
    (hrefl : ∀ vertex, R vertex (family vertex) (family vertex))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (walk : G.Walk start finish)
    (hpreserve : ∀ edge ∈ walk.edges, ∀ {x y}, R (G.source edge) x y →
      R (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hedge : ∀ edge ∈ walk.edges,
      R (G.target edge) (T.edgeMap edge (family (G.source edge))) (family (G.target edge))) :
    R finish (T.walkMap walk (family start)) (family finish) :=
  IsSectionFor.toSimulation (relation := fun edge x y => edge ∈ walk.edges → R _ x y)
    (fun edge hmem => hedge edge hmem) |>.walkMap_rel_of_forall_mem_edges
    (fun vertex _ => hrefl vertex) htrans walk hpreserve (fun _ hmem _ _ h => h hmem) ()

/-- **Walk propagation of sections.**  Let `R` be a fiberwise relation, transitive, reflexive
at the family, and preserved by the edge maps.  If every edge of a walk relates a point to the
family value only when `R` does, then the family value at the start is transported along the
walk to a point `R`-related to the family value at the end.

This is `Maths.Transport.Simulation.walkMap_rel_of_forall_mem_edges` for the simulation out of
the terminal transport.  Every propagation statement for sections is an instance: exact sections
with `R` equality, lax sections with `≤`, oplax sections with `≥`, and mixed sections with the
relation their edge modes select. -/
theorem IsSectionFor.walkMap_rel {R : ∀ vertex, Fiber vertex → Fiber vertex → Prop}
    (hrefl : ∀ vertex, R vertex (family vertex) (family vertex))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (hpreserve : ∀ edge {x y}, R (G.source edge) x y →
      R (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hfamily : T.IsSectionFor relation family) (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges, ∀ x, relation edge x (family (G.target edge)) →
      R (G.target edge) x (family (G.target edge))) :
    R finish (T.walkMap walk (family start)) (family finish) :=
  hfamily.toSimulation.walkMap_rel_of_forall_mem_edges (fun vertex _ => hrefl vertex) htrans
    walk (fun edge _ => hpreserve edge) (fun edge hmem _ _ h => hedge edge hmem _ h) ()

/-- A family carried by every edge map to the family's value at the target: the case `=` of
`Maths.Transport.IsSectionFor`. -/
def IsSection (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) = family (G.target edge)

theorem isSection_iff_isSectionFor :
    T.IsSection family ↔ T.IsSectionFor (fun _ => Eq) family :=
  Iff.rfl

/-- A section is transported exactly along every walk. -/
theorem IsSection.walkMap_eq (hfamily : T.IsSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) = family finish :=
  IsSectionFor.walkMap_rel (R := fun _ => Eq) (fun _ => rfl) (fun _ => Eq.trans)
    (fun _ => congrArg _) hfamily walk fun _ _ _ => id

/-- Every closed-walk holonomy fixes the point marked by a section. -/
theorem IsSection.holonomy_eq (hfamily : T.IsSection family)
    (cycle : G.Walk base base) :
    T.holonomy cycle (family base) = family base :=
  hfamily.walkMap_eq cycle

/-! ### Lax and oplax sections -/

/-- A family whose target value dominates the transported source value on every
edge: the case `≤` of `Maths.Transport.IsSectionFor`.  Only a fiberwise `LE` is needed to
state this predicate. -/
def IsLaxSection [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge)

/-- A family whose target value is below its transported source value on every
edge: the case `≥` of `Maths.Transport.IsSectionFor`.  Only a fiberwise `LE` is needed to
state this predicate. -/
def IsOplaxSection [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, family (G.target edge) ≤ T.edgeMap edge (family (G.source edge))

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- Every edge map is monotone. -/
def IsMonotone (T : Transport G Fiber) : Prop :=
  ∀ edge : E, Monotone (T.edgeMap edge)

/-- Transport along a walk is monotone when every edge map is. -/
theorem IsMonotone.walkMap (hmono : T.IsMonotone) (walk : G.Walk start finish) :
    Monotone (T.walkMap walk) := by
  induction walk with
  | nil => exact monotone_id
  | concat edge walk ih => exact (hmono edge).comp ih

/-- An exact section is a lax section. -/
theorem IsSection.isLaxSection (hfamily : T.IsSection family) : T.IsLaxSection family :=
  fun edge => (hfamily edge).le

/-- An exact section is an oplax section. -/
theorem IsSection.isOplaxSection (hfamily : T.IsSection family) : T.IsOplaxSection family :=
  fun edge => (hfamily edge).ge

/-- With monotone edge maps, a lax section is transported below its value at the
terminal vertex of every walk. -/
theorem IsLaxSection.walkMap_le (hmono : T.IsMonotone)
    (hfamily : T.IsLaxSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) ≤ family finish :=
  IsSectionFor.walkMap_rel (R := fun _ => (· ≤ ·)) (fun _ => le_rfl) (fun _ => le_trans)
    (fun edge _ _ hxy => hmono edge hxy) hfamily walk fun _ _ _ => id

/-- A lax section marks a pre-fixed point of every closed-walk holonomy. -/
theorem IsLaxSection.holonomy_le (hmono : T.IsMonotone)
    (hfamily : T.IsLaxSection family) (cycle : G.Walk base base) :
    T.holonomy cycle (family base) ≤ family base :=
  hfamily.walkMap_le hmono cycle

/-- With monotone edge maps, an oplax section is transported above its value at
the terminal vertex of every walk. -/
theorem IsOplaxSection.le_walkMap (hmono : T.IsMonotone)
    (hfamily : T.IsOplaxSection family) (walk : G.Walk start finish) :
    family finish ≤ T.walkMap walk (family start) :=
  IsSectionFor.walkMap_rel (relation := fun _ => (· ≥ ·)) (R := fun _ => (· ≥ ·))
    (fun _ => le_rfl)
    (fun _ _ _ _ hxy hyz => le_trans hyz hxy) (fun edge _ _ hxy => hmono edge hxy) hfamily walk
    fun _ _ _ => id

/-- An oplax section marks a post-fixed point of every closed-walk holonomy. -/
theorem IsOplaxSection.le_holonomy (hmono : T.IsMonotone)
    (hfamily : T.IsOplaxSection family) (cycle : G.Walk base base) :
    family base ≤ T.holonomy cycle (family base) :=
  hfamily.le_walkMap hmono cycle

end Ordered

end Transport

/-! ## Constant fibers and monoid labels -/

variable {G : EdgeGraph V E} {start finish middle : V}

/-- The transport with one common fiber and prescribed edge-indexed self-maps. -/
def ofEdgeAct (G : EdgeGraph V E) (X : Type uX) (act : E → X → X) :
    Transport G (fun _ : V => X) where
  edgeMap edge := act edge

@[simp] theorem ofEdgeAct_edgeMap {X : Type uX} (act : E → X → X) (edge : E) :
    (ofEdgeAct G X act).edgeMap edge = act edge := rfl

/-- The constant-fiber transport induced by a monoid action. -/
def ofSMul (G : EdgeGraph V E) (X : Type uX) {M : Type uM}
    [Monoid M] [MulAction M X] (label : E → M) : Transport G (fun _ : V => X) :=
  ofEdgeAct G X fun edge point => label edge • point

variable {M : Type uM} [Monoid M] {label : E → M}

@[simp] theorem ofSMul_edgeMap {X : Type uX} [MulAction M X] (edge : E) (point : X) :
    (ofSMul G X label).edgeMap edge point = label edge • point := rfl

/-- The walk map of a monoid-labelled transport is the action of the composite
walk label. -/
theorem walkMap_ofSMul_eq_walkLabel_smul {X : Type uX} [MulAction M X]
    (label : E → M) (walk : G.Walk start finish) (point : X) :
    (ofSMul G X label).walkMap walk point = walkLabel label walk • point := by
  induction walk with
  | nil => simp
  | concat edge walkSoFar ih =>
      rw [Transport.walkMap_concat, ih, walkLabel_concat, mul_smul, ofSMul_edgeMap]

/-- The holonomy of a monoid-labelled constant-fiber transport is the action of
its cycle label. -/
theorem holonomy_ofSMul_eq_walkLabel_smul {X : Type uX} [MulAction M X] (label : E → M)
    {base : V} (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = walkLabel label cycle • point :=
  walkMap_ofSMul_eq_walkLabel_smul label cycle point

/-- Trivial cycle labels make every closed-walk holonomy of the induced
constant-fiber transport the identity. -/
theorem holonomy_ofSMul_eq_self {X : Type uX} [MulAction M X]
    (hflat : HasTrivialCycleLabels G label) {base : V}
    (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = point := by
  rw [holonomy_ofSMul_eq_walkLabel_smul, hflat base cycle, one_smul]

/-- Trivial cycle labels imply trivial holonomy of the induced constant-fiber
transport. -/
theorem hasTrivialHolonomy_ofSMul {X : Type uX} [MulAction M X]
    (hflat : HasTrivialCycleLabels G label) :
    (ofSMul G X label).HasTrivialHolonomy := by
  intro base cycle
  funext point
  exact holonomy_ofSMul_eq_self hflat cycle point

/-- **Flatness is trivial holonomy of the regular representation.**  A monoid labelling has
trivial cycle labels exactly when the transport by left multiplication on the monoid itself
has trivial holonomy.  So statements about flat labels are statements about flat transport. -/
theorem hasTrivialCycleLabels_iff_hasTrivialHolonomy_ofSMul :
    HasTrivialCycleLabels G label ↔ (ofSMul G M label).HasTrivialHolonomy := by
  refine ⟨hasTrivialHolonomy_ofSMul, fun hflat base cycle => ?_⟩
  simpa [holonomy_ofSMul_eq_walkLabel_smul] using hflat.holonomy_eq_self cycle 1

end Maths
