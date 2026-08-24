/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.EdgeGraph
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Monotone.Defs

import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Directed transport on operator-labelled transition graphs

A directed multigraph supplies the control-flow skeleton.  Each vertex carries a
state space (its **fiber**), and each edge carries a map from the fiber at its
source to the fiber at its target.  A walk denotes the chronological composite
of its edge maps; a closed walk denotes an endomorphism of the fiber over its
base vertex.

The phrase **operator-labelled transition graph** names the carrier.  The phrase
**directed transport** names the compositional semantics and its proof tools:
walk maps, holonomy, sections, lax sections, and monoid-valued walk labels.

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
  function.  A lax section is a subsolution, subinvariant family, or inductive
  invariant, according to the application.
* Computationally it is a labelled transition system transforming a per-state
  value, and `walkMap` is the denotational semantics of paths: a walk denotes
  the composite of its edge maps, and concatenation denotes composition
  (`Transport.walkMap_append`).

`DirectedTransport.EdgeGraph` supplies the directed multigraph and its typed
walks.  `DirectedTransport.Additive.Exact` specializes this file to translation
maps, where cycle sums are translation holonomy and coboundaries are sections,
and `DirectedTransport.MaxAffine.Basic` specializes it to monotone max-affine
self-maps of `ℝ`, where the non-additive defect telescope is weighted by suffix
products of slopes.

## Main definitions

* `DirectedTransport.Transport` - vertex-indexed fibers with edge maps.
* `DirectedTransport.Transport.walkMap` - transport along a typed walk.
* `DirectedTransport.Transport.holonomy` - transport around a closed walk.
* `DirectedTransport.Transport.HasTrivialHolonomy` - every closed-walk
  map is the identity.
* `DirectedTransport.Transport.IsSection` and
  `DirectedTransport.Transport.IsLaxSection`.
* `DirectedTransport.ofEdgeAct` and `DirectedTransport.transport` -
  the constant-fiber case.
* `DirectedTransport.walkLabel` and
  `DirectedTransport.HasTrivialCycleLabels` - monoid-labelled walks and
  trivial cycle labels.
* `DirectedTransport.walkSum` - the additive walk sum, the additive sibling
  of `walkLabel`.

## Main results

* `DirectedTransport.Transport.walkMap_append` - path composition.
* `DirectedTransport.Transport.IsSection.walkMap_eq` - exact transport of
  sections.
* `DirectedTransport.Transport.IsLaxSection.walkMap_le` - monotone
  transport of lax sections.
* `DirectedTransport.walkMap_ofEdgeAct` - the dependent and constant-fiber
  semantics agree.
* `DirectedTransport.transport_eq_smul` and
  `DirectedTransport.walkMap_ofSMul_eq_walkLabel_smul` - a monoid-labelled
  walk acts by its composite label.
* `DirectedTransport.hasTrivialHolonomy_ofSMul` - trivial cycle labels
  imply trivial holonomy of the induced transport.

## Implementation notes

This file proves only the structural walk-induction lemmas.  Existence of
sections or lax sections is label-specific potential theory and belongs in the
specialization that supplies the label algebra.

The development is stratified by how much order structure the fibers carry, and
the strata are worth naming because they behave differently under a change of
order.  Transport itself -- `walkMap`, `holonomy`, `IsSection`, and the exact
theory built on them -- assumes no order at all; edge maps are arbitrary
functions between fibers.  `IsLaxSection` and the monotone transport lemmas
assume only a `Preorder`.  Everything beyond that needs a *join*: the least lax
majorant of `DirectedTransport.Closure` is an indexed supremum over all walks
and assumes a `CompleteLattice`, the labels of `DirectedTransport.JoinSemidirect`
act through `⊔` and assume a `SemilatticeSup`, and a max-affine label is defined
by a join against its floor.

So the exact and lax layers are available for any preordered fiber, while the
Bellman and max-affine layers are not: they are unavailable exactly when the
fiber order has no binary joins.  The standard example is the Löwner order on
positive semidefinite operators, which is an anti-lattice -- a supremum exists
only for a comparable pair (Kadison) -- so those layers have no operator-valued
analogue, while the layers below them do.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory
  Ser. B 47 (1989), 32-52, for gain and voltage graphs.
* R. V. Kadison, *Order properties of bounded self-adjoint operators*, Proc.
  Amer. Math. Soc. 2 (1951), 505-510, for the anti-lattice property of the
  Löwner order referred to in the implementation notes.

## Tags

directed transport, quiver, gain graph, voltage graph, holonomy, parallel transport,
labelled transition system
-/

@[expose] public section


namespace DirectedTransport

universe uV uE uF uX uM

variable {V : Type uV} {E : Type uE}

/-- Move a fiber point along an equality of vertices.  This is the coercion
needed when the legality proof of `EdgeGraph.Walk.concat` identifies the source
of the appended edge with the endpoint reached so far. -/
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

theorem fiberCast_fiberCast {first second third : V} (hfirst : first = second)
    (hsecond : second = third) (point : Fiber first) :
    fiberCast Fiber hsecond (fiberCast Fiber hfirst point) =
      fiberCast Fiber (hfirst.trans hsecond) point := by
  subst hfirst
  rfl

/-- `fiberCast` on a constant fiber family is the identity. -/
@[simp] theorem fiberCast_const {X : Type uX} {first second : V}
    (hvertex : first = second) (point : X) :
    fiberCast (fun _ : V => X) hvertex point = point := rfl

theorem fiberCast_le_fiberCast [∀ vertex : V, Preorder (Fiber vertex)]
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
  | _, .concat walkSoFar edge legal =>
      fun point =>
        T.edgeMap edge (fiberCast Fiber legal.symm (walkMap walkSoFar point))

variable {T}

variable {start finish middle finish' base : V}

@[simp] theorem walkMap_nil (point : Fiber start) :
    T.walkMap (.nil : G.Walk start start) point = point := rfl

@[simp] theorem walkMap_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (point : Fiber start) :
    T.walkMap (walk.concat edge legal) point =
      T.edgeMap edge (fiberCast Fiber legal.symm (T.walkMap walk point)) := rfl

@[simp] theorem walkMap_singleton (edge : E) (point : Fiber (G.source edge)) :
    T.walkMap (EdgeGraph.Walk.singleton (G := G) edge) point = T.edgeMap edge point := rfl

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
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, walkMap_concat, walkMap_concat, ih]

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

/-- Every closed-walk holonomy is the identity map on its base fiber. -/
def HasTrivialHolonomy (T : Transport G Fiber) : Prop :=
  ∀ (base : V) (cycle : G.Walk base base), T.holonomy cycle = id

/-- Trivial holonomy fixes every point of every base fiber. -/
theorem HasTrivialHolonomy.holonomy_eq_self (hflat : T.HasTrivialHolonomy)
    (cycle : G.Walk base base) (point : Fiber base) :
    T.holonomy cycle point = point := by
  rw [hflat base cycle]
  rfl

/-! ### Sections -/

/-- A family of fiber points carried by every edge map to the family's value at
the target. -/
def IsSection (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) = family (G.target edge)

variable {family : ∀ vertex, Fiber vertex}

/-- A section is transported exactly along every walk. -/
theorem IsSection.walkMap_eq (hfamily : T.IsSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) = family finish := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [walkMap_concat, ih, fiberCast_family, hfamily edge]

/-- Every closed-walk holonomy fixes the point marked by a section. -/
theorem IsSection.holonomy_eq (hfamily : T.IsSection family)
    (cycle : G.Walk base base) :
    T.holonomy cycle (family base) = family base :=
  hfamily.walkMap_eq cycle

/-! ### Lax sections -/

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A family of fiber points whose target value dominates the transported source
value on every edge. -/
def IsLaxSection (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge)

theorem IsSection.isLaxSection (hfamily : T.IsSection family) : T.IsLaxSection family :=
  fun edge => (hfamily edge).le

/-- With monotone edge maps, a lax section is transported below its value at the
terminal vertex of every walk. -/
theorem IsLaxSection.walkMap_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) ≤ family finish := by
  induction walk with
  | nil => exact le_rfl
  | concat walkSoFar edge legal ih =>
      rw [walkMap_concat]
      refine le_trans (hmono edge ?_) (hfamily edge)
      have hcast := fiberCast_le_fiberCast (Fiber := Fiber) legal.symm ih
      rwa [fiberCast_family] at hcast

/-- A lax section marks a pre-fixed point of every closed-walk holonomy. -/
theorem IsLaxSection.holonomy_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (cycle : G.Walk base base) :
    T.holonomy cycle (family base) ≤ family base :=
  hfamily.walkMap_le hmono cycle

end Ordered

end Transport

/-! ## Constant fibers and monoid labels -/

variable {G : EdgeGraph V E} {start finish middle : V}

/-- The transport with one common fiber and prescribed edge-indexed self-maps. -/
def ofEdgeAct (G : EdgeGraph V E) (X : Type uX) (act : E → X → X) :
    Transport G (fun _ : V => X) where
  edgeMap edge := act edge

/-- Apply edge-indexed self-maps along a walk in chronological order.  This is
the constant-fiber form of `Transport.walkMap`. -/
def transport {X : Type uX} (act : E → X → X) {start : V} :
    {finish : V} → G.Walk start finish → X → X
  | _, .nil => id
  | _, .concat walkSoFar edge _ => act edge ∘ transport act walkSoFar

@[simp] theorem transport_nil {X : Type uX} (act : E → X → X) :
    transport act (.nil : G.Walk start start) = id := rfl

@[simp] theorem transport_concat {X : Type uX} (act : E → X → X)
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    transport act (walk.concat edge legal) = act edge ∘ transport act walk := rfl

/-- Constant-fiber dependent transport agrees with direct composition of the
edge actions. -/
theorem walkMap_ofEdgeAct {X : Type uX} (act : E → X → X)
    (walk : G.Walk start finish) (point : X) :
    (ofEdgeAct G X act).walkMap walk point = transport act walk point := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [Transport.walkMap_concat, fiberCast_const, transport_concat,
        Function.comp_apply, ih]
      rfl

/-- Transport along concatenated constant-fiber walks is chronological
composition. -/
theorem transport_append {X : Type uX} (act : E → X → X)
    (first : G.Walk start middle) (second : G.Walk middle finish) (point : X) :
    transport act (first.append second) point =
      transport act second (transport act first point) := by
  induction second with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, transport_concat, transport_concat,
        Function.comp_apply, Function.comp_apply, ih]

/-- Composite label of a walk, with the last edge outermost so that the label
acts in the same order as `transport`. -/
def walkLabel {M : Type uM} [Monoid M] (label : E → M) {start : V} :
    {finish : V} → G.Walk start finish → M
  | _, .nil => 1
  | _, .concat walkSoFar edge _ => label edge * walkLabel label walkSoFar

variable {M : Type uM} [Monoid M] {label : E → M}

@[simp] theorem walkLabel_nil : walkLabel label (.nil : G.Walk start start) = 1 := rfl

@[simp] theorem walkLabel_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    walkLabel label (walk.concat edge legal) = label edge * walkLabel label walk := rfl

/-- Concatenating walks multiplies labels in chronological-action order. -/
@[simp] theorem walkLabel_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    walkLabel label (first.append second) = walkLabel label second * walkLabel label first := by
  induction second with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, walkLabel_concat, walkLabel_concat, ih, mul_assoc]

/-- Every closed walk has identity composite label.  For group-labelled gain
graphs this is balance or flatness. -/
def HasTrivialCycleLabels (G : EdgeGraph V E) (label : E → M) : Prop :=
  ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkLabel label cycle = 1

/-- When labels act on a common fiber, the composite walk label acts exactly as
the chronological edge transport. -/
theorem transport_eq_smul {X : Type uX} [MulAction M X]
    (walk : G.Walk start finish) (point : X) :
    transport (fun edge value => label edge • value) walk point =
      walkLabel label walk • point := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [transport_concat, Function.comp_apply, ih, walkLabel_concat, mul_smul]

/-- Trivial cycle labels make the induced transport around every cycle the
identity on every acted-on point. -/
theorem transport_cycle_eq_self {X : Type uX} [MulAction M X]
    (hflat : HasTrivialCycleLabels G label) {vertex : V}
    (cycle : G.Walk vertex vertex) (point : X) :
    transport (fun edge value => label edge • value) cycle point = point := by
  rw [transport_eq_smul, hflat vertex cycle, one_smul]

/-- The constant-fiber transport induced by a monoid action. -/
def ofSMul (G : EdgeGraph V E) (X : Type uX) {M : Type uM}
    [Monoid M] [MulAction M X] (label : E → M) : Transport G (fun _ : V => X) :=
  ofEdgeAct G X fun edge point => label edge • point

/-- The dependent transport induced by a monoid action agrees with direct
constant-fiber transport. -/
theorem walkMap_ofSMul {X : Type uX} {M : Type uM} [Monoid M] [MulAction M X]
    (label : E → M) (walk : G.Walk start finish) (point : X) :
    (ofSMul G X label).walkMap walk point =
      transport (fun edge value => label edge • value) walk point :=
  walkMap_ofEdgeAct _ walk point

/-- The walk map of a monoid-labelled transport is the action of the composite
walk label. -/
theorem walkMap_ofSMul_eq_walkLabel_smul {X : Type uX} {M : Type uM}
    [Monoid M] [MulAction M X] (label : E → M) (walk : G.Walk start finish)
    (point : X) :
    (ofSMul G X label).walkMap walk point = walkLabel label walk • point := by
  rw [walkMap_ofSMul, transport_eq_smul]

/-- The holonomy of a monoid-labelled constant-fiber transport is the action of
its cycle label. -/
theorem holonomy_ofSMul_eq_walkLabel_smul {X : Type uX} {M : Type uM}
    [Monoid M] [MulAction M X] (label : E → M) {base : V}
    (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = walkLabel label cycle • point :=
  walkMap_ofSMul_eq_walkLabel_smul label cycle point

/-- Trivial cycle labels make every closed-walk holonomy of the induced
constant-fiber transport the identity. -/
theorem holonomy_ofSMul_eq_self {X : Type uX} {M : Type uM}
    [Monoid M] [MulAction M X] {label : E → M}
    (hflat : HasTrivialCycleLabels G label) {base : V}
    (cycle : G.Walk base base) (point : X) :
    (ofSMul G X label).holonomy cycle point = point := by
  rw [holonomy_ofSMul_eq_walkLabel_smul, hflat base cycle, one_smul]

/-- Trivial cycle labels imply trivial holonomy of the induced constant-fiber
transport. -/
theorem hasTrivialHolonomy_ofSMul {X : Type uX} {M : Type uM}
    [Monoid M] [MulAction M X] {label : E → M}
    (hflat : HasTrivialCycleLabels G label) :
    (ofSMul G X label).HasTrivialHolonomy := by
  intro base cycle
  funext point
  exact holonomy_ofSMul_eq_self hflat cycle point

/-! ## Additive walk sums -/

section WalkSum

variable {A : Type*} [AddCommMonoid A]

/-- Sum of edge data along a finite walk, in chronological order.  Also called
the walk's tension, its line integral, or its cycle sum when the walk is
closed.  This is the additive sibling of `walkLabel`. -/
def walkSum (w : E → A) {start finish : V} (walk : G.Walk start finish) : A :=
  (walk.edges.map w).sum

variable {w : E → A}

@[simp] theorem walkSum_nil : walkSum w (.nil : G.Walk start start) = 0 := rfl

@[simp] theorem walkSum_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    walkSum w (walk.concat edge legal) = walkSum w walk + w edge := by
  simp [walkSum]

@[simp] theorem walkSum_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    walkSum w (first.append second) = walkSum w first + walkSum w second := by
  simp [walkSum]

@[simp] theorem walkSum_singleton (edge : E) :
    walkSum w (EdgeGraph.Walk.singleton (G := G) edge) = w edge := by
  simp [walkSum]

@[simp] theorem walkSum_castFinish {finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    walkSum w (walk.castFinish hfinish) = walkSum w walk := by
  simp [walkSum]

end WalkSum

end DirectedTransport
