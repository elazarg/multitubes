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
* `Maths.Transport.HasTrivialHolonomy` - every closed-walk
  map is the identity.
* `Maths.Transport.IsSectionFor` - a family related along every edge, by an
  edge-indexed relation, from the transported source value to the target value.
* `Maths.Transport.IsSection`, `Maths.Transport.IsLaxSection`, and
  `Maths.Transport.IsOplaxSection` - the cases `=`, `≤`, and `≥`.
* `Maths.ofEdgeAct` and `Maths.transport` -
  the constant-fiber case.
* `Maths.ofSMul` - the constant-fiber transport of a monoid labelling acting
  on a common fiber, whose walk maps are the actions of the walk labels
  `Maths.walkLabel`.

## Main results

* `Maths.Transport.walkMap_castStart` and `Maths.Transport.walkMap_castFinish` -
  endpoint reindexing commutes with transport.
* `Maths.Transport.walkMap_append` - path composition.
* `Maths.Transport.walkMap_injective` - walks of injective edge maps transport injectively.
* `Maths.Transport.walkMap_rel_of_forall_mem_edges` - walk propagation of an edgewise
  relation along one walk, for a transitive relation preserved by its edge maps.
* `Maths.Transport.IsSectionFor.walkMap_rel` - its form for sections.
* `Maths.Transport.IsSection.walkMap_eq`, `Maths.Transport.IsLaxSection.walkMap_le`, and
  `Maths.Transport.IsOplaxSection.le_walkMap` - its exact, lax, and oplax instances.
* `Maths.Transport.IsSection.isLaxSection` and `Maths.Transport.IsSection.isOplaxSection` -
  exact sections are lax and oplax.
* `Maths.walkMap_ofEdgeAct` - the dependent and constant-fiber
  semantics agree.
* `Maths.transport_eq_smul` and
  `Maths.walkMap_ofSMul_eq_walkLabel_smul` - a monoid-labelled
  walk acts by its composite label.
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

/-- Retyping a fiber point leaves it unchanged as a point of the total space. -/
theorem sigma_mk_fiberCast {first second : V} (hvertex : first = second) (point : Fiber first) :
    (⟨second, fiberCast Fiber hvertex point⟩ : Σ vertex, Fiber vertex) = ⟨first, point⟩ := by
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
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, walkMap_concat, walkMap_concat, ih]

/-- Transport along a walk is injective when every edge map is. -/
theorem walkMap_injective (hinjective : ∀ edge, Function.Injective (T.edgeMap edge))
    (walk : G.Walk start finish) : Function.Injective (T.walkMap walk) := by
  induction walk with
  | nil => exact Function.injective_id
  | concat walkSoFar edge legal ih =>
      intro first second hequal
      simp only [walkMap_concat] at hequal
      exact ih (by simpa [fiberCast] using hinjective edge hequal)

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

/-- A family of fiber points related along every edge, by an edge-indexed relation on the
target fiber, from the transported source value to the target value.  Exact, lax, and oplax
sections are the cases `=`, `≤`, and `≥`; a mixed section chooses among them edge by edge. -/
def IsSectionFor (T : Transport G Fiber)
    (relation : ∀ edge : E, Fiber (G.target edge) → Fiber (G.target edge) → Prop)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, relation edge (T.edgeMap edge (family (G.source edge))) (family (G.target edge))

variable {family : ∀ vertex, Fiber vertex}

/-- **Walk propagation.**  Let `R` be a fiberwise relation, transitive, reflexive at a family,
and preserved by the edge maps along a walk.  If every edge of the walk relates the transported
source value to the target value, then so does the whole walk.  Only the edges of the walk are
consulted. -/
theorem walkMap_rel_of_forall_mem_edges {R : ∀ vertex, Fiber vertex → Fiber vertex → Prop}
    (hrefl : ∀ vertex, R vertex (family vertex) (family vertex))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (walk : G.Walk start finish)
    (hpreserve : ∀ edge ∈ walk.edges, ∀ {x y}, R (G.source edge) x y →
      R (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hedge : ∀ edge ∈ walk.edges,
      R (G.target edge) (T.edgeMap edge (family (G.source edge))) (family (G.target edge))) :
    R finish (T.walkMap walk (family start)) (family finish) := by
  induction walk with
  | nil => exact hrefl start
  | concat walk edge legal ih =>
      cases legal
      have hprefix := ih (fun edge' hedge' => hpreserve edge' (by simp [hedge']))
        fun edge' hedge' => hedge edge' (by simp [hedge'])
      exact htrans _ (hpreserve edge (by simp) hprefix) (hedge edge (by simp))

/-- **Walk propagation of sections.**  Let `R` be a fiberwise relation, transitive, reflexive
at the family, and preserved by the edge maps.  If every edge of a walk relates a point to the
family value only when `R` does, then the family value at the start is transported along the
walk to a point `R`-related to the family value at the end.

Every propagation statement for sections is an instance: exact sections with `R` equality, lax
sections with `≤`, oplax sections with `≥`, and mixed sections with the relation their edge
modes select. -/
theorem IsSectionFor.walkMap_rel
    {relation : ∀ edge : E, Fiber (G.target edge) → Fiber (G.target edge) → Prop}
    {R : ∀ vertex, Fiber vertex → Fiber vertex → Prop}
    (hrefl : ∀ vertex, R vertex (family vertex) (family vertex))
    (htrans : ∀ vertex {x y z}, R vertex x y → R vertex y z → R vertex x z)
    (hpreserve : ∀ edge {x y}, R (G.source edge) x y →
      R (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hfamily : T.IsSectionFor relation family) (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges, ∀ x, relation edge x (family (G.target edge)) →
      R (G.target edge) x (family (G.target edge))) :
    R finish (T.walkMap walk (family start)) (family finish) :=
  walkMap_rel_of_forall_mem_edges hrefl htrans walk (fun edge _ => hpreserve edge)
    fun edge hmem => hedge edge hmem _ (hfamily edge)

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

/-- An exact section is a lax section. -/
theorem IsSection.isLaxSection (hfamily : T.IsSection family) : T.IsLaxSection family :=
  fun edge => (hfamily edge).le

/-- An exact section is an oplax section. -/
theorem IsSection.isOplaxSection (hfamily : T.IsSection family) : T.IsOplaxSection family :=
  fun edge => (hfamily edge).ge

/-- With monotone edge maps, a lax section is transported below its value at the
terminal vertex of every walk. -/
theorem IsLaxSection.walkMap_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (walk : G.Walk start finish) :
    T.walkMap walk (family start) ≤ family finish :=
  IsSectionFor.walkMap_rel (R := fun _ => (· ≤ ·)) (fun _ => le_rfl) (fun _ => le_trans)
    (fun edge _ _ hxy => hmono edge hxy) hfamily walk fun _ _ _ => id

/-- A lax section marks a pre-fixed point of every closed-walk holonomy. -/
theorem IsLaxSection.holonomy_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsLaxSection family) (cycle : G.Walk base base) :
    T.holonomy cycle (family base) ≤ family base :=
  hfamily.walkMap_le hmono cycle

/-- With monotone edge maps, an oplax section is transported above its value at
the terminal vertex of every walk. -/
theorem IsOplaxSection.le_walkMap (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsOplaxSection family) (walk : G.Walk start finish) :
    family finish ≤ T.walkMap walk (family start) :=
  IsSectionFor.walkMap_rel (relation := fun _ => (· ≥ ·)) (R := fun _ => (· ≥ ·))
    (fun _ => le_rfl)
    (fun _ _ _ _ hxy hyz => le_trans hyz hxy) (fun edge _ _ hxy => hmono edge hxy) hfamily walk
    fun _ _ _ => id

/-- An oplax section marks a post-fixed point of every closed-walk holonomy. -/
theorem IsOplaxSection.le_holonomy (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
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

/-- Apply edge-indexed self-maps along a walk in chronological order: the walk map of the
constant-fiber transport `ofEdgeAct`. -/
def transport {X : Type uX} (act : E → X → X) {start finish : V}
    (walk : G.Walk start finish) : X → X :=
  (ofEdgeAct G X act).walkMap walk

@[simp] theorem transport_nil {X : Type uX} (act : E → X → X) :
    transport act (.nil : G.Walk start start) = id := rfl

@[simp] theorem transport_concat {X : Type uX} (act : E → X → X)
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    transport act (walk.concat edge legal) = act edge ∘ transport act walk := rfl

/-- Constant-fiber walk transport is direct composition of the edge actions. -/
theorem walkMap_ofEdgeAct {X : Type uX} (act : E → X → X)
    (walk : G.Walk start finish) (point : X) :
    (ofEdgeAct G X act).walkMap walk point = transport act walk point := rfl

/-- Transport along concatenated constant-fiber walks is chronological
composition. -/
theorem transport_append {X : Type uX} (act : E → X → X)
    (first : G.Walk start middle) (second : G.Walk middle finish) (point : X) :
    transport act (first.append second) point =
      transport act second (transport act first point) :=
  (ofEdgeAct G X act).walkMap_append first second point

variable {M : Type uM} [Monoid M] {label : E → M}

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

/-- **Flatness is trivial holonomy of the regular representation.**  A monoid labelling has
trivial cycle labels exactly when the transport by left multiplication on the monoid itself
has trivial holonomy.  So statements about flat labels are statements about flat transport. -/
theorem hasTrivialCycleLabels_iff_hasTrivialHolonomy_ofSMul {M : Type uM} [Monoid M]
    {label : E → M} :
    HasTrivialCycleLabels G label ↔ (ofSMul G M label).HasTrivialHolonomy := by
  refine ⟨hasTrivialHolonomy_ofSMul, fun hflat base cycle => ?_⟩
  simpa [holonomy_ofSMul_eq_walkLabel_smul] using hflat.holonomy_eq_self cycle 1

end Maths
