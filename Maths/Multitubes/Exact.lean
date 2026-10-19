/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Category
public import Mathlib.GroupTheory.DedekindFinite

import Mathlib.Algebra.Group.Units.Basic

/-!
# Exact transport beyond groups

Forward typed walks support exact transport without assuming that
edge labels form a group.  Parallel-walk equality is primitive, while
invertibility is derived on strongly connected flat regions.

Path independence of flat transport and of flat labels is one statement about flat path functors
(`Maths.map_eq_of_isFlatAt_of_return`), and so is their invertibility: a walk with a return
between flat vertices is an isomorphism (`Maths.isoOfIsFlatAt`), which in types is an
equivalence of fibers and for a label functor is a unit.  Monoid labels enter the section theory
through the regular representation: a labelling is flat exactly when left multiplication on the
monoid is flat transport (`Maths.hasTrivialCycleLabels_iff_hasTrivialHolonomy_ofSMul`), and a
unit potential is a section of it.  Units are produced, not assumed: the label of an edge on a
closed walk is a unit, and a flat labelling is a unit-valued coboundary on every strongly
connected component.  Additive edge data are the same theory read through `Multiplicative`.

## Main definitions

* `Maths.Transport.HasRootPathIndependence`: parallel walks out of the base
  agree.
* `Maths.Transport.IsRootedSection` and
  `Maths.Transport.rootedSection`: sections normalized at the base, and the
  canonical one built by transporting a base point.
* `Maths.Transport.IsHolonomyFixedAt`: a point fixed by every closed walk at the base.
* `Maths.IsUnitPotential`: a unit-valued section of the regular representation, the
  multiplicative coboundary condition.
* `Maths.HasSCCUnitPotentialAt`: a unit potential on the strongly connected component of a base.
* `Maths.linkedUnit`: the unit read off the out-and-back walks to a linked vertex.

## Main results

* `Maths.Transport.existsUnique_isRootedSection_iff_pointwise_path_independence` and
  `Maths.Transport.hasRootPathIndependence_iff_unique_section`: rooted integrability without
  inverses, pointwise and for every base point.
* `Maths.Transport.walkMapEquivOfTrivialHolonomy` and
  `Maths.Transport.walkMap_eq_of_trivialHolonomy_of_stronglyConnected`:
  strong connectivity makes flat transport groupoidal.
* `Maths.Transport.existsUnique_section_of_base_fixed_of_injective_returns`:
  the sharp injective-return section criterion, needing only reachability from the base.
* `Maths.hasTrivialCycleLabels_of_base_of_dedekindFinite`: direct finiteness
  is the sufficient one-sided-inverse hypothesis used to move flatness between bases.
* `Maths.walkLabel_eq_of_trivialCycleLabels_of_return`: flat labels are path independent
  between vertices joined by a return walk.
* `Maths.isUnit_edge_of_trivialCycleLabels`: under flatness, the label of an edge on a closed
  walk is a unit.
* `Maths.isUnitPotential_iff_label_eq`: a unit potential is a coboundary.
* `Maths.walkLabel_mul_eq_of_forall_mem_edges` and `Maths.hasTrivialCycleLabels_of_unitPotential`:
  unit-valued coboundaries telescope along walks, so they are flat.
* `Maths.hasSCCUnitPotentialAt_of_trivialCycleLabels`: a flat labelling is a unit-valued
  coboundary on the strongly connected component of any vertex.
* `Maths.hasTrivialCycleLabels_iff_exists_unitPotential`: arbitrary monoid-valued
  flat labels live in the unit group as soon as every edge endpoint is linked to a base
  vertex.
* `Maths.exists_unitPotential_of_trivialCycleLabels_of_hasEdgeReturns`: the same
  conclusion component by component, when every edge merely lies on a closed walk.
* `Maths.exists_addUnitPotential_of_zeroCycleSums` and
  `Maths.isAddUnit_edge_of_zeroCycleSums`: the additive commutative-monoid versions, requiring
  no ambient subtraction or group completion.

## Tags

path independence, flat connection, trivial holonomy, integrability, groupoid, unit,
Dedekind-finite monoid, rooted section
-/

@[expose] public section

noncomputable section

namespace Maths

universe uV uE uF uM uA

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} {T : Transport G Fiber}

/-! ## Rooted path independence and sections -/

namespace Transport

/-- All walks from one root to the same endpoint induce the same map. -/
def HasRootPathIndependence (T : Transport G Fiber) (base : V) : Prop :=
  ∀ (vertex : V) (first second : G.Walk base vertex),
    T.walkMap first = T.walkMap second

/-- A rooted section: a section with a prescribed value at the root `base`. -/
def IsRootedSection (T : Transport G Fiber) (base : V) (point : Fiber base)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  T.IsSection family ∧ family base = point

/-- The section obtained by transporting a base point along chosen root walks. -/
def rootedSection (T : Transport G Fiber) (base : V)
    (hreach : RootReaches G base) (point : Fiber base) : ∀ vertex, Fiber vertex :=
  fun vertex ↦ T.walkMap (hreach vertex).some point

variable {base : V}

/-- A section normalized at the base is the transport of the base point along every walk out of
the base. -/
theorem IsRootedSection.walkMap_eq {point : Fiber base} {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsRootedSection base point family) {vertex : V}
    (walk : G.Walk base vertex) : T.walkMap walk point = family vertex :=
  hfamily.2 ▸ hfamily.1.walkMap_eq walk

theorem eq_rootedSection_of_isRootedSection
    (hreach : RootReaches G base) (point : Fiber base)
    {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsRootedSection base point family) :
    family = T.rootedSection base hreach point :=
  funext fun vertex ↦ (hfamily.walkMap_eq (hreach vertex).some).symm

/-- **Pointwise rooted integrability.**  One base point extends uniquely to a section exactly
when all walks out of the base agree on that point.  No cycle, inverse, or algebraic structure
is used. -/
theorem existsUnique_isRootedSection_iff_pointwise_path_independence
    (hreach : RootReaches G base) (point : Fiber base) :
    (∃! family, T.IsRootedSection base point family) ↔
      ∀ (vertex : V) (first second : G.Walk base vertex),
        T.walkMap first point = T.walkMap second point := by
  refine ⟨fun ⟨_, hfamily, _⟩ _ first second ↦
    (hfamily.walkMap_eq first).trans (hfamily.walkMap_eq second).symm, fun hpoint ↦ ?_⟩
  refine ⟨T.rootedSection base hreach point,
    ⟨fun edge ↦ hpoint _ ((hreach _).some.concat edge) (hreach _).some, hpoint base _ .nil⟩,
    fun _ hfamily ↦ T.eq_rootedSection_of_isRootedSection hreach point hfamily⟩

/-- Rooted path independence is equivalent to unique extension of every base
point to a section. -/
theorem hasRootPathIndependence_iff_unique_section
    (hreach : RootReaches G base) :
    T.HasRootPathIndependence base ↔
      ∀ point : Fiber base, ∃! family, T.IsRootedSection base point family := by
  simp only [existsUnique_isRootedSection_iff_pointwise_path_independence hreach,
    HasRootPathIndependence, funext_iff]
  exact ⟨fun h point vertex first second ↦ h vertex first second point,
    fun h vertex first second point ↦ h point vertex first second⟩

theorem rootedSection_isRootedSection (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.IsRootedSection base point (T.rootedSection base hreach point) := by
  obtain ⟨family, hfamily, -⟩ := (T.hasRootPathIndependence_iff_unique_section hreach).1 hpath point
  exact T.eq_rootedSection_of_isRootedSection hreach point hfamily ▸ hfamily

theorem rootedSection_base (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.rootedSection base hreach point base = point :=
  (T.rootedSection_isRootedSection hpath hreach point).2

theorem rootedSection_isSection (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.IsSection (T.rootedSection base hreach point) :=
  (T.rootedSection_isRootedSection hpath hreach point).1

/-! ## Trivial holonomy on a strongly connected graph -/

/-- Trivial holonomy at both endpoints makes transport along a walk an equivalence whenever a
return walk exists, inverted by the return.  This is `Maths.isoOfIsFlatAt` for the path functor
of the transport. -/
def walkMapEquivOfTrivialHolonomy {start finish : V} (hstart : T.HasTrivialHolonomyAt start)
    (hfinish : T.HasTrivialHolonomyAt finish) (walk : G.Walk start finish)
    (back : G.Walk finish start) : Fiber start ≃ Fiber finish :=
  (isoOfIsFlatAt T.toPathFunctor (T.isFlatAt_toPathFunctor_iff.2 hstart)
    (T.isFlatAt_toPathFunctor_iff.2 hfinish) walk back).toEquiv

@[simp] theorem walkMapEquivOfTrivialHolonomy_apply {start finish : V}
    (hstart : T.HasTrivialHolonomyAt start) (hfinish : T.HasTrivialHolonomyAt finish)
    (walk : G.Walk start finish) (back : G.Walk finish start)
    (point : Fiber start) :
    T.walkMapEquivOfTrivialHolonomy hstart hfinish walk back point = T.walkMap walk point :=
  rfl

/-- Between two vertices at which the transport is flat and which are joined by a return walk,
parallel forward walks induce the same map.
This is `Maths.map_eq_of_isFlatAt_of_return` for the path functor of the transport. -/
theorem walkMap_eq_of_trivialHolonomy_of_return {start finish : V}
    (hstart : T.HasTrivialHolonomyAt start) (hfinish : T.HasTrivialHolonomyAt finish)
    (first second : G.Walk start finish) (back : G.Walk finish start) :
    T.walkMap first = T.walkMap second :=
  funext <| CategoryTheory.ConcreteCategory.congr_hom <|
    map_eq_of_isFlatAt_of_return T.toPathFunctor (T.isFlatAt_toPathFunctor_iff.2 hstart)
      (T.isFlatAt_toPathFunctor_iff.2 hfinish) first second back

/-- Flat transport on a strongly connected graph is path-independent. -/
theorem walkMap_eq_of_trivialHolonomy_of_stronglyConnected
    (hflat : T.HasTrivialHolonomy) (hconnected : G.IsStronglyConnected)
    {start finish : V} (first second : G.Walk start finish) :
    T.walkMap first = T.walkMap second :=
  T.walkMap_eq_of_trivialHolonomy_of_return (hflat start) (hflat finish) first second
    (hconnected finish start).some

/-- Evaluation at any base has exactly one inverse extension for flat strongly
connected transport. -/
theorem existsUnique_section_of_trivialHolonomy_of_stronglyConnected
    (hflat : T.HasTrivialHolonomy) {base : V}
    (hconnected : G.IsStronglyConnected) (point : Fiber base) :
    ∃! family, T.IsRootedSection base point family :=
  (T.hasRootPathIndependence_iff_unique_section (fun vertex ↦ (hconnected base vertex))).mp
    (fun _ first second ↦
      T.walkMap_eq_of_trivialHolonomy_of_stronglyConnected hflat hconnected first second) point

/-! ## Sections from base fixed points and injective returns -/

/-- A point fixed by every holonomy based at one vertex. -/
def IsHolonomyFixedAt (T : Transport G Fiber) (base : V)
    (point : Fiber base) : Prop :=
  ∀ cycle : G.Walk base base, T.holonomy cycle point = point

/-- A common fixed point of the base holonomies extends uniquely when every vertex is reached
from the base and the walk map of one chosen return walk at each vertex is injective. -/
theorem existsUnique_section_of_base_fixed_of_injective_returns
    {base : V} (hreach : RootReaches G base)
    (point : Fiber base) (hfixed : T.IsHolonomyFixedAt base point)
    (returns : ∀ vertex, G.Walk vertex base)
    (hinjective : ∀ vertex, Function.Injective (T.walkMap (returns vertex))) :
    ∃! family, T.IsRootedSection base point family := by
  refine (T.existsUnique_isRootedSection_iff_pointwise_path_independence hreach point).2
    fun vertex first second ↦ hinjective vertex ?_
  rw [← T.walkMap_append, ← T.walkMap_append]
  exact (hfixed _).trans (hfixed _).symm

end Transport

/-! ## Monoid-valued balance -/

section Monoid

variable {M : Type uM} [Monoid M] {label : E → M}

/-- In a directly finite monoid, one-base flatness on a strongly connected
graph propagates to every base. -/
theorem hasTrivialCycleLabels_of_base_of_dedekindFinite
    [IsDedekindFiniteMonoid M] {base : V}
    (hconnected : G.IsStronglyConnected)
    (hbase : HasTrivialCycleLabelsAt G label base) :
    HasTrivialCycleLabels G label := by
  intro vertex cycle
  let out := (hconnected base vertex).some
  let back := (hconnected vertex base).some
  have hbackOut : walkLabel label back * walkLabel label out = 1 := by
    simpa [out, back] using hbase (out.append back)
  have houtBack : walkLabel label out * walkLabel label back = 1 :=
    mul_eq_one_comm.mp hbackOut
  have hloop :
      walkLabel label back * walkLabel label cycle * walkLabel label out = 1 := by
    simpa [out, back, mul_assoc] using hbase (out.append (cycle.append back))
  calc
    walkLabel label cycle =
        (walkLabel label out * walkLabel label back) * walkLabel label cycle *
          (walkLabel label out * walkLabel label back) := by simp [houtBack]
    _ = walkLabel label out *
          (walkLabel label back * walkLabel label cycle * walkLabel label out) *
          walkLabel label back := by simp only [mul_assoc]
    _ = 1 := by rw [hloop, mul_one, houtBack]

/-- Two parallel walks with a common return walk have equal labels when the labelling is flat at
both endpoints.  This is `Maths.map_eq_of_isFlatAt_of_return` for the label functor. -/
theorem walkLabel_eq_of_trivialCycleLabels_of_return {start finish : V}
    (hstart : HasTrivialCycleLabelsAt G label start)
    (hfinish : HasTrivialCycleLabelsAt G label finish)
    (first second : G.Walk start finish) (back : G.Walk finish start) :
    walkLabel label first = walkLabel label second :=
  map_eq_of_isFlatAt_of_return (labelFunctor label) hstart hfinish first second back

/-- A **unit potential** for a monoid labelling: a unit-valued family that is a section of the
regular representation, so that crossing an edge multiplies it by the edge's label,
`label edge * potential (source edge) = potential (target edge)`.  Equivalently the label of
each edge is the ratio of the potential across it (`Maths.isUnitPotential_iff_label_eq`): this
is the multiplicative coboundary condition, and it is the shape of every witness produced
below. -/
def IsUnitPotential (G : EdgeGraph V E) (label : E → M) (potential : V → Mˣ) : Prop :=
  (ofSMul G M label).IsSection fun vertex => (potential vertex : M)

theorem isUnitPotential_iff {potential : V → Mˣ} :
    IsUnitPotential G label potential ↔
      ∀ edge, label edge * potential (G.source edge) = potential (G.target edge) :=
  Iff.rfl

/-- The coboundary form of a unit potential: each label is the ratio of the potential across
its edge. -/
theorem isUnitPotential_iff_label_eq {potential : V → Mˣ} :
    IsUnitPotential G label potential ↔
      ∀ edge, label edge = (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ) :=
  forall_congr' fun _ => by
    rw [Units.val_mul, Units.eq_mul_inv_iff_mul_eq]
    rfl

/-- Telescoping: along a walk whose every edge satisfies the equation of a unit potential, the
walk label carries the potential at the start to the potential at the end. -/
theorem walkLabel_mul_eq_of_forall_mem_edges (potential : V → Mˣ) {start finish : V}
    (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges,
      label edge * potential (G.source edge) = potential (G.target edge)) :
    walkLabel label walk * potential start = potential finish := by
  have h := (ofSMul G M label).walkMap_rel_of_forall_mem_edges
    (family := fun vertex => (potential vertex : M)) (R := fun _ => Eq) (fun _ => rfl)
    (fun _ => Eq.trans) walk (fun _ _ _ _ hxy => congrArg _ hxy) hedge
  rwa [walkMap_ofSMul_eq_walkLabel_smul, smul_eq_mul] at h

/-- The unit represented by the chosen out-and-back walks between a base and a linked
vertex: the isomorphism `Maths.isoOfIsFlatAt` of the label functor, read as a unit by
`Maths.unitOfLabelIso`. -/
noncomputable def linkedUnit (hflat : HasTrivialCycleLabels G label) {base vertex : V}
    (hlinked : LinkedTo G base vertex) : Mˣ :=
  unitOfLabelIso <|
    isoOfIsFlatAt (labelFunctor label) (hflat base) (hflat vertex) hlinked.1.some hlinked.2.some

/-- The linked unit is the label of the chosen walk out to the linked vertex. -/
@[simp] theorem val_linkedUnit (hflat : HasTrivialCycleLabels G label) {base vertex : V}
    (hlinked : LinkedTo G base vertex) :
    (linkedUnit hflat hlinked : M) = walkLabel label hlinked.1.some :=
  rfl

/-- The linked unit depends on the base only through its value. -/
theorem linkedUnit_congr (hflat : HasTrivialCycleLabels G label) {base base' vertex : V}
    (hbase : base = base') (hlinked : LinkedTo G base vertex)
    (hlinked' : LinkedTo G base' vertex) :
    linkedUnit hflat hlinked = linkedUnit hflat hlinked' := by
  subst hbase
  rfl

/-- An edge whose endpoints are linked to a common base carries the linked unit at its source
to the linked unit at its target. -/
theorem label_mul_linkedUnit (hflat : HasTrivialCycleLabels G label) {base : V} (edge : E)
    (hsource : LinkedTo G base (G.source edge)) (htarget : LinkedTo G base (G.target edge)) :
    label edge * linkedUnit hflat hsource = linkedUnit hflat htarget :=
  walkLabel_eq_of_trivialCycleLabels_of_return (hflat _) (hflat _) (hsource.1.some.concat edge)
    htarget.1.some htarget.2.some

/-- A unit potential local to the strongly connected component of `base`: only edges whose
endpoints both lie in that component are constrained. -/
def HasSCCUnitPotentialAt (G : EdgeGraph V E) (label : E → M) (base : V) : Prop :=
  ∃ potential : V → Mˣ, ∀ edge : E,
    LinkedTo G base (G.source edge) → LinkedTo G base (G.target edge) →
      label edge * potential (G.source edge) = potential (G.target edge)

/-- **Component-wise coboundary.**  On the strongly connected component of a base vertex, a
flat monoid labelling is a unit-valued coboundary.  Vertices outside the component receive the
trivial unit. -/
theorem hasSCCUnitPotentialAt_of_trivialCycleLabels (hflat : HasTrivialCycleLabels G label)
    (base : V) : HasSCCUnitPotentialAt G label base := by
  classical
  refine ⟨fun vertex ↦ if h : LinkedTo G base vertex then linkedUnit hflat h else 1,
    fun edge hsource htarget ↦ ?_⟩
  simp only [dite_eq_left hsource, dite_eq_left htarget]
  exact label_mul_linkedUnit hflat edge hsource htarget

/-- Every flat monoid labelling whose edge endpoints are all linked to a base
vertex is a unit-valued coboundary, even when the ambient monoid is not a group. -/
theorem exists_unitPotential_of_trivialCycleLabels {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃ potential : V → Mˣ, IsUnitPotential G label potential :=
  let ⟨potential, hpotential⟩ := hasSCCUnitPotentialAt_of_trivialCycleLabels hflat base
  ⟨potential, fun edge ↦ hpotential edge (hlinked edge).1 (hlinked edge).2⟩

/-- **Coboundary reconstruction.**  A flat monoid labelling is a unit-valued
coboundary as soon as every edge lies on a closed walk.  No base vertex and no
connectivity between strongly connected components is assumed: the potential is assembled
from one linked unit per component, at a representative chosen uniformly across it.

The hypothesis cannot be dropped.  Two parallel edges carrying different labels form a
graph without closed walks, so its labels are vacuously flat, yet no potential exists. -/
theorem exists_unitPotential_of_trivialCycleLabels_of_hasEdgeReturns
    (hreturn : HasEdgeReturns G) (hflat : HasTrivialCycleLabels G label) :
    ∃ potential : V → Mˣ, IsUnitPotential G label potential := by
  let representative : V → V := fun vertex ↦
    @Classical.epsilon V ⟨vertex⟩ fun base ↦ LinkedTo G base vertex
  have hrepresentative (vertex : V) : LinkedTo G (representative vertex) vertex :=
    @Classical.epsilon_spec V (fun base ↦ LinkedTo G base vertex) ⟨vertex, .refl vertex⟩
  have hsame (edge : E) :
      representative (G.source edge) = representative (G.target edge) := by
    have hlink := hreturn.linkedTo edge
    have hpred : (fun base ↦ LinkedTo G base (G.source edge)) =
        fun base ↦ LinkedTo G base (G.target edge) :=
      funext fun base ↦ propext ⟨fun h ↦ h.trans hlink, fun h ↦ h.trans hlink.symm⟩
    simp only [representative]
    congr 1
  refine ⟨fun vertex ↦ linkedUnit hflat (hrepresentative vertex), fun edge ↦ ?_⟩
  have hsource : LinkedTo G (representative (G.target edge)) (G.source edge) :=
    hsame edge ▸ hrepresentative (G.source edge)
  change label edge * linkedUnit hflat (hrepresentative (G.source edge)) = _
  rw [linkedUnit_congr hflat (hsame edge) (hrepresentative (G.source edge)) hsource]
  exact label_mul_linkedUnit hflat edge hsource (hrepresentative (G.target edge))

/-- A unit-valued coboundary has trivial labels on every closed walk. -/
theorem hasTrivialCycleLabels_of_unitPotential
    (potential : V → Mˣ) (hpotential : IsUnitPotential G label potential) :
    HasTrivialCycleLabels G label := fun vertex cycle ↦ by
  have h := Transport.IsSection.holonomy_eq hpotential cycle
  rw [holonomy_ofSMul_eq_walkLabel_smul, smul_eq_mul] at h
  calc walkLabel label cycle
      = walkLabel label cycle * potential vertex * ((potential vertex)⁻¹ : Mˣ) := by
        simp [mul_assoc]
    _ = 1 := by rw [h, Units.mul_inv]

/-- Flatness is exactly the existence of a unit-valued coboundary potential, when every edge
endpoint is linked to a base vertex. -/
theorem hasTrivialCycleLabels_iff_exists_unitPotential {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base) :
    HasTrivialCycleLabels G label ↔ ∃ potential : V → Mˣ, IsUnitPotential G label potential :=
  ⟨exists_unitPotential_of_trivialCycleLabels hlinked,
    fun ⟨potential, hpotential⟩ => hasTrivialCycleLabels_of_unitPotential potential hpotential⟩

/-- Under flatness, an edge lying on a closed walk carries a unit label: its label and that of
the return walk are mutually inverse, by `Maths.isoOfIsFlatAt` for the label functor. -/
theorem isUnit_edge_of_trivialCycleLabels (hflat : HasTrivialCycleLabels G label) {edge : E}
    (back : G.Walk (G.target edge) (G.source edge)) : IsUnit (label edge) :=
  ⟨unitOfLabelIso (isoOfIsFlatAt (labelFunctor label) (hflat _) (hflat _) (.singleton edge) back),
    walkLabel_singleton edge⟩

/-- A chosen root-and-return test.  It checks one equation at every edge; it is
not the smaller non-tree-edge test obtained from a specified arborescence.
The equations are inverse-free, and direct finiteness manufactures the missing
reverse identities during the proof. -/
theorem hasTrivialCycleLabels_of_chosen_tests
    [IsDedekindFiniteMonoid M] {base : V}
    (walks : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (hreturn : ∀ vertex,
      walkLabel label (returns vertex) * walkLabel label (walks vertex) = 1)
    (hedge : ∀ edge,
      walkLabel label (returns (G.target edge)) * label edge *
          walkLabel label (walks (G.source edge)) = 1) :
    HasTrivialCycleLabels G label := by
  have hreverse (vertex : V) :
      walkLabel label (walks vertex) * walkLabel label (returns vertex) = 1 :=
    mul_eq_one_comm.mp (hreturn vertex)
  let potential : V → Mˣ := fun vertex ↦
    { val := walkLabel label (walks vertex)
      inv := walkLabel label (returns vertex)
      val_inv := hreverse vertex
      inv_val := hreturn vertex }
  refine hasTrivialCycleLabels_of_unitPotential potential fun edge ↦ ?_
  change label edge * walkLabel label (walks (G.source edge)) =
    walkLabel label (walks (G.target edge))
  calc label edge * walkLabel label (walks (G.source edge))
      = (walkLabel label (walks (G.target edge)) * walkLabel label (returns (G.target edge))) *
          (label edge * walkLabel label (walks (G.source edge))) := by rw [hreverse, one_mul]
    _ = walkLabel label (walks (G.target edge)) *
          (walkLabel label (returns (G.target edge)) * label edge *
            walkLabel label (walks (G.source edge))) := by simp only [mul_assoc]
    _ = walkLabel label (walks (G.target edge)) := by rw [hedge, mul_one]

end Monoid

/-! ## Additive commutative monoids

Additive statements are the multiplicative ones read through `Multiplicative`: zero cycle sums
are trivial cycle labels of the multiplicative reading (`Maths.hasTrivialCycleLabels_ofAdd_iff`),
and a unit of `Multiplicative A` is an additive unit of `A`. -/

section AdditiveMonoid

variable {A : Type uA} [AddCommMonoid A] {weight : E → A}

/-- A unit of the multiplicative reading is an additive unit. -/
private def addUnitsOfUnits (unit : (Multiplicative A)ˣ) : AddUnits A where
  val := (unit : Multiplicative A).toAdd
  neg := ((unit⁻¹ : (Multiplicative A)ˣ) : Multiplicative A).toAdd
  val_neg := congrArg Multiplicative.toAdd unit.mul_inv
  neg_val := congrArg Multiplicative.toAdd unit.inv_mul

/-- **Additive coboundary reconstruction.**  Edge data in an arbitrary additive commutative
monoid with zero cycle sums is the coboundary of a potential valued in the additive units, as
soon as every edge lies on a closed walk.  No subtraction or group completion is assumed. -/
theorem exists_addUnitPotential_of_zeroCycleSums
    (hreturn : HasEdgeReturns G) (hzero : HasZeroCycleSums G weight) :
    ∃ potential : V → AddUnits A, ∀ edge : E,
      (potential (G.source edge) : A) + weight edge = potential (G.target edge) := by
  obtain ⟨potential, hpotential⟩ := exists_unitPotential_of_trivialCycleLabels_of_hasEdgeReturns
    hreturn (hasTrivialCycleLabels_ofAdd_iff.2 hzero)
  exact ⟨fun vertex ↦ addUnitsOfUnits (potential vertex), fun edge ↦
    (add_comm _ _).trans (congrArg Multiplicative.toAdd (hpotential edge))⟩

/-- Under zero cycle sums, an edge lying on a closed walk carries an additive unit. -/
theorem isAddUnit_edge_of_zeroCycleSums (hzero : HasZeroCycleSums G weight) {edge : E}
    (back : G.Walk (G.target edge) (G.source edge)) : IsAddUnit (weight edge) :=
  let ⟨unit, hunit⟩ :=
    isUnit_edge_of_trivialCycleLabels (hasTrivialCycleLabels_ofAdd_iff.2 hzero) back
  ⟨addUnitsOfUnits unit, congrArg Multiplicative.toAdd hunit⟩

end AdditiveMonoid

end Maths

end
