/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Mathlib.GroupTheory.DedekindFinite

/-!
# Exact transport beyond groups

Forward typed walks support exact transport without assuming that
edge labels form a group.  Parallel-walk equality is primitive, while
invertibility is derived on recurrent flat regions.

Monoid labels enter through the regular representation: a labelling is flat exactly when
left multiplication on the monoid is flat transport
(`Maths.hasTrivialCycleLabels_iff_hasTrivialHolonomy_ofSMul`), so path independence of flat
labels is path independence of flat transport.  Units are produced, not assumed: the label of
an edge on a closed walk is a unit, and a flat labelling is a unit-valued coboundary on every
strongly connected component.  Additive edge data are the same theory read through
`Multiplicative`.

## Main definitions

* `Maths.Transport.HasRootPathIndependence`: parallel walks out of the base
  agree.
* `Maths.Transport.IsSectionWithBase` and
  `Maths.Transport.rootedSection`: sections normalised at the base, and the
  canonical one built by transporting a base point.
* `Maths.Transport.IsBaseHolonomyFixed`: every closed walk at the base fixes
  the base fiber pointwise.
* `Maths.Transport.ingressMap`, `Maths.Transport.returnMap`, and
  `Maths.Transport.retractProjector`: the split retract data attached to
  chosen path families.
* `Maths.HasTrivialBaseLabels`: closed walks at one base carry trivial labels.
* `Maths.IsUnitPotential`: the multiplicative coboundary condition on a
  unit-valued function on vertices.
* `Maths.linkedUnit`: the unit read off the out-and-back walks to a linked vertex.

## Main results

* `Maths.Transport.hasRootPathIndependence_iff_unique_section`: rooted
  integrability without inverses.
* `Maths.Transport.walkMapEquivOfTrivialHolonomy` and
  `Maths.Transport.walkMap_eq_of_trivialHolonomy_of_stronglyConnected`:
  recurrence makes flat transport groupoidal.
* `Maths.Transport.existsUnique_section_of_base_fixed_of_injective_returns`:
  the sharp injective-return section criterion.
* `Maths.Transport.compressed_walkMap_eq`: one-base flatness is
  path-independent on chosen split retracts.
* `Maths.hasTrivialCycleLabels_of_base_of_dedekindFinite`: direct finiteness
  is the sufficient one-sided-inverse hypothesis used to move flatness between bases.
* `Maths.walkLabel_eq_of_trivialCycleLabels_of_return`: flat labels are path independent
  on recurrent regions.
* `Maths.isUnit_edge_of_trivialCycleLabels`: under flatness, the label of an edge on a closed
  walk is a unit.
* `Maths.walkLabel_eq_of_forall_mem_edges` and `Maths.hasTrivialCycleLabels_of_unitPotential`:
  unit-valued coboundaries telescope along walks, so they are flat.
* `Maths.exists_unitPotential_on_component`: a flat labelling is a unit-valued coboundary on
  the strongly connected component of any vertex.
* `Maths.exists_unitPotential_of_trivialCycleLabels`: arbitrary monoid-valued
  flat labels live in the unit group as soon as every edge endpoint is linked to a base
  vertex.
* `Maths.exists_unitPotential_of_trivialCycleLabels_of_hasEdgeReturns`: the same
  conclusion component by component, when every edge merely lies on a closed walk.
* `Maths.exists_addUnitPotential_of_zeroCycleSums` and
  `Maths.isAddUnit_edge_of_zeroCycleSums`: the additive commutative-monoid versions, requiring
  no ambient subtraction or group completion.
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

/-- A section with prescribed value at one base vertex. -/
def IsSectionWithBase (T : Transport G Fiber) (base : V) (point : Fiber base)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  T.IsSection family ∧ family base = point

/-- The section obtained by transporting a base point along chosen root walks. -/
def rootedSection (T : Transport G Fiber) (base : V)
    (hreach : RootReaches G base) (point : Fiber base) : ∀ vertex, Fiber vertex :=
  fun vertex ↦ T.walkMap (hreach vertex).some point

variable {base : V}

theorem rootedSection_base (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.rootedSection base hreach point base = point := by
  rw [rootedSection, hpath base (hreach base).some .nil]
  rfl

theorem rootedSection_isSection (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.IsSection (T.rootedSection base hreach point) := by
  intro edge
  let sourceWalk := (hreach (G.source edge)).some
  let targetWalk := (hreach (G.target edge)).some
  have hmaps := hpath (G.target edge) (sourceWalk.concat edge rfl) targetWalk
  exact congrFun hmaps point

theorem rootedSection_isSectionWithBase (hpath : T.HasRootPathIndependence base)
    (hreach : RootReaches G base) (point : Fiber base) :
    T.IsSectionWithBase base point (T.rootedSection base hreach point) :=
  ⟨T.rootedSection_isSection hpath hreach point,
    T.rootedSection_base hpath hreach point⟩

theorem eq_rootedSection_of_isSectionWithBase
    (hreach : RootReaches G base) (point : Fiber base)
    {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsSectionWithBase base point family) :
    family = T.rootedSection base hreach point := by
  funext vertex
  rw [rootedSection, ← hfamily.2]
  exact (hfamily.1.walkMap_eq (hreach vertex).some).symm

/-- Rooted path independence is equivalent to unique extension of every base
point to a section.  No cycle, inverse, or algebraic structure is used. -/
theorem hasRootPathIndependence_iff_unique_section
    (hreach : RootReaches G base) :
    T.HasRootPathIndependence base ↔
      ∀ point : Fiber base, ∃! family, T.IsSectionWithBase base point family := by
  constructor
  · intro hpath point
    refine ⟨T.rootedSection base hreach point,
      T.rootedSection_isSectionWithBase hpath hreach point, ?_⟩
    intro family hfamily
    exact T.eq_rootedSection_of_isSectionWithBase hreach point hfamily
  · intro hextends vertex first second
    funext point
    obtain ⟨family, hfamily, _⟩ := hextends point
    calc
      T.walkMap first point = T.walkMap first (family base) := by rw [hfamily.2]
      _ = family vertex := hfamily.1.walkMap_eq first
      _ = T.walkMap second (family base) := (hfamily.1.walkMap_eq second).symm
      _ = T.walkMap second point := by rw [hfamily.2]

/-- Pointwise rooted integrability: one base point extends uniquely exactly
when all root paths agree on that point. -/
theorem existsUnique_sectionWithBase_iff_pointwise_path_independence
    (hreach : RootReaches G base) (point : Fiber base) :
    (∃! family, T.IsSectionWithBase base point family) ↔
      ∀ (vertex : V) (first second : G.Walk base vertex),
        T.walkMap first point = T.walkMap second point := by
  constructor
  · rintro ⟨family, hfamily, _⟩ vertex first second
    calc
      T.walkMap first point = T.walkMap first (family base) := by rw [hfamily.2]
      _ = family vertex := hfamily.1.walkMap_eq first
      _ = T.walkMap second (family base) := (hfamily.1.walkMap_eq second).symm
      _ = T.walkMap second point := by rw [hfamily.2]
  · intro hpoint
    let family : ∀ vertex, Fiber vertex :=
      fun vertex ↦ T.walkMap (hreach vertex).some point
    have hsection : T.IsSection family := by
      intro edge
      exact hpoint (G.target edge)
        ((hreach (G.source edge)).some.concat edge rfl)
        (hreach (G.target edge)).some
    have hbase : family base = point := hpoint base (hreach base).some .nil
    refine ⟨family, ⟨hsection, hbase⟩, ?_⟩
    intro other hother
    funext vertex
    change other vertex = T.walkMap (hreach vertex).some point
    rw [← hother.2]
    exact (hother.1.walkMap_eq (hreach vertex).some).symm

/-! ## Trivial holonomy on a strongly connected graph -/

/-- Trivial holonomy makes transport along a walk an equivalence whenever a
return walk exists.  The chosen return is proved to be a two-sided inverse. -/
def walkMapEquivOfTrivialHolonomy (hflat : T.HasTrivialHolonomy)
    {start finish : V} (walk : G.Walk start finish)
    (back : G.Walk finish start) : Fiber start ≃ Fiber finish where
  toFun := T.walkMap walk
  invFun := T.walkMap back
  left_inv point := by
    rw [← T.walkMap_append walk back]
    exact hflat.holonomy_eq_self (walk.append back) point
  right_inv point := by
    rw [← T.walkMap_append back walk]
    exact hflat.holonomy_eq_self (back.append walk) point

@[simp] theorem walkMapEquivOfTrivialHolonomy_apply
    (hflat : T.HasTrivialHolonomy) {start finish : V}
    (walk : G.Walk start finish) (back : G.Walk finish start)
    (point : Fiber start) :
    T.walkMapEquivOfTrivialHolonomy hflat walk back point = T.walkMap walk point :=
  rfl

/-- On a recurrent flat region, parallel forward walks induce the same map. -/
theorem walkMap_eq_of_trivialHolonomy_of_return
    (hflat : T.HasTrivialHolonomy) {start finish : V}
    (first second : G.Walk start finish) (back : G.Walk finish start) :
    T.walkMap first = T.walkMap second := by
  funext point
  apply (T.walkMapEquivOfTrivialHolonomy hflat back first).injective
  change T.walkMap back (T.walkMap first point) =
    T.walkMap back (T.walkMap second point)
  rw [← T.walkMap_append first back, ← T.walkMap_append second back]
  exact (hflat.holonomy_eq_self (first.append back) point).trans
    (hflat.holonomy_eq_self (second.append back) point).symm

/-- Flat transport on a strongly connected graph is path-independent. -/
theorem walkMap_eq_of_trivialHolonomy_of_stronglyConnected
    (hflat : T.HasTrivialHolonomy) {base : V}
    (hconnected : IsStronglyConnectedAt G base)
    {start finish : V} (first second : G.Walk start finish) :
    T.walkMap first = T.walkMap second :=
  T.walkMap_eq_of_trivialHolonomy_of_return hflat first second
    (hconnected.nonempty_walk finish start).some

/-- Evaluation at any base has exactly one inverse extension for flat strongly
connected transport. -/
theorem existsUnique_section_of_trivialHolonomy_of_stronglyConnected
    (hflat : T.HasTrivialHolonomy) {base : V}
    (hconnected : IsStronglyConnectedAt G base) (point : Fiber base) :
    ∃! family, T.IsSectionWithBase base point family := by
  apply (T.hasRootPathIndependence_iff_unique_section
    (fun vertex ↦ (hconnected vertex).1)).mp
  intro vertex first second
  exact T.walkMap_eq_of_trivialHolonomy_of_stronglyConnected
    hflat hconnected first second

/-! ## Sections from base fixed points and injective returns -/

/-- A point fixed by every holonomy based at one vertex. -/
def IsBaseHolonomyFixed (T : Transport G Fiber) (base : V)
    (point : Fiber base) : Prop :=
  ∀ cycle : G.Walk base base, T.holonomy cycle point = point

/-- A common fixed point of the base holonomies extends uniquely when one
chosen return map at each vertex is injective. -/
theorem existsUnique_section_of_base_fixed_of_injective_returns
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (point : Fiber base) (hfixed : T.IsBaseHolonomyFixed base point)
    (returns : ∀ vertex, G.Walk vertex base)
    (hinjective : ∀ vertex, Function.Injective (T.walkMap (returns vertex))) :
    ∃! family, T.IsSectionWithBase base point family := by
  let paths : ∀ vertex, G.Walk base vertex :=
    fun vertex ↦ (hconnected vertex).1.some
  let family : ∀ vertex, Fiber vertex :=
    fun vertex ↦ T.walkMap (paths vertex) point
  have hfamily : T.IsSection family := by
    intro edge
    apply hinjective (G.target edge)
    change T.walkMap (returns (G.target edge))
        (T.walkMap ((paths (G.source edge)).concat edge rfl) point) =
      T.walkMap (returns (G.target edge))
        (T.walkMap (paths (G.target edge)) point)
    rw [← T.walkMap_append, ← T.walkMap_append]
    exact (hfixed _).trans (hfixed _).symm
  have hbase : family base = point := hfixed (paths base)
  refine ⟨family, ⟨hfamily, hbase⟩, ?_⟩
  intro other hother
  funext vertex
  change other vertex = T.walkMap (paths vertex) point
  rw [← hother.2]
  exact (hother.1.walkMap_eq (paths vertex)).symm

/-! ## One-base split retracts -/

section Retracts

variable {base : V}
variable (ingress : ∀ vertex, G.Walk base vertex)
variable (returns : ∀ vertex, G.Walk vertex base)

/-- Chosen transport from the base into a vertex fiber. -/
def ingressMap (vertex : V) : Fiber base → Fiber vertex :=
  T.walkMap (ingress vertex)

/-- Chosen transport from a vertex fiber back to the base. -/
def returnMap (vertex : V) : Fiber vertex → Fiber base :=
  T.walkMap (returns vertex)

/-- The chosen split idempotent on a vertex fiber. -/
def retractProjector (vertex : V) : Fiber vertex → Fiber vertex :=
  T.ingressMap ingress vertex ∘ T.returnMap returns vertex

theorem returnMap_comp_ingressMap
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    (vertex : V) :
    T.returnMap returns vertex ∘ T.ingressMap ingress vertex = id := by
  funext point
  rw [returnMap, ingressMap, Function.comp_apply,
    ← T.walkMap_append (ingress vertex) (returns vertex)]
  exact congrFun (hbaseFlat _) point

theorem retractProjector_idempotent
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    (vertex : V) :
    T.retractProjector ingress returns vertex ∘
        T.retractProjector ingress returns vertex =
      T.retractProjector ingress returns vertex := by
  funext point
  change T.ingressMap ingress vertex
      (T.returnMap returns vertex
        (T.ingressMap ingress vertex (T.returnMap returns vertex point))) =
    T.ingressMap ingress vertex (T.returnMap returns vertex point)
  rw [show T.returnMap returns vertex
      (T.ingressMap ingress vertex (T.returnMap returns vertex point)) =
      T.returnMap returns vertex point from
    congrFun (T.returnMap_comp_ingressMap ingress returns hbaseFlat vertex)
      (T.returnMap returns vertex point)]

/-- **Retract flatness.**  Compressing any forward walk by the chosen split
idempotents gives the same map, independently of the walk. -/
theorem compressed_walkMap_eq {start finish : V}
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    (walk : G.Walk start finish) :
    T.retractProjector ingress returns finish ∘ T.walkMap walk ∘
        T.retractProjector ingress returns start =
      T.ingressMap ingress finish ∘ T.returnMap returns start := by
  funext point
  simp only [retractProjector, ingressMap, returnMap, Function.comp_apply]
  congr 1
  rw [← T.walkMap_append (ingress start) walk,
    ← T.walkMap_append ((ingress start).append walk) (returns finish)]
  exact congrFun (hbaseFlat (((ingress start).append walk).append
    (returns finish))) (T.walkMap (returns start) point)

/-- The compressed forward and backward maps are mutually inverse on their
projectors, the concrete function-level content of the Karoubi-envelope
groupoid statement. -/
theorem compressed_maps_comp
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    {first second : V} :
    (T.ingressMap ingress first ∘ T.returnMap returns second) ∘
        (T.ingressMap ingress second ∘ T.returnMap returns first) =
      T.retractProjector ingress returns first := by
  funext point
  change T.ingressMap ingress first
      (T.returnMap returns second
        (T.ingressMap ingress second (T.returnMap returns first point))) =
    T.ingressMap ingress first (T.returnMap returns first point)
  rw [show T.returnMap returns second
      (T.ingressMap ingress second (T.returnMap returns first point)) =
      T.returnMap returns first point from
    congrFun (T.returnMap_comp_ingressMap ingress returns hbaseFlat second)
      (T.returnMap returns first point)]

end Retracts

end Transport

/-! ## Monoid-valued balance -/

section Monoid

variable {M : Type uM} [Monoid M] {label : E → M}

/-- Flatness only at one selected base. -/
def HasTrivialBaseLabels (G : EdgeGraph V E) (label : E → M) (base : V) : Prop :=
  ∀ cycle : G.Walk base base, walkLabel label cycle = 1

/-- In a directly finite monoid, one-base flatness on a strongly connected
graph propagates to every base. -/
theorem hasTrivialCycleLabels_of_base_of_dedekindFinite
    [IsDedekindFiniteMonoid M] {base : V}
    (hconnected : IsStronglyConnectedAt G base)
    (hbase : HasTrivialBaseLabels G label base) :
    HasTrivialCycleLabels G label := by
  intro vertex cycle
  let out := (hconnected vertex).1.some
  let back := (hconnected vertex).2.some
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

/-- Under global flatness, two parallel walks with a common return walk have equal labels.  This
is path independence of flat transport, read in the regular representation. -/
theorem walkLabel_eq_of_trivialCycleLabels_of_return
    (hflat : HasTrivialCycleLabels G label)
    {start finish : V} (first second : G.Walk start finish)
    (back : G.Walk finish start) :
    walkLabel label first = walkLabel label second := by
  simpa [walkMap_ofSMul_eq_walkLabel_smul] using
    congrFun ((ofSMul G M label).walkMap_eq_of_trivialHolonomy_of_return
      (hasTrivialHolonomy_ofSMul hflat) first second back) 1

/-- A **unit potential** for a monoid labelling: a unit-valued function on vertices whose ratio
across each edge is the label of that edge.  This is the multiplicative coboundary condition, and
it is the shape of every witness produced below. -/
def IsUnitPotential (G : EdgeGraph V E) (label : E → M) (potential : V → Mˣ) : Prop :=
  ∀ edge : E,
    label edge = (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ)

/-- Telescoping: along a walk whose every edge satisfies the coboundary equation of a unit
potential, the walk label is the ratio of the potential at the endpoints. -/
theorem walkLabel_eq_of_forall_mem_edges (potential : V → Mˣ) {start finish : V}
    (walk : G.Walk start finish)
    (hedge : ∀ edge ∈ walk.edges,
      label edge = (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ)) :
    walkLabel label walk = (potential finish * (potential start)⁻¹ : Mˣ) := by
  have h := (ofSMul G M label).walkMap_rel_of_forall_mem_edges
    (family := fun vertex => (potential vertex : M)) (R := fun _ => Eq) (fun _ => rfl)
    (fun _ => Eq.trans) walk (fun _ _ _ _ hxy => congrArg _ hxy) fun edge hmem => by
      change label edge * _ = _
      simp [hedge edge hmem, mul_assoc]
  rw [walkMap_ofSMul_eq_walkLabel_smul, smul_eq_mul] at h
  simp [← h, mul_assoc]

/-- The unit represented by the chosen out-and-back walks between a base and a linked
vertex.  Flatness makes the two composite labels mutually inverse. -/
noncomputable def linkedUnit (hflat : HasTrivialCycleLabels G label) {base vertex : V}
    (hlinked : LinkedTo G base vertex) : Mˣ where
  val := walkLabel label hlinked.1.some
  inv := walkLabel label hlinked.2.some
  val_inv := by simpa using hflat vertex (hlinked.2.some.append hlinked.1.some)
  inv_val := by simpa using hflat base (hlinked.1.some.append hlinked.2.some)

/-- The linked unit depends on the base only through its value. -/
theorem linkedUnit_congr (hflat : HasTrivialCycleLabels G label) {base base' vertex : V}
    (hbase : base = base') (hlinked : LinkedTo G base vertex)
    (hlinked' : LinkedTo G base' vertex) :
    linkedUnit hflat hlinked = linkedUnit hflat hlinked' := by
  subst hbase
  rfl

/-- An edge whose endpoints are linked to a common base carries the ratio of the linked
units at its endpoints. -/
theorem label_eq_linkedUnit (hflat : HasTrivialCycleLabels G label) {base : V} (edge : E)
    (hsource : LinkedTo G base (G.source edge)) (htarget : LinkedTo G base (G.target edge)) :
    label edge =
      (linkedUnit hflat htarget * (linkedUnit hflat hsource)⁻¹ : Mˣ) := by
  have hparallel := walkLabel_eq_of_trivialCycleLabels_of_return hflat
    (hsource.1.some.concat edge rfl) htarget.1.some htarget.2.some
  simp only [walkLabel_concat] at hparallel
  have hpathReturn : walkLabel label hsource.1.some * walkLabel label hsource.2.some = 1 := by
    simpa using hflat (G.source edge) (hsource.2.some.append hsource.1.some)
  change label edge = walkLabel label htarget.1.some * walkLabel label hsource.2.some
  rw [← hparallel, mul_assoc, hpathReturn, mul_one]

/-- **Component-wise coboundary.**  On the strongly connected component of a base vertex, a
flat monoid labelling is a unit-valued coboundary: one potential satisfies the coboundary
equation on every edge whose endpoints are linked to the base.  Vertices outside the component
receive the trivial unit. -/
theorem exists_unitPotential_on_component (hflat : HasTrivialCycleLabels G label) (base : V) :
    ∃ potential : V → Mˣ, ∀ edge : E,
      LinkedTo G base (G.source edge) → LinkedTo G base (G.target edge) →
        label edge = (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ) := by
  classical
  refine ⟨fun vertex ↦ if h : LinkedTo G base vertex then linkedUnit hflat h else 1,
    fun edge hsource htarget ↦ ?_⟩
  simp only [dite_eq_left hsource, dite_eq_left htarget]
  exact label_eq_linkedUnit hflat edge hsource htarget

/-- Every flat monoid labelling whose edge endpoints are all linked to a base
vertex is a unit-valued coboundary, even when the ambient monoid is not a group. -/
theorem exists_unitPotential_of_trivialCycleLabels {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃ potential : V → Mˣ, IsUnitPotential G label potential :=
  let ⟨potential, hpotential⟩ := exists_unitPotential_on_component hflat base
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
  rw [label_eq_linkedUnit hflat edge hsource (hrepresentative (G.target edge)),
    linkedUnit_congr hflat (hsame edge).symm hsource (hrepresentative (G.source edge))]

/-- A unit-valued coboundary has trivial labels on every closed walk. -/
theorem hasTrivialCycleLabels_of_unitPotential
    (potential : V → Mˣ) (hedge : IsUnitPotential G label potential) :
    HasTrivialCycleLabels G label := fun _ cycle ↦ by
  rw [walkLabel_eq_of_forall_mem_edges potential cycle fun edge _ ↦ hedge edge]
  simp

/-- Under flatness, an edge lying on a closed walk carries a unit label: its label and that of
the return walk are mutually inverse. -/
theorem isUnit_edge_of_trivialCycleLabels (hflat : HasTrivialCycleLabels G label) {edge : E}
    (back : G.Walk (G.target edge) (G.source edge)) : IsUnit (label edge) :=
  ⟨⟨label edge, walkLabel label back,
      by simpa using hflat (G.target edge) (back.append (.singleton edge)),
      by simpa using hflat (G.source edge) ((EdgeGraph.Walk.singleton edge).append back)⟩, rfl⟩

/-- On a strongly connected graph, flatness implies both parallel-path
equality and existence of a unit-valued potential; either conjunct separately
also characterizes flatness via the pairwise theorems in the normal-form API. -/
theorem hasTrivialCycleLabels_iff_parallelLabels_and_unitPotential {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    HasTrivialCycleLabels G label ↔
      (∀ {start finish : V} (first second : G.Walk start finish),
        walkLabel label first = walkLabel label second) ∧
      (∃ potential : V → Mˣ, IsUnitPotential G label potential) := by
  constructor
  · intro hflat
    refine ⟨?_, exists_unitPotential_of_trivialCycleLabels
      hconnected.edgeEndpointsLinkedTo hflat⟩
    intro start finish first second
    exact walkLabel_eq_of_trivialCycleLabels_of_return hflat first second
      (hconnected.nonempty_walk finish start).some
  · rintro ⟨_, potential, hedge⟩
    exact hasTrivialCycleLabels_of_unitPotential potential hedge

/-- A chosen root-and-return test.  It checks one equation at every edge; it is
not the smaller non-tree-edge test obtained from a specified arborescence.
The equations are inverse-free, and direct finiteness manufactures the missing
reverse identities during the proof. -/
theorem hasTrivialCycleLabels_of_chosen_tests
    [IsDedekindFiniteMonoid M] {base : V}
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (hreturn : ∀ vertex,
      walkLabel label (returns vertex) * walkLabel label (paths vertex) = 1)
    (hedge : ∀ edge,
      walkLabel label (returns (G.target edge)) * label edge *
          walkLabel label (paths (G.source edge)) = 1) :
    HasTrivialCycleLabels G label := by
  let potential : V → Mˣ := fun vertex ↦
    { val := walkLabel label (paths vertex)
      inv := walkLabel label (returns vertex)
      val_inv := mul_eq_one_comm.mp (hreturn vertex)
      inv_val := hreturn vertex }
  apply hasTrivialCycleLabels_of_unitPotential potential
  intro edge
  change label edge = walkLabel label (paths (G.target edge)) *
    walkLabel label (returns (G.source edge))
  have hreverse (vertex : V) :
      walkLabel label (paths vertex) * walkLabel label (returns vertex) = 1 :=
    mul_eq_one_comm.mp (hreturn vertex)
  calc
    label edge =
        (walkLabel label (paths (G.target edge)) *
            walkLabel label (returns (G.target edge))) * label edge *
          (walkLabel label (paths (G.source edge)) *
            walkLabel label (returns (G.source edge))) := by
      rw [hreverse, hreverse, one_mul, mul_one]
    _ = walkLabel label (paths (G.target edge)) *
        (walkLabel label (returns (G.target edge)) * label edge *
          walkLabel label (paths (G.source edge))) *
        walkLabel label (returns (G.source edge)) := by
      simp only [mul_assoc]
    _ = walkLabel label (paths (G.target edge)) *
        walkLabel label (returns (G.source edge)) := by
      rw [hedge, mul_one]

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
  refine ⟨fun vertex ↦ addUnitsOfUnits (potential vertex), fun edge ↦ ?_⟩
  have hedge : Multiplicative.ofAdd (weight edge) = _ := hpotential edge
  change ((potential (G.source edge) : Multiplicative A) *
    Multiplicative.ofAdd (weight edge)).toAdd = _
  rw [hedge, Units.val_mul, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  rfl

/-- Under zero cycle sums, an edge lying on a closed walk carries an additive unit. -/
theorem isAddUnit_edge_of_zeroCycleSums (hzero : HasZeroCycleSums G weight) {edge : E}
    (back : G.Walk (G.target edge) (G.source edge)) : IsAddUnit (weight edge) :=
  let ⟨unit, hunit⟩ :=
    isUnit_edge_of_trivialCycleLabels (hasTrivialCycleLabels_ofAdd_iff.2 hzero) back
  ⟨addUnitsOfUnits unit, congrArg Multiplicative.toAdd hunit⟩

end AdditiveMonoid

end Maths

end
