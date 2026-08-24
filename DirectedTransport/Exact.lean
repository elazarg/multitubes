/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Basic
public import Mathlib.GroupTheory.DedekindFinite

/-!
# Exact directed transport beyond groups

Forward typed walks support exact directed transport without assuming that
edge labels form a group.  Parallel-walk equality is primitive, while
invertibility is derived on recurrent flat regions.

## Main definitions

* `DirectedTransport.Transport.RootReaches`: every vertex is reachable from a chosen base.
* `DirectedTransport.Transport.HasRootPathIndependence`: parallel walks out of the base
  agree.
* `DirectedTransport.Transport.IsSectionWithBase` and
  `DirectedTransport.Transport.rootedSection`: sections normalised at the base, and the
  canonical one built by transporting a base point.
* `DirectedTransport.Transport.IsBaseHolonomyFixed`: every closed walk at the base fixes
  the base fiber pointwise.
* `DirectedTransport.Transport.ingressMap`, `DirectedTransport.Transport.returnMap`, and
  `DirectedTransport.Transport.retractProjector`: the split retract data attached to
  chosen path families.
* `DirectedTransport.HasTrivialBaseLabels`: closed walks at one base carry trivial labels.
* `DirectedTransport.unitPotential` and `DirectedTransport.addUnitPotential`: the
  unit-valued potentials extracted from flat labels.

## Main results

* `DirectedTransport.Transport.hasRootPathIndependence_iff_unique_section`: rooted
  integrability without inverses.
* `DirectedTransport.Transport.walkMapEquivOfTrivialHolonomy` and
  `DirectedTransport.Transport.walkMap_eq_of_trivialHolonomy_of_stronglyConnected`:
  recurrence makes flat transport groupoidal.
* `DirectedTransport.Transport.existsUnique_section_of_base_fixed_of_injective_returns`:
  the sharp injective-return section criterion.
* `DirectedTransport.Transport.compressed_walkMap_eq`: one-base flatness is
  path-independent on chosen split retracts.
* `DirectedTransport.hasTrivialCycleLabels_of_base_of_dedekindFinite`: direct finiteness
  is the sufficient one-sided-inverse hypothesis used to move flatness between bases.
* `DirectedTransport.exists_unitPotential_of_trivialCycleLabels`: arbitrary monoid-valued
  flat labels on a strongly connected graph live in the unit group.
* `DirectedTransport.exists_addUnitPotential_of_zeroCycleSums`: the additive
  commutative-monoid version, requiring no ambient subtraction or group completion.
-/

@[expose] public section

noncomputable section

namespace DirectedTransport

universe uV uE uF uM uA

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} {T : Transport G Fiber}

/-! ## Rooted path independence and sections -/

namespace Transport

/-- Every vertex is reachable from `base` by a directed walk. -/
def RootReaches (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ vertex : V, Nonempty (G.Walk base vertex)

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

/-- Under global flatness, any two parallel walks have equal monoid labels. -/
theorem walkLabel_eq_of_trivialCycleLabels_of_return
    (hflat : HasTrivialCycleLabels G label)
    {start finish : V} (first second : G.Walk start finish)
    (back : G.Walk finish start) :
    walkLabel label first = walkLabel label second := by
  have hsecond : walkLabel label back * walkLabel label second = 1 := by
    simpa using hflat start (second.append back)
  exact left_inv_eq_right_inv
    (by simpa using hflat finish (back.append first)) hsecond

/-- The unit represented by any chosen root-to-vertex walk. -/
def unitPotential (hflat : HasTrivialCycleLabels G label) {base : V}
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) : Mˣ where
  val := walkLabel label (paths vertex)
  inv := walkLabel label (returns vertex)
  val_inv := by simpa using hflat vertex ((returns vertex).append (paths vertex))
  inv_val := by simpa using hflat base ((paths vertex).append (returns vertex))

/-- Every flat monoid labelling on a strongly connected graph is a
unit-valued coboundary, even when the ambient monoid is not a group. -/
theorem exists_unitPotential_of_trivialCycleLabels {base : V}
    (hconnected : IsStronglyConnectedAt G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃ potential : V → Mˣ, ∀ edge : E,
      label edge =
        (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ) := by
  let paths : ∀ vertex, G.Walk base vertex :=
    fun vertex ↦ (hconnected vertex).1.some
  let returns : ∀ vertex, G.Walk vertex base :=
    fun vertex ↦ (hconnected vertex).2.some
  let potential : V → Mˣ := unitPotential hflat paths returns
  refine ⟨potential, fun edge ↦ ?_⟩
  have hparallel := walkLabel_eq_of_trivialCycleLabels_of_return hflat
    ((paths (G.source edge)).concat edge rfl) (paths (G.target edge))
    (returns (G.target edge))
  simp only [walkLabel_concat] at hparallel
  have hpathReturn : walkLabel label (paths (G.source edge)) *
      walkLabel label (returns (G.source edge)) = 1 := by
    simpa using hflat (G.source edge)
      ((returns (G.source edge)).append (paths (G.source edge)))
  change label edge = walkLabel label (paths (G.target edge)) *
    walkLabel label (returns (G.source edge))
  calc
    label edge = label edge *
        (walkLabel label (paths (G.source edge)) *
          walkLabel label (returns (G.source edge))) := by rw [hpathReturn, mul_one]
    _ = (label edge * walkLabel label (paths (G.source edge))) *
        walkLabel label (returns (G.source edge)) := by rw [mul_assoc]
    _ = walkLabel label (paths (G.target edge)) *
        walkLabel label (returns (G.source edge)) := by rw [hparallel]

/-- A unit-valued coboundary has trivial labels on every closed walk. -/
theorem hasTrivialCycleLabels_of_unitPotential
    (potential : V → Mˣ)
    (hedge : ∀ edge : E,
      label edge =
        (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ)) :
    HasTrivialCycleLabels G label := by
  have hwalk {start finish : V} (walk : G.Walk start finish) :
      walkLabel label walk =
        (potential finish * (potential start)⁻¹ : Mˣ) := by
    induction walk with
    | nil => simp
    | @concat middle walk edge legal ih =>
        rw [walkLabel_concat, hedge edge, ih, legal]
        have hunits :
            (potential (G.target edge) * (potential middle)⁻¹) *
                (potential middle * (potential start)⁻¹) =
              potential (G.target edge) * (potential start)⁻¹ := by
          simp
        exact congrArg (fun unit : Mˣ ↦ (unit : M)) hunits
  intro vertex cycle
  rw [hwalk cycle]
  simp

/-- On a strongly connected graph, flatness implies both parallel-path
equality and existence of a unit-valued potential; either conjunct separately
also characterizes flatness via the pairwise theorems in the normal-form API. -/
theorem hasTrivialCycleLabels_iff_parallelLabels_and_unitPotential {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    HasTrivialCycleLabels G label ↔
      (∀ {start finish : V} (first second : G.Walk start finish),
        walkLabel label first = walkLabel label second) ∧
      (∃ potential : V → Mˣ, ∀ edge : E,
        label edge =
          (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ)) := by
  constructor
  · intro hflat
    refine ⟨?_, exists_unitPotential_of_trivialCycleLabels hconnected hflat⟩
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

/-! ## Additive commutative monoids -/

section AdditiveMonoid

variable {A : Type uA} [AddCommMonoid A] {weight : E → A}

/-- A zero-cycle sum makes the sum along any root path an additive unit. -/
def addUnitPotential {base : V}
    (hzero : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSum weight cycle = 0)
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) (vertex : V) : AddUnits A where
  val := walkSum weight (paths vertex)
  neg := walkSum weight (returns vertex)
  val_neg := by simpa using hzero base ((paths vertex).append (returns vertex))
  neg_val := by simpa using hzero vertex ((returns vertex).append (paths vertex))

/-- Zero circulation in an arbitrary additive commutative monoid forces all
recurrent edge data into its additive unit group. -/
theorem exists_addUnitPotential_of_zeroCycleSums {base : V}
    (hconnected : IsStronglyConnectedAt G base)
    (hzero : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSum weight cycle = 0) :
    ∃ potential : V → AddUnits A, ∀ edge : E,
      (potential (G.source edge) : A) + weight edge =
        potential (G.target edge) := by
  let paths : ∀ vertex, G.Walk base vertex :=
    fun vertex ↦ (hconnected vertex).1.some
  let returns : ∀ vertex, G.Walk vertex base :=
    fun vertex ↦ (hconnected vertex).2.some
  let potential : V → AddUnits A := addUnitPotential hzero paths returns
  refine ⟨potential, fun edge ↦ ?_⟩
  change walkSum weight (paths (G.source edge)) + weight edge =
    walkSum weight (paths (G.target edge))
  have hleft := hzero base
    (((paths (G.source edge)).concat edge rfl).append
      (returns (G.target edge)))
  have hright := hzero base
    ((paths (G.target edge)).append (returns (G.target edge)))
  simp only [walkSum_append, walkSum_concat] at hleft hright
  calc
    walkSum weight (paths (G.source edge)) + weight edge =
        (walkSum weight (paths (G.source edge)) + weight edge) + 0 := by simp
    _ = (walkSum weight (paths (G.source edge)) + weight edge) +
        (walkSum weight (returns (G.target edge)) +
          walkSum weight (paths (G.target edge))) := by
      rw [add_comm (walkSum weight (returns (G.target edge))), hright]
    _ = ((walkSum weight (paths (G.source edge)) + weight edge) +
        walkSum weight (returns (G.target edge))) +
          walkSum weight (paths (G.target edge)) := by
      ac_rfl
    _ = walkSum weight (paths (G.target edge)) := by rw [hleft, zero_add]

/-- Every individual edge weight is an additive unit under zero circulation. -/
theorem isAddUnit_edge_of_zeroCycleSums {base : V}
    (hconnected : IsStronglyConnectedAt G base)
    (hzero : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkSum weight cycle = 0) (edge : E) :
    IsAddUnit (weight edge) := by
  let back := (hconnected.nonempty_walk (G.target edge) (G.source edge)).some
  refine ⟨⟨weight edge, walkSum weight back, ?_, ?_⟩, rfl⟩
  · simpa using hzero (G.source edge)
      ((EdgeGraph.Walk.singleton (G := G) edge).append back)
  · simpa using hzero (G.target edge)
      (back.append (EdgeGraph.Walk.singleton (G := G) edge))

end AdditiveMonoid

end DirectedTransport

end
