/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Exact

/-!
# Rigidity of monoid-valued transport potentials

On a rooted reachable graph, two unit-valued coboundary potentials for the
same monoid labelling differ by one global right factor.  Thus flat transport
on a strongly connected graph has a unique potential after fixing its value at
one vertex.  This identifies the potential space as a torsor for the unit group
even though the ambient labels live in an arbitrary monoid.

## Main results

* `Maths.trivialCycleLabels_iff_chosen_root_return_tests` and
  `Maths.hasTrivialCycleLabels_iff_parallelLabels`: reformulations of flatness
  over a reachable root.
* `Maths.hasTrivialCycleLabels_iff_exists_unitPotential`: flatness is exactly
  the existence of a unit-valued coboundary potential.
* `Maths.isUnit_edge_of_trivialCycleLabels`: every edge label is a unit as
  soon as its endpoints are linked to a base vertex.
* `Maths.unitPotential_ratio_eq_of_rootReaches`: **the ratio of two potentials for
  the same labelling is constant** on the vertices reachable from the base.
* `Maths.unitPotential_eq_mul_constant_of_rootReaches`: two potentials for the
  same labelling differ by one global right factor, that constant ratio.
* `Maths.unitPotential_eq_of_rootReaches_of_eq_base`: agreement at the root
  forces agreement everywhere.
* `Maths.existsUnique_normalizedUnitPotential_of_trivialCycleLabels`: the
  potential normalised at the root is unique, so the potential space is a torsor for the
  unit group.
-/

@[expose] public section

noncomputable section

namespace Maths

universe uV uE uM

variable {V : Type uV} {E : Type uE} {M : Type uM}
variable {G : EdgeGraph V E} [Monoid M] {label : E → M}

/-- Arbitrary chosen root/return walks give a complete finite-style test for
global flatness in a directly finite monoid.  No tree or arborescence
invariants are required: the vertex return loops and one loop per edge are
necessary and sufficient. -/
theorem trivialCycleLabels_iff_chosen_root_return_tests
    [IsDedekindFiniteMonoid M] {base : V}
    (paths : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base) :
    HasTrivialCycleLabels G label ↔
      (∀ vertex,
        walkLabel label (returns vertex) * walkLabel label (paths vertex) = 1) ∧
      ∀ edge,
        walkLabel label (returns (G.target edge)) * label edge *
          walkLabel label (paths (G.source edge)) = 1 := by
  constructor
  · intro hflat
    refine ⟨fun vertex => ?_, fun edge => ?_⟩
    · simpa using hflat base ((paths vertex).append (returns vertex))
    · simpa [mul_assoc] using hflat base
        (((paths (G.source edge)).concat edge rfl).append
          (returns (G.target edge)))
  · rintro ⟨hreturn, hedge⟩
    exact hasTrivialCycleLabels_of_chosen_tests paths returns hreturn hedge

/-- On a strongly connected graph, global trivial cycle labels are equivalent
to equality of every pair of parallel walk labels. -/
theorem hasTrivialCycleLabels_iff_parallelLabels {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    HasTrivialCycleLabels G label ↔
      ∀ {start finish : V} (first second : G.Walk start finish),
        walkLabel label first = walkLabel label second := by
  constructor
  · intro hflat start finish first second
    exact walkLabel_eq_of_trivialCycleLabels_of_return hflat first second
      (hconnected.nonempty_walk finish start).some
  · intro hparallel vertex cycle
    simpa using hparallel cycle (.nil : G.Walk vertex vertex)

/-- When every edge endpoint is linked to a base vertex, flatness is equivalent
to existence of a unit-valued coboundary potential. -/
theorem hasTrivialCycleLabels_iff_exists_unitPotential {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base) :
    HasTrivialCycleLabels G label ↔
      ∃ potential : V → Mˣ, ∀ edge : E,
        label edge =
          (potential (G.target edge) *
            (potential (G.source edge))⁻¹ : Mˣ) := by
  exact ⟨exists_unitPotential_of_trivialCycleLabels hlinked,
    fun ⟨potential, hpotential⟩ => hasTrivialCycleLabels_of_unitPotential potential hpotential⟩

/-- Every recurrent edge label is a unit under global flatness. -/
theorem isUnit_edge_of_trivialCycleLabels {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hflat : HasTrivialCycleLabels G label) (edge : E) :
    IsUnit (label edge) := by
  obtain ⟨potential, hpotential⟩ :=
    exists_unitPotential_of_trivialCycleLabels hlinked hflat
  refine ⟨potential (G.target edge) *
    (potential (G.source edge))⁻¹, ?_⟩
  exact (hpotential edge).symm

private theorem unit_ratio_eq_of_edge
    (first second : V → Mˣ)
    (hfirst : IsUnitPotential G label first)
    (hsecond : IsUnitPotential G label second)
    (edge : E) :
    (second (G.target edge))⁻¹ * first (G.target edge) =
      (second (G.source edge))⁻¹ * first (G.source edge) := by
  have hedge :
      first (G.target edge) * (first (G.source edge))⁻¹ =
        second (G.target edge) * (second (G.source edge))⁻¹ := by
    apply Units.ext
    exact (hfirst edge).symm.trans (hsecond edge)
  calc
    (second (G.target edge))⁻¹ * first (G.target edge) =
        (second (G.target edge))⁻¹ *
          (first (G.target edge) * (first (G.source edge))⁻¹) *
            first (G.source edge) := by
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = (second (G.target edge))⁻¹ *
          (second (G.target edge) * (second (G.source edge))⁻¹) *
            first (G.source edge) := by rw [hedge]
    _ = (second (G.source edge))⁻¹ * first (G.source edge) := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- **The ratio of two unit potentials is constant.**  On every vertex reachable from the base
the pointwise ratio of two potentials for the same labels is the same unit, namely its value at
the base: each edge of a walk out of the base leaves the ratio unchanged, because both potentials
cross that edge by the same label. -/
theorem unitPotential_ratio_eq_of_rootReaches {base : V}
    (hreaches : Transport.RootReaches G base)
    (first second : V → Mˣ)
    (hfirst : IsUnitPotential G label first)
    (hsecond : IsUnitPotential G label second) (vertex : V) :
    (second vertex)⁻¹ * first vertex = (second base)⁻¹ * first base := by
  induction (hreaches vertex).some with
  | nil => rfl
  | @concat finish path edge legal ih =>
      subst legal
      exact (unit_ratio_eq_of_edge first second hfirst hsecond edge).trans ih

/-- Two potentials for the same labels differ by one global right unit on
every vertex reachable from the base.  This is the constant ratio of
`Maths.unitPotential_ratio_eq_of_rootReaches` moved to the other side. -/
theorem unitPotential_eq_mul_constant_of_rootReaches {base : V}
    (hreaches : Transport.RootReaches G base)
    (first second : V → Mˣ)
    (hfirst : IsUnitPotential G label first)
    (hsecond : IsUnitPotential G label second) :
    ∀ vertex : V,
      first vertex = second vertex * ((second base)⁻¹ * first base) := by
  intro vertex
  calc
    first vertex =
        second vertex * ((second vertex)⁻¹ * first vertex) := by simp
    _ = second vertex * ((second base)⁻¹ * first base) := by
      rw [unitPotential_ratio_eq_of_rootReaches hreaches first second hfirst hsecond vertex]

/-- In particular, base-normalized potentials are unique. -/
theorem unitPotential_eq_of_rootReaches_of_eq_base {base : V}
    (hreaches : Transport.RootReaches G base)
    (first second : V → Mˣ)
    (hfirst : IsUnitPotential G label first)
    (hsecond : IsUnitPotential G label second)
    (hbase : first base = second base) :
    first = second := by
  funext vertex
  rw [unitPotential_eq_mul_constant_of_rootReaches
    hreaches first second hfirst hsecond vertex, hbase]
  simp

/-- Flat monoid transport on a strongly connected graph has one and only one
base-normalized unit potential. -/
theorem existsUnique_normalizedUnitPotential_of_trivialCycleLabels
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃! potential : V → Mˣ,
      potential base = 1 ∧
        ∀ edge : E,
          label edge =
            (potential (G.target edge) *
              (potential (G.source edge))⁻¹ : Mˣ) := by
  obtain ⟨potential, hpotential⟩ :=
    exists_unitPotential_of_trivialCycleLabels
      hconnected.edgeEndpointsLinkedTo hflat
  let normalized : V → Mˣ :=
    fun vertex => potential vertex * (potential base)⁻¹
  have hnormalized (edge : E) :
      label edge =
        (normalized (G.target edge) *
          (normalized (G.source edge))⁻¹ : Mˣ) := by
    rw [hpotential edge]
    apply congrArg fun unit : Mˣ => (unit : M)
    simp [normalized]
  refine ⟨normalized, ⟨by simp [normalized], hnormalized⟩, ?_⟩
  intro other hother
  apply unitPotential_eq_of_rootReaches_of_eq_base
    (fun vertex => (hconnected vertex).1)
    other normalized hother.2 hnormalized
  rw [hother.1]
  simp [normalized]

end Maths

end
