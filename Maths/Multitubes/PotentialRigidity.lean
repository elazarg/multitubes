/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Exact

/-!
# Rigidity of monoid-valued transport potentials

A unit potential stays a unit potential when multiplied on the right by a constant unit.  On a
rooted reachable graph this is the only freedom: two unit-valued coboundary potentials for the
same monoid labelling differ by one global right factor.  Thus flat transport on a strongly
connected graph has a unique potential after fixing its value at one vertex, and the potentials
form a torsor for the unit group, even though the ambient labels live in an arbitrary monoid.

## Main results

* `Maths.hasTrivialCycleLabels_iff_parallelLabels`: on a strongly connected graph, flatness is
  equality of the labels of parallel walks.
* `Maths.IsUnitPotential.mul_const`: right multiplication by a unit preserves unit potentials.
* `Maths.unitPotential_ratio_eq_of_rootReaches`: **the ratio of two potentials for
  the same labelling is constant** on the vertices reachable from the base.
* `Maths.unitPotential_eq_mul_constant_of_rootReaches`: two potentials for the
  same labelling differ by one global right factor, that constant ratio.
* `Maths.unitPotential_eq_of_rootReaches_of_eq_base`: agreement at the root
  forces agreement everywhere.
* `Maths.existsUnique_normalizedUnitPotential_of_trivialCycleLabels`: the
  potential normalized at the root is unique, so the potential space is a torsor for the
  unit group.
-/

@[expose] public section

noncomputable section

namespace Maths

universe uV uE uM

variable {V : Type uV} {E : Type uE} {M : Type uM}
variable {G : EdgeGraph V E} [Monoid M] {label : E → M}

/-- On a strongly connected graph, global trivial cycle labels are equivalent
to equality of every pair of parallel walk labels. -/
theorem hasTrivialCycleLabels_iff_parallelLabels {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    HasTrivialCycleLabels G label ↔
      ∀ {start finish : V} (first second : G.Walk start finish),
        walkLabel label first = walkLabel label second := by
  constructor
  · intro hflat start finish first second
    exact walkLabel_eq_of_trivialCycleLabels_of_return (hflat _) (hflat _) first second
      (hconnected.nonempty_walk finish start).some
  · intro hparallel vertex cycle
    simpa using hparallel cycle (.nil : G.Walk vertex vertex)

/-- Right multiplication by a constant unit preserves unit potentials. -/
theorem IsUnitPotential.mul_const {potential : V → Mˣ}
    (hpotential : IsUnitPotential G label potential) (constant : Mˣ) :
    IsUnitPotential G label fun vertex => potential vertex * constant := fun edge => by
  change label edge * ((potential _ * constant : Mˣ) : M) = ((potential _ * constant : Mˣ) : M)
  rw [Units.val_mul, Units.val_mul, ← mul_assoc, ← isUnitPotential_iff.mp hpotential edge]

/-- Two potentials for one labelling have the same ratio at both endpoints of every edge. -/
private theorem unit_ratio_eq_of_edge {first second : V → Mˣ}
    (hfirst : IsUnitPotential G label first) (hsecond : IsUnitPotential G label second)
    (edge : E) :
    (second (G.target edge))⁻¹ * first (G.target edge) =
      (second (G.source edge))⁻¹ * first (G.source edge) := by
  have hedge :
      first (G.target edge) * (first (G.source edge))⁻¹ =
        second (G.target edge) * (second (G.source edge))⁻¹ :=
    Units.ext ((isUnitPotential_iff_label_eq.mp hfirst edge).symm.trans
      (isUnitPotential_iff_label_eq.mp hsecond edge))
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
    (hreaches : RootReaches G base) {first second : V → Mˣ}
    (hfirst : IsUnitPotential G label first) (hsecond : IsUnitPotential G label second)
    (vertex : V) :
    (second vertex)⁻¹ * first vertex = (second base)⁻¹ * first base := by
  induction (hreaches vertex).some with
  | nil => rfl
  | concat edge path ih => exact (unit_ratio_eq_of_edge hfirst hsecond edge).trans ih

/-- Two potentials for the same labels differ by one global right unit on
every vertex reachable from the base.  This is the constant ratio of
`Maths.unitPotential_ratio_eq_of_rootReaches` moved to the other side. -/
theorem unitPotential_eq_mul_constant_of_rootReaches {base : V}
    (hreaches : RootReaches G base) {first second : V → Mˣ}
    (hfirst : IsUnitPotential G label first) (hsecond : IsUnitPotential G label second)
    (vertex : V) :
    first vertex = second vertex * ((second base)⁻¹ * first base) := by
  rw [← unitPotential_ratio_eq_of_rootReaches hreaches hfirst hsecond vertex,
    mul_inv_cancel_left]

/-- In particular, base-normalized potentials are unique. -/
theorem unitPotential_eq_of_rootReaches_of_eq_base {base : V}
    (hreaches : RootReaches G base) {first second : V → Mˣ}
    (hfirst : IsUnitPotential G label first) (hsecond : IsUnitPotential G label second)
    (hbase : first base = second base) :
    first = second := by
  funext vertex
  rw [unitPotential_eq_mul_constant_of_rootReaches hreaches hfirst hsecond vertex, hbase,
    inv_mul_cancel, mul_one]

/-- Flat monoid transport on a strongly connected graph has one and only one
base-normalized unit potential. -/
theorem existsUnique_normalizedUnitPotential_of_trivialCycleLabels
    {base : V} (hconnected : IsStronglyConnectedAt G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃! potential : V → Mˣ, potential base = 1 ∧ IsUnitPotential G label potential := by
  obtain ⟨potential, hpotential⟩ :=
    exists_unitPotential_of_trivialCycleLabels hconnected.edgeEndpointsLinkedTo hflat
  refine ⟨fun vertex => potential vertex * (potential base)⁻¹,
    ⟨mul_inv_cancel _, hpotential.mul_const _⟩, fun other hother => ?_⟩
  exact unitPotential_eq_of_rootReaches_of_eq_base (fun vertex => (hconnected vertex).1)
    hother.2 (hpotential.mul_const _) (hother.1.trans (mul_inv_cancel _).symm)

end Maths

end
