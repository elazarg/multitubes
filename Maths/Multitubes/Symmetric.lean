/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Exact
public import Maths.Multitubes.Switching
public import Mathlib.Logic.Equiv.Defs

/-!
# Symmetric transport: classical gain graphs and bijective constraints

Classical gain graphs are undirected: an edge may be traversed against its orientation, and
then carries the inverse gain.  Directed closed walks do not see this, so balance in the sense
of `Maths.HasTrivialCycleLabels` is weaker on a general directed graph; on a directed acyclic
graph every gain is vacuously balanced.  The classical notions are recovered on the
symmetrization `Maths.EdgeGraph.symmetrization`, whose backward orientations carry the
inverse labels.  Every edge of the symmetrization lies on a closed walk, so component-wise
coboundary reconstruction applies without any connectivity hypothesis.

* For unit-valued gains, `Maths.symmetricGain` labels the backward orientation by the inverse
  unit.  Its balance on the symmetrization is exactly switching-triviality of the original gain
  (`Maths.hasTrivialCycleLabels_symmetricGain_iff`): Zaslavsky's balance theorem, for gains in
  the unit group of an arbitrary monoid, on an arbitrary graph.
* For dependent bijections on fibers, `Maths.Transport.ofEquivs` transports backward
  along the inverse bijection.  Its sections are the assignments satisfying every edge
  constraint (`Maths.Transport.isSection_ofEquivs_iff`).  On a connected graph, evaluation at
  a base vertex identifies them with the points fixed by every base holonomy
  (`Maths.Transport.ofEquivsSectionEquiv`).

A constraint system whose every constraint is a bijection between the values of its two
variables, such as a Unique Games instance, is satisfiable exactly when the base holonomy group
has a fixed point, and its solutions correspond to those fixed points.  This is weaker than
balance: a single vertex with a loop labelled by a transposition of three letters is satisfied
by the remaining letter, yet its gain is unbalanced.  The two notions agree when the labels act
simply transitively, as for linear equations modulo `k`.

## Main definitions

* `Maths.symmetricGain`: a unit-valued gain extended to the symmetrization by inverses.
* `Maths.Transport.ofEquivs`: transport by fiber bijections on the symmetrization.

## Main results

* `Maths.hasTrivialCycleLabels_symmetricGain_iff`: classical balance is switching-triviality.
* `Maths.Transport.isSection_ofEquivs_iff`: sections of the symmetric transport are the
  assignments satisfying every forward constraint.
* `Maths.Transport.ofEquivsSectionEquiv`: on a connected graph, solutions correspond to the
  common fixed points of the base holonomies.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory Ser. B 47
  (1989), 32-52.
* S. Khot, *On the power of unique 2-prover 1-round games*, STOC 2002.

## Tags

gain graph, balance, switching, symmetrization, unique games, constraint satisfaction
-/

@[expose] public section

namespace Maths

universe uV uE uM uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Classical balance -/

section Gain

variable {M : Type uM} [Monoid M]

/-- A unit-valued gain extended to the symmetrization: the forward orientation of an edge
carries its gain, the backward orientation the inverse gain. -/
def symmetricGain (gain : E → Mˣ) : E × Bool → M
  | (edge, false) => gain edge
  | (edge, true) => ((gain edge)⁻¹ : Mˣ)

@[simp] theorem symmetricGain_false (gain : E → Mˣ) (edge : E) :
    symmetricGain gain (edge, false) = gain edge := rfl

@[simp] theorem symmetricGain_true (gain : E → Mˣ) (edge : E) :
    symmetricGain gain (edge, true) = ((gain edge)⁻¹ : Mˣ) := rfl

/-- **Zaslavsky's balance theorem.**  A unit-valued gain is balanced in the classical,
undirected sense exactly when it is a switching of the trivial gain.  No connectivity is
assumed. -/
theorem hasTrivialCycleLabels_symmetricGain_iff (gain : E → Mˣ) :
    HasTrivialCycleLabels G.symmetrization (symmetricGain gain) ↔
      ∃ η : V → Mˣ, (fun edge => (gain edge : M)) = switch G η 1 := by
  rw [hasTrivialCycleLabels_iff_exists_switch_one_of_hasEdgeReturns
    EdgeGraph.symmetrization_hasEdgeReturns]
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η, funext fun edge => by simpa using congrFun hη (edge, false)⟩
  · rintro ⟨η, hη⟩
    refine ⟨η, funext ?_⟩
    rintro ⟨edge, _ | _⟩
    · simpa using congrFun hη edge
    · have hunit : gain edge = η (G.target edge) * (η (G.source edge))⁻¹ :=
        Units.ext (by simpa using congrFun hη edge)
      simp [hunit]

end Gain

/-! ### Bijective constraints -/

namespace Transport

variable {Fiber : V → Type uF}

/-- Transport by fiber bijections on the symmetrization: forward along each bijection,
backward along its inverse. -/
def ofEquivs (constraint : ∀ edge, Fiber (G.source edge) ≃ Fiber (G.target edge)) :
    Transport G.symmetrization Fiber where
  edgeMap
    | (edge, false) => constraint edge
    | (edge, true) => (constraint edge).symm

variable (constraint : ∀ edge, Fiber (G.source edge) ≃ Fiber (G.target edge))

/-- Every edge map of the symmetric transport is injective. -/
theorem ofEquivs_edgeMap_injective (edge : E × Bool) :
    Function.Injective ((ofEquivs constraint).edgeMap edge) := by
  rcases edge with ⟨edge, _ | _⟩
  · exact (constraint edge).injective
  · exact (constraint edge).symm.injective

/-- The sections of the symmetric transport are the assignments satisfying every forward
constraint; the backward constraints are then automatic. -/
theorem isSection_ofEquivs_iff (family : ∀ vertex, Fiber vertex) :
    (ofEquivs constraint).IsSection family ↔
      ∀ edge, constraint edge (family (G.source edge)) = family (G.target edge) := by
  constructor
  · intro hsection edge
    exact hsection (edge, false)
  · rintro hconstraint ⟨edge, _ | _⟩
    · exact hconstraint edge
    · exact (Equiv.symm_apply_eq _).mpr (hconstraint edge).symm

/-- **Solutions are holonomy fixed points.**  On a connected graph, evaluation at a base
vertex is a bijection from the assignments satisfying every bijective constraint to the
points fixed by every base holonomy of the symmetric transport. -/
noncomputable def ofEquivsSectionEquiv {base : V}
    (hconnected : IsStronglyConnectedAt G.symmetrization base) :
    {family : ∀ vertex, Fiber vertex // (ofEquivs constraint).IsSection family} ≃
      {point : Fiber base // (ofEquivs constraint).IsBaseHolonomyFixed base point} where
  toFun family := ⟨family.1 base, fun cycle => family.2.holonomy_eq cycle⟩
  invFun point :=
    let hunique := existsUnique_section_of_base_fixed_of_injective_returns hconnected
      point.1 point.2 (fun vertex => (hconnected vertex).2.some)
      (fun vertex => walkMap_injective (ofEquivs_edgeMap_injective constraint) _)
    ⟨hunique.exists.choose, hunique.exists.choose_spec.1⟩
  left_inv family := by
    have hunique := existsUnique_section_of_base_fixed_of_injective_returns hconnected
      (family.1 base) (fun cycle => family.2.holonomy_eq cycle)
      (fun vertex => (hconnected vertex).2.some)
      (fun vertex => walkMap_injective (ofEquivs_edgeMap_injective constraint) _)
    exact Subtype.ext (hunique.unique hunique.exists.choose_spec ⟨family.2, rfl⟩)
  right_inv point := by
    have hunique := existsUnique_section_of_base_fixed_of_injective_returns hconnected
      point.1 point.2 (fun vertex => (hconnected vertex).2.some)
      (fun vertex => walkMap_injective (ofEquivs_edgeMap_injective constraint) _)
    exact Subtype.ext hunique.exists.choose_spec.2

end Transport

end Maths
