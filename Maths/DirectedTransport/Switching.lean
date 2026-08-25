/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs

import Maths.DirectedTransport.Exact
import Mathlib.Algebra.Group.Basic

/-!
# Switching and balance for gain graphs

A monoid-valued edge labelling of a directed multigraph is a gain function in the sense of
Zaslavsky, and switching is the classical way to modify a gain without changing which closed
walks are balanced: a vertex function `η` corrects the gain of each edge by the value of `η`
at the edge's target on the left and by the inverse of the value at its source on the right.

Classically the gains take values in a group and every vertex function into that group
switches.  Here the labels live in an arbitrary monoid, where transport is
one-directional and labels need not invert, so only *unit-valued* vertex functions can
switch: `Maths.switch` takes `η : V → Mˣ`.  Over a group every element is a unit
and the classical notion is recovered.

Switching corrects walk labels at their endpoints only
(`Maths.walkLabel_switch`), so balance - trivial labels on all closed walks,
`Maths.HasTrivialCycleLabels` - is a switching invariant.
`Maths.switch_switch` and `Maths.switch_one` make switching an
action of the group of unit-valued vertex functions on gains; it is stated as rewriting
lemmas, not as a `MulAction` instance, because the action depends on the edge graph,
not only on the types involved.

The main result says that when every edge endpoint is linked to a base vertex balance is
exactly switching-triviality: a gain has trivial cycle labels precisely when it is a switching of
the constant-one gain.  The switching function exhibited is the unit potential of
`Maths.exists_unitPotential_of_trivialCycleLabels`, and
`Maths.existsUnique_normalizedUnitPotential_of_trivialCycleLabels` measures its
uniqueness: the switching functions trivializing a flat gain form a torsor for the unit group.

## Main definitions

* `Maths.switch` - the switching of a gain by a unit-valued vertex function.

## Main results

* `Maths.walkLabel_switch` - walk labels transform by endpoint correction.
* `Maths.switch_switch` and `Maths.switch_one` - switching is an
  action of the group of unit-valued vertex functions on gains.
* `Maths.hasTrivialCycleLabels_switch_iff` - balance is a switching invariant.
* `Maths.hasTrivialCycleLabels_iff_exists_switch_one` - when every edge
  endpoint is linked to a base vertex, a gain is balanced exactly when it is a switching
  of the trivial gain.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory Ser. B 47
  (1989), 32-52, §5, for gains, switching and balance.

## Tags

gain graph, voltage graph, switching, balance, biased graph
-/

@[expose] public section

namespace Maths

universe uV uE uM

variable {V : Type uV} {E : Type uE} {M : Type uM} [Monoid M] {G : EdgeGraph V E}

/-! ### The switching action -/

/-- Switching of a gain by a unit-valued vertex function: the gain of an edge is corrected
by the unit at its target on the left and by the inverse of the unit at its source on the
right.  Restricting switching functions to units is what makes the notion meaningful over a
monoid; over a group it is Zaslavsky's classical switching. -/
def switch (G : EdgeGraph V E) (η : V → Mˣ) (label : E → M) : E → M :=
  fun edge => (η (G.target edge) : M) * label edge * Units.val (η (G.source edge))⁻¹

/-- The switched gain of one edge, unfolded. -/
@[simp] theorem switch_apply (η : V → Mˣ) (label : E → M) (edge : E) :
    switch G η label edge =
      (η (G.target edge) : M) * label edge * Units.val (η (G.source edge))⁻¹ := rfl

/-- Switching by the constant unit function leaves the gain unchanged. -/
@[simp] theorem switch_one (label : E → M) : switch G 1 label = label := by
  funext edge
  simp

/-- Switching by `θ` after switching by `η` is switching by the pointwise product `θ * η`.
Together with `Maths.switch_one` this makes switching an action of the group
`V → Mˣ` on gains; the action depends on `G`, so it is not registered as a `MulAction`. -/
theorem switch_switch (θ η : V → Mˣ) (label : E → M) :
    switch G θ (switch G η label) = switch G (θ * η) label := by
  funext edge
  simp only [switch_apply, Pi.mul_apply, Units.val_mul, mul_inv_rev, mul_assoc]

/-! ### Walk labels under switching -/

variable {label : E → M}

/-- Switching corrects the composite label of a walk by the units at its endpoints only:
the corrections at interior vertices cancel telescopically. -/
theorem walkLabel_switch (η : V → Mˣ) {start finish : V} (walk : G.Walk start finish) :
    walkLabel (switch G η label) walk =
      (η finish : M) * walkLabel label walk * Units.val (η start)⁻¹ := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkLabel_concat, ih, walkLabel_concat, switch_apply, legal]
      simp only [mul_assoc, Units.inv_mul_cancel_left]

/-! ### The trivial gain -/

/-- The trivial gain gives every walk the trivial label. -/
@[simp] theorem walkLabel_one {start finish : V} (walk : G.Walk start finish) :
    walkLabel (1 : E → M) walk = 1 := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [ih]

/-- The trivial gain is balanced. -/
theorem hasTrivialCycleLabels_one : HasTrivialCycleLabels G (1 : E → M) :=
  fun _ cycle => walkLabel_one cycle

/-! ### Balance as a switching invariant -/

/-- **Balance is a switching invariant.**  A gain and any of its switchings have trivial
labels on exactly the same closed walks. -/
theorem hasTrivialCycleLabels_switch_iff (η : V → Mˣ) :
    HasTrivialCycleLabels G (switch G η label) ↔ HasTrivialCycleLabels G label := by
  constructor <;> intro h vertex cycle
  · have hswitched := h vertex cycle
    rw [walkLabel_switch] at hswitched
    calc walkLabel label cycle
        = Units.val (η vertex)⁻¹ *
            ((η vertex : M) * walkLabel label cycle * Units.val (η vertex)⁻¹) *
              (η vertex : M) := by simp [mul_assoc]
      _ = Units.val (η vertex)⁻¹ * 1 * (η vertex : M) := by rw [hswitched]
      _ = 1 := by simp
  · rw [walkLabel_switch, h vertex cycle]
    simp

/-- **Balance is switching-triviality.**  When every edge endpoint is linked to a base
vertex, a monoid-valued gain is balanced exactly when it is a switching of the trivial
gain.  The switching function exhibited in the forward direction is the unit potential of
`Maths.exists_unitPotential_of_trivialCycleLabels`. -/
theorem hasTrivialCycleLabels_iff_exists_switch_one {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base) :
    HasTrivialCycleLabels G label ↔ ∃ η : V → Mˣ, label = switch G η 1 := by
  constructor
  · intro hflat
    obtain ⟨potential, hpotential⟩ :=
      exists_unitPotential_of_trivialCycleLabels hlinked hflat
    refine ⟨potential, funext fun edge => ?_⟩
    rw [hpotential edge, switch_apply, Pi.one_apply, mul_one, Units.val_mul]
  · rintro ⟨η, rfl⟩
    exact (hasTrivialCycleLabels_switch_iff η).mpr hasTrivialCycleLabels_one

end Maths
