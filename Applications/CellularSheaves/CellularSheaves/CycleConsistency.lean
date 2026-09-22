/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import CellularSheaves.OptimalTolerance
public import Maths.Multitubes.Additive.MixedQuantitative

/-!
# Cycle characterization of unit-scale sensor consistency

When both endpoint scales are one, an affine sensor discrepancy is the absolute additive defect
of its offset-labelled edge. Exact-mode laxification replaces each comparison by its two signed
directions. Uniform consistency is therefore equivalent to a mean bound on every closed walk of
this signed graph.

The characterization includes networks with no edges. Adding nonnegativity gives the existing
uniform-tolerance set, and a positive-length cycle attaining the proposed bound certifies that
the tolerance is optimal.

## Main definitions

* `CellularSheaves.RationalSensorNetwork.signedComparisonGraph`: the doubled directed graph.
* `CellularSheaves.RationalSensorNetwork.signedComparisonWeight`: signed real offsets.

## Main results

* `CellularSheaves.RationalSensorNetwork.exists_isConsistent_uniform_iff_closedWalk_le`:
  uniform consistency is exactly the closed-walk mean bound.
* `CellularSheaves.RationalSensorNetwork.mem_uniformToleranceLevels_iff_closedWalk_le`:
  nonnegative feasible tolerances have the same cycle characterization.
* `CellularSheaves.RationalSensorNetwork.minimumUniformTolerance_eq_of_cycle`:
  a consistent reading and a saturating nonempty signed cycle certify optimality.

## Tags

cellular sheaf, sensor consistency, cycle mean, additive residual, optimal tolerance
-/

@[expose] public section

namespace CellularSheaves.RationalSensorNetwork

open Maths

variable {n m : ℕ}

/-- Treat every sensor comparison as an exact additive constraint. -/
def exactMode (_ : Fin m) : EdgeMode := .exact

/-- The signed doubled graph of a unit-scale sensor network. -/
abbrev signedComparisonGraph (network : RationalSensorNetwork n m) :=
  Transport.laxificationGraph network.graph (exactMode (m := m))

/-- Signed real offsets on the doubled comparison graph. -/
def signedComparisonWeight (network : RationalSensorNetwork n m) :
    Transport.LaxificationEdge (exactMode (m := m)) → ℝ :=
  MixedAdditiveTransport.laxifiedWeight (exactMode (m := m))
    fun edge => (network.offset edge : ℝ)

private theorem exists_isConsistent_uniform_iff_mixedResidual
    (network : RationalSensorNetwork n m)
    (hsource : ∀ edge, network.sourceScale edge = 1)
    (htarget : ∀ edge, network.targetScale edge = 1) (level : ℝ) :
    (∃ reading, network.IsConsistent (fun _ => level) reading) ↔
      MixedAdditiveTransport.MixedResidualAtMost network.graph (exactMode (m := m))
        (fun edge => (network.offset edge : ℝ)) level := by
  apply exists_congr
  intro reading
  apply forall_congr'
  intro edge
  simp only [exactMode, MaxPlusPotential.defect]
  rw [hsource edge, htarget edge]
  norm_num
  rw [abs_sub_comm]
  simp [graph]

/-- Unit-scale uniform consistency holds exactly when every signed closed walk has weight at
most its length times the tolerance. -/
theorem exists_isConsistent_uniform_iff_closedWalk_le
    (network : RationalSensorNetwork n m)
    (hsource : ∀ edge, network.sourceScale edge = 1)
    (htarget : ∀ edge, network.targetScale edge = 1) (level : ℝ) :
    (∃ reading, network.IsConsistent (fun _ => level) reading) ↔
      ∀ (vertex : Fin n) (cycle : network.signedComparisonGraph.Walk vertex vertex),
        MaxPlusPotential.walkWeight network.signedComparisonWeight cycle ≤
          cycle.length * level := by
  let forgetSign : Transport.LaxificationEdge (exactMode (m := m)) → Fin m ⊕ Fin m
    | .inl edge => .inl edge.1
    | .inr edge => .inr edge.1
  let _ : Finite (Transport.LaxificationEdge (exactMode (m := m))) :=
    Finite.of_injective forgetSign (by
      intro first second heq
      rcases first with first | first <;> rcases second with second | second
      · simp only [forgetSign, Sum.inl.injEq] at heq
        exact congrArg Sum.inl (Subtype.ext heq)
      · simp only [forgetSign] at heq
        injection heq
      · simp only [forgetSign] at heq
        injection heq
      · simp only [forgetSign, Sum.inr.injEq] at heq
        exact congrArg Sum.inr (Subtype.ext heq))
  rw [network.exists_isConsistent_uniform_iff_mixedResidual hsource htarget]
  exact MixedAdditiveTransport.mixedResidualAtMost_iff_laxified_closedWalk_le
    network.graph (exactMode (m := m)) (fun edge => (network.offset edge : ℝ)) level

/-- A nonnegative level belongs to the uniform-tolerance set exactly when every signed closed
walk satisfies its mean bound. -/
theorem mem_uniformToleranceLevels_iff_closedWalk_le
    (network : RationalSensorNetwork n m)
    (hsource : ∀ edge, network.sourceScale edge = 1)
    (htarget : ∀ edge, network.targetScale edge = 1) (level : ℝ) :
    level ∈ network.uniformToleranceLevels ↔
      0 ≤ level ∧
      ∀ (vertex : Fin n) (cycle : network.signedComparisonGraph.Walk vertex vertex),
        MaxPlusPotential.walkWeight network.signedComparisonWeight cycle ≤
          cycle.length * level := by
  rw [uniformToleranceLevels, Set.mem_ofPred_eq,
    network.exists_isConsistent_uniform_iff_closedWalk_le hsource htarget]

/-- A feasible nonnegative tolerance attained by a positive-length signed cycle is the minimum
uniform tolerance. -/
theorem minimumUniformTolerance_eq_of_cycle
    (network : RationalSensorNetwork n m)
    (hsource : ∀ edge, network.sourceScale edge = 1)
    (htarget : ∀ edge, network.targetScale edge = 1)
    {level : ℝ} (hnonneg : 0 ≤ level) {reading : Fin n → ℝ}
    (hreading : network.IsConsistent (fun _ => level) reading)
    {vertex : Fin n} (cycle : network.signedComparisonGraph.Walk vertex vertex)
    (hlength : 0 < cycle.length)
    (hweight : MaxPlusPotential.walkWeight network.signedComparisonWeight cycle =
      cycle.length * level) :
    network.minimumUniformTolerance = level := by
  apply le_antisymm
  · exact network.isLeast_minimumUniformTolerance.2 ⟨hnonneg, reading, hreading⟩
  · have hminimum := network.isLeast_minimumUniformTolerance.1
    have hcycle :=
      (network.mem_uniformToleranceLevels_iff_closedWalk_le hsource htarget
        network.minimumUniformTolerance).mp hminimum |>.2 vertex cycle
    have hlengthReal : (0 : ℝ) < cycle.length := by exact_mod_cast hlength
    rw [hweight] at hcycle
    nlinarith

end CellularSheaves.RationalSensorNetwork
