/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Cycles
public import Maths.Multitubes.Additive.Mixed

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative additive mixed transport

For real additive transport, a mixed section has a directed residual on lax
edges, the opposite residual on oplax edges, and a two-sided residual on exact
edges.  The mixed residual threshold is the ordinary directed residual
threshold on the laxification graph with signed edge weights.

## Main definitions

* `Maths.MixedAdditiveTransport.MixedResidualAtMost` - existence of a
  potential satisfying a prescribed mixed residual threshold.

## Main results

* `Maths.MixedAdditiveTransport.mixedResidualAtMost_iff_worstDirectedResidualAtMost` -
  the residual threshold is the directed threshold on the signed laxification.
* `Maths.MixedAdditiveTransport.mixedResidualAtMost_iff_laxified_closedWalk_le` -
  the closed-walk characterization of the mixed threshold.
* `Maths.MixedAdditiveTransport.mixedResidualAtMost_iff_laxified_simpleCycle_le` -
  the simple-cycle characterization of the mixed threshold.
* `Maths.MixedAdditiveTransport.exists_isMixedSection_iff_mixedResidualAtMost_zero` -
  the zero-threshold specialization to mixed sections.
* `Maths.MixedAdditiveTransport.exists_isMixedSection_iff_forall_laxified_simpleCycle_nonpos` -
  the finite-edge simple-cycle feasibility criterion.

## Tags

transport, additive transport, mixed polarity, residual, cycle mean
-/

@[expose] public section

namespace Maths

namespace MixedAdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- A potential whose mixed additive residual is at most `level` on every edge.
Lax edges bound the usual defect, oplax edges bound its negation, and exact
edges bound its absolute value. -/
def MixedResidualAtMost (G : EdgeGraph V E) (mode : E → EdgeMode)
    (weight : E → ℝ) (level : ℝ) : Prop :=
  ∃ potential : V → ℝ, ∀ edge : E,
    match mode edge with
    | .lax => MaxPlusPotential.defect G weight potential edge ≤ level
    | .exact => |MaxPlusPotential.defect G weight potential edge| ≤ level
    | .oplax => -MaxPlusPotential.defect G weight potential edge ≤ level

/-- The mixed residual threshold is the ordinary directed residual threshold on
the signed laxification graph. -/
theorem mixedResidualAtMost_iff_worstDirectedResidualAtMost
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → ℝ) (level : ℝ) :
    MixedResidualAtMost G mode weight level ↔
      AdditiveTransport.WorstDirectedResidualAtMost
        (Transport.laxificationGraph G mode) (laxifiedWeight mode weight) level := by
  apply exists_congr
  intro potential
  have hforward_defect (edge : Transport.LaxificationForwardEdge mode) :
      MaxPlusPotential.defect (Transport.laxificationGraph G mode)
          (laxifiedWeight mode weight) potential (.inl edge) =
        MaxPlusPotential.defect G weight potential edge.1 := by
    rfl
  have hreverse_defect (edge : Transport.LaxificationReverseEdge mode) :
      MaxPlusPotential.defect (Transport.laxificationGraph G mode)
          (laxifiedWeight mode weight) potential (.inr edge) =
        -MaxPlusPotential.defect G weight potential edge.1 := by
    simp only [MaxPlusPotential.defect, Transport.laxificationGraph,
      laxifiedWeight]
    ring
  constructor
  · intro h edge
    rcases edge with edge | edge
    · rcases edge.property with hmode | hmode
      · rw [hforward_defect]
        simpa [hmode] using h edge.1
      · have hbound := h edge.1
        rw [hforward_defect]
        exact (le_abs_self _).trans (by simpa [hmode] using hbound)
    · rcases edge.property with hmode | hmode
      · rw [hreverse_defect]
        simpa [hmode] using h edge.1
      · have hbound : |MaxPlusPotential.defect G weight potential edge.1| ≤ level := by
          simpa [hmode] using h edge.1
        have hneg := neg_le_of_abs_le hbound
        rw [hreverse_defect]
        linarith
  · intro h edge
    cases hmode : mode edge with
    | lax =>
        have hbound := h (.inl ⟨edge, Or.inl hmode⟩)
        rw [hforward_defect] at hbound
        exact hbound
    | exact =>
        have hforward_bound := h (.inl ⟨edge, Or.inr hmode⟩)
        have hreverse_bound := h (.inr ⟨edge, Or.inr hmode⟩)
        rw [hforward_defect] at hforward_bound
        rw [hreverse_defect] at hreverse_bound
        exact (abs_le).2 ⟨by linarith, hforward_bound⟩
    | oplax =>
        have hbound := h (.inr ⟨edge, Or.inl hmode⟩)
        rw [hreverse_defect] at hbound
        exact hbound

/-- The mixed residual threshold is equivalent to the signed closed-walk
inequality on the laxification graph. -/
theorem mixedResidualAtMost_iff_laxified_closedWalk_le
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → ℝ) (level : ℝ)
    [Finite (Transport.LaxificationEdge mode)] :
    MixedResidualAtMost G mode weight level ↔
      ∀ (vertex : V)
        (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
        MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤
          cycle.length * level := by
  rw [mixedResidualAtMost_iff_worstDirectedResidualAtMost,
    AdditiveTransport.worstDirectedResidualAtMost_iff_closedWalk_le]

/-- The mixed residual threshold is equivalent to the signed simple-cycle
inequality on the laxification graph. -/
theorem mixedResidualAtMost_iff_laxified_simpleCycle_le
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → ℝ) (level : ℝ)
    [Finite (Transport.LaxificationEdge mode)] :
    MixedResidualAtMost G mode weight level ↔
      ∀ (vertex : V)
        (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
        AdditiveTransport.IsSimpleCycle cycle →
        MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤
          cycle.length * level := by
  rw [mixedResidualAtMost_iff_worstDirectedResidualAtMost,
    AdditiveTransport.worstDirectedResidualAtMost_iff_simpleCycles_le]

/-- At threshold zero, mixed residual feasibility is exactly existence of an
additive mixed section. -/
theorem exists_isMixedSection_iff_mixedResidualAtMost_zero
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → ℝ) :
    (∃ potential : V → ℝ,
      (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential) ↔
      MixedResidualAtMost G mode weight 0 := by
  rw [mixedResidualAtMost_iff_worstDirectedResidualAtMost]
  calc
    (∃ potential : V → ℝ,
        (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential) ↔
        ∃ potential : V → ℝ,
          MaxPlusPotential.IsPotential (Transport.laxificationGraph G mode)
            (laxifiedWeight mode weight) potential := by
      simp only [isMixedSection_iff_isPotential_laxified]
    _ ↔ AdditiveTransport.WorstDirectedResidualAtMost
        (Transport.laxificationGraph G mode) (laxifiedWeight mode weight) 0 := by
      apply exists_congr
      intro potential
      rw [MaxPlusPotential.isPotential_iff_forall_defect_nonpos]

/-- A real mixed additive section exists exactly when every signed simple
cycle in the laxification graph has nonpositive weight. -/
theorem exists_isMixedSection_iff_forall_laxified_simpleCycle_nonpos
    (G : EdgeGraph V E) (mode : E → EdgeMode)
    [Finite (Transport.LaxificationEdge mode)] (weight : E → ℝ) :
    (∃ potential : V → ℝ,
      (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential) ↔
      ∀ (vertex : V)
        (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
        AdditiveTransport.IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤ 0 := by
  rw [exists_isMixedSection_iff_mixedResidualAtMost_zero,
    mixedResidualAtMost_iff_laxified_simpleCycle_le]
  simp

end MixedAdditiveTransport

end Maths
