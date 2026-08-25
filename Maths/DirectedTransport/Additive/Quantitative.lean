/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Potentials
public import Maths.DirectedTransport.FiniteInequality.Quantitative

/-!
# Exact quantitative duality for additive transport

The one-sided theorem is the threshold form of the maximum-cycle-mean
identity.  It is meaningful on acyclic graphs too: every real threshold is
attainable there, expressing an infimum of `-∞` without a convention.

The symmetric theorem identifies the exact signed-row threshold with
normalized signed circulations.  For a nonempty edge type this is the usual
sup-norm threshold.  With no edges it instead follows the row-maximum
convention `max ∅ = -∞`, so every real threshold is feasible.

## Main definitions

* `Maths.AdditiveTransport.WorstDirectedResidualAtMost`: existence of a potential
  whose largest directed additive residual is at most a given level.
* `Maths.AdditiveTransport.SymmetricResidualAtMost`: the same with both signed
  residual rows bounded, so the defect is bounded in absolute value.
* `Maths.AdditiveTransport.SignedEdge`, `signedDelta` and `signedBase`: the two
  orientations of each edge, the incidence row in the selected orientation, and the weight
  carrying the orientation's sign.

## Main results

* `Maths.AdditiveTransport.worstDirectedResidualAtMost_iff_closedWalk_le`: a
  one-sided residual threshold is attainable exactly when every closed walk has mean at most
  that threshold.  It is stated by multiplication rather than division, which keeps empty
  walks safe and leaves the statement meaningful on acyclic graphs.
* `Maths.AdditiveTransport.symmetricResidualAtMost_iff_finiteInequality`: symmetric
  signed-row feasibility is exactly the doubled finite row system, the bridge to
  `Maths.FiniteInequality`.
* `Maths.AdditiveTransport.symmetricResidualAtMost_iff_normalizedSignedDual_le`: the
  exact symmetric dual, characterizing the threshold by balanced probability distributions on
  signed edge rows.
* `Maths.AdditiveTransport.exists_zero_defect_iff_normalizedSignedDual_nonpos`: at
  threshold zero the symmetric theory becomes exact additive transport, with all edge defects
  vanishing.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## One-sided cycle-mean threshold -/

/-- A potential whose largest directed additive residual is at most `level`. -/
def WorstDirectedResidualAtMost (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) : Prop :=
  ∃ potential : V → ℝ,
    ∀ edge, MaxPlusPotential.defect G weight potential edge ≤ level

/-- **Exact one-sided Chebyshev threshold.**  A residual threshold is
attainable exactly when every closed walk has mean at most that threshold.
The multiplication form includes empty walks safely. -/
theorem worstDirectedResidualAtMost_iff_closedWalk_le
    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    WorstDirectedResidualAtMost G weight level ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level := by
  have hpotential : WorstDirectedResidualAtMost G weight level ↔
      ∃ potential : V → ℝ,
        MaxPlusPotential.IsPotential G (fun edge => weight edge - level) potential := by
    apply exists_congr
    intro potential
    constructor
    · intro h edge
      have := h edge
      change potential (G.source edge) + (weight edge - level) ≤
        potential (G.target edge)
      simp only [MaxPlusPotential.defect] at this
      linarith
    · intro h edge
      have := h edge
      change potential (G.source edge) + (weight edge - level) ≤
        potential (G.target edge) at this
      simp only [MaxPlusPotential.defect]
      linarith
  rw [hpotential,
    MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos]
  apply forall_congr'
  intro vertex
  apply forall_congr'
  intro cycle
  rw [MaxPlusPotential.walkWeight_sub_const]
  constructor <;> intro h <;> linarith

/-! ## Symmetric signed-circulation threshold -/

/-- Two orientations of every directed edge. -/
abbrev SignedEdge (E : Type uE) := E × Bool

/-- Incidence row in the selected orientation. -/
def signedDelta [DecidableEq V] (G : EdgeGraph V E) : SignedEdge E → V → ℝ
  | (edge, false) => fun vertex =>
      (if vertex = G.target edge then 1 else 0) -
        (if vertex = G.source edge then 1 else 0)
  | (edge, true) => fun vertex =>
      (if vertex = G.source edge then 1 else 0) -
        (if vertex = G.target edge then 1 else 0)

/-- Weight with the sign selected by the orientation. -/
def signedBase (weight : E → ℝ) : SignedEdge E → ℝ
  | (edge, false) => weight edge
  | (edge, true) => -weight edge

theorem dotProduct_signedDelta_false [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) :
    dotProduct (signedDelta G (edge, false)) potential =
      potential (G.target edge) - potential (G.source edge) := by
  simp only [dotProduct, signedDelta, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib]
  simp

theorem dotProduct_signedDelta_true [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) :
    dotProduct (signedDelta G (edge, true)) potential =
      potential (G.source edge) - potential (G.target edge) := by
  simp only [dotProduct, signedDelta, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib]
  simp

/-- A potential whose two signed residual rows at every edge are at most
`level`.  When edges are nonempty this is the usual sup-norm condition. -/
def SymmetricResidualAtMost (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) : Prop :=
  ∃ potential : V → ℝ,
    ∀ edge, |MaxPlusPotential.defect G weight potential edge| ≤ level

/-- Symmetric signed-row feasibility is exactly the doubled finite row
system. -/
theorem symmetricResidualAtMost_iff_finiteInequality
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    SymmetricResidualAtMost G weight level ↔
      FiniteInequality.WorstResidualAtMost (signedDelta G)
        (signedBase weight) level := by
  apply exists_congr
  intro potential
  constructor
  · intro h signed
    rcases signed with ⟨edge, orientation⟩
    cases orientation with
    | false =>
        rw [signedBase, dotProduct_signedDelta_false]
        have hedge := (abs_le.mp (h edge)).2
        simp only [MaxPlusPotential.defect] at hedge
        linarith
    | true =>
        rw [signedBase, dotProduct_signedDelta_true]
        have hedge := (abs_le.mp (h edge)).1
        simp only [MaxPlusPotential.defect] at hedge
        linarith
  · intro h edge
    apply abs_le.mpr
    constructor
    · have hedge := h (edge, true)
      rw [signedBase, dotProduct_signedDelta_true] at hedge
      simp only [MaxPlusPotential.defect]
      linarith
    · have hedge := h (edge, false)
      rw [signedBase, dotProduct_signedDelta_false] at hedge
      simp only [MaxPlusPotential.defect]
      linarith

/-- **Exact symmetric normalized dual.**  The best signed-row additive
residual is characterized at every threshold by balanced probability
distributions on signed edge rows.  For nonempty edges this is the sup-norm
residual. -/
theorem symmetricResidualAtMost_iff_normalizedSignedDual_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) :
    SymmetricResidualAtMost G weight level ↔
      ∀ coefficient : SignedEdge E → ℝ,
        FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
          FiniteInequality.certificateValue (signedBase weight) coefficient ≤ level := by
  rw [symmetricResidualAtMost_iff_finiteInequality,
    FiniteInequality.worstResidualAtMost_iff_normalizedDual_le]

/-- At threshold zero, the symmetric theory becomes exact additive transport:
all edge defects vanish. -/
theorem exists_zero_defect_iff_normalizedSignedDual_nonpos
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (weight : E → ℝ) :
    (∃ potential : V → ℝ,
      ∀ edge, MaxPlusPotential.defect G weight potential edge = 0) ↔
      ∀ coefficient : SignedEdge E → ℝ,
        FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
          FiniteInequality.certificateValue (signedBase weight) coefficient ≤ 0 := by
  rw [← symmetricResidualAtMost_iff_normalizedSignedDual_le G weight 0]
  apply exists_congr
  intro potential
  apply forall_congr'
  intro edge
  exact abs_nonpos_iff.symm

end AdditiveTransport

end

end Maths
