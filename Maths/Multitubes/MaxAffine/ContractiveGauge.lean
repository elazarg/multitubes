/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.Slopes

import Maths.Multitubes.Additive.ShortCycles

/-!
# Strict contraction gauges for scalar gains

Nonnegative edge gains on a finite graph admit a positive vertex scaling with one
contraction factor below one exactly when every nonempty directed cycle has gain product
below one. Individual edges may amplify. Zero gains and acyclic graphs are allowed.

Taking logarithms only on positive-gain edges reduces synthesis to a strictly negative
additive residual bound. Finiteness makes a uniform strict margin possible.

## Main definitions

* `Maths.MaxAffineTransport.IsContractiveGauge`: positive scales with a common contraction rate.

## Main results

* `Maths.MaxAffineTransport.walkSlopeProduct_mul_gauge_le_pow`: a geometric bound along walks.
* `Maths.MaxAffineTransport.exists_contractiveGauge_iff_cycleProduct_lt_one`: exact cycle
  criterion for a strict contraction gauge, including zero-gain transitions.
* `Maths.MaxAffineTransport.exists_contractiveGauge_iff_shortCycleProduct_lt_one`: it suffices
  to check nonempty closed walks up to the number of vertices.
-/

@[expose] public section

namespace Maths.MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- Positive vertex scales for which every normalized edge gain is at most `rate`. -/
def IsContractiveGauge (gain : E → ℝ) (rate : ℝ) (gauge : V → ℝ) : Prop :=
  (∀ vertex, 0 < gauge vertex) ∧
    ∀ edge, gain edge * gauge (G.source edge) ≤ rate * gauge (G.target edge)

/-- A nonnegative contraction rate controls every walk gain by its geometric power. -/
theorem walkSlopeProduct_mul_gauge_le_pow (gain : E → ℝ)
    (hnonneg : ∀ edge, 0 ≤ gain edge) {rate : ℝ} (hrate : 0 ≤ rate)
    {gauge : V → ℝ} (hgauge : IsContractiveGauge (G := G) gain rate gauge)
    {start finish : V} (walk : G.Walk start finish) :
    walkSlopeProduct gain walk * gauge start ≤ rate ^ walk.length * gauge finish := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      cases legal
      rw [walkSlopeProduct_concat, EdgeGraph.Walk.length_concat, pow_succ]
      calc
        walkSlopeProduct gain walk * gain edge * gauge start =
            gain edge * (walkSlopeProduct gain walk * gauge start) := by ring
        _ ≤ gain edge * (rate ^ walk.length * gauge _) :=
          mul_le_mul_of_nonneg_left ih (hnonneg edge)
        _ = rate ^ walk.length * (gain edge * gauge _) := by ring
        _ ≤ rate ^ walk.length * (rate * gauge _) :=
          mul_le_mul_of_nonneg_left (hgauge.2 edge) (pow_nonneg hrate _)
        _ = _ := by ring

/-- A strict contraction gauge forces every nonempty directed cycle product below one. -/
theorem cycleProduct_lt_one_of_contractiveGauge (gain : E → ℝ)
    (hnonneg : ∀ edge, 0 ≤ gain edge) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    {gauge : V → ℝ} (hgauge : IsContractiveGauge (G := G) gain rate gauge)
    {vertex : V} (cycle : G.Walk vertex vertex) (hcycle : 0 < cycle.length) :
    walkSlopeProduct gain cycle < 1 := by
  have hwalk := walkSlopeProduct_mul_gauge_le_pow gain hnonneg hrate hgauge cycle
  have hpower : rate ^ cycle.length < 1 := pow_lt_one₀ hrate hlt (by omega)
  have hbound := mul_lt_mul_of_pos_right hpower (hgauge.1 vertex)
  nlinarith

/-- A finite nonnegative gain graph has a strict contraction gauge exactly when nonempty
closed walks up to the number of vertices have gain product below one. -/
theorem exists_contractiveGauge_iff_shortCycleProduct_lt_one [Fintype V] [Finite E]
    (gain : E → ℝ) (hnonneg : ∀ edge, 0 ≤ gain edge) :
    (∃ (rate : ℝ) (gauge : V → ℝ),
      0 < rate ∧ rate < 1 ∧ IsContractiveGauge (G := G) gain rate gauge) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → cycle.length ≤ Fintype.card V →
          walkSlopeProduct gain cycle < 1 := by
  classical
  constructor
  · rintro ⟨rate, gauge, hpos, hlt, hgauge⟩ vertex cycle hcycle _
    exact cycleProduct_lt_one_of_contractiveGauge gain hnonneg hpos.le hlt hgauge cycle hcycle
  · intro hcycles
    have hnegative (vertex : V)
        (cycle : (positiveSlopeGraph (G := G) gain).Walk vertex vertex)
        (hcycle : 0 < cycle.length) (hcard : cycle.length ≤ Fintype.card V) :
        MaxPlusPotential.walkWeight
          (fun edge : PositiveSlopeEdge gain => Real.log (gain edge.1)) cycle < 0 := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_zero, exp_walkWeight_log_eq_walkSlopeProduct,
        ← walkSlopeProduct_forgetPositiveWalk]
      have hlength := congrArg List.length (edges_forgetPositiveWalk gain cycle)
      simp only [List.length_map, EdgeGraph.Walk.edges_length] at hlength
      exact hcycles vertex (forgetPositiveWalk gain cycle)
        (hlength.symm ▸ hcycle) (hlength.symm ▸ hcard)
    obtain ⟨level, hlevel, potential, hpotential⟩ :=
      AdditiveTransport.exists_negative_residual_bound_of_short
        (positiveSlopeGraph (G := G) gain)
        (fun edge : PositiveSlopeEdge gain => Real.log (gain edge.1)) hnegative
    refine ⟨Real.exp level, fun vertex => Real.exp (potential vertex),
      Real.exp_pos _, ?_, fun vertex => Real.exp_pos _, ?_⟩
    · simpa using Real.exp_lt_exp.mpr hlevel
    · intro edge
      by_cases hedge : 0 < gain edge
      · have hrow := hpotential (⟨edge, hedge⟩ : PositiveSlopeEdge gain)
        simp only [MaxPlusPotential.defect] at hrow
        have hexp := Real.exp_le_exp.mpr (show
            Real.log (gain edge) + potential (G.source edge) ≤
              level + potential (G.target edge) by linarith)
        simpa only [Real.exp_add, Real.exp_log hedge] using hexp
      · have hzero : gain edge = 0 := le_antisymm (le_of_not_gt hedge) (hnonneg edge)
        rw [hzero, zero_mul]
        positivity

/-- A finite nonnegative gain graph has a strict positive contraction gauge exactly when all
nonempty directed cycle products are below one. The chosen rate is strictly positive even
when the graph has no positive-gain cycle. -/
theorem exists_contractiveGauge_iff_cycleProduct_lt_one [Fintype V] [Finite E]
    (gain : E → ℝ) (hnonneg : ∀ edge, 0 ≤ gain edge) :
    (∃ (rate : ℝ) (gauge : V → ℝ),
      0 < rate ∧ rate < 1 ∧ IsContractiveGauge (G := G) gain rate gauge) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → walkSlopeProduct gain cycle < 1 := by
  constructor
  · rintro ⟨rate, gauge, hpos, hlt, hgauge⟩ vertex cycle hcycle
    exact cycleProduct_lt_one_of_contractiveGauge gain hnonneg hpos.le hlt hgauge cycle hcycle
  · intro hcycles
    exact (exists_contractiveGauge_iff_shortCycleProduct_lt_one gain hnonneg).mpr
      fun vertex cycle hpos _ => hcycles vertex cycle hpos

end Maths.MaxAffineTransport
