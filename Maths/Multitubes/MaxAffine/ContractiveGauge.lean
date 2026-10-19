/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.Slopes

import Maths.Multitubes.Additive.ShortCycles

/-!
# Strict contractive gauges for scalar slopes

Nonnegative edge slopes on a finite graph admit a positive vertex scaling with one
contraction factor below one exactly when every nonempty directed cycle has slope product
below one. Individual edges may amplify. Zero slopes and acyclic graphs are allowed.

Taking logarithms only on positive-slope edges reduces synthesis to a strictly negative
additive residual bound. Finiteness makes a uniform strict margin possible.

## Main definitions

* `Maths.MaxAffineTransport.IsContractiveGauge`: positive scales with a common contraction rate.

## Main results

* `Maths.MaxAffineTransport.walkProd_mul_gauge_le_pow`: a geometric bound along walks.
* `Maths.MaxAffineTransport.exists_contractiveGauge_iff_cycleProduct_lt_one`: exact cycle
  criterion for a strict contractive gauge, including zero-slope edges.
* `Maths.MaxAffineTransport.exists_contractiveGauge_iff_shortCycleProduct_lt_one`: it suffices
  to check nonempty closed walks up to the number of vertices.

## Tags

contraction, contractive gauge, diagonal scaling, weighted sup norm, cycle product, spectral radius
-/

@[expose] public section

namespace Maths.MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- Positive vertex scales for which every normalized edge slope is at most `rate`. -/
def IsContractiveGauge (slope : E → ℝ) (rate : ℝ) (gauge : V → ℝ) : Prop :=
  (∀ vertex, 0 < gauge vertex) ∧
    ∀ edge, slope edge * gauge (G.source edge) ≤ rate * gauge (G.target edge)

/-- A nonnegative contraction rate controls every walk slope by its geometric power. -/
theorem walkProd_mul_gauge_le_pow (slope : E → ℝ)
    (hnonneg : ∀ edge, 0 ≤ slope edge) {rate : ℝ} (hrate : 0 ≤ rate)
    {gauge : V → ℝ} (hgauge : IsContractiveGauge (G := G) slope rate gauge)
    {start finish : V} (walk : G.Walk start finish) :
    walkProd slope walk * gauge start ≤ rate ^ walk.length * gauge finish := by
  induction walk with
  | nil => simp
  | concat edge walk ih =>
      rw [walkProd_concat, EdgeGraph.Walk.length_concat, pow_succ]
      calc
        walkProd slope walk * slope edge * gauge start =
            slope edge * (walkProd slope walk * gauge start) := by ring
        _ ≤ slope edge * (rate ^ walk.length * gauge _) :=
          mul_le_mul_of_nonneg_left ih (hnonneg edge)
        _ = rate ^ walk.length * (slope edge * gauge _) := by ring
        _ ≤ rate ^ walk.length * (rate * gauge _) :=
          mul_le_mul_of_nonneg_left (hgauge.2 edge) (pow_nonneg hrate _)
        _ = _ := by ring

/-- A strict contractive gauge forces every nonempty directed cycle product below one. -/
theorem cycleProduct_lt_one_of_contractiveGauge (slope : E → ℝ)
    (hnonneg : ∀ edge, 0 ≤ slope edge) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    {gauge : V → ℝ} (hgauge : IsContractiveGauge (G := G) slope rate gauge)
    {vertex : V} (cycle : G.Walk vertex vertex) (hcycle : 0 < cycle.length) :
    walkProd slope cycle < 1 := by
  have hwalk := walkProd_mul_gauge_le_pow slope hnonneg hrate hgauge cycle
  have hpower : rate ^ cycle.length < 1 := pow_lt_one₀ hrate hlt (by omega)
  have hbound := mul_lt_mul_of_pos_right hpower (hgauge.1 vertex)
  nlinarith

/-- A finite graph with nonnegative edge slopes has a strict contractive gauge exactly when nonempty
closed walks up to the number of vertices have slope product below one. -/
theorem exists_contractiveGauge_iff_shortCycleProduct_lt_one [Fintype V] [Finite E]
    (slope : E → ℝ) (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∃ (rate : ℝ) (gauge : V → ℝ),
      0 < rate ∧ rate < 1 ∧ IsContractiveGauge (G := G) slope rate gauge) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → cycle.length ≤ Fintype.card V →
          walkProd slope cycle < 1 := by
  classical
  constructor
  · rintro ⟨rate, gauge, hpos, hlt, hgauge⟩ vertex cycle hcycle _
    exact cycleProduct_lt_one_of_contractiveGauge slope hnonneg hpos.le hlt hgauge cycle hcycle
  · intro hcycles
    have hnegative (vertex : V)
        (cycle : (positiveSlopeGraph (G := G) slope).Walk vertex vertex)
        (hcycle : 0 < cycle.length) (hcard : cycle.length ≤ Fintype.card V) :
        walkSum
          (fun edge : PositiveSlopeEdge slope => Real.log (slope edge.1)) cycle < 0 := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_zero,
        exp_walkSum_log_eq_walkProd (fun edge : PositiveSlopeEdge slope => slope edge.1)
          (fun edge => edge.2),
        ← walkProd_ofRestrictEdges]
      have hlength := congrArg List.length (EdgeGraph.Walk.edges_ofRestrictEdges cycle)
      simp only [List.length_map, EdgeGraph.Walk.edges_length] at hlength
      exact hcycles vertex cycle.ofRestrictEdges
        (hlength.symm ▸ hcycle) (hlength.symm ▸ hcard)
    obtain ⟨level, hlevel, potential, hpotential⟩ :=
      AdditiveTransport.exists_negative_residual_bound_of_short
        (positiveSlopeGraph (G := G) slope)
        (fun edge : PositiveSlopeEdge slope => Real.log (slope edge.1)) hnegative
    refine ⟨Real.exp level, fun vertex => Real.exp (potential vertex),
      Real.exp_pos _, ?_, fun vertex => Real.exp_pos _, ?_⟩
    · simpa using Real.exp_lt_exp.mpr hlevel
    · intro edge
      by_cases hedge : 0 < slope edge
      · have hrow := hpotential (⟨edge, hedge⟩ : PositiveSlopeEdge slope)
        simp only [MaxPlusPotential.defect] at hrow
        have hexp := Real.exp_le_exp.mpr (show
            Real.log (slope edge) + potential (G.source edge) ≤
              level + potential (G.target edge) by linarith)
        simpa only [Real.exp_add, Real.exp_log hedge] using hexp
      · have hzero : slope edge = 0 := le_antisymm (le_of_not_gt hedge) (hnonneg edge)
        rw [hzero, zero_mul]
        positivity

/-- A finite graph with nonnegative edge slopes has a strict positive contractive gauge exactly
when all nonempty directed cycle products are below one. The chosen rate is strictly positive even
when the graph has no positive-slope cycle. -/
theorem exists_contractiveGauge_iff_cycleProduct_lt_one [Fintype V] [Finite E]
    (slope : E → ℝ) (hnonneg : ∀ edge, 0 ≤ slope edge) :
    (∃ (rate : ℝ) (gauge : V → ℝ),
      0 < rate ∧ rate < 1 ∧ IsContractiveGauge (G := G) slope rate gauge) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        0 < cycle.length → walkProd slope cycle < 1 := by
  constructor
  · rintro ⟨rate, gauge, hpos, hlt, hgauge⟩ vertex cycle hcycle
    exact cycleProduct_lt_one_of_contractiveGauge slope hnonneg hpos.le hlt hgauge cycle hcycle
  · intro hcycles
    exact (exists_contractiveGauge_iff_shortCycleProduct_lt_one slope hnonneg).mpr
      fun vertex cycle hpos _ => hcycles vertex cycle hpos

end Maths.MaxAffineTransport
