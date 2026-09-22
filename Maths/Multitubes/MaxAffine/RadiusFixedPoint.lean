/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.ContractiveGauge
public import Maths.Multitubes.MaxAffine.Contraction

import Mathlib.Data.Fintype.Sum

/-!
# Least radii from a contractive gauge

A positive contraction gauge turns affine edge demands into a contraction after dividing each
vertex coordinate by its gauge.  A constant synthetic edge at every vertex incorporates an
arbitrary lower bound.  Consequently the Bellman operator has a unique fixed point even at
vertices with no original incoming edges, and that fixed point is the least radius satisfying
the lower and edge constraints.

## Main definitions

* `Maths.MaxAffineTransport.radiusOperator`: the maximum of a vertex lower bound and all
  incoming affine demands.
* `Maths.MaxAffineTransport.leastRadius`: the fixed point selected by a contraction gauge.

## Main results

* `Maths.MaxAffineTransport.leastRadius_fixedPoint`: the selected radius satisfies the Bellman
  equation.
* `Maths.MaxAffineTransport.leastRadius_le`: the selected radius is below every feasible radius.
* `Maths.MaxAffineTransport.tendsto_iterate_radiusOperator`: Bellman iteration converges to the
  least radius from every initial radius.
* `Maths.MaxAffineTransport.dist_iterate_normalizedRadiusOperator_le`: normalized Bellman
  iteration has an explicit geometric error bound.
* `Maths.MaxAffineTransport.exists_feasible_bounded_iff_leastRadius_le`: upper-budget
  feasibility is equivalent to the least radius respecting the budget.

## Tags

Bellman operator, contraction gauge, least fixed point, invariant radius
-/

@[expose] public section

namespace Maths.MaxAffineTransport

noncomputable section

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- A radius satisfies its vertex lower bounds and every affine edge demand. -/
def IsFeasibleRadius (bias gain : E → ℝ) (lower radius : V → ℝ) : Prop :=
  (∀ vertex, lower vertex ≤ radius vertex) ∧
    ∀ edge, bias edge + gain edge * radius (G.source edge) ≤ radius (G.target edge)

/-- Add one constant lower-bound edge entering every vertex. -/
def radiusGraph (G : EdgeGraph V E) : EdgeGraph V (E ⊕ V) where
  source
    | Sum.inl edge => G.source edge
    | Sum.inr vertex => vertex
  target
    | Sum.inl edge => G.target edge
    | Sum.inr vertex => vertex

/-- Gauge-normalized labels for affine demands and vertex lower bounds. -/
def normalizedRadiusLabel (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) : E ⊕ V → Label
  | Sum.inl edge =>
      ⟨⊥, bias edge / gauge (G.target edge),
        gain edge * gauge (G.source edge) / gauge (G.target edge)⟩
  | Sum.inr vertex => ⟨⊥, lower vertex / gauge vertex, 0⟩

/-- Labels for affine demands together with constant vertex lower bounds. -/
def radiusLabel (bias gain : E → ℝ) (lower : V → ℝ) : E ⊕ V → Label
  | Sum.inl edge => ⟨⊥, bias edge, gain edge⟩
  | Sum.inr vertex => ⟨⊥, lower vertex, 0⟩

/-- The Bellman radius operator: the maximum of the lower bound and incoming affine demands. -/
def radiusOperator [Fintype E] [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (bias gain : E → ℝ) (lower radius : V → ℝ) : V → ℝ :=
  vertexOperator (radiusGraph G) (radiusLabel bias gain lower) radius

/-- The radius operator after division of each coordinate by a positive gauge. -/
def normalizedRadiusOperator [Fintype E] [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (bias gain : E → ℝ) (lower gauge scaled : V → ℝ) : V → ℝ :=
  vertexOperator (radiusGraph G) (normalizedRadiusLabel G bias gain lower gauge) scaled

section Finite

variable [Fintype E] [Fintype V] [DecidableEq V]

/-- Every vertex has a synthetic lower-bound edge entering it. -/
theorem incoming_radiusGraph_nonempty (G : EdgeGraph V E) (vertex : V) :
    (incoming (radiusGraph G) vertex).Nonempty := by
  exact ⟨Sum.inr vertex, mem_incoming.2 rfl⟩

/-- The Bellman inequality is exactly lower-bound and edge feasibility. -/
theorem radiusOperator_le_iff (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower radius : V → ℝ) :
    (∀ vertex, radiusOperator G bias gain lower radius vertex ≤ radius vertex) ↔
      IsFeasibleRadius (G := G) bias gain lower radius := by
  rw [radiusOperator, ← isLaxSection_iff_vertexOperator_le
    (radiusGraph G) (radiusLabel bias gain lower) radius (incoming_radiusGraph_nonempty G)]
  constructor
  · intro h
    constructor
    · intro vertex
      simpa [radiusGraph, radiusLabel, Label.apply_of_floor_bot, Label.affinePart] using
        h (Sum.inr vertex)
    · intro edge
      simpa [radiusGraph, radiusLabel, Label.apply_of_floor_bot, Label.affinePart] using
        h (Sum.inl edge)
  · rintro ⟨hlower, hedge⟩ action
    cases action with
    | inl edge =>
        simpa [radiusGraph, radiusLabel, Label.apply_of_floor_bot, Label.affinePart] using
          hedge edge
    | inr vertex =>
        simpa [radiusGraph, radiusLabel, Label.apply_of_floor_bot, Label.affinePart] using
          hlower vertex

/-- Gauge conjugation identifies the normalized and original Bellman operators. -/
theorem radiusOperator_gauge_conjugate (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge scaled : V → ℝ) (hgauge : ∀ vertex, 0 < gauge vertex) (vertex : V) :
    radiusOperator G bias gain lower (fun v => gauge v * scaled v) vertex =
      gauge vertex * normalizedRadiusOperator G bias gain lower gauge scaled vertex := by
  rw [radiusOperator, normalizedRadiusOperator,
    vertexOperator_eq_sup' (incoming_radiusGraph_nonempty G vertex),
    vertexOperator_eq_sup' (incoming_radiusGraph_nonempty G vertex),
    Finset.mul₀_sup' (hgauge vertex).le]
  apply Finset.sup'_congr
  · rfl
  intro action haction
  have htarget := mem_incoming.1 haction
  cases action with
  | inl edge =>
      simp only [radiusGraph] at htarget
      subst vertex
      simp only [radiusLabel, normalizedRadiusLabel, Label.apply_of_floor_bot,
        Label.affinePart, radiusGraph]
      field_simp [(hgauge (G.target edge)).ne', (hgauge (G.source edge)).ne']
  | inr target =>
      simp only [radiusGraph] at htarget
      subst vertex
      simp only [radiusLabel, normalizedRadiusLabel, Label.apply_of_floor_bot,
        Label.affinePart, zero_mul, add_zero]
      field_simp [(hgauge target).ne']

/-- A contractive gauge makes the normalized radius operator a contraction. -/
theorem contractingWith_normalizedRadiusOperator (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) :
    ContractingWith ⟨rate, hrate⟩ (normalizedRadiusOperator G bias gain lower gauge) := by
  apply contractingWith_vertexOperator
  · exact hlt
  · intro action
    cases action with
    | inl edge =>
        simp only [normalizedRadiusLabel]
        rw [abs_of_nonneg]
        · exact (div_le_iff₀ (hgauge.1 (G.target edge))).2 (hgauge.2 edge)
        · exact div_nonneg (mul_nonneg (hgain edge) (hgauge.1 (G.source edge)).le)
            (hgauge.1 (G.target edge)).le
    | inr vertex =>
        simp only [normalizedRadiusLabel, abs_zero]
        exact hrate

/-- The least radius selected by Banach's fixed-point theorem in gauge coordinates. -/
def leastRadius (G : EdgeGraph V E) (bias gain : E → ℝ) (lower gauge : V → ℝ)
    {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) : V → ℝ :=
  let contraction := contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt
    hgain hgauge
  fun vertex => gauge vertex *
    (@ContractingWith.fixedPoint (V → ℝ) _ _ _ contraction) vertex

/-- The selected least radius is a fixed point of the Bellman radius operator. -/
theorem leastRadius_fixedPoint (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) :
    radiusOperator G bias gain lower
        (leastRadius G bias gain lower gauge hrate hlt hgain hgauge) =
      leastRadius G bias gain lower gauge hrate hlt hgain hgauge := by
  let contraction := contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt
    hgain hgauge
  let fixed := @ContractingWith.fixedPoint (V → ℝ) _ _ _ contraction
  have hfixed : normalizedRadiusOperator G bias gain lower gauge fixed = fixed :=
    contraction.fixedPoint_isFixedPt
  funext vertex
  rw [leastRadius]
  change radiusOperator G bias gain lower (fun v => gauge v * fixed v) vertex = _
  rw [radiusOperator_gauge_conjugate G bias gain lower gauge fixed hgauge.1, hfixed]

/-- The selected fixed point is the unique Bellman fixed point. -/
theorem leastRadius_unique (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) {radius : V → ℝ}
    (hradius : radiusOperator G bias gain lower radius = radius) :
    radius = leastRadius G bias gain lower gauge hrate hlt hgain hgauge := by
  let contraction := contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt
    hgain hgauge
  let scaled := fun vertex => radius vertex / gauge vertex
  have hscaled : normalizedRadiusOperator G bias gain lower gauge scaled = scaled := by
    funext vertex
    have hconj := radiusOperator_gauge_conjugate G bias gain lower gauge scaled hgauge.1 vertex
    have hradiusVertex := congrFun hradius vertex
    have hg : gauge vertex ≠ 0 := (hgauge.1 vertex).ne'
    have hunscale : (fun v => gauge v * scaled v) = radius := by
      funext v
      dsimp [scaled]
      field_simp [(hgauge.1 v).ne']
    rw [hunscale, hradiusVertex] at hconj
    apply (mul_left_cancel₀ hg)
    rw [← hconj]
    dsimp [scaled]
    field_simp [hg]
  have heq : scaled = (contraction.fixedPoint : V → ℝ) :=
    contraction.fixedPoint_unique hscaled
  funext vertex
  rw [leastRadius]
  change radius vertex = gauge vertex *
    (contraction.fixedPoint : V → ℝ) vertex
  rw [← heq]
  dsimp [scaled]
  field_simp [(hgauge.1 vertex).ne']

/-- The selected fixed point satisfies all lower and affine radius constraints. -/
theorem leastRadius_feasible (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) :
    IsFeasibleRadius (G := G) bias gain lower
      (leastRadius G bias gain lower gauge hrate hlt hgain hgauge) := by
  rw [← radiusOperator_le_iff]
  intro vertex
  exact le_of_eq (congrFun
    (leastRadius_fixedPoint G bias gain lower gauge hrate hlt hgain hgauge) vertex)

/-- The normalized Bellman operator is monotone when the gains are nonnegative. -/
theorem monotone_normalizedRadiusOperator (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : ∀ vertex, 0 < gauge vertex) :
    Monotone (normalizedRadiusOperator G bias gain lower gauge) := by
  apply monotone_vertexOperator
  intro action
  cases action with
  | inl edge =>
      exact div_nonneg (mul_nonneg (hgain edge) (hgauge (G.source edge)).le)
        (hgauge (G.target edge)).le
  | inr vertex => exact le_rfl

/-- The selected radius is pointwise below every feasible radius. -/
theorem leastRadius_le (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) {radius : V → ℝ}
    (hfeasible : IsFeasibleRadius (G := G) bias gain lower radius) :
    leastRadius G bias gain lower gauge hrate hlt hgain hgauge ≤ radius := by
  let operator := normalizedRadiusOperator G bias gain lower gauge
  let contraction := contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt
    hgain hgauge
  let scaled := fun vertex => radius vertex / gauge vertex
  have hscaled : operator scaled ≤ scaled := by
    rw [Pi.le_def]
    intro vertex
    have hconj := radiusOperator_gauge_conjugate G bias gain lower gauge scaled hgauge.1 vertex
    have horiginal := (radiusOperator_le_iff G bias gain lower radius).2 hfeasible vertex
    have hg : gauge vertex ≠ 0 := (hgauge.1 vertex).ne'
    have hunscale : (fun v => gauge v * scaled v) = radius := by
      funext v
      dsimp [scaled]
      field_simp [(hgauge.1 v).ne']
    rw [hunscale] at hconj
    rw [hconj] at horiginal
    rw [← congrFun hunscale vertex] at horiginal
    exact le_of_mul_le_mul_left horiginal (hgauge.1 vertex)
  have hiterate : ∀ n : ℕ, operator^[n] scaled ≤ scaled := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans (monotone_normalizedRadiusOperator G bias gain lower gauge hgain hgauge.1 ih)
          hscaled
  have htendsto := contraction.tendsto_iterate_fixedPoint scaled
  rw [Pi.le_def]
  intro vertex
  have hlimit : (contraction.fixedPoint : V → ℝ) vertex ≤
      scaled vertex :=
    le_of_tendsto' (tendsto_pi_nhds.1 htendsto vertex) fun n => hiterate n vertex
  rw [leastRadius]
  change gauge vertex * (contraction.fixedPoint : V → ℝ) vertex ≤
    radius vertex
  calc
    _ ≤ gauge vertex * scaled vertex := mul_le_mul_of_nonneg_left hlimit (hgauge.1 vertex).le
    _ = radius vertex := by
      dsimp [scaled]
      field_simp [(hgauge.1 vertex).ne']

/-- Bellman iteration from any initial radius converges to the least radius. -/
theorem tendsto_iterate_radiusOperator (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge initial : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) :
    Filter.Tendsto
      (fun n => (radiusOperator G bias gain lower)^[n] initial)
      Filter.atTop
      (nhds (leastRadius G bias gain lower gauge hrate hlt hgain hgauge)) := by
  let operator := radiusOperator G bias gain lower
  let normalized := normalizedRadiusOperator G bias gain lower gauge
  let contraction := contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt
    hgain hgauge
  let scaled := fun vertex => initial vertex / gauge vertex
  have hiterate (n : ℕ) :
      operator^[n] initial = fun vertex => gauge vertex * (normalized^[n] scaled) vertex := by
    induction n with
    | zero =>
        funext vertex
        dsimp [scaled]
        field_simp [(hgauge.1 vertex).ne']
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        funext vertex
        exact radiusOperator_gauge_conjugate G bias gain lower gauge
          (normalized^[n] scaled) hgauge.1 vertex
  have htendsto := contraction.tendsto_iterate_fixedPoint scaled
  rw [tendsto_pi_nhds]
  intro vertex
  have hcoordinate := (tendsto_pi_nhds.1 htendsto vertex).const_mul (gauge vertex)
  convert hcoordinate using 1
  · funext n
    exact congrFun (hiterate n) vertex
  · rw [leastRadius]

/-- Quantitative convergence in normalized sup distance. -/
theorem dist_iterate_normalizedRadiusOperator_le (G : EdgeGraph V E)
    (bias gain : E → ℝ) (lower gauge initial : V → ℝ) {rate : ℝ}
    (hrate : 0 ≤ rate) (hlt : rate < 1) (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) (n : ℕ) :
    dist ((normalizedRadiusOperator G bias gain lower gauge)^[n] initial)
        ((contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt hgain
          hgauge).fixedPoint) ≤
      dist initial (normalizedRadiusOperator G bias gain lower gauge initial) * rate ^ n /
        (1 - rate) := by
  exact (contractingWith_normalizedRadiusOperator G bias gain lower gauge hrate hlt hgain
    hgauge).apriori_dist_iterate_fixedPoint_le initial n

/-- A feasible radius within an upper budget exists exactly when the least radius is within it. -/
theorem exists_feasible_bounded_iff_leastRadius_le (G : EdgeGraph V E) (bias gain : E → ℝ)
    (lower gauge upper : V → ℝ) {rate : ℝ} (hrate : 0 ≤ rate) (hlt : rate < 1)
    (hgain : ∀ edge, 0 ≤ gain edge)
    (hgauge : IsContractiveGauge (G := G) gain rate gauge) :
    (∃ radius : V → ℝ,
      IsFeasibleRadius (G := G) bias gain lower radius ∧ radius ≤ upper) ↔
      leastRadius G bias gain lower gauge hrate hlt hgain hgauge ≤ upper := by
  constructor
  · rintro ⟨radius, hfeasible, hupper⟩
    exact (leastRadius_le G bias gain lower gauge hrate hlt hgain hgauge hfeasible).trans hupper
  · intro hupper
    exact ⟨leastRadius G bias gain lower gauge hrate hlt hgain hgauge,
      leastRadius_feasible G bias gain lower gauge hrate hlt hgain hgauge, hupper⟩

end Finite

end

end Maths.MaxAffineTransport
