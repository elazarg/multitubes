/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import SwitchedHybridControl.Control
public import Maths.Multitubes.FiniteInequality.Sparse

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Sum

/-!
# Error bounds for switched and hybrid executions

Concrete and approximate transports over one graph can have different,
vertex-dependent state spaces.  A local affine error estimate and a compatible
family of radii imply an error bound along every shared execution path.

For finite graphs, lower bounds, upper budgets, and affine edge constraints on
the radii are represented exactly as a finite linear-inequality system.  Thus
the general theorem of alternatives supplies certificates for infeasibility of
the comparison constraints.  Such a certificate does not assert that the
physical system itself is unsafe.

## Main definitions

* `SwitchedHybridControl.ErrorComparison` - local affine error propagation data.
* `SwitchedHybridControl.IsRadiusFamily` - edge-compatible error radii.
* `SwitchedHybridControl.RadiusRow` - finite inequality rows for bounded radii.
* `SwitchedHybridControl.radiusDelta` and `SwitchedHybridControl.radiusBase` - row data.

## Main results

* `SwitchedHybridControl.ErrorComparison.walk_error_le` - error bounds propagate along walks.
* `SwitchedHybridControl.radius_feasible_iff` - exact finite-inequality encoding of radii.
* `SwitchedHybridControl.exists_sparse_radius_certificate_of_infeasible` - a sparse
  certificate for infeasible comparison constraints.
* `SwitchedHybridControl.exampleErrorComparison_walk_le` - a heterogeneous worked example.
* `SwitchedHybridControl.exampleTightBudget_infeasible` - rejection of incompatible budgets.

## Tags

switched systems, hybrid systems, approximation, error bound, affine comparison,
certificate of infeasibility
-/

@[expose] public section

namespace SwitchedHybridControl

universe uV uE uC uA

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}
variable {Concrete : V → Type uC} {Approximate : V → Type uA}

/-- A local affine comparison between concrete and approximate transitions. -/
structure ErrorComparison (concrete : Maths.Transport G Concrete)
    (approximate : Maths.Transport G Approximate) where
  /-- Error between a concrete and an approximate state in one mode. -/
  error : (vertex : V) → Concrete vertex → Approximate vertex → ℝ
  /-- Additive error introduced by each transition. -/
  bias : E → ℝ
  /-- Multiplicative error gain of each transition. -/
  gain : E → ℝ
  /-- Transition gains are nonnegative. -/
  gain_nonneg : ∀ edge, 0 ≤ gain edge
  /-- Each pair of corresponding transitions satisfies the affine error estimate. -/
  step_le : ∀ (edge : E) (c : Concrete (G.source edge))
      (a : Approximate (G.source edge)),
    error (G.target edge) (concrete.edgeMap edge c) (approximate.edgeMap edge a) ≤
      bias edge + gain edge * error (G.source edge) c a

/-- A radius family closed under all affine error comparisons. -/
def IsRadiusFamily {concrete : Maths.Transport G Concrete}
    {approximate : Maths.Transport G Approximate}
    (comparison : ErrorComparison concrete approximate) (radius : V → ℝ) : Prop :=
  ∀ edge, comparison.bias edge + comparison.gain edge * radius (G.source edge) ≤
    radius (G.target edge)

namespace ErrorComparison

/-- A compatible radius bounds the error after every shared finite execution. -/
theorem walk_error_le {concrete : Maths.Transport G Concrete}
    {approximate : Maths.Transport G Approximate}
    (comparison : ErrorComparison concrete approximate) (radius : V → ℝ)
    (hradius : IsRadiusFamily comparison radius) {start finish : V}
    (walk : G.Walk start finish) (c : Concrete start) (a : Approximate start)
    (hinitial : comparison.error start c a ≤ radius start) :
    comparison.error finish (concrete.walkMap walk c) (approximate.walkMap walk a) ≤
      radius finish := by
  induction walk with
  | nil => exact hinitial
  | concat walk edge legal ih =>
      cases legal
      rw [Maths.Transport.walkMap_concat, Maths.Transport.walkMap_concat]
      calc
        comparison.error _ (concrete.edgeMap edge _) (approximate.edgeMap edge _) ≤
            comparison.bias edge + comparison.gain edge *
              comparison.error _ (concrete.walkMap walk c)
                (approximate.walkMap walk a) := comparison.step_le edge _ _
        _ ≤ comparison.bias edge + comparison.gain edge * radius _ := by
          gcongr
          exact comparison.gain_nonneg edge
        _ ≤ radius _ := hradius edge

end ErrorComparison

/-! ## Main definitions -/

/-- Rows encoding lower bounds, upper budgets, and affine edge constraints. -/
inductive RadiusRow (V : Type uV) (E : Type uE)
  | lower (vertex : V)
  | upper (vertex : V)
  | edge (candidate : E)

/-- Finite vertices and edges give finitely many bounded-radius rows. -/
instance instFintypeRadiusRow [Fintype V] [Fintype E] : Fintype (RadiusRow V E) :=
  Fintype.ofEquiv (Sum (Sum V V) E)
    { toFun := fun row =>
        match row with
        | .inl (.inl vertex) => .lower vertex
        | .inl (.inr vertex) => .upper vertex
        | .inr edge => .edge edge
      invFun := fun row =>
        match row with
        | .lower vertex => .inl (.inl vertex)
        | .upper vertex => .inl (.inr vertex)
        | .edge edge => .inr edge
      left_inv := by intro row; rcases row with ((vertex | vertex) | edge) <;> rfl
      right_inv := by intro row; cases row <;> rfl }

/-- Normal vector of a bounded-radius inequality. -/
def radiusDelta [DecidableEq V] (G : Maths.EdgeGraph V E) (gain : E → ℝ) :
    RadiusRow V E → V → ℝ
  | .lower vertex, coordinate => if coordinate = vertex then 1 else 0
  | .upper vertex, coordinate => if coordinate = vertex then -1 else 0
  | .edge edge, coordinate =>
      (if coordinate = G.target edge then 1 else 0) -
        gain edge * if coordinate = G.source edge then 1 else 0

/-- Right-hand side of a bounded-radius inequality. -/
def radiusBase (lower upper : V → ℝ) (bias : E → ℝ) : RadiusRow V E → ℝ
  | .lower vertex => lower vertex
  | .upper vertex => -upper vertex
  | .edge edge => bias edge

private theorem radiusDelta_edge_dotProduct [Fintype V] [DecidableEq V]
    (G : Maths.EdgeGraph V E) (gain : E → ℝ) (radius : V → ℝ) (edge : E) :
    dotProduct (radiusDelta G gain (.edge edge)) radius =
      radius (G.target edge) - gain edge * radius (G.source edge) := by
  classical
  simp [radiusDelta, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- Finite linear feasibility is exactly existence of radii within their
bounds and closed under every affine edge comparison. -/
theorem radius_feasible_iff [Fintype V] [Fintype E] [DecidableEq V]
    (G : Maths.EdgeGraph V E) (gain bias : E → ℝ) (lower upper : V → ℝ) :
    Maths.LinearProgramming.IsFeasible
        (Maths.finiteInequalityMatrix (radiusDelta G gain))
        (radiusBase lower upper bias) ↔
      ∃ radius : V → ℝ,
        (∀ vertex, lower vertex ≤ radius vertex) ∧
        (∀ vertex, radius vertex ≤ upper vertex) ∧
        ∀ edge, bias edge + gain edge * radius (G.source edge) ≤
          radius (G.target edge) := by
  rw [Maths.finiteInequality_feasible_iff]
  constructor
  · rintro ⟨radius, hradius⟩
    refine ⟨radius, fun vertex => ?_, fun vertex => ?_, fun edge => ?_⟩
    · simpa [radiusBase, radiusDelta, dotProduct] using hradius (.lower vertex)
    · have h := hradius (.upper vertex)
      simpa [radiusBase, radiusDelta, dotProduct, Finset.sum_sub_distrib,
        Finset.mul_sum] using h
    · have h := hradius (.edge edge)
      rw [radiusBase, radiusDelta_edge_dotProduct] at h
      linarith
  · rintro ⟨radius, hlower, hupper, hedge⟩
    refine ⟨radius, ?_⟩
    intro row
    cases row with
    | lower vertex =>
        simpa [radiusBase, radiusDelta, dotProduct] using hlower vertex
    | upper vertex =>
        simpa [radiusBase, radiusDelta, dotProduct] using hupper vertex
    | edge edge =>
        rw [radiusBase, radiusDelta_edge_dotProduct]
        linarith [hedge edge]

/-- An infeasible bounded-radius comparison admits a normalized certificate
supported on at most the number of modes plus one rows. -/
theorem exists_sparse_radius_certificate_of_infeasible
    [Fintype V] [Fintype E] [DecidableEq V]
    (G : Maths.EdgeGraph V E) (gain bias : E → ℝ) (lower upper : V → ℝ)
    (hinfeasible : ¬Maths.LinearProgramming.IsFeasible
      (Maths.finiteInequalityMatrix (radiusDelta G gain))
      (radiusBase lower upper bias)) :
    ∃ coefficient : RadiusRow V E → ℝ,
      Maths.FiniteInequality.IsNormalizedCertificate (radiusDelta G gain) coefficient ∧
      0 < Maths.FiniteInequality.certificateValue
        (radiusBase lower upper bias) coefficient ∧
      Fintype.card {row : RadiusRow V E // coefficient row ≠ 0} ≤
        Fintype.card V + 1 := by
  have hpotential : ¬∃ radius : V → ℝ, ∀ row,
      radiusBase lower upper bias row ≤
        dotProduct (radiusDelta G gain row) radius := by
    intro hexists
    exact hinfeasible <|
      (Maths.finiteInequality_feasible_iff _ _).mpr hexists
  obtain ⟨coefficient, hcertificate, hpositive, hcard⟩ :=
    Maths.FiniteInequality.exists_positive_normalizedCertificate_support_card_le_rank_add_one
      (radiusDelta G gain) (radiusBase lower upper bias) hpotential
  refine ⟨coefficient, hcertificate, hpositive, hcard.trans ?_⟩
  apply Nat.add_le_add_right
  calc
    Set.finrank ℝ (Set.range (radiusDelta G gain)) ≤
        Module.finrank ℝ (V → ℝ) := Submodule.finrank_le _
    _ = Fintype.card V := Module.finrank_pi ℝ

/-! ## Main results -/

/-- The example mode type is finite. -/
instance instFintypeExampleMode : Fintype ExampleMode :=
  Fintype.ofList [.bool, .fin3] (by intro mode; cases mode <;> simp)

/-- The example edge type is finite. -/
instance instFintypeExampleEdge : Fintype ExampleEdge :=
  Fintype.ofList [.expand, .reset] (by intro edge; cases edge <;> simp)

/-- Approximate states for the example: unit data in Boolean mode and a Boolean in finite mode. -/
def exampleApproximateState : ExampleMode → Type
  | .bool => Unit
  | .fin3 => Bool

/-- Approximate transitions for the heterogeneous example. -/
def exampleApproximateStep : (edge : ExampleEdge) →
    exampleApproximateState (examplePhysicalGraph.source edge) →
      exampleApproximateState (examplePhysicalGraph.target edge)
  | .expand, _ => false
  | .reset, _ => ()

/-- Approximate transport for the heterogeneous example. -/
def exampleApproximateTransport :
    Maths.Transport examplePhysicalGraph exampleApproximateState where
  edgeMap := exampleApproximateStep

/-- Error used in the heterogeneous example. -/
def exampleError : (vertex : ExampleMode) →
    exampleState vertex → exampleApproximateState vertex → ℝ
  | .bool, concrete, _ => concrete.toNat
  | .fin3, concrete, _ => concrete.val

/-- Local affine error comparison for the heterogeneous example. -/
def exampleErrorComparison :
    ErrorComparison examplePhysicalTransport exampleApproximateTransport where
  error := exampleError
  bias
    | .expand => 1
    | .reset => 1
  gain
    | .expand => 1
    | .reset => 0
  gain_nonneg edge := by cases edge <;> norm_num
  step_le edge c a := by
    cases edge with
    | expand =>
        change exampleError .fin3 (exampleExpand c) false ≤
          1 + 1 * exampleError .bool c a
        cases c <;> norm_num [exampleError, exampleExpand]
    | reset =>
        change exampleError .bool (exampleReset c) () ≤
          1 + 0 * exampleError .fin3 c a
        simp only [zero_mul, add_zero, exampleError]
        cases exampleReset c <;> norm_num

/-- Radius one in Boolean mode and radius two in finite mode. -/
def exampleRadius : ExampleMode → ℝ
  | .bool => 1
  | .fin3 => 2

/-- The example radii satisfy both affine edge constraints. -/
theorem exampleRadius_isRadiusFamily :
    IsRadiusFamily exampleErrorComparison exampleRadius := by
  intro edge
  cases edge with
  | expand => change 1 + 1 * 1 ≤ 2; norm_num
  | reset => change 1 + 0 * 2 ≤ 1; norm_num

/-- Every shared example execution preserves the stated mode-dependent error radius. -/
theorem exampleErrorComparison_walk_le {start finish : ExampleMode}
    (walk : examplePhysicalGraph.Walk start finish)
    (c : exampleState start) (a : exampleApproximateState start)
    (hinitial : exampleError start c a ≤ exampleRadius start) :
    exampleError finish (examplePhysicalTransport.walkMap walk c)
        (exampleApproximateTransport.walkMap walk a) ≤ exampleRadius finish :=
  exampleErrorComparison.walk_error_le exampleRadius exampleRadius_isRadiusFamily
    walk c a hinitial

/-- Initial lower radii for the budget-rejection example. -/
def exampleLowerRadius : ExampleMode → ℝ
  | .bool => 1
  | .fin3 => 0

/-- Budgets allowing radius one in Boolean mode but only `3 / 2` in finite mode. -/
noncomputable def exampleTightUpperRadius : ExampleMode → ℝ
  | .bool => 1
  | .fin3 => 3 / 2

/-- The tight budgets make the affine comparison constraints infeasible.

The Boolean lower bound and expansion edge force the finite-mode radius to be
at least two, contradicting its budget `3 / 2`.  This rejects this comparison
model and does not assert physical unsafety. -/
theorem exampleTightBudget_infeasible :
    ¬Maths.LinearProgramming.IsFeasible
      (Maths.finiteInequalityMatrix
        (radiusDelta examplePhysicalGraph exampleErrorComparison.gain))
      (radiusBase exampleLowerRadius exampleTightUpperRadius
        exampleErrorComparison.bias) := by
  rw [radius_feasible_iff]
  rintro ⟨radius, hlower, hupper, hedge⟩
  have hstart := hlower ExampleMode.bool
  have hfinish := hupper ExampleMode.fin3
  have hstep := hedge ExampleEdge.expand
  norm_num [exampleLowerRadius, exampleTightUpperRadius] at hstart hfinish
  change 1 + 1 * radius .bool ≤ radius .fin3 at hstep
  linarith

end SwitchedHybridControl
