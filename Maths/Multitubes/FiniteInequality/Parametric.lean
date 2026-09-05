/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.FiniteInequality.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Linarith

/-!
# Parameter sets of finite inequalities

When the row normals of a finite inequality system are fixed, feasibility is a closed condition
on continuously varying lower bounds. Farkas duality expresses the feasible parameter set as an
intersection of closed dual inequalities. No boundedness of the primal witnesses is required.
For affinely varying real lower bounds, the feasible parameter set is also convex.

## Main definitions

* `Maths.FiniteInequality.feasibleParameters` - parameters admitting a feasible potential.

## Main results

* `Maths.FiniteInequality.isClosed_feasibleParameters` - closedness for continuous lower bounds.
* `Maths.FiniteInequality.convex_feasibleParameters` - convexity for affine real lower bounds.
-/

@[expose] public section

namespace Maths.FiniteInequality

open scoped BigOperators

variable {State Row Parameter : Type*} [Fintype State] [Fintype Row]

/-- The parameters for which a fixed finite family of row normals admits a feasible potential. -/
def feasibleParameters (delta : Row → State → ℝ) (base : Parameter → Row → ℝ) : Set Parameter :=
  {parameter | ∃ potential : State → ℝ,
    ∀ row, base parameter row ≤ dotProduct (delta row) potential}

/-- Continuously varying lower bounds give a closed feasible parameter set when the row normals
are fixed. The primal feasible potentials need not be bounded. -/
theorem isClosed_feasibleParameters [TopologicalSpace Parameter]
    (delta : Row → State → ℝ) (base : Parameter → Row → ℝ)
    (hbase : ∀ row, Continuous (fun parameter => base parameter row)) :
    IsClosed (feasibleParameters delta base) := by
  classical
  simp only [feasibleParameters, exists_potential_iff_no_nonnegative_incompatibility,
    not_exists, not_and, not_lt, Set.ofPred_forall]
  refine isClosed_iInter fun coefficient => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => ?_
  apply isClosed_le _ continuous_const
  exact continuous_finsetSum _ fun row _ => continuous_const.mul (hbase row)

omit [Fintype Row] in
/-- Affine dependence of the lower bounds on a real parameter gives a convex feasible set. -/
theorem convex_feasibleParameters (delta : Row → State → ℝ) (offset rate : Row → ℝ) :
    Convex ℝ
      (feasibleParameters delta (fun parameter row => offset row + parameter * rate row)) := by
  intro first hfirst second hsecond a b ha hb hab
  obtain ⟨x, hx⟩ := hfirst
  obtain ⟨y, hy⟩ := hsecond
  refine ⟨a • x + b • y, fun row => ?_⟩
  have hfirst := mul_le_mul_of_nonneg_left (hx row) ha
  have hsecond := mul_le_mul_of_nonneg_left (hy row) hb
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hoffset : a * offset row + b * offset row = offset row := by
    rw [← add_mul, hab, one_mul]
  nlinarith

end Maths.FiniteInequality
