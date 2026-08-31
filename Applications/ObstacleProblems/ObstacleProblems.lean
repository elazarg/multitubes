/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths

/-!
# Scalar obstacle transport

A scalar obstacle problem confines a continuation value to a lower and an upper obstacle.  The
clamped affine action in `Maths.TransferSummary.ClampedAffineSummary` gives a deterministic client
for this interpretation: its lower and upper clamps are the contact obstacles, and its affine
branch is the continuation operator.

## Main definitions

* `ObstacleProblems.LowerContact` - contact with the lower obstacle.
* `ObstacleProblems.Continuation` - strict interior continuation.
* `ObstacleProblems.UpperContact` - contact with the upper obstacle.
* `ObstacleProblems.IsObstacleSolution` - the clamped fixed-point equation.

## Main results

* `ObstacleProblems.existsUnique_obstacleSolution` - an obstacle operator with slope below one
  has one solution.
* `ObstacleProblems.obstacleSolution_contact_or_continuation` - every solution is at lower
  contact, upper contact, or strict continuation.
* `ObstacleProblems.tendsto_iterate_obstacleSolution` - finite-horizon iterations converge to
  the unique obstacle solution.

## Tags

obstacle problem, stopping game, clamped affine, contact set, continuation
-/

@[expose] public section

namespace ObstacleProblems

open Maths.TransferSummary

/-! ## Obstacle predicates -/

/-- The value is in contact with the lower obstacle. -/
def LowerContact (lo : ℝ) (x : ℝ) : Prop := x = lo

/-- The value is strictly between the two obstacles. -/
def Continuation (lo hi : ℝ) (x : ℝ) : Prop := lo < x ∧ x < hi

/-- The value is in contact with the upper obstacle. -/
def UpperContact (hi : ℝ) (x : ℝ) : Prop := x = hi

/-- A scalar value solves the two-sided obstacle equation for a clamped summary. -/
def IsObstacleSolution (f : ClampedAffineSummary) (x : ℝ) : Prop := f.apply x = x

/-! ## Existence and uniqueness -/

/-- A clamped affine obstacle problem with slope below one has exactly one solution. -/
theorem existsUnique_obstacleSolution {f : ClampedAffineSummary} (hband : f.lo ≤ f.hi)
    (hcontract : f.slope < 1) :
    ∃! x : ℝ, IsObstacleSolution f x := by
  refine ⟨f.fixedPoint, ?_, ?_⟩
  · exact f.apply_fixedPoint hband hcontract
  · intro y hy
    exact f.fixedPoint_unique hband hcontract hy

/-- Every obstacle solution lies in the closed obstacle band. -/
theorem obstacleSolution_mem_Icc {f : ClampedAffineSummary} (hband : f.lo ≤ f.hi)
    (x : ℝ) (hx : IsObstacleSolution f x) : x ∈ Set.Icc f.lo f.hi := by
  rw [← hx]
  exact f.apply_mem_Icc hband x

/-! ## Contact and continuation -/

/-- A solution is in lower contact, strict continuation, or upper contact. -/
theorem obstacleSolution_contact_or_continuation {f : ClampedAffineSummary}
    (hband : f.lo ≤ f.hi) {x : ℝ} (hx : IsObstacleSolution f x) :
    LowerContact f.lo x ∨
      (Continuation f.lo f.hi x ∧ f.shift + f.slope * x = x) ∨ UpperContact f.hi x := by
  have hmem := obstacleSolution_mem_Icc hband x hx
  by_cases hlo : x = f.lo
  · exact Or.inl hlo
  · by_cases hhi : x = f.hi
    · exact Or.inr (Or.inr hhi)
    · have hlo' : f.lo < x := lt_of_le_of_ne hmem.1 (Ne.symm hlo)
      have hhi' : x < f.hi := lt_of_le_of_ne hmem.2 hhi
      have hbranch : f.shift + f.slope * x = x := by
        have hfixed : min f.hi (max f.lo (f.shift + f.slope * x)) = x := hx
        have hmax_upper : max f.lo (f.shift + f.slope * x) ≤ f.hi := by
          by_contra hnot
          have hge : f.hi ≤ max f.lo (f.shift + f.slope * x) := le_of_not_ge hnot
          rw [min_eq_left hge] at hfixed
          linarith
        have hmax : max f.lo (f.shift + f.slope * x) = x := by
          rw [min_eq_right hmax_upper] at hfixed
          exact hfixed
        have hbranch_lower : f.lo ≤ f.shift + f.slope * x := by
          by_contra hnot
          have hle : f.shift + f.slope * x ≤ f.lo := le_of_not_ge hnot
          rw [max_eq_left hle] at hmax
          linarith
        have hbranch_upper : f.shift + f.slope * x ≤ x := by
          exact (le_max_right _ _).trans_eq hmax
        have hbranch_lower' : x ≤ f.shift + f.slope * x := by
          calc
            x = max f.lo (f.shift + f.slope * x) := hmax.symm
            _ ≤ f.shift + f.slope * x := max_le hbranch_lower le_rfl
        exact le_antisymm hbranch_upper hbranch_lower'
      exact Or.inr (Or.inl ⟨⟨hlo', hhi'⟩, hbranch⟩)

/-! ## Finite-horizon convergence -/

/-- Iterating the obstacle operator converges to its unique solution from every initial value. -/
theorem tendsto_iterate_obstacleSolution {f : ClampedAffineSummary}
    (hband : f.lo ≤ f.hi) (hcontract : |f.slope| < 1) (x : ℝ) :
    Filter.Tendsto (fun n => f.apply^[n] x) Filter.atTop (nhds f.fixedPoint) :=
  f.tendsto_iterate_fixedPoint hband hcontract x

end ObstacleProblems
