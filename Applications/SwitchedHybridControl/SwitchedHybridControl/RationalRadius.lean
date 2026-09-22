/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import SwitchedHybridControl.ErrorBounds
public import Maths.LinearProgramming.CertificateCheck

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Executable rational certificates for bounded error radii

A finite comparison graph with rational gains, biases, lower bounds, and upper budgets gives an
explicit rational inequality system. Proposed radii and Farkas row weights can therefore be
checked by exact computation. A checked radius supplies all-walk error bounds for any real error
comparison whose data are the casts of the rational input. A checked certificate rules out every
real radius satisfying the same bounds and affine edge constraints.

The checkers consume witnesses and do not search for them. Rows are ordered as lower bounds,
upper budgets, and edge constraints, and are encoded by `Fin (n + n + m)`.

## Main definitions

* `SwitchedHybridControl.RationalRadiusData`: finite rational bounded-radius input.
* `SwitchedHybridControl.RationalRadiusData.checkRadius`: exact radius-witness checker.
* `SwitchedHybridControl.RationalRadiusData.checkCertificate`: exact Farkas-certificate checker.

## Main results

* `SwitchedHybridControl.RationalRadiusData.checkRadius_eq_true_iff`: exact acceptance is
  equivalent to the lower, upper, and affine transition constraints.
* `SwitchedHybridControl.RationalRadiusData.walk_error_le_of_checkRadius`: a checked witness
  gives an error bound after every walk.
* `SwitchedHybridControl.RationalRadiusData.not_exists_real_radius_of_checkCertificate`: a
  checked Farkas witness proves real infeasibility.
* `SwitchedHybridControl.twoModeRadius_check`: the radii `3 / 2` and `4` are accepted for an
  expanding and resetting two-mode comparison.
* `SwitchedHybridControl.twoModeTightCertificate_check`: a sparse certificate rejects a tighter
  upper budget.

## Tags

rational arithmetic, executable verification, switched systems, error bounds, Farkas certificate
-/

@[expose] public section

namespace SwitchedHybridControl

open Finset

/-- Executable rational data for a graph with `n` modes and `m` transitions. -/
structure RationalRadiusData (n m : ℕ) where
  /-- Source mode of each transition. -/
  source : Fin m → Fin n
  /-- Target mode of each transition. -/
  target : Fin m → Fin n
  /-- Nonnegative multiplicative gain of each transition. -/
  gain : Fin m → ℚ
  /-- Additive bias of each transition. -/
  bias : Fin m → ℚ
  /-- Lower bound on each radius. -/
  lower : Fin n → ℚ
  /-- Upper budget on each radius. -/
  upper : Fin n → ℚ
  /-- Transition gains are nonnegative. -/
  gain_nonneg : ∀ edge, 0 ≤ gain edge

namespace RationalRadiusData

variable {n m : ℕ}

/-- The finite graph underlying rational bounded-radius data. -/
def graph (data : RationalRadiusData n m) : Maths.EdgeGraph (Fin n) (Fin m) where
  source := data.source
  target := data.target

/-- Canonical encoding of lower, upper, and edge rows by a finite index. -/
def rowEquiv : (Fin n ⊕ Fin n) ⊕ Fin m ≃ Fin (n + n + m) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin m))).trans finSumFinEquiv

/-- Decode a finite row index as a lower, upper, or edge row. -/
def row (index : Fin (n + n + m)) : (Fin n ⊕ Fin n) ⊕ Fin m :=
  rowEquiv.symm index

/-- Rational coefficient matrix for lower, upper, and affine transition constraints. -/
def matrix (data : RationalRadiusData n m) : Fin (n + n + m) → Fin n → ℚ :=
  fun index coordinate =>
    match row index with
    | .inl (.inl vertex) => if coordinate = vertex then 1 else 0
    | .inl (.inr vertex) => if coordinate = vertex then -1 else 0
    | .inr edge =>
        (if coordinate = data.target edge then 1 else 0) -
          data.gain edge * if coordinate = data.source edge then 1 else 0

/-- Rational right-hand side for lower, upper, and affine transition constraints. -/
def base (data : RationalRadiusData n m) : Fin (n + n + m) → ℚ :=
  fun index =>
    match row index with
    | .inl (.inl vertex) => data.lower vertex
    | .inl (.inr vertex) => -data.upper vertex
    | .inr edge => data.bias edge

/-- Check a proposed rational bounded-radius family by exact arithmetic. -/
def checkRadius (data : RationalRadiusData n m) (radius : Fin n → ℚ) : Bool :=
  Maths.LinearProgramming.checkRationalPoint data.matrix data.base radius

/-- Check proposed rational Farkas row weights by exact arithmetic. -/
def checkCertificate (data : RationalRadiusData n m)
    (coefficient : Fin (n + n + m) → ℚ) : Bool :=
  Maths.LinearProgramming.checkRationalCertificate data.matrix data.base coefficient

private theorem rowEquiv_apply (candidate : (Fin n ⊕ Fin n) ⊕ Fin m) :
    row (rowEquiv candidate) = candidate := by
  simp [row]

private theorem rowEval_lower (data : RationalRadiusData n m) (radius : Fin n → ℚ)
    (vertex : Fin n) :
    Maths.LinearProgramming.rowEval data.matrix (rowEquiv (.inl (.inl vertex))) radius =
      radius vertex := by
  simp [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply]

private theorem rowEval_upper (data : RationalRadiusData n m) (radius : Fin n → ℚ)
    (vertex : Fin n) :
    Maths.LinearProgramming.rowEval data.matrix (rowEquiv (.inl (.inr vertex))) radius =
      -radius vertex := by
  simp [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply]

private theorem rowEval_edge (data : RationalRadiusData n m) (radius : Fin n → ℚ)
    (edge : Fin m) :
    Maths.LinearProgramming.rowEval data.matrix (rowEquiv (.inr edge)) radius =
      radius (data.target edge) - data.gain edge * radius (data.source edge) := by
  simp [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply, sub_mul,
    Finset.sum_sub_distrib]

private theorem realRowEval (data : RationalRadiusData n m) (radius : Fin n → ℝ)
    (candidate : (Fin n ⊕ Fin n) ⊕ Fin m) :
    Maths.LinearProgramming.rowEval
        (fun i j => (data.matrix i j : ℝ)) (rowEquiv candidate) radius =
      match candidate with
      | .inl (.inl vertex) => radius vertex
      | .inl (.inr vertex) => -radius vertex
      | .inr edge => radius (data.target edge) -
          (data.gain edge : ℝ) * radius (data.source edge) := by
  classical
  obtain (vertex | edge) := candidate
  · obtain (vertex | vertex) := vertex
    · have hcast (x : Fin n) :
          ((if x = vertex then (1 : ℚ) else 0 : ℚ) : ℝ) =
            if x = vertex then 1 else 0 := by
        split <;> simp_all
      simp_rw [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply, hcast]
      simp
    · have hcast (x : Fin n) :
          ((if x = vertex then (-1 : ℚ) else 0 : ℚ) : ℝ) =
            if x = vertex then -1 else 0 := by
        split <;> simp_all
      simp_rw [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply, hcast]
      simp
  · have htarget (x : Fin n) :
        ((if x = data.target edge then (1 : ℚ) else 0 : ℚ) : ℝ) =
          if x = data.target edge then 1 else 0 := by
      split <;> simp_all
    have hsource (x : Fin n) :
        ((data.gain edge * if x = data.source edge then 1 else 0 : ℚ) : ℝ) =
          (data.gain edge : ℝ) * if x = data.source edge then 1 else 0 := by
      by_cases h : x = data.source edge <;> simp [h]
    simp_rw [Maths.LinearProgramming.rowEval, matrix, rowEquiv_apply, Rat.cast_sub,
      htarget, hsource]
    simp [sub_mul, Finset.sum_sub_distrib]

/-- The executable radius check accepts exactly the bounded affine-compatible radii. -/
theorem checkRadius_eq_true_iff (data : RationalRadiusData n m) (radius : Fin n → ℚ) :
    data.checkRadius radius = true ↔
      (∀ vertex, data.lower vertex ≤ radius vertex) ∧
      (∀ vertex, radius vertex ≤ data.upper vertex) ∧
      ∀ edge, data.bias edge + data.gain edge * radius (data.source edge) ≤
        radius (data.target edge) := by
  unfold checkRadius
  rw [Maths.LinearProgramming.checkRationalPoint_eq_true_iff]
  constructor
  · intro hrows
    refine ⟨fun vertex => ?_, fun vertex => ?_, fun edge => ?_⟩
    · have h := hrows (rowEquiv (.inl (.inl vertex)))
      rw [base, rowEquiv_apply, rowEval_lower] at h
      exact h
    · have h := hrows (rowEquiv (.inl (.inr vertex)))
      rw [base, rowEquiv_apply, rowEval_upper] at h
      linarith
    · have h := hrows (rowEquiv (.inr edge))
      rw [base, rowEquiv_apply, rowEval_edge] at h
      linarith
  · rintro ⟨hlower, hupper, hedge⟩ index
    obtain ⟨candidate, rfl⟩ := rowEquiv.surjective index
    obtain (vertex | edge) := candidate
    · obtain (vertex | vertex) := vertex
      · rw [base, rowEquiv_apply, rowEval_lower]
        exact hlower vertex
      · rw [base, rowEquiv_apply, rowEval_upper]
        linarith [hupper vertex]
    · rw [base, rowEquiv_apply, rowEval_edge]
      linarith [hedge edge]

/-- A checked radius lies between its bounds and satisfies every affine edge constraint. -/
theorem bounds_of_checkRadius (data : RationalRadiusData n m) (radius : Fin n → ℚ)
    (hcheck : data.checkRadius radius = true) :
    (∀ vertex, data.lower vertex ≤ radius vertex) ∧
      (∀ vertex, radius vertex ≤ data.upper vertex) ∧
      ∀ edge, data.bias edge + data.gain edge * radius (data.source edge) ≤
        radius (data.target edge) :=
  (data.checkRadius_eq_true_iff radius).mp hcheck

/-- A checked rational radius becomes a real compatible radius after casting. -/
theorem isRadiusFamily_of_checkRadius (data : RationalRadiusData n m)
    {Concrete Approximate : Fin n → Type*}
    {concrete : Maths.Transport data.graph Concrete}
    {approximate : Maths.Transport data.graph Approximate}
    (comparison : ErrorComparison concrete approximate)
    (hgain : ∀ edge, comparison.gain edge = (data.gain edge : ℝ))
    (hbias : ∀ edge, comparison.bias edge = (data.bias edge : ℝ))
    (radius : Fin n → ℚ) (hcheck : data.checkRadius radius = true) :
    IsRadiusFamily comparison (fun vertex => (radius vertex : ℝ)) := by
  intro edge
  have hedge := (data.bounds_of_checkRadius radius hcheck).2.2 edge
  have hcast := Rat.cast_mono (K := ℝ) hedge
  rw [hgain, hbias]
  change (data.bias edge : ℝ) + (data.gain edge : ℝ) *
      (radius (data.source edge) : ℝ) ≤ (radius (data.target edge) : ℝ)
  simpa only [Rat.cast_add, Rat.cast_mul] using hcast

/-- A checked rational radius gives an error bound after every shared finite execution. -/
theorem walk_error_le_of_checkRadius (data : RationalRadiusData n m)
    {Concrete Approximate : Fin n → Type*}
    {concrete : Maths.Transport data.graph Concrete}
    {approximate : Maths.Transport data.graph Approximate}
    (comparison : ErrorComparison concrete approximate)
    (hgain : ∀ edge, comparison.gain edge = (data.gain edge : ℝ))
    (hbias : ∀ edge, comparison.bias edge = (data.bias edge : ℝ))
    (radius : Fin n → ℚ) (hcheck : data.checkRadius radius = true)
    {start finish : Fin n} (walk : data.graph.Walk start finish)
    (c : Concrete start) (a : Approximate start)
    (hinitial : comparison.error start c a ≤ (radius start : ℝ)) :
    comparison.error finish (concrete.walkMap walk c) (approximate.walkMap walk a) ≤
      (radius finish : ℝ) :=
  comparison.walk_error_le _
    (data.isRadiusFamily_of_checkRadius comparison hgain hbias radius hcheck)
    walk c a hinitial

/-- A checked Farkas certificate rules out every real bounded compatible radius. -/
theorem not_exists_real_radius_of_checkCertificate (data : RationalRadiusData n m)
    (coefficient : Fin (n + n + m) → ℚ)
    (hcheck : data.checkCertificate coefficient = true) :
    ¬∃ radius : Fin n → ℝ,
      (∀ vertex, (data.lower vertex : ℝ) ≤ radius vertex) ∧
      (∀ vertex, radius vertex ≤ (data.upper vertex : ℝ)) ∧
      ∀ edge, (data.bias edge : ℝ) + (data.gain edge : ℝ) *
        radius (data.source edge) ≤ radius (data.target edge) := by
  classical
  intro hexists
  apply Maths.LinearProgramming.not_realFeasible_of_checkRationalCertificate
    data.matrix data.base coefficient hcheck
  rcases hexists with ⟨radius, hlower, hupper, hedge⟩
  refine ⟨radius, fun index => ?_⟩
  generalize hrow : row index = candidate
  have hindex : index = rowEquiv candidate := by
    rw [← hrow]
    exact (rowEquiv.apply_symm_apply index).symm
  obtain (vertex | edge) := candidate
  · obtain (vertex | vertex) := vertex
    · rw [hindex, realRowEval]
      simpa [base, rowEquiv_apply] using hlower vertex
    · rw [hindex, realRowEval]
      simp only [base, rowEquiv_apply, Rat.cast_neg]
      linarith [hupper vertex]
  · rw [hindex, realRowEval]
    simp only [base, rowEquiv_apply]
    linarith [hedge edge]

end RationalRadiusData

/-! ## Main results -/

/-- Two-mode expanding/resetting data with gains `2` and `1 / 8` and unit biases. -/
def twoModeRadiusData : RationalRadiusData 2 2 where
  source
    | 0 => 0
    | 1 => 1
  target
    | 0 => 1
    | 1 => 0
  gain
    | 0 => 2
    | 1 => 1 / 8
  bias := fun _ => 1
  lower := fun _ => 0
  upper
    | 0 => 3 / 2
    | 1 => 4
  gain_nonneg edge := by fin_cases edge <;> norm_num

/-- The exact rational checker accepts radii `3 / 2` and `4`. -/
theorem twoModeRadius_check :
    twoModeRadiusData.checkRadius ![3 / 2, 4] = true := by
  apply (Maths.LinearProgramming.checkRationalPoint_eq_true_iff _ _ _).mpr
  intro index
  obtain ⟨candidate, rfl⟩ := RationalRadiusData.rowEquiv.surjective index
  obtain (vertex | edge) := candidate
  · obtain (vertex | vertex) := vertex <;> fin_cases vertex <;>
      first
      | rw [RationalRadiusData.rowEval_lower]
        norm_num [RationalRadiusData.base, RationalRadiusData.rowEquiv_apply,
          twoModeRadiusData]
      | rw [RationalRadiusData.rowEval_upper]
        norm_num [RationalRadiusData.base, RationalRadiusData.rowEquiv_apply,
          twoModeRadiusData]
  · fin_cases edge <;>
      rw [RationalRadiusData.rowEval_edge] <;>
      norm_num [RationalRadiusData.base, RationalRadiusData.rowEquiv_apply,
        twoModeRadiusData]

/-- The same system with a finite-mode upper budget of `7 / 2`. -/
def twoModeTightData : RationalRadiusData 2 2 :=
  { twoModeRadiusData with upper := ![3 / 2, 7 / 2] }

/-- Sparse row weights: the mode-one upper row and both transition rows. -/
def twoModeTightCertificate : Fin 6 → ℚ := fun index =>
  match RationalRadiusData.row (n := 2) (m := 2) index with
  | .inl (.inl _) => 0
  | .inl (.inr vertex) => if vertex = 1 then 3 else 0
  | .inr edge => if edge = 0 then 4 else 8

/-- The sparse certificate exactly rejects the tighter budget. -/
theorem twoModeTightCertificate_check :
    twoModeTightData.checkCertificate twoModeTightCertificate = true := by
  apply (Maths.LinearProgramming.checkRationalCertificate_eq_true_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro index
    generalize hrow : RationalRadiusData.row index = candidate
    obtain (vertex | edge) := candidate
    · obtain (vertex | vertex) := vertex <;> fin_cases vertex <;>
        norm_num [twoModeTightCertificate, hrow]
    · fin_cases edge <;> norm_num [twoModeTightCertificate, hrow]
  · intro coordinate
    rw [← Equiv.sum_comp RationalRadiusData.rowEquiv]
    fin_cases coordinate <;>
      norm_num [RationalRadiusData.matrix, RationalRadiusData.rowEquiv_apply,
        twoModeTightData, twoModeRadiusData, twoModeTightCertificate]
  · rw [← Equiv.sum_comp RationalRadiusData.rowEquiv]
    norm_num [RationalRadiusData.base, RationalRadiusData.rowEquiv_apply,
      twoModeTightData, twoModeRadiusData, twoModeTightCertificate]

end SwitchedHybridControl
