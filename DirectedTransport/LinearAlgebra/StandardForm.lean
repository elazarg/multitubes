/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

import DirectedTransport.LinearAlgebra.FourierMotzkin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# Standard-form linear programs

A *standard-form* polyhedron is the nonnegative affine fiber
`standardFeasibleSet A rhs = {z | 0 ≤ z ∧ A *ᵥ z = rhs}` of a matrix `A` over a linearly
ordered field. This file develops the basic theory of such polyhedra and of linear
optimization over them.

Almost everything here — the fiber itself, its convexity, Farkas' lemma, and the identification
of the extreme points with the basic feasible solutions — is proved over an arbitrary linearly
ordered field `𝕜`, with the certificate direction of Farkas coming from the theorem of the
alternative in `DirectedTransport.LinearAlgebra.FourierMotzkin`. Only the three results that
genuinely use topology are stated over `ℝ`: closedness of the fiber, the continuous functional
`finiteDotContinuousLinearMap`, and attainment of an optimum at an extreme point, which goes
through Krein–Milman.

Three things are proved.

*Farkas' lemma in standard form.* Exactly one of `{z | 0 ≤ z ∧ A *ᵥ z = rhs}` and
`{y | 0 ≤ Aᵀ *ᵥ y ∧ ⟪y, rhs⟫ < 0}` is nonempty. The certificate direction is obtained from
the inequality-form theorem of the alternative in
`DirectedTransport.LinearAlgebra.FourierMotzkin`, applied to the dual system in the free
variable `y`, whose Farkas certificate is exactly a scaled primal feasible point.

*Basic feasible solutions.* A feasible point is an extreme point of the fiber exactly when the
columns carrying its positive support are linearly independent. Consequently the support of an
extreme point has at most `Fintype.card Row` elements: extreme points are sparse.

*Attainment at an extreme point.* Every attained linear optimum over the fiber is attained at
an extreme point, with no boundedness hypothesis on the fiber. The proof passes to the exposed
optimal face, minimizes total nonnegative mass on it, and applies Krein–Milman to the resulting
compact minimum-mass face.

Together these are the standard-form counterparts of the inequality-form results in
`DirectedTransport.LinearAlgebra.FourierMotzkin`, and they are what the sparse-certificate
arguments in `DirectedTransport.FiniteInequality` and `DirectedTransport.MaxAffine` consume.

## Main definitions

* `DirectedTransport.LinearAlgebra.standardFeasibleSet`: the standard-form nonnegative affine
  fiber `{z | 0 ≤ z ∧ A *ᵥ z = rhs}`.
* `DirectedTransport.LinearAlgebra.IsStandardOptimal`: optimality of a feasible point for a
  linear objective over a standard-form fiber.
* `DirectedTransport.LinearAlgebra.finiteDotContinuousLinearMap`: the continuous linear
  functional given by a finite coefficient vector.

## Main results

* `DirectedTransport.LinearAlgebra.mem_standardFeasibleSet`: the membership criterion.
* `DirectedTransport.LinearAlgebra.isClosed_standardFeasibleSet`: a standard-form fiber is
  closed.
* `DirectedTransport.LinearAlgebra.nonempty_standardFeasibleSet_iff`,
  `DirectedTransport.LinearAlgebra.not_nonempty_standardFeasibleSet_iff`: **Farkas' lemma** in
  standard form, as an alternative between the fiber and the dual certificate set.
* `DirectedTransport.LinearAlgebra.linearIndependent_supportColumns_of_extreme_standardFeasible`,
  `DirectedTransport.LinearAlgebra.mem_extremePoints_standardFeasibleSet_of_linearIndependent`,
  `DirectedTransport.LinearAlgebra.mem_extremePoints_standardFeasibleSet_iff`: extreme points
  are exactly the basic feasible solutions.
* `DirectedTransport.LinearAlgebra.card_support_le_of_extreme_standardFeasible`: an extreme
  point is supported on at most `Fintype.card Row` coordinates.
* `DirectedTransport.LinearAlgebra.exists_extreme_standardOptimal_of_standardOptimal`: an
  attained linear optimum is attained at an extreme point.

## TODO

* The Cramer/parametric-basis theory (support Gram matrices, analytic selection of a basis
  along a parameter) that a quantitative *stability* result would need.

## Tags

linear programming, standard form, polyhedron, Farkas lemma, basic feasible solution,
extreme point, Krein-Milman
-/

open Finset Matrix Set

@[expose] public section

namespace DirectedTransport
namespace LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### The standard-form feasible set -/

/-- A standard-form nonnegative affine fiber: the vectors that are nonnegative in every
coordinate and are mapped to `rhs` by `A`. -/
def standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) : Set (Col → 𝕜) :=
  {z | (∀ j, 0 ≤ z j) ∧ A *ᵥ z = rhs}

omit [IsStrictOrderedRing 𝕜] in
/-- Membership in a standard-form fiber unfolds to nonnegativity together with the affine
equation. -/
@[simp] theorem mem_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (z : Col → 𝕜) :
    z ∈ standardFeasibleSet A rhs ↔ (∀ j, 0 ≤ z j) ∧ A *ᵥ z = rhs := Iff.rfl

omit [IsStrictOrderedRing 𝕜] in
/-- Every point of a standard-form fiber is nonnegative. -/
theorem nonneg_of_mem_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {z : Col → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (j : Col) : 0 ≤ z j := hz.1 j

omit [IsStrictOrderedRing 𝕜] in
/-- Every point of a standard-form fiber satisfies the affine equation, row by row. -/
theorem mulVec_apply_of_mem_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {z : Col → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (i : Row) : (A *ᵥ z) i = rhs i :=
  congrFun hz.2 i

/-- A standard-form fiber is convex: it is cut out by linear equations and inequalities. -/
theorem convex_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) :
    Convex 𝕜 (standardFeasibleSet A rhs) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun j => ?_, ?_⟩
  · have := hx.1 j
    have := hy.1 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx.2, hy.2,
      ← add_smul, hab, one_smul]

/-- A standard-form nonnegative affine fiber is closed: it is the intersection of the closed
half-spaces `0 ≤ z j` with the closed level sets of the coordinates of `z ↦ A *ᵥ z`. -/
theorem isClosed_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ) :
    IsClosed (standardFeasibleSet A rhs) := by
  rw [show standardFeasibleSet A rhs =
      (⋂ j, {z : Col → ℝ | 0 ≤ z j}) ∩
        ⋂ i, {z : Col → ℝ | (A *ᵥ z) i = rhs i} by
    ext z
    simp only [mem_standardFeasibleSet, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hz, heq⟩
      exact ⟨hz, fun i => congrFun heq i⟩
    · rintro ⟨hz, heq⟩
      exact ⟨hz, funext heq⟩]
  refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_iInter fun i => ?_)
  · exact isClosed_le continuous_const (continuous_apply j)
  · have hrow : (fun z : Col → ℝ => (A *ᵥ z) i) = fun z => ∑ j, A i j * z j := by
      funext z
      simp [Matrix.mulVec, dotProduct]
    have hcont : Continuous fun z : Col → ℝ => (A *ᵥ z) i := by
      rw [hrow]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
    exact isClosed_eq hcont continuous_const

/-! ### Farkas' lemma in standard form

The dual object to a standard-form fiber is a vector `y` on the rows with `Aᵀ *ᵥ y` nonnegative
and `⟪y, rhs⟫` negative: pairing such a `y` with a feasible `z` would give
`0 ≤ ⟪Aᵀ y, z⟫ = ⟪y, A z⟫ = ⟪y, rhs⟫ < 0`. Farkas' lemma says this obvious obstruction is the
only one. -/

/-- A dual certificate of infeasibility of the standard-form system `0 ≤ z`, `A *ᵥ z = rhs`:
a row vector that is nonnegative against every column of `A` but pairs negatively with the
right-hand side. -/
def IsStandardCertificate
    {Row Col : Type*} [Fintype Row]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (y : Row → 𝕜) : Prop :=
  (∀ j, 0 ≤ ∑ i, y i * A i j) ∧ ∑ i, y i * rhs i < 0

/-- A standard-form fiber and a dual certificate cannot both exist: evaluating the certificate
on a feasible point gives `0 ≤ ⟪y, rhs⟫ < 0`. -/
theorem not_isStandardCertificate_of_mem_standardFeasibleSet
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {z : Col → 𝕜} {y : Row → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) : ¬ IsStandardCertificate A rhs y := by
  rintro ⟨hy, hneg⟩
  have hr (i : Row) : rhs i = ∑ j, A i j * z j := by
    rw [← mulVec_apply_of_mem_standardFeasibleSet hz i]
    simp [Matrix.mulVec, dotProduct]
  have hpair : ∑ i, y i * rhs i = ∑ j, (∑ i, y i * A i j) * z j := by
    simp only [hr, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rw [hpair] at hneg
  exact absurd hneg (not_lt.mpr (Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (hz.1 j)))

/-- **Farkas' lemma**, standard form, infeasible direction: if the nonnegative affine fiber of
`A` over `rhs` is empty, a dual certificate exists.

The proof applies the inequality-form theorem of the alternative
(`DirectedTransport.LinearAlgebra.theorem_of_alternative`) to the dual system
`Aᵀ *ᵥ y ≥ 0`, `-⟪y, rhs⟫ ≥ 1` in the free variable `y`. A Farkas certificate of *that* system
is a nonnegative vector on `Col ⊕ Unit` whose `Col` part solves `A *ᵥ z = t • rhs` with
`0 < t`; dividing by `t` produces a point of the fiber. -/
theorem exists_isStandardCertificate_of_not_nonempty
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    (hempty : ¬ (standardFeasibleSet A rhs).Nonempty) :
    ∃ y : Row → 𝕜, IsStandardCertificate A rhs y := by
  classical
  by_contra hnocert
  push Not at hnocert
  -- The dual system, transported to the variable index `Fin (card Row)`.
  set e : Row ≃ Fin (Fintype.card Row) := Fintype.equivFin Row with he
  set M : (Col ⊕ Unit) → Fin (Fintype.card Row) → 𝕜 :=
    Sum.elim (fun j k => A (e.symm k) j) (fun _ k => -rhs (e.symm k)) with hM
  set bvec : (Col ⊕ Unit) → 𝕜 := Sum.elim (fun _ => 0) (fun _ => 1) with hb
  -- It is infeasible, since a solution would be a dual certificate.
  have hinfeasible : ¬ IsFeasible M bvec := by
    rintro ⟨x, hx⟩
    refine absurd ⟨fun j => ?_, ?_⟩ (hnocert fun i => x (e i))
    · have hxj := hx (Sum.inl j)
      simp only [hb, hM, Sum.elim_inl, rowEval] at hxj
      have hEq : ∑ i, x (e i) * A i j = ∑ k, A (e.symm k) j * x k :=
        Fintype.sum_equiv e _ _ fun i => by rw [Equiv.symm_apply_apply]; ring
      rw [hEq]
      exact hxj
    · have hxu := hx (Sum.inr ())
      simp only [hb, hM, Sum.elim_inr, rowEval] at hxu
      have hEq : ∑ i, x (e i) * rhs i = -∑ k, -rhs (e.symm k) * x k := by
        rw [← Finset.sum_neg_distrib]
        exact Fintype.sum_equiv e _ _ fun i => by rw [Equiv.symm_apply_apply]; ring
      rw [hEq]
      linarith
  -- So it has a Farkas certificate, whose `Col` part is a scaled point of the fiber.
  obtain ⟨u, hu_nonneg, hu_zero, hu_pos⟩ := (theorem_of_alternative M bvec).mp hinfeasible
  set t : 𝕜 := u (Sum.inr ()) with ht
  have htpos : 0 < t := by
    have hval : ∑ i, u i * bvec i = t := by
      rw [Fintype.sum_sum_type, hb, ht]
      simp
    rwa [hval] at hu_pos
  have hrow (i : Row) : (A *ᵥ fun j => u (Sum.inl j)) i = t * rhs i := by
    have hk := hu_zero (e i)
    rw [Fintype.sum_sum_type] at hk
    simp only [hM, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply] at hk
    have hunit : ∑ _b : Unit, u (Sum.inr ()) * -rhs i = t * -rhs i := by
      rw [ht]
      simp
    rw [hunit, mul_neg] at hk
    have hcol : ∑ j, u (Sum.inl j) * A i j = t * rhs i := by linarith
    rw [← hcol]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine hempty ⟨fun j => u (Sum.inl j) / t, fun j => div_nonneg (hu_nonneg _) htpos.le, ?_⟩
  funext i
  have hsmul : (fun j => u (Sum.inl j) / t) = t⁻¹ • fun j => u (Sum.inl j) := by
    funext j
    simp [div_eq_inv_mul]
  rw [hsmul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hrow i, ← mul_assoc,
    inv_mul_cancel₀ htpos.ne', one_mul]

/-- **Farkas' lemma**, standard form: the nonnegative affine fiber `{z | 0 ≤ z ∧ A *ᵥ z = rhs}`
is empty exactly when a dual certificate `y` exists, with `Aᵀ *ᵥ y` nonnegative and
`⟪y, rhs⟫` negative. -/
theorem not_nonempty_standardFeasibleSet_iff
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) :
    ¬ (standardFeasibleSet A rhs).Nonempty ↔ ∃ y : Row → 𝕜, IsStandardCertificate A rhs y :=
  ⟨exists_isStandardCertificate_of_not_nonempty A rhs, by
    rintro ⟨y, hy⟩ ⟨z, hz⟩
    exact not_isStandardCertificate_of_mem_standardFeasibleSet hz hy⟩

/-- **Farkas' lemma**, standard form, stated positively: the fiber is nonempty exactly when no
dual certificate exists. -/
theorem nonempty_standardFeasibleSet_iff
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) :
    (standardFeasibleSet A rhs).Nonempty ↔ ¬ ∃ y : Row → 𝕜, IsStandardCertificate A rhs y := by
  rw [← not_nonempty_standardFeasibleSet_iff, not_not]

/-! ### Linear objectives and standard-form optima -/

/-- The continuous linear functional `z ↦ ∑ j, c j * z j` represented by a finite coefficient
vector `c`. -/
noncomputable def finiteDotContinuousLinearMap
    {Col : Type*} [Fintype Col] (c : Col → ℝ) :
    (Col → ℝ) →L[ℝ] ℝ :=
  ∑ j, c j • ContinuousLinearMap.proj j

/-- `finiteDotContinuousLinearMap c` acts as the dot product with `c`. -/
@[simp] theorem finiteDotContinuousLinearMap_apply
    {Col : Type*} [Fintype Col] (c z : Col → ℝ) :
    finiteDotContinuousLinearMap c z = ∑ j, c j * z j := by
  simp [finiteDotContinuousLinearMap]

/-- A feasible vector of a standard-form fiber that maximizes a linear objective over it. -/
def IsStandardOptimal
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    (objective : Col → 𝕜) (z : Col → 𝕜) : Prop :=
  z ∈ standardFeasibleSet A rhs ∧
    ∀ w ∈ standardFeasibleSet A rhs,
      (∑ j, objective j * w j) ≤ ∑ j, objective j * z j

/-- Every attained linear optimum over a standard-form nonnegative affine fiber is attained at
an extreme point.

The feasible set need not be bounded. The proof first passes to the exposed optimal face,
minimizes total nonnegative mass there, and applies Krein–Milman to the resulting compact
minimum-mass face. -/
theorem exists_extreme_standardOptimal_of_standardOptimal
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ) (objective : Col → ℝ)
    {z : Col → ℝ}
    (hz : IsStandardOptimal A rhs objective z) :
    ∃ zExtreme : Col → ℝ,
      zExtreme ∈ (standardFeasibleSet A rhs).extremePoints ℝ ∧
        IsStandardOptimal A rhs objective zExtreme ∧
        (∑ j, objective j * zExtreme j) = ∑ j, objective j * z j := by
  classical
  set feasible : Set (Col → ℝ) := standardFeasibleSet A rhs with hfeasible
  set objectiveMap : (Col → ℝ) →L[ℝ] ℝ := finiteDotContinuousLinearMap objective with hobj
  set massMap : (Col → ℝ) →L[ℝ] ℝ := finiteDotContinuousLinearMap (fun _ => 1) with hmass
  set optimalFace : Set (Col → ℝ) := objectiveMap.toExposed feasible with hface
  have hzOptimalFace : z ∈ optimalFace := by
    refine ⟨hz.1, fun w hw => ?_⟩
    simpa [hobj, finiteDotContinuousLinearMap_apply] using hz.2 w hw
  have hoptimalExposed : IsExposed ℝ feasible optimalFace :=
    ContinuousLinearMap.toExposed.isExposed
  have hoptimalClosed : IsClosed optimalFace :=
    hoptimalExposed.isClosed (isClosed_standardFeasibleSet A rhs)
  set upper : Col → ℝ := fun _ => massMap z with hupper
  set truncated : Set (Col → ℝ) := optimalFace ∩ Set.Icc 0 upper with htrunc
  have hzTruncated : z ∈ truncated := by
    refine ⟨hzOptimalFace, hz.1.1, fun j => ?_⟩
    change z j ≤ massMap z
    simpa [hmass, finiteDotContinuousLinearMap_apply] using
      Finset.single_le_sum (fun k _ => hz.1.1 k) (Finset.mem_univ j)
  have htruncatedCompact : IsCompact truncated := by
    simpa [htrunc, Set.inter_comm] using
      (isCompact_Icc (a := (0 : Col → ℝ)) (b := upper)).inter_right hoptimalClosed
  obtain ⟨m, hmTruncated, hmMin⟩ :=
    htruncatedCompact.exists_isMinOn ⟨z, hzTruncated⟩ massMap.continuous.continuousOn
  have hmOptimalFace : m ∈ optimalFace := hmTruncated.1
  have hmGlobalMin (w) (hw : w ∈ optimalFace) : massMap m ≤ massMap w := by
    by_cases hwMass : massMap w ≤ massMap z
    · refine hmMin ⟨hw, (hoptimalExposed.subset hw).1, fun j => ?_⟩
      calc
        w j ≤ massMap w := by
          simpa [hmass, finiteDotContinuousLinearMap_apply] using
            Finset.single_le_sum (fun k _ => (hoptimalExposed.subset hw).1 k)
              (Finset.mem_univ j)
        _ ≤ upper j := hwMass
    · exact (hmMin hzTruncated).trans (le_of_lt (lt_of_not_ge hwMass))
  set minimumMassFace : Set (Col → ℝ) := (-massMap).toExposed optimalFace with hminFace
  have hmMinimumMassFace : m ∈ minimumMassFace := by
    refine ⟨hmOptimalFace, fun w hw => ?_⟩
    simpa using neg_le_neg (hmGlobalMin w hw)
  have hminimumMassExposed : IsExposed ℝ optimalFace minimumMassFace :=
    ContinuousLinearMap.toExposed.isExposed
  have hminimumMassFace_subset :
      minimumMassFace ⊆ Set.Icc (0 : Col → ℝ) fun _ => massMap m := by
    intro w hw
    have hwFeasible := hoptimalExposed.subset (hminimumMassExposed.subset hw)
    have hwMassLe : massMap w ≤ massMap m := by
      simpa using neg_le_neg (hw.2 m hmOptimalFace)
    refine ⟨hwFeasible.1, fun j => ?_⟩
    calc
      w j ≤ massMap w := by
        simpa [hmass, finiteDotContinuousLinearMap_apply] using
          Finset.single_le_sum (fun k _ => hwFeasible.1 k) (Finset.mem_univ j)
      _ ≤ massMap m := hwMassLe
  have hminimumMassCompact : IsCompact minimumMassFace :=
    isCompact_Icc.of_isClosed_subset (hminimumMassExposed.isClosed hoptimalClosed)
      hminimumMassFace_subset
  obtain ⟨zExtreme, hzExtremeMinimum⟩ :=
    hminimumMassCompact.extremePoints_nonempty ⟨m, hmMinimumMassFace⟩
  have hzExtremeOptimalFace : zExtreme ∈ optimalFace :=
    hminimumMassExposed.subset (extremePoints_subset hzExtremeMinimum)
  have hzExtremeFeasible : zExtreme ∈ feasible := hoptimalExposed.subset hzExtremeOptimalFace
  have hzExtremeOriginal : zExtreme ∈ feasible.extremePoints ℝ :=
    (hoptimalExposed.isExtreme.trans
      hminimumMassExposed.isExtreme).extremePoints_subset_extremePoints hzExtremeMinimum
  have hzExtremeOptimal : IsStandardOptimal A rhs objective zExtreme := by
    refine ⟨hzExtremeFeasible, fun w hw => ?_⟩
    simpa [hobj, finiteDotContinuousLinearMap_apply] using hzExtremeOptimalFace.2 w hw
  exact ⟨zExtreme, hzExtremeOriginal, hzExtremeOptimal,
    le_antisymm (hz.2 zExtreme hzExtremeFeasible) (hzExtremeOptimal.2 z hz.1)⟩

/-! ### Basic feasible solutions

A feasible point is *basic* when the columns carrying its positive support are linearly
independent. Basic feasible solutions are exactly the extreme points of the fiber, and being
supported on an independent family of columns of `A` immediately bounds their sparsity. -/

omit [IsStrictOrderedRing 𝕜] in
/-- Splitting a vector supported on the positive coordinates of `z` into its support columns:
`A *ᵥ d` is the combination of the support columns of `A` with the coefficients of `d`. -/
theorem mulVec_eq_sum_supportColumns
    {Row Col : Type*} [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col 𝕜) {z d : Col → 𝕜} (hd_supp : ∀ j, z j = 0 → d j = 0) :
    A *ᵥ d = ∑ k : {k : Col // z k ≠ 0}, d k.1 • A.col k.1 := by
  classical
  have hcol (k : Col) : A *ᵥ (Pi.single k (1 : 𝕜)) = A.col k :=
    Matrix.mulVec_single_one A k
  have hsplit : d = ∑ k : {k : Col // z k ≠ 0}, d k.1 • Pi.single k.1 (1 : 𝕜) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hj : z j = 0
    · rw [hd_supp j hj]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      have hne : j ≠ k.1 := fun hkj => k.property (hkj ▸ hj)
      rw [if_neg hne]
      simp
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : {k : Col // z k ≠ 0})]
      · simp
      · intro k _ hkj
        rw [if_neg fun hkj' => hkj (Subtype.ext hkj'.symm)]
        simp
      · simp
  calc
    A *ᵥ d = A *ᵥ ∑ k : {k : Col // z k ≠ 0}, d k.1 • Pi.single k.1 (1 : 𝕜) := by rw [← hsplit]
    _ = ∑ k : {k : Col // z k ≠ 0}, d k.1 • (A *ᵥ Pi.single k.1 (1 : 𝕜)) := by
        change A.mulVecLin _ = _
        simp
    _ = ∑ k : {k : Col // z k ≠ 0}, d k.1 • A.col k.1 :=
        Finset.sum_congr rfl fun k _ => by rw [hcol k.1]

/-- An extreme point of a standard-form nonnegative affine fiber admits no nonzero kernel
direction supported on its positive coordinates: such a direction could be added and subtracted
without leaving the fiber, exhibiting the point as an interior point of a segment. -/
theorem eq_zero_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    {z d : Col → 𝕜}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints 𝕜)
    (hd_supp : ∀ j, z j = 0 → d j = 0)
    (hd_kernel : A *ᵥ d = 0) :
    d = 0 := by
  classical
  by_contra hd_ne
  have hCol : Nonempty Col := by
    by_contra h
    have : IsEmpty Col := not_nonempty_iff.mp h
    exact hd_ne (Subsingleton.elim d 0)
  obtain ⟨hz_nonnegative, hz_equation⟩ := extremePoints_subset hz
  have hbound_pos (j : Col) : (0 : 𝕜) < if z j = 0 then 1 else z j / (|d j| + 1) := by
    split_ifs with hj
    · norm_num
    · have hzj_pos : 0 < z j := lt_of_le_of_ne (hz_nonnegative j) (Ne.symm hj)
      positivity
  set ε : 𝕜 := Finset.univ.inf' Finset.univ_nonempty
    (fun j : Col => if z j = 0 then (1 : 𝕜) else z j / (|d j| + 1)) with hε
  have hε_pos : 0 < ε := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => hbound_pos j
  have hcoordinate_bound (j : Col) : ε * |d j| ≤ z j := by
    have hbound : ε ≤ if z j = 0 then (1 : 𝕜) else z j / (|d j| + 1) :=
      Finset.inf'_le _ (Finset.mem_univ j)
    by_cases hzj : z j = 0
    · rw [hzj, hd_supp j hzj]
      simp
    · simp only [hzj, if_false] at hbound
      have hdenom_pos : (0 : 𝕜) < |d j| + 1 := by positivity
      have hfull : ε * (|d j| + 1) ≤ z j := (le_div_iff₀ hdenom_pos).mp hbound
      nlinarith
  have habs (j : Col) (σ : 𝕜) (hσ : σ = 1 ∨ σ = -1) : |σ * (ε * d j)| ≤ z j := by
    have hσ_abs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    calc
      |σ * (ε * d j)| = ε * |d j| := by
        rw [abs_mul, abs_mul, hσ_abs, one_mul, abs_of_pos hε_pos]
      _ ≤ z j := hcoordinate_bound j
  have hmem (σ : 𝕜) (hσ : σ = 1 ∨ σ = -1) :
      (fun j => z j + σ * (ε * d j)) ∈ standardFeasibleSet A rhs := by
    refine ⟨fun j => by linarith [(abs_le.mp (habs j σ hσ)).1], ?_⟩
    have hvector : (fun j => z j + σ * (ε * d j)) = z + (σ * ε) • d := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hvector, Matrix.mulVec_add, Matrix.mulVec_smul, hz_equation, hd_kernel]
    simp
  have hplus := hmem 1 (Or.inl rfl)
  have hminus := hmem (-1) (Or.inr rfl)
  simp only [one_mul] at hplus
  have hsegment : z ∈ openSegment 𝕜 (fun j => z j + ε * d j)
      (fun j => z j + (-1) * (ε * d j)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := hz.2 hplus hminus hsegment
  refine hd_ne (funext fun j => ?_)
  have hj : z j + ε * d j = z j := congrFun heq j
  rcases mul_eq_zero.mp (show ε * d j = 0 by linarith) with hzero | hzero
  · exact absurd hzero hε_pos.ne'
  · exact hzero

/-- The columns carrying the positive support of an extreme standard-form feasible point are
linearly independent. -/
theorem linearIndependent_supportColumns_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    {z : Col → 𝕜}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints 𝕜) :
    LinearIndependent 𝕜 (fun j : {j : Col // z j ≠ 0} => A.col j.1) := by
  classical
  refine Fintype.linearIndependent_iffₛ.mpr fun f g hfg j => ?_
  set d : Col → 𝕜 := ∑ k : {k : Col // z k ≠ 0}, (f k - g k) • Pi.single k.1 1 with hd
  have hd_supp (k : Col) (hk : z k = 0) : d k = 0 := by
    simp only [hd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : k ≠ i.1 := fun hki => i.property (hki ▸ hk)
    rw [if_neg hne]
    simp
  have hd_eval (k : {k : Col // z k ≠ 0}) : d k.1 = f k - g k := by
    simp only [hd, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hlk
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [if_neg fun heq => hlk (Subtype.ext heq.symm)]
      simp
    · simp
  have hd_kernel : A *ᵥ d = 0 := by
    rw [mulVec_eq_sum_supportColumns A hd_supp]
    have (k : {k : Col // z k ≠ 0}) : d k.1 • A.col k.1 = (f k - g k) • A.col k.1 := by
      rw [hd_eval k]
    rw [Finset.sum_congr rfl fun k _ => this k]
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hfg, sub_self]
  have hj := hd_eval j
  rw [eq_zero_of_extreme_standardFeasible A rhs hz hd_supp hd_kernel] at hj
  exact sub_eq_zero.mp hj.symm

/-- Conversely, a feasible point whose support columns are linearly independent is an extreme
point: a segment through it inside the fiber has both endpoints supported on the same
coordinates, so their difference is a kernel relation among independent columns. -/
theorem mem_extremePoints_standardFeasibleSet_of_linearIndependent
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    {z : Col → 𝕜} (hz : z ∈ standardFeasibleSet A rhs)
    (hindep : LinearIndependent 𝕜 (fun j : {j : Col // z j ≠ 0} => A.col j.1)) :
    z ∈ (standardFeasibleSet A rhs).extremePoints 𝕜 := by
  classical
  refine ⟨hz, fun x hx y hy hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
  -- Both endpoints vanish wherever `z` does, since `z` is a positive combination of them.
  have hvanish (j : Col) (hj : z j = 0) : x j = 0 ∧ y j = 0 := by
    have hsum : a * x j + b * y j = 0 := by
      have := congrFun hcomb j
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hj] using this
    have hxj : a * x j = 0 := le_antisymm
      (by nlinarith [mul_nonneg hb.le (hy.1 j)]) (mul_nonneg ha.le (hx.1 j))
    have hyj : b * y j = 0 := by linarith
    exact ⟨by simpa [ha.ne'] using mul_eq_zero.mp hxj |>.resolve_left ha.ne',
      by simpa using mul_eq_zero.mp hyj |>.resolve_left hb.ne'⟩
  -- Their difference is therefore a kernel vector on the support of `z`.
  have hd_supp (j : Col) (hj : z j = 0) : (x - y) j = 0 := by
    simp [Pi.sub_apply, (hvanish j hj).1, (hvanish j hj).2]
  have hd_kernel : A *ᵥ (x - y) = 0 := by
    rw [show x - y = x + (-1 : 𝕜) • y by funext j; simp [Pi.sub_apply]; ring,
      Matrix.mulVec_add, Matrix.mulVec_smul, hx.2, hy.2]
    simp
  have hxy : x = y := by
    have hzero : x - y = 0 := by
      rw [mulVec_eq_sum_supportColumns A hd_supp] at hd_kernel
      have hcoeff := Fintype.linearIndependent_iff.mp hindep (fun k => (x - y) k.1) hd_kernel
      funext j
      by_cases hj : z j = 0
      · exact hd_supp j hj
      · simpa using hcoeff ⟨j, hj⟩
    have := congrFun hzero
    funext j
    simpa [sub_eq_zero] using this j
  subst hxy
  have hzx : z = x := by
    rw [← hcomb]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  exact hzx.symm

/-- **Basic feasible solutions are exactly the extreme points** of a standard-form fiber. -/
theorem mem_extremePoints_standardFeasibleSet_iff
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (z : Col → 𝕜) :
    z ∈ (standardFeasibleSet A rhs).extremePoints 𝕜 ↔
      z ∈ standardFeasibleSet A rhs ∧
        LinearIndependent 𝕜 (fun j : {j : Col // z j ≠ 0} => A.col j.1) :=
  ⟨fun hz => ⟨extremePoints_subset hz,
      linearIndependent_supportColumns_of_extreme_standardFeasible A rhs hz⟩,
    fun hz => mem_extremePoints_standardFeasibleSet_of_linearIndependent A rhs hz.1 hz.2⟩

/-- **Extreme points are sparse**: an extreme point of a standard-form fiber is supported on at
most `Fintype.card Row` coordinates, because its support columns are linearly independent in
the `Fintype.card Row`-dimensional space `Row → ℝ`. -/
theorem card_support_le_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜)
    {z : Col → 𝕜} (hz : z ∈ (standardFeasibleSet A rhs).extremePoints 𝕜) :
    Fintype.card {j : Col // z j ≠ 0} ≤ Fintype.card Row := by
  classical
  have hindep := linearIndependent_supportColumns_of_extreme_standardFeasible A rhs hz
  have := hindep.fintype_card_le_finrank (R := 𝕜) (M := Row → 𝕜)
  simpa [Module.finrank_fintype_fun_eq_card] using this

end LinearAlgebra
end DirectedTransport
