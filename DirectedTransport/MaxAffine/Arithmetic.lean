/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.FiniteInequality.Arithmetic
public import DirectedTransport.MaxAffine.Duality

import DirectedTransport.FiniteInequality.Sparse

/-!
# Rational data for max-affine transport

Rational max-affine labels have a `WithBot ℚ` floor and rational affine
coefficients.  Casting them to real labels identifies their genuine branch
system with a rational finite inequality system.  Consequently real
feasibility is equivalent to rational feasibility, and real infeasibility has
an integer-valued branch certificate while the balance and objective are
evaluated over `ℚ`.

## Main definitions

* `DirectedTransport.MaxAffineTransport.RationalLabel` and
  `DirectedTransport.MaxAffineTransport.RationalLabel.toLabel`: rational max-affine labels
  and their cast to real labels.
* `DirectedTransport.MaxAffineTransport.rationalBranchDelta` and
  `DirectedTransport.MaxAffineTransport.rationalBranchBase`: the rational branch system.
* `DirectedTransport.MaxAffineTransport.IsRationalLaxSection`: a lax section with rational
  values.

## Main results

* `DirectedTransport.MaxAffineTransport.rationalBranchDelta_cast` and
  `DirectedTransport.MaxAffineTransport.rationalBranchBase_cast`: the rational branch
  system casts to the real one.
* `DirectedTransport.MaxAffineTransport.exists_rationalLaxSection_iff_exists_realLaxSection`:
  real feasibility is equivalent to rational feasibility.
* `DirectedTransport.MaxAffineTransport.exists_integralBranchCertificate_of_real_infeasible`:
  real infeasibility has an integer-valued branch certificate.
* In the namespace `DirectedTransport.MaxAffineTransport`, the results
  `exists_rankSparse_rationalBranchCertificate_of_real_infeasible` and
  `exists_rankSparse_integralBranchCertificate_of_real_infeasible`: the same certificates
  with support bounded by the rank.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

/-- A max-affine label whose finite coefficients are rational. -/
structure RationalLabel where
  floor : WithBot ℚ
  shift : ℚ
  slope : ℚ

namespace RationalLabel

/-- Cast a rational max-affine label to the real label type. -/
def toLabel (label : RationalLabel) : Label where
  floor := label.floor.map fun value : ℚ => (value : ℝ)
  shift := label.shift
  slope := label.slope

@[simp] theorem floor_toLabel (label : RationalLabel) :
    label.toLabel.floor =
      label.floor.map fun value : ℚ => (value : ℝ) := rfl

@[simp] theorem shift_toLabel (label : RationalLabel) :
    label.toLabel.shift = label.shift := rfl

@[simp] theorem slope_toLabel (label : RationalLabel) :
    label.toLabel.slope = label.slope := rfl

@[simp] theorem floor_toLabel_eq_bot_iff (label : RationalLabel) :
    label.toLabel.floor = ⊥ ↔ label.floor = ⊥ := WithBot.map_eq_bot_iff

@[simp] theorem unbotD_floor_toLabel (label : RationalLabel) :
    label.toLabel.floor.unbotD 0 =
      ((label.floor.unbotD (0 : ℚ) : ℚ) : ℝ) := by
  cases hfloor : label.floor with
  | bot => simp [toLabel, hfloor]
  | coe floor => simp [toLabel, hfloor]

end RationalLabel

variable {V : Type uV} {E : Type uE}

section

variable [Fintype V] [DecidableEq V] [Fintype E]
variable (G : EdgeGraph V E) (label : E → RationalLabel)

/-- Rational normal vector of a genuine branch of the cast real system. -/
def rationalBranchDelta
    (branch : Branch (fun edge => (label edge).toLabel)) : V → ℚ :=
  match branch.1 with
  | Sum.inl edge => fun vertex =>
      (if vertex = G.target edge then 1 else 0) -
        (label edge).slope *
          (if vertex = G.source edge then 1 else 0)
  | Sum.inr edge => fun vertex =>
      if vertex = G.target edge then 1 else 0

/-- Rational lower bound of a genuine branch of the cast real system. -/
def rationalBranchBase
    (branch : Branch (fun edge => (label edge).toLabel)) : ℚ :=
  match branch.1 with
  | Sum.inl edge => (label edge).shift
  | Sum.inr edge => (label edge).floor.unbotD 0

/-- A rational potential satisfying every genuine max-affine branch row. -/
def IsRationalLaxSection (potential : V → ℚ) : Prop :=
  ∀ branch : Branch (fun edge => (label edge).toLabel),
    rationalBranchBase label branch ≤
      FiniteInequality.ratDotProduct
        (rationalBranchDelta G label branch) potential

omit [Fintype E] in
/-- Casting a rational branch normal gives the real branch normal. -/
theorem rationalBranchDelta_cast
    (branch : Branch (fun edge => (label edge).toLabel)) (vertex : V) :
    (rationalBranchDelta G label branch vertex : ℝ) =
      branchDelta G (fun edge => (label edge).toLabel) branch vertex := by
  rcases branch with ⟨action, hgenuine⟩
  cases action with
  | inl edge =>
      simp [rationalBranchDelta, branchDelta, rowDelta,
        RationalLabel.toLabel]
      split_ifs <;> norm_num
  | inr edge =>
      cases hfloor : (label edge).floor with
      | bot =>
          simp [IsGenuineBranch, RationalLabel.toLabel, hfloor] at hgenuine
      | coe floor =>
          simp [rationalBranchDelta, branchDelta, rowDelta,
            RationalLabel.toLabel, hfloor]
          split_ifs <;> norm_num

omit [Fintype E] in
/-- Casting a rational branch bound gives the real branch bound. -/
theorem rationalBranchBase_cast
    (branch : Branch (fun edge => (label edge).toLabel)) :
    (rationalBranchBase label branch : ℝ) =
      branchBase (fun edge => (label edge).toLabel) branch := by
  rcases branch with ⟨action, hgenuine⟩
  cases action with
  | inl edge =>
      simp [rationalBranchBase, branchBase, rowBase,
        RationalLabel.toLabel]
  | inr edge =>
      change ((label edge).floor.unbotD (0 : ℚ) : ℚ) =
        ((label edge).toLabel.floor.unbotD 0 : ℝ)
      exact (RationalLabel.unbotD_floor_toLabel (label edge)).symm

/-- Real feasibility of a rational max-affine system is equivalent to a
rational potential satisfying its genuine branch inequalities over `ℚ`. -/
theorem exists_rationalLaxSection_iff_exists_realLaxSection :
    (∃ potential : V → ℚ, IsRationalLaxSection G label potential) ↔
      ∃ potential : V → ℝ,
        IsLaxSection G (fun edge => (label edge).toLabel) potential := by
  unfold IsRationalLaxSection
  rw [FiniteInequality.exists_rationalPotential_iff_exists_realPotential]
  apply exists_congr
  intro potential
  rw [isLaxSection_iff_forall_branch]
  apply forall_congr'
  intro branch
  rw [rationalBranchBase_cast]
  have hdelta :
      (fun vertex =>
        (rationalBranchDelta G label branch vertex : ℝ)) =
        branchDelta G (fun edge => (label edge).toLabel) branch := by
    funext vertex
    exact rationalBranchDelta_cast G label branch vertex
  rw [hdelta]

omit [Fintype E] in
private theorem rationalBranchSystem_infeasible
    (hinfeasible : ¬∃ potential : V → ℝ,
      IsLaxSection G (fun edge => (label edge).toLabel) potential) :
    ¬∃ potential : V → ℝ,
      ∀ branch : Branch (fun edge => (label edge).toLabel),
        (rationalBranchBase label branch : ℝ) ≤
          ∑ vertex,
            (rationalBranchDelta G label branch vertex : ℝ) *
              potential vertex := by
  rintro ⟨potential, hpotential⟩
  apply hinfeasible
  refine ⟨potential,
    (isLaxSection_iff_forall_branch G
      (fun edge => (label edge).toLabel) potential).mpr ?_⟩
  intro branch
  have hrow := hpotential branch
  rw [rationalBranchBase_cast] at hrow
  change branchBase (fun edge => (label edge).toLabel) branch ≤
    dotProduct
      (branchDelta G (fun edge => (label edge).toLabel) branch) potential
  rw [dotProduct]
  simpa only [rationalBranchDelta_cast] using hrow

/-- Real infeasibility of rational max-affine data has a nonnegative integer
branch certificate.  Balance and strict positivity are exact statements over
the rational coefficient field. -/
theorem exists_integralBranchCertificate_of_real_infeasible
    (hinfeasible : ¬∃ potential : V → ℝ,
      IsLaxSection G (fun edge => (label edge).toLabel) potential) :
    ∃ coefficient :
        Branch (fun edge => (label edge).toLabel) → ℤ,
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex,
        ∑ branch, (coefficient branch : ℚ) *
          rationalBranchDelta G label branch vertex = 0) ∧
      0 < ∑ branch, (coefficient branch : ℚ) *
        rationalBranchBase label branch := by
  have hrows := rationalBranchSystem_infeasible G label hinfeasible
  exact
    FiniteInequality.exists_integralCoefficientCertificate_of_real_infeasible
      (rationalBranchDelta G label) (rationalBranchBase label) hrows

/-- Real infeasibility of rational max-affine data has a rational branch
certificate supported on at most one more than the rank of the real branch
normals. -/
theorem exists_rankSparse_rationalBranchCertificate_of_real_infeasible
    (hinfeasible : ¬∃ potential : V → ℝ,
      IsLaxSection G (fun edge => (label edge).toLabel) potential) :
    ∃ (selected : Finset
        (Branch (fun edge => (label edge).toLabel)))
        (coefficient : {branch // branch ∈ selected} → ℚ),
      selected.card ≤
        (Set.range
          (branchDelta G (fun edge => (label edge).toLabel))).finrank ℝ + 1 ∧
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex,
        ∑ branch, coefficient branch *
          rationalBranchDelta G label branch.1 vertex = 0) ∧
      0 < ∑ branch, coefficient branch *
        rationalBranchBase label branch.1 := by
  have hrows := rationalBranchSystem_infeasible G label hinfeasible
  obtain ⟨selected, coefficient, hcard, hnonnegative,
      hbalance, hpositive⟩ :=
    FiniteInequality.exists_rankSparse_rationalCertificate_of_real_infeasible
      (rationalBranchDelta G label) (rationalBranchBase label) hrows
  have hdelta :
      (fun branch vertex =>
        (rationalBranchDelta G label branch vertex : ℝ)) =
        branchDelta G (fun edge => (label edge).toLabel) := by
    funext branch vertex
    exact rationalBranchDelta_cast G label branch vertex
  rw [hdelta] at hcard
  exact ⟨selected, coefficient, hcard, hnonnegative,
    hbalance, hpositive⟩

/-- Real infeasibility of rational max-affine data has an integer-valued
branch certificate with the rank-plus-one support bound.  Balance and strict
positivity remain exact statements over `ℚ`. -/
theorem exists_rankSparse_integralBranchCertificate_of_real_infeasible
    (hinfeasible : ¬∃ potential : V → ℝ,
      IsLaxSection G (fun edge => (label edge).toLabel) potential) :
    ∃ (selected : Finset
        (Branch (fun edge => (label edge).toLabel)))
        (coefficient : {branch // branch ∈ selected} → ℤ),
      selected.card ≤
        (Set.range
          (branchDelta G (fun edge => (label edge).toLabel))).finrank ℝ + 1 ∧
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex,
        ∑ branch, (coefficient branch : ℚ) *
          rationalBranchDelta G label branch.1 vertex = 0) ∧
      0 < ∑ branch, (coefficient branch : ℚ) *
        rationalBranchBase label branch.1 := by
  have hrows := rationalBranchSystem_infeasible G label hinfeasible
  obtain ⟨selected, coefficient, hcard, hnonnegative,
      hbalance, hpositive⟩ :=
    FiniteInequality.exists_rankSparse_integralCoefficientCertificate_of_real_infeasible
      (rationalBranchDelta G label) (rationalBranchBase label) hrows
  have hdelta :
      (fun branch vertex =>
        (rationalBranchDelta G label branch vertex : ℝ)) =
        branchDelta G (fun edge => (label edge).toLabel) := by
    funext branch vertex
    exact rationalBranchDelta_cast G label branch vertex
  rw [hdelta] at hcard
  exact ⟨selected, coefficient, hcard, hnonnegative,
    hbalance, hpositive⟩

end

end MaxAffineTransport

end

end DirectedTransport
