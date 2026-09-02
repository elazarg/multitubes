/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.Farkas

import Maths.Multitubes.FiniteInequality.Quantitative

/-!
# Quantitative and recession duality for finite max-affine transport

The genuine branch type contains every affine branch and exactly the finite
floor branches.  Omitting absent-floor zero rows is necessary when certificate
mass is normalized to one.

The central theorem `worstResidualAtMost_iff_normalizedDual_le` is threshold
strong duality.  It avoids prematurely assigning a real number to an infimum
that may be `-∞`: a uniform residual threshold is attainable exactly when all
balanced mass-one branch certificates have value below it.

For finite inequality systems, every dual certificate is supported on rows
critical for a common recession direction, and feasibility reduces exactly to
that critical subsystem.

## Main definitions

* `Maths.MaxAffineTransport.IsGenuineBranch` and
  `Maths.MaxAffineTransport.Branch`: the branch index, containing every affine
  branch and exactly the finite floor branches.
* `Maths.MaxAffineTransport.branchDelta`,
  `Maths.MaxAffineTransport.branchBase`,
  `Maths.MaxAffineTransport.branchResidual`: the branch inequality system and
  its residual.
* `Maths.MaxAffineTransport.IsNormalizedBranchCertificate` and
  `Maths.MaxAffineTransport.branchCertificateValue`: balanced mass-one dual
  certificates and their value.
* `Maths.MaxAffineTransport.WorstResidualAtMost`: attainability of a uniform
  residual threshold.

## Main results

* `Maths.MaxAffineTransport.isLaxSection_iff_forall_branch`: a lax section is
  exactly a solution of the branch system.
* `Maths.MaxAffineTransport.worstResidualAtMost_iff_exists_edge_defect_le`: the
  threshold restated edgewise.
* `Maths.MaxAffineTransport.branchCertificateValue_le_of_worstResidualAtMost`:
  weak duality.
* `Maths.MaxAffineTransport.worstResidualAtMost_iff_normalizedDual_le`:
  threshold strong duality, stated without assigning a real number to an infimum that may
  be `-∞`.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_normalizedBranchCertificate_nonpos`:
  existence of a lax section at threshold zero.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## Genuine branch rows -/

/-- The affine copy of every edge is genuine; the floor copy is genuine only
when the floor is present. -/
def IsGenuineBranch (label : E → Label) : E ⊕ E → Prop
  | Sum.inl _ => True
  | Sum.inr edge => (label edge).floor ≠ ⊥

/-- All actual affine/floor branches of a labelled graph. -/
abbrev Branch (label : E → Label) :=
  {action : E ⊕ E // IsGenuineBranch label action}

instance instFiniteBranch [Finite E] (label : E → Label) : Finite (Branch label) := by
  classical
  infer_instance

noncomputable instance instFintypeBranch [Fintype E]
    (label : E → Label) : Fintype (Branch label) :=
  Fintype.ofFinite (Branch label)

/-- Row vector of one genuine branch. -/
def branchDelta [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (label : E → Label) (branch : Branch label) : V → ℝ :=
  rowDelta G label branch.1

/-- Lower bound of one genuine branch. -/
def branchBase (label : E → Label) (branch : Branch label) : ℝ :=
  rowBase label branch.1

/-- Residual of one genuine branch at a candidate potential. -/
def branchResidual [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (label : E → Label)
    (potential : V → ℝ) (branch : Branch label) : ℝ :=
  branchBase label branch - dotProduct (branchDelta G label branch) potential

/-- Lax max-affine sections are exactly the potentials satisfying every
genuine branch row. -/
theorem isLaxSection_iff_forall_branch
    [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (label : E → Label) (potential : V → ℝ) :
    IsLaxSection G label potential ↔
      ∀ branch : Branch label,
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) potential := by
  constructor
  · intro hsection branch
    exact (isLaxSection_iff_forall_row G label potential).mp hsection branch.1
  · intro hbranch
    apply (isLaxSection_iff_forall_row G label potential).mpr
    intro action
    cases action with
    | inl edge =>
        exact hbranch ⟨Sum.inl edge, trivial⟩
    | inr edge =>
        by_cases hfloor : (label edge).floor = ⊥
        · rw [rowBase, hfloor, WithBot.unbotD_bot,
            dotProduct_rowDelta_inr_of_floor_bot hfloor]
        · exact hbranch ⟨Sum.inr edge, hfloor⟩

/-! ## Threshold-normalized strong duality -/

section Quantitative

variable [Fintype V] [DecidableEq V] [Fintype E]
variable {G : EdgeGraph V E} {label : E → Label}

/-- A nonnegative, balanced certificate of total mass one. -/
def IsNormalizedBranchCertificate (coefficient : Branch label → ℝ) : Prop :=
  (∀ branch, 0 ≤ coefficient branch) ∧
    (∑ branch, coefficient branch = 1) ∧
    ∀ vertex : V,
      ∑ branch,
        coefficient branch * branchDelta G label branch vertex = 0

/-- Objective value of a normalized branch certificate. -/
def branchCertificateValue (coefficient : Branch label → ℝ) : ℝ :=
  ∑ branch, coefficient branch * branchBase label branch

/-- Feasibility with every actual branch residual at most `level`. -/
def WorstResidualAtMost (level : ℝ) : Prop :=
  ∃ potential : V → ℝ,
    ∀ branch : Branch label,
      branchResidual G label potential branch ≤ level

omit [Fintype E] in
/-- A branch residual threshold is the branch row inequality with its base
shifted by the threshold. -/
theorem branchResidual_le_iff (potential : V → ℝ) (branch : Branch label)
    (level : ℝ) :
    branchResidual G label potential branch ≤ level ↔
      branchBase label branch - level ≤
        dotProduct (branchDelta G label branch) potential := by
  rw [branchResidual, sub_le_comm]

omit [Fintype E] in
/-- At threshold zero the branch residual inequality is the branch row itself. -/
theorem branchResidual_nonpos_iff (potential : V → ℝ) (branch : Branch label) :
    branchResidual G label potential branch ≤ 0 ↔
      branchBase label branch ≤
        dotProduct (branchDelta G label branch) potential := by
  rw [branchResidual, sub_nonpos]

omit [Fintype E] in
/-- The genuine-branch worst-residual threshold is equivalent to the
edge-indexed max-affine defect threshold. -/
theorem worstResidualAtMost_iff_exists_edge_defect_le (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      ∃ potential : V → ℝ,
        ∀ edge : E, defect G label potential edge ≤ level := by
  classical
  apply exists_congr
  intro potential
  constructor
  · intro hbranch edge
    have haffine := hbranch ⟨Sum.inl edge, trivial⟩
    rw [branchResidual, branchBase, branchDelta, rowBase,
      dotProduct_rowDelta_inl] at haffine
    rcases (label edge).floor_cases with hfloor | ⟨floor, hfloor⟩
    · rw [defect, (label edge).apply_of_floor_bot hfloor,
        Label.affinePart]
      linarith
    · have hfloorBranch := hbranch
        (⟨Sum.inr edge, by
          change (label edge).floor ≠ ⊥
          rw [hfloor]
          exact WithBot.coe_ne_bot⟩ : Branch label)
      change (rowBase label (Sum.inr edge) -
        dotProduct (rowDelta G label (Sum.inr edge)) potential ≤ level) at hfloorBranch
      have hbase : rowBase label (Sum.inr edge) = floor := by
        simp [rowBase, hfloor]
      rw [hbase, dotProduct_rowDelta_inr_of_floor_coe hfloor] at hfloorBranch
      rw [defect, (label edge).apply_of_floor_coe hfloor,
        ← max_sub_sub_right]
      exact max_le (by simpa using hfloorBranch) (by
        simp only [Label.affinePart]
        linarith)
  · intro hedge branch
    rcases branch with ⟨action, hgenuine⟩
    cases action with
    | inl edge =>
        have hdefect := hedge edge
        have haffine := (label edge).affinePart_le_apply
          (potential (G.source edge))
        rw [branchResidual, branchBase, branchDelta, rowBase,
          dotProduct_rowDelta_inl]
        rw [defect] at hdefect
        simp only [Label.affinePart] at haffine
        linarith
    | inr edge =>
        rcases (label edge).floor_cases with hfloor | ⟨floor, hfloor⟩
        · exact (hgenuine hfloor).elim
        · have hdefect := hedge edge
          have hfloorLe := (label edge).floor_le_coe_apply
            (potential (G.source edge))
          rw [hfloor, WithBot.coe_le_coe] at hfloorLe
          rw [branchResidual, branchBase, branchDelta, rowBase, hfloor,
            dotProduct_rowDelta_inr_of_floor_coe hfloor]
          simp only [WithBot.unbotD_coe]
          rw [defect] at hdefect
          linarith

private theorem weighted_shiftedBase_eq
    (coefficient : Branch label → ℝ) (level : ℝ) :
    (∑ branch, coefficient branch * (branchBase label branch - level)) =
      branchCertificateValue coefficient -
        level * ∑ branch, coefficient branch := by
  rw [branchCertificateValue]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Weak normalized duality at one threshold. -/
theorem branchCertificateValue_le_of_worstResidualAtMost
    {level : ℝ} (hlevel : WorstResidualAtMost (G := G) (label := label) level)
    (coefficient : Branch label → ℝ)
    (hcertificate : IsNormalizedBranchCertificate (G := G) (label := label)
      coefficient) :
    branchCertificateValue coefficient ≤ level := by
  classical
  rcases hlevel with ⟨potential, hpotential⟩
  have hrows (branch : Branch label) :
      branchBase label branch - level ≤
        dotProduct (branchDelta G label branch) potential :=
    (branchResidual_le_iff potential branch level).mp (hpotential branch)
  have hweak := not_nonnegative_incompatibility_of_potential
    (delta := branchDelta G label)
    (base := fun branch ↦ branchBase label branch - level)
    hrows hcertificate.1 hcertificate.2.2
  rw [weighted_shiftedBase_eq, hcertificate.2.1] at hweak
  linarith

private theorem coefficient_eq_zero_of_sum_eq_zero
    (coefficient : Branch label → ℝ)
    (hnonneg : ∀ branch, 0 ≤ coefficient branch)
    (hsum : ∑ branch, coefficient branch = 0) :
    ∀ branch, coefficient branch = 0 := by
  intro branch
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun index _ ↦ hnonneg index)).mp hsum
  exact hall branch (Finset.mem_univ branch)

/-- **Exact normalized threshold duality.**  A candidate with worst genuine
branch residual at most `level` exists exactly when every balanced mass-one
certificate has value at most `level`.  This statement is meaningful in
the `-∞` case, when normalized certificates may not exist. -/
theorem worstResidualAtMost_iff_normalizedDual_le (level : ℝ) :
    WorstResidualAtMost (G := G) (label := label) level ↔
      ∀ coefficient : Branch label → ℝ,
        IsNormalizedBranchCertificate (G := G) (label := label) coefficient →
        branchCertificateValue coefficient ≤ level := by
  change FiniteInequality.WorstResidualAtMost
      (branchDelta G label) (branchBase label) level ↔
    ∀ coefficient : Branch label → ℝ,
      FiniteInequality.IsNormalizedCertificate
          (branchDelta G label) coefficient →
        FiniteInequality.certificateValue (branchBase label) coefficient ≤ level
  exact FiniteInequality.worstResidualAtMost_iff_normalizedDual_le
    (branchDelta G label) (branchBase label) level

/-- Qualitative Farkas is the positive-threshold specialization: a lax section
exists exactly when no normalized certificate has positive value. -/
theorem exists_isLaxSection_iff_normalizedBranchCertificate_nonpos :
    (∃ potential : V → ℝ, IsLaxSection G label potential) ↔
      ∀ coefficient : Branch label → ℝ,
        IsNormalizedBranchCertificate (G := G) (label := label) coefficient →
        branchCertificateValue coefficient ≤ 0 := by
  rw [← worstResidualAtMost_iff_normalizedDual_le (G := G) (label := label) 0]
  constructor
  · rintro ⟨potential, hpotential⟩
    exact ⟨potential, fun branch ↦ (branchResidual_nonpos_iff potential branch).mpr
      ((isLaxSection_iff_forall_branch G label potential).mp hpotential branch)⟩
  · rintro ⟨potential, hpotential⟩
    refine ⟨potential, (isLaxSection_iff_forall_branch G label potential).mpr ?_⟩
    intro branch
    exact (branchResidual_nonpos_iff potential branch).mp (hpotential branch)

end Quantitative

end MaxAffineTransport

end

end Maths
