/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.FiniteInequality.Sparse
public import Maths.Multitubes.MaxAffine.Duality

import Maths.Multitubes.FiniteInequality.Arithmetic
import Mathlib.Analysis.Convex.Radon

/-!
# Sparse finite obstructions for max-affine transport

Helly's theorem shows that infeasibility of the genuine max-affine branch
system is visible on at most `|V| + 1` branch inequalities.  This is a
primal sparsity statement: it does not claim that an arbitrary certificate is
sparse, but guarantees a dimension-bounded infeasible subsystem and hence,
by Farkas on that subsystem, real, rational, and integral certificates with
the same support bound whenever the branch data have the corresponding type.
The normalized dual also inherits the sharper rank-plus-one support bound from
the generic finite-inequality theory.

## Main definitions

* `Maths.MaxAffineTransport.branchHalfspace`: the closed halfspace of candidate
  potentials imposed by one genuine branch.

## Main results

* `Maths.MaxAffineTransport.exists_sparse_infeasible_branch_subsystem`: **Helly
  sparsity** - if no lax section exists, some subsystem of at most `Fintype.card V + 1`
  genuine branches is already infeasible. Absent floors are not branches, so they never
  enter the subsystem.
* `Maths.MaxAffineTransport.exists_sparse_farkas_certificate`: that sparse
  subsystem carries a nonnegative real Farkas certificate, indexed by the selected subtype,
  so its support is bounded without padding by zero rows.
* `Maths.MaxAffineTransport.exists_sparse_rational_farkas_certificate`,
  `Maths.MaxAffineTransport.exists_sparse_integral_farkas_certificate`: the same
  bound with rational and integral coefficients, given branch data of the corresponding type
  presented as exact casts of the real data.
* `Maths.MaxAffineTransport.exists_rankSparse_normalizedBranchCertificate`: a
  positive normalized certificate supported on at most one more than the rank of the branch
  normals, which can be sharper than the ambient `Fintype.card V + 1` bound.
* `Maths.MaxAffineTransport.exists_positiveBranchCircuit_of_infeasible`:
  infeasibility yields a positive-objective circuit of genuine branch normals.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

section

variable [Fintype V] [DecidableEq V] [Fintype E]
variable {G : EdgeGraph V E} {label : E → Label}

/-- **Rank-sparse max-affine certificate.**  Infeasibility has a positive
normalized branch certificate supported on at most one more than the rank of
the genuine branch normals.  This can be sharper than the ambient
`|V| + 1` Helly bound. -/
theorem exists_rankSparse_normalizedBranchCertificate
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ coefficient : Branch label → ℝ,
      IsNormalizedBranchCertificate (G := G) (label := label) coefficient ∧
      0 < branchCertificateValue (label := label) coefficient ∧
      Fintype.card {branch : Branch label // coefficient branch ≠ 0} ≤
        (Set.range (branchDelta G label)).finrank ℝ + 1 := by
  have hrows : ¬∃ potential : V → ℝ,
      ∀ branch : Branch label,
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) potential := by
    rintro ⟨potential, hpotential⟩
    exact hinfeasible
      ⟨potential,
        (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩
  simpa only [IsNormalizedBranchCertificate, branchCertificateValue,
    FiniteInequality.IsNormalizedCertificate,
    FiniteInequality.certificateValue] using
    FiniteInequality.exists_positive_normalizedCertificate_support_card_le_rank_add_one
      (branchDelta G label) (branchBase label) hrows

/-- Infeasibility has a positive-objective circuit of genuine max-affine
branch normals. -/
theorem exists_positiveBranchCircuit_of_infeasible
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ coefficient : Branch label → ℝ,
      FiniteInequality.IsPositiveCircuit (branchDelta G label) coefficient ∧
        0 < branchCertificateValue (label := label) coefficient := by
  have hrows : ¬∃ potential : V → ℝ,
      ∀ branch : Branch label,
        branchBase label branch ≤
          dotProduct (branchDelta G label branch) potential := by
    rintro ⟨potential, hpotential⟩
    exact hinfeasible
      ⟨potential,
        (isLaxSection_iff_forall_branch G label potential).mpr hpotential⟩
  simpa only [branchCertificateValue,
    FiniteInequality.certificateValue] using
    FiniteInequality.exists_positiveCircuit_of_infeasible
      (branchDelta G label) (branchBase label) hrows

/-- The closed halfspace imposed by one genuine max-affine branch. -/
def branchHalfspace (branch : Branch label) : Set (V → ℝ) :=
  {potential |
    branchBase label branch ≤
      dotProduct (branchDelta G label branch) potential}

omit [Fintype E] in
theorem convex_branchHalfspace (branch : Branch label) :
    Convex ℝ (branchHalfspace (G := G) branch) := by
  apply convex_halfSpace_ge
  exact
    { map_add := fun left right => dotProduct_add _ _ _
      map_smul := fun scalar point => dotProduct_smul _ _ _ }

/-- **Helly sparsity.**  If the full max-affine lax-section system is
infeasible, some subsystem of at most `|V| + 1` genuine affine/floor branches
is infeasible.  Absent floors are not branches and cannot enter the
subsystem. -/
theorem exists_sparse_infeasible_branch_subsystem
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ selected : Finset (Branch label),
      selected.card ≤ Fintype.card V + 1 ∧
        ¬∃ potential : V → ℝ, ∀ branch ∈ selected,
          branchBase label branch ≤
            dotProduct (branchDelta G label branch) potential := by
  classical
  by_cases hexists : ∃ selected : Finset (Branch label),
      selected.card ≤ Fintype.card V + 1 ∧
        ¬∃ potential : V → ℝ, ∀ branch ∈ selected,
          branchBase label branch ≤
            dotProduct (branchDelta G label branch) potential
  · exact hexists
  · exfalso
    have hsmall (selected : Finset (Branch label)) (_ : selected ⊆ Finset.univ)
        (hcard : selected.card ≤ Module.finrank ℝ (V → ℝ) + 1) :
        (⋂ branch ∈ selected,
          branchHalfspace (G := G) branch).Nonempty := by
      have hcard' : selected.card ≤ Fintype.card V + 1 := by
        simpa only [Module.finrank_pi] using hcard
      by_contra hempty
      apply hexists
      refine ⟨selected, hcard', ?_⟩
      rintro ⟨potential, hpotential⟩
      apply hempty
      refine ⟨potential, ?_⟩
      simp only [Set.mem_iInter, branchHalfspace]
      exact hpotential
    have hfull := Convex.helly_theorem'
      (s := Finset.univ)
      (fun branch _ => convex_branchHalfspace (G := G) branch) hsmall
    apply hinfeasible
    obtain ⟨potential, hpotential⟩ := hfull
    refine ⟨potential, (isLaxSection_iff_forall_branch G label potential).mpr ?_⟩
    intro branch
    have := hpotential
    simp only [Set.mem_iInter, Finset.mem_univ, forall_const,
      branchHalfspace] at this
    exact this branch

/-- A sparse infeasible subsystem carries a Farkas certificate on that
subsystem.  The coefficient type is the selected subtype, so its support has
cardinality at most `|V| + 1` without padding by zero rows. -/
theorem exists_sparse_farkas_certificate
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ (selected : Finset (Branch label))
        (coefficient : {branch // branch ∈ selected} → ℝ),
      selected.card ≤ Fintype.card V + 1 ∧
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex : V,
        ∑ branch, coefficient branch *
          branchDelta G label branch.1 vertex = 0) ∧
      0 < ∑ branch,
        coefficient branch * branchBase label branch.1 := by
  classical
  obtain ⟨selected, hcard, hinfeasibleSelected⟩ :=
    exists_sparse_infeasible_branch_subsystem hinfeasible
  let delta : {branch // branch ∈ selected} → V → ℝ :=
    fun branch => branchDelta G label branch.1
  let base : {branch // branch ∈ selected} → ℝ :=
    fun branch => branchBase label branch.1
  have hnotPotential : ¬∃ potential : V → ℝ,
      ∀ branch, base branch ≤ dotProduct (delta branch) potential := by
    rintro ⟨potential, hpotential⟩
    apply hinfeasibleSelected
    exact ⟨potential, fun branch hbranch => hpotential ⟨branch, hbranch⟩⟩
  rcases exists_potential_or_nonnegative_incompatibility delta base with
    hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
  · exact (hnotPotential hpotential).elim
  · exact ⟨selected, coefficient, hcard, hnonneg, hbalance, hpositive⟩

/-- Rational branch data admit a rational Farkas certificate on a Helly-sparse
infeasible subsystem. -/
theorem exists_sparse_rational_farkas_certificate
    (deltaQ : Branch label → V → ℚ) (baseQ : Branch label → ℚ)
    (hdelta : ∀ branch vertex,
      (deltaQ branch vertex : ℝ) = branchDelta G label branch vertex)
    (hbase : ∀ branch,
      (baseQ branch : ℝ) = branchBase label branch)
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ (selected : Finset (Branch label))
        (coefficient : {branch // branch ∈ selected} → ℚ),
      selected.card ≤ Fintype.card V + 1 ∧
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex : V,
        ∑ branch, coefficient branch * deltaQ branch.1 vertex = 0) ∧
      0 < ∑ branch, coefficient branch * baseQ branch.1 := by
  classical
  obtain ⟨selected, hcard, hinfeasibleSelected⟩ :=
    exists_sparse_infeasible_branch_subsystem hinfeasible
  let selectedDelta : {branch // branch ∈ selected} → V → ℚ :=
    fun branch => deltaQ branch.1
  let selectedBase : {branch // branch ∈ selected} → ℚ :=
    fun branch => baseQ branch.1
  have hselectedReal : ¬∃ potential : V → ℝ,
      ∀ branch, (selectedBase branch : ℝ) ≤
        ∑ vertex, (selectedDelta branch vertex : ℝ) * potential vertex := by
    rintro ⟨potential, hpotential⟩
    apply hinfeasibleSelected
    refine ⟨potential, fun branch hbranch => ?_⟩
    have hrow := hpotential
      (⟨branch, hbranch⟩ : {candidate // candidate ∈ selected})
    rw [show (selectedBase ⟨branch, hbranch⟩ : ℚ) = baseQ branch by rfl,
      hbase branch] at hrow
    change branchBase label branch ≤
      dotProduct (branchDelta G label branch) potential
    rw [dotProduct]
    simpa only [selectedDelta, hdelta] using hrow
  obtain ⟨coefficient, hnonneg, hbalance, hpositive⟩ :=
    FiniteInequality.exists_rationalCertificate_of_real_infeasible
      selectedDelta selectedBase hselectedReal
  exact ⟨selected, coefficient, hcard, hnonneg, hbalance, hpositive⟩

/-- Integral branch data admit a nonnegative integral certificate on a
Helly-sparse infeasible subsystem. -/
theorem exists_sparse_integral_farkas_certificate
    (deltaZ : Branch label → V → ℤ) (baseZ : Branch label → ℤ)
    (hdelta : ∀ branch vertex,
      (deltaZ branch vertex : ℝ) = branchDelta G label branch vertex)
    (hbase : ∀ branch,
      (baseZ branch : ℝ) = branchBase label branch)
    (hinfeasible : ¬∃ potential : V → ℝ, IsLaxSection G label potential) :
    ∃ (selected : Finset (Branch label))
        (coefficient : {branch // branch ∈ selected} → ℤ),
      selected.card ≤ Fintype.card V + 1 ∧
      (∀ branch, 0 ≤ coefficient branch) ∧
      (∀ vertex : V,
        ∑ branch, coefficient branch * deltaZ branch.1 vertex = 0) ∧
      0 < ∑ branch, coefficient branch * baseZ branch.1 := by
  classical
  obtain ⟨selected, hcard, hinfeasibleSelected⟩ :=
    exists_sparse_infeasible_branch_subsystem hinfeasible
  let selectedDelta : {branch // branch ∈ selected} → V → ℤ :=
    fun branch => deltaZ branch.1
  let selectedBase : {branch // branch ∈ selected} → ℤ :=
    fun branch => baseZ branch.1
  have hselectedReal : ¬∃ potential : V → ℝ,
      ∀ branch, (selectedBase branch : ℝ) ≤
        ∑ vertex, (selectedDelta branch vertex : ℝ) * potential vertex := by
    rintro ⟨potential, hpotential⟩
    apply hinfeasibleSelected
    refine ⟨potential, fun branch hbranch => ?_⟩
    have hrow := hpotential
      (⟨branch, hbranch⟩ : {candidate // candidate ∈ selected})
    rw [show (selectedBase ⟨branch, hbranch⟩ : ℤ) = baseZ branch by rfl,
      hbase branch] at hrow
    change branchBase label branch ≤
      dotProduct (branchDelta G label branch) potential
    rw [dotProduct]
    simpa only [selectedDelta, hdelta] using hrow
  obtain ⟨coefficient, hnonneg, hbalance, hpositive⟩ :=
    FiniteInequality.exists_integralCertificate_of_real_infeasible
      selectedDelta selectedBase hselectedReal
  exact ⟨selected, coefficient, hcard, hnonneg, hbalance, hpositive⟩

end

end MaxAffineTransport

end

end Maths
