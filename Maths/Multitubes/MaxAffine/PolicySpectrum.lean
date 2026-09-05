/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.LeastEigenvalue
public import Maths.Multitubes.FiniteInequality.Parametric

/-!
# Finite-policy description of the max-affine spectrum

A policy selects one genuine incoming affine or floor branch at every vertex. The eigenvalue
equation holds exactly when all branch residuals lie below the level and the selected residual
at every vertex equals it. Each policy therefore gives a finite linear inequality system whose
lower bounds depend affinely on the level.

The levels of one policy form a closed convex subset of the real line. The whole spectrum is
their finite union, hence closed. Neither nonnegative slopes nor strong connectivity is needed;
only finiteness and an incoming edge at every vertex are required.

## Main definitions

* `Maths.MaxAffineTransport.BranchPolicy` - one genuine incoming branch at each vertex.
* `Maths.MaxAffineTransport.policyDelta`, `Maths.MaxAffineTransport.policyOffset`, and
  `Maths.MaxAffineTransport.policyRate` - the finite inequality system for a policy.
* `Maths.MaxAffineTransport.policyLevels` - the admissible levels of a policy.

## Main results

* `Maths.MaxAffineTransport.mem_policyLevels_iff` - all branches are bounded and the policy is
  tight at every vertex.
* `Maths.MaxAffineTransport.eigenvalues_eq_iUnion_policyLevels` - the finite-policy spectrum.
* `Maths.MaxAffineTransport.isClosed_policyLevels` and
  `Maths.MaxAffineTransport.convex_policyLevels` - each policy contributes a closed interval,
  allowing empty sets, points, rays, and the whole line.
* `Maths.MaxAffineTransport.isClosed_eigenvalues` - the entire spectrum is closed.
* `Maths.MaxAffineTransport.isLeast_csInf_eigenvalues` - a nonempty spectrum bounded below
  attains its infimum, even with negative slopes or without strong connectivity.
-/

@[expose] public section

noncomputable section

namespace Maths.MaxAffineTransport

variable {V E : Type*} (G : EdgeGraph V E) (label : E → Label)

/-- A selection of one genuine incoming branch at every vertex. -/
abbrev BranchPolicy :=
  ∀ vertex : V, {branch : Branch label // G.target (branchEdge label branch) = vertex}

/-- Some genuine branch of an edge attains its max-affine value at each point. -/
theorem exists_branch_apply_eq (edge : E) (point : ℝ) :
    ∃ branch : Branch label, branchEdge label branch = edge ∧
      branchBase label branch + branchSlope label branch * point = (label edge).apply point := by
  obtain hbot | ⟨floor, hfloor⟩ := (label edge).floor_cases
  · refine ⟨⟨Sum.inl edge, trivial⟩, rfl, ?_⟩
    simp [branchBase, rowBase, branchSlope, Label.apply_of_floor_bot hbot, Label.affinePart]
  · by_cases hle : floor ≤ (label edge).affinePart point
    · refine ⟨⟨Sum.inl edge, trivial⟩, rfl, ?_⟩
      rw [Label.apply_of_floor_coe hfloor, max_eq_right hle]
      rfl
    · have hgenuine : IsGenuineBranch label (Sum.inr edge) := by
        simp [IsGenuineBranch, hfloor]
      refine ⟨⟨Sum.inr edge, hgenuine⟩, rfl, ?_⟩
      simp [branchBase, rowBase, branchSlope, hfloor, Label.apply_of_floor_coe hfloor,
        max_eq_left (le_of_not_ge hle)]

variable [Fintype V] [DecidableEq V]

/-- Policy rows consist of all branch rows and the negatives of the selected branch rows. -/
def policyDelta (policy : BranchPolicy G label) : Branch label ⊕ V → V → ℝ
  | Sum.inl branch => branchDelta G label branch
  | Sum.inr vertex => -branchDelta G label (policy vertex).1

/-- The constant lower bound in each policy row. -/
def policyOffset (policy : BranchPolicy G label) : Branch label ⊕ V → ℝ
  | Sum.inl branch => branchBase label branch
  | Sum.inr vertex => -branchBase label (policy vertex).1

/-- The coefficient of the level in each policy row. -/
def policyRate : Branch label ⊕ V → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

/-- The real levels for which all branch inequalities and the policy equalities are feasible. -/
def policyLevels (policy : BranchPolicy G label) : Set ℝ :=
  FiniteInequality.feasibleParameters (policyDelta G label policy)
    (fun level row => policyOffset G label policy row + level * policyRate label row)

/-- A policy level has a potential bounding every branch residual and attaining the level on
the selected incoming branch at every vertex. -/
theorem mem_policyLevels_iff (policy : BranchPolicy G label) (level : ℝ) :
    level ∈ policyLevels G label policy ↔
      ∃ potential : V → ℝ,
        (∀ branch, branchResidual G label potential branch ≤ level) ∧
        ∀ vertex, branchResidual G label potential (policy vertex).1 = level := by
  constructor
  · rintro ⟨potential, hpotential⟩
    have hle (branch : Branch label) : branchResidual G label potential branch ≤ level := by
      have hrow := hpotential (Sum.inl branch)
      simp only [policyOffset, policyRate, policyDelta, mul_neg, mul_one] at hrow
      dsimp [branchResidual]
      linarith
    refine ⟨potential, hle, fun vertex => ?_⟩
    have hrow := hpotential (Sum.inr vertex)
    simp only [policyOffset, policyRate, policyDelta, mul_one, neg_dotProduct] at hrow
    have hupper := hle (policy vertex).1
    dsimp [branchResidual] at hupper ⊢
    linarith
  · rintro ⟨potential, hle, heq⟩
    refine ⟨potential, fun row => ?_⟩
    cases row with
    | inl branch =>
        have hrow := hle branch
        simp only [policyOffset, policyRate, policyDelta, mul_neg, mul_one]
        dsimp [branchResidual] at hrow
        linarith
    | inr vertex =>
        have hrow := heq vertex
        simp only [policyOffset, policyRate, policyDelta, mul_one, neg_dotProduct]
        dsimp [branchResidual] at hrow
        linarith

variable [Fintype E]

/-- The levels of a fixed policy form a closed set, even when feasible potentials are unbounded. -/
theorem isClosed_policyLevels (policy : BranchPolicy G label) :
    IsClosed (policyLevels G label policy) := by
  apply FiniteInequality.isClosed_feasibleParameters
  intro row
  exact continuous_const.add (continuous_id.mul continuous_const)

omit [Fintype E] in
/-- The levels of a fixed policy form a convex subset of the real line. -/
theorem convex_policyLevels (policy : BranchPolicy G label) :
    Convex ℝ (policyLevels G label policy) :=
  FiniteInequality.convex_feasibleParameters _ _ _

/-- An eigenvector selects an incoming branch attaining its level at every vertex. -/
theorem IsEigenvector.exists_policy {level : ℝ} {potential : V → ℝ}
    (hvector : IsEigenvector G label level potential)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    ∃ policy : BranchPolicy G label,
      ∀ vertex, branchResidual G label potential (policy vertex).1 = level := by
  classical
  have htight := ((isEigenvector_iff G label level potential hin).mp hvector).2
  have hbranch (vertex : V) :
      ∃ branch : Branch label, G.target (branchEdge label branch) = vertex ∧
        branchResidual G label potential branch = level := by
    obtain ⟨edge, htarget, hedge⟩ := htight vertex
    obtain ⟨branch, hbranch, hvalue⟩ := exists_branch_apply_eq label edge
      (potential (G.source edge))
    refine ⟨branch, hbranch ▸ htarget, ?_⟩
    rw [branchResidual_eq, hbranch, htarget, hvalue, hedge]
    ring
  choose branch htarget hvalue using hbranch
  exact ⟨fun vertex => ⟨branch vertex, htarget vertex⟩, hvalue⟩

/-- A potential satisfying a policy system is an eigenvector at its level. -/
theorem isEigenvector_of_policy {policy : BranchPolicy G label} {level : ℝ}
    {potential : V → ℝ}
    (hbound : ∀ branch, branchResidual G label potential branch ≤ level)
    (htight : ∀ vertex, branchResidual G label potential (policy vertex).1 = level)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    IsEigenvector G label level potential := by
  have hedge : ∀ edge, (label edge).apply (potential (G.source edge)) ≤
      level + potential (G.target edge) := by
    intro edge
    obtain ⟨branch, hbranch, hvalue⟩ := exists_branch_apply_eq label edge
      (potential (G.source edge))
    have hrow := hbound branch
    rw [branchResidual_eq, hbranch, hvalue] at hrow
    linarith
  apply (isEigenvector_iff G label level potential hin).mpr
  refine ⟨hedge, fun vertex => ?_⟩
  let branch := (policy vertex).1
  have htarget : G.target (branchEdge label branch) = vertex := (policy vertex).2
  refine ⟨branchEdge label branch, htarget, ?_⟩
  have hrow := htight vertex
  change branchResidual G label potential branch = level at hrow
  rw [branchResidual_eq, htarget] at hrow
  have hbelow := branchBase_add_branchSlope_mul_le_apply label branch
    (potential (G.source (branchEdge label branch)))
  have habove := hedge (branchEdge label branch)
  rw [htarget] at habove
  linarith

/-- The spectrum is exactly the union of the admissible levels of its finitely many policies. -/
theorem eigenvalues_eq_iUnion_policyLevels
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    eigenvalues G label = ⋃ policy : BranchPolicy G label, policyLevels G label policy := by
  ext level
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨potential, hvector⟩
    obtain ⟨policy, hpolicy⟩ := hvector.exists_policy G label hin
    refine ⟨policy, (mem_policyLevels_iff G label policy level).mpr ⟨potential, ?_, hpolicy⟩⟩
    exact branchResidual_le_of_forall_apply_le
      ((isEigenvector_iff G label level potential hin).mp hvector).1
  · rintro ⟨policy, hpolicy⟩
    obtain ⟨potential, hbound, htight⟩ := (mem_policyLevels_iff G label policy level).mp hpolicy
    exact ⟨potential, isEigenvector_of_policy G label hbound htight hin⟩

/-- The spectrum of a finite max-affine vertex operator is closed, with arbitrary slope signs. -/
theorem isClosed_eigenvalues (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    IsClosed (eigenvalues G label) := by
  rw [eigenvalues_eq_iUnion_policyLevels G label hin]
  exact isClosed_iUnion_of_finite (isClosed_policyLevels G label)

/-- A nonempty spectrum bounded below has a least eigenvalue, without a sign restriction on
slopes or a connectivity hypothesis. -/
theorem isLeast_csInf_eigenvalues (hin : ∀ vertex : V, (incoming G vertex).Nonempty)
    (hne : (eigenvalues G label).Nonempty) (hbdd : BddBelow (eigenvalues G label)) :
    IsLeast (eigenvalues G label) (sInf (eigenvalues G label)) :=
  (isClosed_eigenvalues G label hin).isLeast_csInf hne hbdd

end Maths.MaxAffineTransport
