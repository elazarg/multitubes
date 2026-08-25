/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.MaxAffine.Duality
public import Maths.DirectedTransport.MaxAffine.Spectrum

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The least relaxation level is the least eigenvalue

`Maths.MaxAffineTransport.eigenvalues_subset_relaxationLevels` places the eigenvalues
of a max-affine vertex operator inside the up-set of relaxation levels, and leaves open which
levels are attained.  This file settles the bottom of that up-set: **whenever the relaxation
levels have a least element, that element is the least eigenvalue**.  Since the relaxation levels
are the feasible levels of an explicit finite linear program in the pair `(lam, x)`, this is the
formula for the least eigenvalue that the cycle mean of the translation regime fails to supply at
mixed slopes.

The argument is linear programming and monotone convergence, and uses no fixed-point theorem.
Splitting each label into its genuine branches -- an affine branch for every edge and a floor branch
for every finite floor -- turns the relaxed inequality `F x ≤ lam + x` into the finite system
`gamma_b + alpha_b * x (sigma_b) - x (tau_b) ≤ lam` of `Maths.DirectedTransport.MaxAffine.Duality`,
whose dual is the **normalized gain-flow polytope**: the nonnegative branch weights of total mass
one that balance, at every vertex, the mass arriving against the gain-weighted mass leaving.  That
polytope is a closed subset of the standard simplex, hence compact, and threshold duality identifies
the relaxation levels with the upper bounds of its objective.  A least relaxation level is therefore
the value of an optimal certificate.

Complementary slackness then does the work.  Against an optimal potential the certificate's value
is a convex combination of residuals equal to their common bound, so every branch the certificate
charges is tight.  The **critical vertices** -- the targets of the charged branches -- are closed
under the positive-gain dependencies of the certificate, because balance at the source of a
charged branch of positive slope forces some charged branch to arrive there.  Consequently one
step of the relaxed operator `x ↦ F x - lam` returns the optimal potential on the critical set,
for any candidate below it agreeing with it there.

Iterating the relaxed operator from an optimal potential therefore gives a decreasing sequence
frozen on the critical set.  Strong connectivity carries those frozen values along a walk to any
vertex, and since each edge bounds the next iterate below by an increasing affine function of the
previous one, the sequence is bounded below at every coordinate.  A finite maximum of affine maps
is continuous, so the pointwise limit is an eigenvector at the least relaxation level.

The hypothesis that a least relaxation level exists is what excludes the contraction regime, and
that regime is settled by the same duality.  Summing the balance conditions over the vertices
gives `∑ p_b = ∑ alpha_b * p_b`, so with every slope below one the polytope is empty
(`Maths.MaxAffineTransport.not_isNormalizedBranchCertificate_of_slope_lt_one`), every real
number is a relaxation level, and there is no least one.  That argument sees only the balance
conditions, so it asks nothing of the graph, of the floors, or of the sign of the slopes.  At a
common nonnegative slope other than one, expansive slopes included, every real number is even an
eigenvalue (`Maths.MaxAffineTransport.eigenvalues_eq_univ_of_slope_eq`).

## Main definitions

* `Maths.MaxAffineTransport.branchEdge` and
  `Maths.MaxAffineTransport.branchSlope`: the edge and the gain of a genuine branch.
* `Maths.MaxAffineTransport.criticalVertices`: the targets of the branches a
  normalized certificate charges.

## Main results

* `Maths.MaxAffineTransport.mem_relaxationLevels_iff_forall_branchCertificateValue_le`:
  **the relaxation levels are the upper bounds of the normalized gain-flow objective.**
* `Maths.MaxAffineTransport.isCompact_setOf_isNormalizedBranchCertificate`: the
  gain-flow polytope is compact.
* `Maths.MaxAffineTransport.exists_isNormalizedBranchCertificate_value_eq`: a least
  relaxation level is the value of an optimal certificate.
* `Maths.MaxAffineTransport.branchResidual_eq_of_pos`: **complementary slackness**,
  every branch charged by an optimal certificate is tight.
* `Maths.MaxAffineTransport.source_mem_criticalVertices`: the critical set absorbs the
  positive-gain dependencies of the certificate.
* `Maths.MaxAffineTransport.vertexOperator_eq_of_mem_criticalVertices`: **the critical
  coordinates are frozen** by the relaxed operator.
* `Maths.MaxAffineTransport.isLeast_eigenvalues_of_isLeast_relaxationLevels`: **a least
  relaxation level is the least eigenvalue.**
* `Maths.MaxAffineTransport.exists_isLeast_eigenvalues_of_translation`: at floorless
  unit slopes the value is the maximum cycle mean.
* `Maths.MaxAffineTransport.sum_branchDelta`: a branch row sums to one minus its gain,
  the whole geometric content of the contraction regime.
* `Maths.MaxAffineTransport.not_isNormalizedBranchCertificate_of_slope_lt_one` and
  `Maths.MaxAffineTransport.relaxationLevels_eq_univ_of_slope_lt_one`: **with every slope
  below one the gain-flow polytope is empty**, so every real number is a relaxation level.
* `Maths.MaxAffineTransport.not_isLeast_relaxationLevels_of_slope_lt_one`: hence no least
  relaxation level, on an arbitrary graph with arbitrary floors.
* `Maths.MaxAffineTransport.not_isLeast_relaxationLevels_of_slope_eq`: at a common
  nonnegative slope other than one there is no least relaxation level; this also covers the
  expansive common slopes, which the polytope argument does not.
* `Maths.MaxAffineTransport.isLeast_eigenvalues_loopLabel`: for the two-loop labelling
  the value is `5`.

## Implementation notes

The branch system is the one of `Maths.DirectedTransport.MaxAffine.Duality` rather than a fresh
copy, so that threshold strong duality applies verbatim.  What this file adds to it is the geometry
of a branch: `Maths.MaxAffineTransport.branchEdge` and `Maths.MaxAffineTransport.branchSlope` name
the edge and the gain that `Maths.MaxAffineTransport.branchDelta` encodes implicitly, and
`Maths.MaxAffineTransport.branchBase_add_branchSlope_mul_le_apply` is the single fact that a branch
is below the label it comes from, which powers both the freezing step and the lower bound along a
walk.

The hypothesis of an incoming edge at every vertex is what makes the real-valued vertex operator
faithful; without it the operator takes a junk value where the inequality system is vacuous, and
the iteration would leave the relaxation levels behind.  Strong connectivity is used only for the
lower bound.

## References

* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992).

## Tags

eigenvalue, linear programming, duality, complementary slackness, max-affine, vertex operator
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

namespace Label

/-- **The action of a label is continuous**: it is the maximum of a constant and an affine map,
or that affine map alone when the floor is absent. -/
theorem continuous_apply (f : Label) : Continuous f.apply := by
  rcases f.floor_cases with hbot | ⟨c, hc⟩
  · have hrewrite : f.apply = fun x : ℝ => f.shift + f.slope * x :=
      funext fun x => by rw [apply_of_floor_bot hbot, affinePart]
    rw [hrewrite]
    exact continuous_const.add (continuous_const.mul continuous_id)
  · have hrewrite : f.apply = fun x : ℝ => max c (f.shift + f.slope * x) :=
      funext fun x => by rw [apply_of_floor_coe hc, affinePart]
    rw [hrewrite]
    exact continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))

end Label

/-! ## The geometry of a genuine branch -/

/-- The edge a genuine branch belongs to. -/
def branchEdge (label : E → Label) (branch : Branch label) : E :=
  Sum.elim id id branch.1

/-- The **gain** of a genuine branch: the slope of the label on an affine branch, and `0` on a
floor branch, whose inequality does not see the source vertex. -/
def branchSlope (label : E → Label) (branch : Branch label) : ℝ :=
  Sum.elim (fun e => (label e).slope) (fun _ => 0) branch.1

/-- Nonnegative slopes give nonnegative gains. -/
theorem branchSlope_nonneg {label : E → Label} (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (branch : Branch label) : 0 ≤ branchSlope label branch := by
  obtain ⟨action, hgenuine⟩ := branch
  cases action with
  | inl e => exact hslope e
  | inr e => exact le_rfl

/-- **Every genuine branch is below the label it comes from.**  The affine branch is the affine
part of the label and the floor branch is its floor, and the label is their maximum. -/
theorem branchBase_add_branchSlope_mul_le_apply (label : E → Label) (branch : Branch label)
    (z : ℝ) :
    branchBase label branch + branchSlope label branch * z ≤
      (label (branchEdge label branch)).apply z := by
  obtain ⟨action, hgenuine⟩ := branch
  cases action with
  | inl e =>
      have haffine := (label e).affinePart_le_apply z
      simp only [Label.affinePart] at haffine
      simpa [branchBase, rowBase, branchEdge, branchSlope] using haffine
  | inr e =>
      obtain hbot | ⟨c, hc⟩ := (label e).floor_cases
      · exact absurd hbot hgenuine
      · have hfloor := (label e).floor_le_coe_apply z
        rw [hc, WithBot.coe_le_coe] at hfloor
        simpa [branchBase, rowBase, hc, branchEdge, branchSlope] using hfloor

section Rows

variable [Fintype V] [DecidableEq V] {G : EdgeGraph V E} {label : E → Label}

/-- The row of a genuine branch, entrywise: a unit at its target, less its gain at its source. -/
theorem branchDelta_apply (G : EdgeGraph V E) (label : E → Label) (branch : Branch label)
    (v : V) :
    branchDelta G label branch v =
      (if v = G.target (branchEdge label branch) then (1 : ℝ) else 0) -
        branchSlope label branch *
          (if v = G.source (branchEdge label branch) then (1 : ℝ) else 0) := by
  obtain ⟨action, hgenuine⟩ := branch
  cases action with
  | inl e => rfl
  | inr e =>
      obtain hbot | ⟨c, hc⟩ := (label e).floor_cases
      · exact absurd hbot hgenuine
      · simp only [branchDelta, rowDelta, hc, WithBot.recBotCoe_coe, branchEdge, branchSlope,
          Sum.elim_inr, id_eq, zero_mul, sub_zero]
        rfl

/-- **A branch row sums to one minus its gain.**  The row carries a unit at its target and its
gain, negated, at its source, so pairing it with the all-ones direction leaves `1 - alpha_b`.
This is the only fact about the geometry of the polytope that the contraction regime needs. -/
theorem sum_branchDelta (branch : Branch label) :
    ∑ v : V, branchDelta G label branch v = 1 - branchSlope label branch := by
  simp [branchDelta_apply]

/-- The row of a genuine branch, paired with a candidate potential. -/
theorem dotProduct_branchDelta (G : EdgeGraph V E) (label : E → Label) (branch : Branch label)
    (x : V → ℝ) :
    dotProduct (branchDelta G label branch) x =
      x (G.target (branchEdge label branch)) -
        branchSlope label branch * x (G.source (branchEdge label branch)) := by
  obtain ⟨action, hgenuine⟩ := branch
  cases action with
  | inl e => exact dotProduct_rowDelta_inl e x
  | inr e =>
      obtain hbot | ⟨c, hc⟩ := (label e).floor_cases
      · exact absurd hbot hgenuine
      · simp only [branchDelta, dotProduct_rowDelta_inr_of_floor_coe hc, branchEdge,
          branchSlope, Sum.elim_inr, id_eq, zero_mul, sub_zero]

/-- The residual of a genuine branch, written out as a defect of the branch inequality. -/
theorem branchResidual_eq (G : EdgeGraph V E) (label : E → Label) (x : V → ℝ)
    (branch : Branch label) :
    branchResidual G label x branch =
      branchBase label branch +
        branchSlope label branch * x (G.source (branchEdge label branch)) -
        x (G.target (branchEdge label branch)) := by
  simp only [branchResidual, dotProduct_branchDelta]
  ring

/-- A candidate overshooting no edge by more than a level overshoots no genuine branch by more
than that level. -/
theorem branchResidual_le_of_forall_apply_le {x : V → ℝ} {lam : ℝ}
    (hx : ∀ e : E, (label e).apply (x (G.source e)) ≤ lam + x (G.target e))
    (branch : Branch label) : branchResidual G label x branch ≤ lam := by
  have hbelow := branchBase_add_branchSlope_mul_le_apply label branch
    (x (G.source (branchEdge label branch)))
  have hedge := hx (branchEdge label branch)
  rw [branchResidual_eq]
  linarith

end Rows

/-! ## Relaxation levels as attainable residual thresholds -/

section Threshold

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

omit [Fintype E] in
/-- **A relaxation level is exactly an attainable uniform branch-residual threshold.** -/
theorem mem_relaxationLevels_iff_worstResidualAtMost (lam : ℝ) :
    lam ∈ relaxationLevels G label ↔ WorstResidualAtMost (G := G) (label := label) lam := by
  simp [mem_relaxationLevels_iff, worstResidualAtMost_iff_exists_edge_defect_le, defect]

/-- **The relaxation levels are the upper bounds of the normalized gain-flow objective.**  This is
threshold strong duality read at the relaxation levels, and it needs no hypothesis on the slopes:
the level is feasible exactly when no balanced mass-one branch certificate exceeds it. -/
theorem mem_relaxationLevels_iff_forall_branchCertificateValue_le (lam : ℝ) :
    lam ∈ relaxationLevels G label ↔
      ∀ coefficient : Branch label → ℝ,
        IsNormalizedBranchCertificate (G := G) (label := label) coefficient →
        branchCertificateValue coefficient ≤ lam := by
  rw [mem_relaxationLevels_iff_worstResidualAtMost, worstResidualAtMost_iff_normalizedDual_le]

end Threshold

/-! ## The optimal certificate -/

section Optimal

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

/-- **The normalized gain-flow polytope is compact.**  It is a closed subset of the standard
simplex, itself a closed box. -/
theorem isCompact_setOf_isNormalizedBranchCertificate :
    IsCompact {coefficient : Branch label → ℝ |
      IsNormalizedBranchCertificate (G := G) (label := label) coefficient} := by
  classical
  have hbox : IsCompact (Set.univ.pi fun _ : Branch label => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsubset : {coefficient : Branch label → ℝ |
        IsNormalizedBranchCertificate (G := G) (label := label) coefficient} ⊆
      Set.univ.pi fun _ : Branch label => Set.Icc (0 : ℝ) 1 := by
    intro coefficient hcoefficient branch _
    refine ⟨hcoefficient.1 branch, ?_⟩
    have hle := Finset.single_le_sum (f := coefficient)
      (fun c _ => hcoefficient.1 c) (Finset.mem_univ branch)
    rw [hcoefficient.2.1] at hle
    exact hle
  have heq : {coefficient : Branch label → ℝ |
        IsNormalizedBranchCertificate (G := G) (label := label) coefficient} =
      (⋂ branch : Branch label, {coefficient : Branch label → ℝ | 0 ≤ coefficient branch}) ∩
        ({coefficient : Branch label → ℝ | ∑ branch, coefficient branch = 1} ∩
          ⋂ v : V, {coefficient : Branch label → ℝ |
            ∑ branch, coefficient branch * branchDelta G label branch v = 0}) := by
    ext coefficient
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      IsNormalizedBranchCertificate]
  have hclosed : IsClosed {coefficient : Branch label → ℝ |
      IsNormalizedBranchCertificate (G := G) (label := label) coefficient} := by
    rw [heq]
    refine IsClosed.inter (isClosed_iInter fun branch => ?_)
      (IsClosed.inter ?_ (isClosed_iInter fun v => ?_))
    · exact isClosed_le continuous_const (continuous_apply branch)
    · exact isClosed_eq (continuous_finsetSum _ fun branch _ => continuous_apply branch)
        continuous_const
    · exact isClosed_eq
        (continuous_finsetSum _ fun branch _ => (continuous_apply branch).mul continuous_const)
        continuous_const
  exact hbox.of_isClosed_subset hclosed hsubset

/-- **A least relaxation level is the optimum of the dual program.**  Some normalized certificate
has exactly that value: the certificates form a nonempty compact set, so the objective attains a
maximum, and threshold duality pins that maximum to the least level. -/
theorem exists_isNormalizedBranchCertificate_value_eq {lam : ℝ}
    (hleast : IsLeast (relaxationLevels G label) lam) :
    ∃ coefficient : Branch label → ℝ,
      IsNormalizedBranchCertificate (G := G) (label := label) coefficient ∧
        branchCertificateValue coefficient = lam := by
  classical
  have hnotmem : lam - 1 ∉ relaxationLevels G label := fun hmem => by
    have hge := hleast.2 hmem
    linarith
  obtain ⟨witness, hwitness, -⟩ : ∃ coefficient : Branch label → ℝ,
      IsNormalizedBranchCertificate (G := G) (label := label) coefficient ∧
        ¬branchCertificateValue coefficient ≤ lam - 1 := by
    by_contra hcon
    refine hnotmem ((mem_relaxationLevels_iff_forall_branchCertificateValue_le _).2 fun c hc => ?_)
    by_contra hvalue
    exact hcon ⟨c, hc, hvalue⟩
  obtain ⟨best, hbest, hmax⟩ := isCompact_setOf_isNormalizedBranchCertificate.exists_isMaxOn
    (f := branchCertificateValue (label := label)) ⟨witness, hwitness⟩
    ((continuous_finsetSum _ fun branch _ =>
      (continuous_apply branch).mul continuous_const).continuousOn)
  refine ⟨best, hbest, le_antisymm ?_ ?_⟩
  · exact (mem_relaxationLevels_iff_forall_branchCertificateValue_le _).1 hleast.1 best hbest
  · exact hleast.2 ((mem_relaxationLevels_iff_forall_branchCertificateValue_le _).2
      fun c hc => isMaxOn_iff.1 hmax c hc)

end Optimal

/-! ## Complementary slackness and the critical vertices -/

section Critical

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

/-- **Complementary slackness.**  A certificate whose value is the common bound on the residuals
pairs to a convex combination of residuals equal to that bound, so every branch it charges is
tight. -/
theorem branchResidual_eq_of_pos {coefficient : Branch label → ℝ} {x : V → ℝ} {lam : ℝ}
    (hcoefficient : IsNormalizedBranchCertificate (G := G) (label := label) coefficient)
    (hvalue : branchCertificateValue coefficient = lam)
    (hx : ∀ branch : Branch label, branchResidual G label x branch ≤ lam)
    {branch : Branch label} (hpos : 0 < coefficient branch) :
    branchResidual G label x branch = lam := by
  classical
  have hdot : ∑ c, coefficient c * dotProduct (branchDelta G label c) x = 0 := by
    have hterm : ∀ c : Branch label, coefficient c * dotProduct (branchDelta G label c) x
        = ∑ v : V, coefficient c * branchDelta G label c v * x v := by
      intro c
      rw [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← Finset.sum_mul, hcoefficient.2.2 v, zero_mul]
  have hpair : ∑ c, coefficient c * branchResidual G label x c = lam := by
    simp only [branchResidual, mul_sub]
    rw [Finset.sum_sub_distrib, hdot, sub_zero]
    exact hvalue
  have hnonneg : ∀ c ∈ Finset.univ,
      0 ≤ coefficient c * (lam - branchResidual G label x c) := fun c _ =>
    mul_nonneg (hcoefficient.1 c) (by linarith [hx c])
  have hzero : ∑ c, coefficient c * (lam - branchResidual G label x c) = 0 := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcoefficient.2.1, hpair]
    ring
  rcases mul_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero branch (Finset.mem_univ branch)) with
    hcoef | hres
  · exact absurd hcoef (ne_of_gt hpos)
  · linarith

/-- The **critical vertices** of a normalized branch certificate: the targets of the branches it
charges. -/
def criticalVertices (G : EdgeGraph V E) (label : E → Label) (coefficient : Branch label → ℝ) :
    Set V :=
  {v | ∃ branch : Branch label, 0 < coefficient branch ∧
    G.target (branchEdge label branch) = v}

/-- **The critical set is nonempty**: a certificate of total mass one charges some branch. -/
theorem criticalVertices_nonempty {coefficient : Branch label → ℝ}
    (hcoefficient : IsNormalizedBranchCertificate (G := G) (label := label) coefficient) :
    (criticalVertices G label coefficient).Nonempty := by
  classical
  obtain ⟨branch, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hcoefficient.2.1]; exact one_ne_zero)
  exact ⟨G.target (branchEdge label branch),
    branch, lt_of_le_of_ne (hcoefficient.1 branch) (Ne.symm hne), rfl⟩

/-- **The critical set absorbs the positive-gain dependencies of the certificate.**  Balance at
the source of a charged branch of positive gain forces some charged branch to arrive there. -/
theorem source_mem_criticalVertices (hslope : ∀ e : E, 0 ≤ (label e).slope)
    {coefficient : Branch label → ℝ}
    (hcoefficient : IsNormalizedBranchCertificate (G := G) (label := label) coefficient)
    {branch : Branch label} (hpos : 0 < coefficient branch)
    (hgain : 0 < branchSlope label branch) :
    G.source (branchEdge label branch) ∈ criticalVertices G label coefficient := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : V, u = G.source (branchEdge label branch) := ⟨_, rfl⟩
  rw [← hu]
  have hbalance : ∑ c, (coefficient c *
        (if u = G.target (branchEdge label c) then (1 : ℝ) else 0) -
      coefficient c * branchSlope label c *
        (if u = G.source (branchEdge label c) then (1 : ℝ) else 0)) = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (hcoefficient.2.2 u)
    rw [branchDelta_apply]
    ring
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hbalance
  have hgainNonneg : ∀ c ∈ Finset.univ, 0 ≤ coefficient c * branchSlope label c *
      (if u = G.source (branchEdge label c) then (1 : ℝ) else 0) := by
    intro c _
    refine mul_nonneg (mul_nonneg (hcoefficient.1 c) (branchSlope_nonneg hslope c)) ?_
    split_ifs <;> norm_num
  have hlower : 0 < ∑ c, coefficient c * branchSlope label c *
      (if u = G.source (branchEdge label c) then (1 : ℝ) else 0) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hgainNonneg (Finset.mem_univ branch))
    rw [if_pos hu, mul_one]
    exact mul_pos hpos hgain
  obtain ⟨c, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hbalance]; exact hlower.ne')
  have hcoef : coefficient c ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have htarget : u = G.target (branchEdge label c) := by
    by_contra hcon
    exact hne (by rw [if_neg hcon, mul_zero])
  exact ⟨c, lt_of_le_of_ne (hcoefficient.1 c) (Ne.symm hcoef), htarget.symm⟩

/-- **The critical coordinates are frozen.**  A candidate below an optimal potential and agreeing
with it on the critical set is carried by one step of the relaxed vertex operator back to that
potential on the critical set: a charged branch arriving at a critical vertex is tight, and its
source is critical whenever its gain is positive, so the branch already attains the value; and
monotonicity keeps the step from exceeding it. -/
theorem vertexOperator_eq_of_mem_criticalVertices (hslope : ∀ e : E, 0 ≤ (label e).slope)
    {coefficient : Branch label → ℝ}
    (hcoefficient : IsNormalizedBranchCertificate (G := G) (label := label) coefficient)
    {lam : ℝ} (hvalue : branchCertificateValue coefficient = lam) {x y : V → ℝ}
    (hres : ∀ branch : Branch label, branchResidual G label x branch ≤ lam)
    (hsub : ∀ v : V, vertexOperator G label x v ≤ lam + x v) (hle : y ≤ x)
    (hfrozen : ∀ u ∈ criticalVertices G label coefficient, y u = x u)
    {v : V} (hv : v ∈ criticalVertices G label coefficient) :
    vertexOperator G label y v = lam + x v := by
  obtain ⟨branch, hpos, htarget⟩ := hv
  have htight : branchResidual G label x branch = lam :=
    branchResidual_eq_of_pos hcoefficient hvalue hres hpos
  rw [branchResidual_eq, htarget] at htight
  have hsource : branchSlope label branch * y (G.source (branchEdge label branch))
      = branchSlope label branch * x (G.source (branchEdge label branch)) := by
    rcases eq_or_lt_of_le (branchSlope_nonneg hslope branch) with hzero | hgain
    · rw [← hzero, zero_mul, zero_mul]
    · rw [hfrozen _ (source_mem_criticalVertices hslope hcoefficient hpos hgain)]
  have hbelow := branchBase_add_branchSlope_mul_le_apply label branch
    (y (G.source (branchEdge label branch)))
  have hattain : lam + x v ≤ (label (branchEdge label branch)).apply
      (y (G.source (branchEdge label branch))) := by linarith
  refine le_antisymm ?_ (le_trans hattain (le_vertexOperator htarget))
  exact le_trans (monotone_vertexOperator G hslope hle v) (hsub v)

end Critical

/-! ## The decreasing iteration -/

section Iteration

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

omit [Fintype V] in
/-- **The vertex operator is continuous** at a vertex with an incoming edge: it is a finite
maximum of continuous functions of one coordinate. -/
theorem continuous_vertexOperator (G : EdgeGraph V E) (label : E → Label) {v : V}
    (hne : (incoming G v).Nonempty) :
    Continuous fun x : V → ℝ => vertexOperator G label x v := by
  have hrewrite : (fun x : V → ℝ => vertexOperator G label x v)
      = fun x : V → ℝ => (incoming G v).sup' hne fun e => (label e).apply (x (G.source e)) :=
    funext fun _ => vertexOperator_eq_sup' hne
  rw [hrewrite]
  exact Continuous.finset_sup'_apply hne fun e _ =>
    (Label.continuous_apply (label e)).comp (continuous_apply (G.source e))

omit [Fintype V] in
/-- **A lower bound propagates along a walk.**  Each edge bounds the next iterate at its target
below by an increasing affine function of the current one at its source, so a uniform lower bound
at the start of a walk yields one at its end, offset by the length of the walk. -/
theorem exists_lowerBound_of_walk (hslope : ∀ e : E, 0 ≤ (label e).slope) {lam : ℝ}
    {iterate : ℕ → V → ℝ}
    (hstep : ∀ (n : ℕ) (v : V), vertexOperator G label (iterate n) v - lam ≤ iterate (n + 1) v)
    {start finish : V} (walk : G.Walk start finish) {bound : ℝ}
    (hstart : ∀ n : ℕ, bound ≤ iterate n start) :
    ∃ C : ℝ, ∀ n : ℕ, C ≤ iterate (n + walk.length) finish := by
  induction walk with
  | nil => exact ⟨bound, fun n => by simpa using hstart n⟩
  | concat walkSoFar edge legal ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨(label edge).shift + (label edge).slope * C - lam, fun n => ?_⟩
      have hmid : C ≤ iterate (n + walkSoFar.length) (G.source edge) := by
        rw [legal]
        exact hC n
      have haffine := (label edge).affinePart_le_apply
        (iterate (n + walkSoFar.length) (G.source edge))
      have hedge : (label edge).apply (iterate (n + walkSoFar.length) (G.source edge))
          ≤ vertexOperator G label (iterate (n + walkSoFar.length)) (G.target edge) :=
        le_vertexOperator rfl
      have hnext := hstep (n + walkSoFar.length) (G.target edge)
      have hgrow : (label edge).slope * C
          ≤ (label edge).slope * iterate (n + walkSoFar.length) (G.source edge) :=
        mul_le_mul_of_nonneg_left hmid (hslope edge)
      simp only [Label.affinePart] at haffine
      have hlength : n + (walkSoFar.length + 1) = n + walkSoFar.length + 1 := by omega
      rw [EdgeGraph.Walk.length_concat, hlength]
      linarith

end Iteration

/-! ## The least eigenvalue -/

section Main

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

open Filter Topology

/-- **The least relaxation level is the least eigenvalue.**  With
`Maths.MaxAffineTransport.eigenvalues_subset_relaxationLevels` this identifies the
least eigenvalue of the vertex operator with the optimum of an explicit finite linear program in
the pair `(lam, x)`, equivalently with the maximum of the shift sum over the normalized gain-flow
polytope.

No fixed-point theorem is used.  Duality supplies an optimal certificate, complementary slackness
freezes an optimal potential on the vertices that certificate charges, and the relaxed iteration
decreases from that potential while staying bounded below, because strong connectivity carries the
frozen values to every vertex.  Its limit is an eigenvector.

The hypotheses are those the proof uses: nonnegative slopes for monotonicity, an incoming edge at
every vertex so that the real-valued vertex operator is faithful, and strong connectivity only for
the lower bound.  Nothing is assumed about the gain-flow polytope: the hypothesis that a least
relaxation level exists is what rules out the empty case, where the levels are unbounded below. -/
theorem isLeast_eigenvalues_of_isLeast_relaxationLevels
    (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) {lam : ℝ}
    (hleast : IsLeast (relaxationLevels G label) lam) :
    IsLeast (eigenvalues G label) lam := by
  classical
  refine ⟨?_, fun mu hmu => hleast.2 (eigenvalues_subset_relaxationLevels G label hmu)⟩
  obtain ⟨coefficient, hcoefficient, hvalue⟩ :=
    exists_isNormalizedBranchCertificate_value_eq hleast
  obtain ⟨xstar, hxstar⟩ := (mem_relaxationLevels_iff G label lam).1 hleast.1
  have hres : ∀ branch : Branch label, branchResidual G label xstar branch ≤ lam :=
    branchResidual_le_of_forall_apply_le hxstar
  have hsub : ∀ v : V, vertexOperator G label xstar v ≤ lam + xstar v := by
    intro v
    rw [vertexOperator_eq_sup' (hin v)]
    refine Finset.sup'_le _ _ fun e he => ?_
    have hedge := hxstar e
    rw [mem_incoming.1 he] at hedge
    exact hedge
  obtain ⟨iterate, hzero, hsucc⟩ : ∃ f : ℕ → V → ℝ, f 0 = xstar ∧
      ∀ n : ℕ, f (n + 1) = fun v => vertexOperator G label (f n) v - lam :=
    ⟨fun n => (fun x v => vertexOperator G label x v - lam)^[n] xstar, rfl,
      fun n => Function.iterate_succ_apply' _ n xstar⟩
  have hstepEq : ∀ (n : ℕ) (v : V),
      iterate (n + 1) v = vertexOperator G label (iterate n) v - lam := fun n v => by
    rw [hsucc n]
  have hantitone : Antitone iterate := by
    refine antitone_nat_of_succ_le fun n => ?_
    induction n with
    | zero =>
        rw [Pi.le_def]
        intro v
        rw [hstepEq 0 v, hzero]
        linarith [hsub v]
    | succ n ih =>
        rw [Pi.le_def]
        intro v
        rw [hstepEq (n + 1) v, hstepEq n v]
        have hmono := monotone_vertexOperator G hslope ih v
        linarith
  have hfrozen : ∀ n : ℕ, ∀ v ∈ criticalVertices G label coefficient, iterate n v = xstar v := by
    intro n
    induction n with
    | zero =>
        intro v _
        rw [hzero]
    | succ n ih =>
        intro v hv
        have hle : iterate n ≤ xstar := by
          have hmono := hantitone (Nat.zero_le n)
          rwa [hzero] at hmono
        rw [hstepEq n v, vertexOperator_eq_of_mem_criticalVertices hslope hcoefficient hvalue
          hres hsub hle ih hv]
        ring
  obtain ⟨critical, hcritical⟩ := criticalVertices_nonempty hcoefficient
  have hstepLe : ∀ (n : ℕ) (v : V),
      vertexOperator G label (iterate n) v - lam ≤ iterate (n + 1) v :=
    fun n v => le_of_eq (hstepEq n v).symm
  have hbdd : ∀ v : V, BddBelow (Set.range fun n : ℕ => iterate n v) := by
    intro v
    obtain ⟨walk⟩ := hconn critical v
    obtain ⟨C, hC⟩ := exists_lowerBound_of_walk hslope hstepLe walk
      (bound := xstar critical) fun n => le_of_eq (hfrozen n critical hcritical).symm
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact le_trans (hC n) (Pi.le_def.mp (hantitone (Nat.le_add_right n walk.length)) v)
  obtain ⟨limitPoint, hlimitPoint⟩ : ∃ f : V → ℝ, ∀ v : V, f v = ⨅ n : ℕ, iterate n v :=
    ⟨fun v => ⨅ n : ℕ, iterate n v, fun _ => rfl⟩
  have htend : ∀ v : V, Tendsto (fun n : ℕ => iterate n v) atTop (𝓝 (limitPoint v)) := by
    intro v
    rw [hlimitPoint v]
    exact tendsto_atTop_ciInf (fun m n hmn => Pi.le_def.mp (hantitone hmn) v) (hbdd v)
  refine ⟨limitPoint, fun v => ?_⟩
  have hcont : Tendsto (fun n : ℕ => vertexOperator G label (iterate n) v) atTop
      (𝓝 (vertexOperator G label limitPoint v)) :=
    ((continuous_vertexOperator G label (hin v)).tendsto limitPoint).comp
      (tendsto_pi_nhds.2 htend)
  have hshift : Tendsto (fun n : ℕ => vertexOperator G label (iterate n) v) atTop
      (𝓝 (lam + limitPoint v)) := by
    have hnext : Tendsto (fun n : ℕ => iterate (n + 1) v) atTop (𝓝 (limitPoint v)) :=
      (htend v).comp (tendsto_add_atTop_nat 1)
    have hadd : Tendsto (fun n : ℕ => iterate (n + 1) v + lam) atTop (𝓝 (limitPoint v + lam)) :=
      hnext.add tendsto_const_nhds
    have heq : (fun n : ℕ => vertexOperator G label (iterate n) v)
        = fun n : ℕ => iterate (n + 1) v + lam := by
      funext n
      rw [hstepEq n v]
      ring
    rw [heq, add_comm lam (limitPoint v)]
    exact hadd
  exact tendsto_nhds_unique hcont hshift

end Main

/-! ## The three regimes -/

section Regimes

open MaxPlusPotential

/-- **At floorless unit slopes the least eigenvalue is the maximum cycle mean.**  The mean of a
mean-maximizing closed walk is a relaxation level, because it carries an eigenvector, and it is
the least one, because a candidate feasible at a level is a potential for the shifts reduced by
that level and so forbids a closed walk of larger mean.  The value is the eigenvalue produced by
`Maths.MaxAffineTransport.exists_isEigenvector_of_translation`, so the formula agrees
with the translation regime. -/
theorem exists_isLeast_eigenvalues_of_translation [Fintype V] [DecidableEq V] [Fintype E]
    [Nonempty V] (G : EdgeGraph V E) {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    (hfloor : ∀ e : E, (label e).floor = ⊥) (hin : ∀ vertex : V, (incoming G vertex).Nonempty)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) :
    ∃ (base : V) (best : G.Walk base base), 0 < best.length ∧
      IsLeast (relaxationLevels G label)
          (walkWeight (fun e => (label e).shift) best / best.length) ∧
        IsLeast (eigenvalues G label)
          (walkWeight (fun e => (label e).shift) best / best.length) := by
  obtain ⟨lam, base, best, hpos, -, hlam, -, x, hx⟩ :=
    exists_isEigenvector_of_translation G hslope hfloor
      (fun vertex => by
        obtain ⟨e, he⟩ := hin vertex
        exact ⟨e, mem_incoming.1 he⟩) hconn
  subst hlam
  have hlenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  have hleast : IsLeast (relaxationLevels G label)
      (walkWeight (fun e => (label e).shift) best / best.length) := by
    refine ⟨eigenvalues_subset_relaxationLevels G label ⟨x, hx⟩, fun mu hmu => ?_⟩
    obtain ⟨y, hy⟩ := (mem_relaxationLevels_iff G label mu).1 hmu
    have hpot : IsPotential G (fun e => (label e).shift - mu) y := by
      intro e
      have hvalue := hy e
      rw [Label.apply_of_floor_bot (hfloor e), Label.affinePart, hslope e, one_mul] at hvalue
      simp only
      linarith
    have hcycle := hpot.closedWalk_nonpos best
    rw [walkWeight_sub_const] at hcycle
    rw [div_le_iff₀ hlenPos]
    linarith
  exact ⟨base, best, hpos, hleast,
    isLeast_eigenvalues_of_isLeast_relaxationLevels (fun e => (hslope e) ▸ zero_le_one) hin
      hconn hleast⟩

/-- **With every slope below one the gain-flow polytope is empty.**  Summing the balance
conditions over the vertices turns them into `∑ p_b = ∑ alpha_b * p_b`, by
`Maths.MaxAffineTransport.sum_branchDelta`.  A nonnegative family with every gain below one
therefore has `∑ p_b * (1 - alpha_b) = 0` with every summand nonnegative, so the family vanishes
and cannot have total mass one.  Nothing is assumed of the graph, of the floors, or of the sign
of the slopes. -/
theorem not_isNormalizedBranchCertificate_of_slope_lt_one [Fintype V] [DecidableEq V] [Fintype E]
    {G : EdgeGraph V E} {label : E → Label} (hslope : ∀ e : E, (label e).slope < 1)
    (coefficient : Branch label → ℝ) :
    ¬IsNormalizedBranchCertificate (G := G) (label := label) coefficient := by
  rintro ⟨hnonneg, hmass, hbalance⟩
  have hgain : ∀ branch : Branch label, branchSlope label branch < 1 := by
    rintro ⟨action, hgenuine⟩
    cases action with
    | inl e => exact hslope e
    | inr e => exact zero_lt_one
  have hzero : ∑ branch : Branch label,
      coefficient branch * (1 - branchSlope label branch) = 0 := by
    have hswap : ∑ v : V, ∑ branch : Branch label,
        coefficient branch * branchDelta G label branch v = 0 := by
      simp [hbalance]
    rw [Finset.sum_comm] at hswap
    calc ∑ branch : Branch label, coefficient branch * (1 - branchSlope label branch)
        = ∑ branch : Branch label, ∑ v : V,
            coefficient branch * branchDelta G label branch v := by
          refine Finset.sum_congr rfl fun branch _ => ?_
          rw [← Finset.mul_sum, sum_branchDelta]
      _ = 0 := hswap
  have hall : ∀ branch ∈ Finset.univ,
      coefficient branch * (1 - branchSlope label branch) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun branch _ =>
      mul_nonneg (hnonneg branch) (by linarith [hgain branch])).mp hzero
  have hcoeff : ∀ branch : Branch label, coefficient branch = 0 := by
    intro branch
    rcases mul_eq_zero.mp (hall branch (Finset.mem_univ branch)) with h | h
    · exact h
    · linarith [hgain branch]
  simp [hcoeff] at hmass

/-- **In the contraction regime every real number is a relaxation level.**  The relaxation levels
are the upper bounds of the gain-flow objective, and with every slope below one there is nothing
to bound. -/
theorem relaxationLevels_eq_univ_of_slope_lt_one [Fintype V] [DecidableEq V] [Fintype E]
    {G : EdgeGraph V E} {label : E → Label} (hslope : ∀ e : E, (label e).slope < 1) :
    relaxationLevels G label = Set.univ := by
  refine Set.eq_univ_of_forall fun lam => ?_
  rw [mem_relaxationLevels_iff_forall_branchCertificateValue_le]
  intro coefficient hcoefficient
  exact absurd hcoefficient (not_isNormalizedBranchCertificate_of_slope_lt_one hslope _)

/-- **Strictly subunit slopes admit no least relaxation level.**  This is the dual reading of the
contraction regime, and it needs neither a common slope, nor floorlessness, nor connectivity, nor
an incoming edge at every vertex: emptiness of the polytope is visible from the balance
conditions alone. -/
theorem not_isLeast_relaxationLevels_of_slope_lt_one [Fintype V] [DecidableEq V] [Fintype E]
    {G : EdgeGraph V E} {label : E → Label} (hslope : ∀ e : E, (label e).slope < 1) (lam : ℝ) :
    ¬IsLeast (relaxationLevels G label) lam := by
  rintro ⟨-, hlower⟩
  have hmem : lam - 1 ∈ relaxationLevels G label := by
    rw [relaxationLevels_eq_univ_of_slope_lt_one hslope]; trivial
  linarith [hlower hmem]

/-- **Below unit slope there is no least relaxation level.**  At a common nonnegative slope other
than one every real number is an eigenvalue, hence a relaxation level, and a set containing every
real number has no least element.  So the hypothesis of
`Maths.MaxAffineTransport.isLeast_eigenvalues_of_isLeast_relaxationLevels` is exactly
what rules out the contraction regime, where the gain-flow polytope is empty.  Unlike
`Maths.MaxAffineTransport.not_isLeast_relaxationLevels_of_slope_lt_one` this covers the
expansive common slopes as well, at the cost of the hypotheses that carry an eigenvector. -/
theorem not_isLeast_relaxationLevels_of_slope_eq [Fintype V] [DecidableEq V] [Fintype E]
    [Nonempty V] (G : EdgeGraph V E) (label : E → Label) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≠ 1)
    (hslope : ∀ e : E, (label e).slope = s) (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) (lam : ℝ) :
    ¬IsLeast (relaxationLevels G label) lam := by
  intro hleast
  have huniv : eigenvalues G label = Set.univ :=
    eigenvalues_eq_univ_of_slope_eq G label hs0 hs1 hslope hfloor hin hconn
  have hmem : lam - 1 ∈ relaxationLevels G label :=
    eigenvalues_subset_relaxationLevels G label (by rw [huniv]; exact Set.mem_univ _)
  have hge := hleast.2 hmem
  linarith

/-- **The two-loop labelling: the least eigenvalue is `5`.**  Its relaxation levels are the
half-line above `5` (`Maths.MaxAffineTransport.relaxationLevels_loopLabel`), so the
formula returns `5`, in agreement with
`Maths.MaxAffineTransport.eigenvalues_loopLabel`.  The dual reading is the balance
`p_reset + p_double = 2 * p_double` of the normalized gain-flow polytope, which with total mass
one puts half the mass on each loop and values the certificate at `5`. -/
theorem isLeast_eigenvalues_loopLabel : IsLeast (eigenvalues loopGraph loopLabel) 5 := by
  refine isLeast_eigenvalues_of_isLeast_relaxationLevels slope_loopLabel_nonneg
    (fun _ => ⟨false, mem_incoming.2 rfl⟩) (fun _ _ => ⟨EdgeGraph.Walk.nil⟩) ?_
  rw [relaxationLevels_loopLabel]
  exact isLeast_Ici

end Regimes

end MaxAffineTransport

end

end Maths
