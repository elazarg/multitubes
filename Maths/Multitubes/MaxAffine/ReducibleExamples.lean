/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.AnchoredEigenvalue

/-!
# Reducible max-affine spectral examples

Two finite examples isolate the role of reachability in turning an attained least relaxation
level into an additive eigenvalue.  In the first, two isolated unit-slope loops demand incompatible
eigenvalues.  In the second, the loop of maximal shift reaches the remaining vertex, and its value
propagates to an eigenvector even though the graph is not strongly connected.

## Main definitions

* `Maths.MaxAffineTransport.separatedLoopsGraph` and
  `Maths.MaxAffineTransport.separatedLoopsLabel`: two isolated loops with shifts `1` and `0`.
* `Maths.MaxAffineTransport.feedingGraph` and `Maths.MaxAffineTransport.feedingLabel`: a loop
  of shift `1` feeding a second vertex through a doubling edge.

## Main results

* `Maths.MaxAffineTransport.isLeast_relaxationLevels_separatedLoopsLabel`: the first example has
  attained least relaxation level `1`.
* `Maths.MaxAffineTransport.eigenvalues_separatedLoopsLabel_eq_empty`: the first example has no
  additive eigenvalue at any level.
* `Maths.MaxAffineTransport.isLeast_relaxationLevels_feedingLabel`: the second example also has
  least relaxation level `1`.
* `Maths.MaxAffineTransport.isEigenvector_feedingLabel`: the potential `(0, -1)` is an
  eigenvector at level `1`.
* `Maths.MaxAffineTransport.isLeast_eigenvalues_feedingLabel`: a normalized certificate on the
  critical loop and directed reachability prove that `1` is the least eigenvalue.
* `Maths.MaxAffineTransport.eigenvalues_loopLabel_eq_relaxationLevels`: the reset branch in the
  mixed reset-doubling example makes every feasible relaxation level an eigenvalue.

## Tags

max-affine, eigenvalue, reducible graph, relaxation level, reachability
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

/-! ## Main definitions -/

/-- Two isolated vertices, each carrying its own loop. -/
def separatedLoopsGraph : EdgeGraph Bool Bool where
  source := id
  target := id

/-- Unit-slope labels of shifts `1` and `0` on the two separated loops. -/
def separatedLoopsLabel : Bool → Label
  | false => ⟨⊥, 1, 1⟩
  | true => ⟨⊥, 0, 1⟩

/-- The shift-one loop acts by translation. -/
@[simp] theorem apply_separatedLoopsLabel_false (x : ℝ) :
    (separatedLoopsLabel false).apply x = 1 + x := by
  simp [separatedLoopsLabel]

/-- The shift-zero loop acts as the identity. -/
@[simp] theorem apply_separatedLoopsLabel_true (x : ℝ) :
    (separatedLoopsLabel true).apply x = x := by
  simp [separatedLoopsLabel]

/-- Both slopes in the separated-loop example are nonnegative. -/
theorem slope_separatedLoopsLabel_nonneg (edge : Bool) :
    0 ≤ (separatedLoopsLabel edge).slope := by
  cases edge <;> norm_num [separatedLoopsLabel]

/-- Each vertex of the separated-loop graph has an incoming edge. -/
theorem incoming_separatedLoopsGraph_nonempty (vertex : Bool) :
    (incoming separatedLoopsGraph vertex).Nonempty := by
  exact ⟨vertex, mem_incoming.2 rfl⟩

/-- The vertex operator of the separated loops applies the label at that vertex. -/
theorem vertexOperator_separatedLoopsLabel (x : Bool → ℝ) (vertex : Bool) :
    vertexOperator separatedLoopsGraph separatedLoopsLabel x vertex =
      (separatedLoopsLabel vertex).apply (x vertex) := by
  rw [vertexOperator_eq_sup' (incoming_separatedLoopsGraph_nonempty vertex)]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun edge hedge => ?_
    have heq : edge = vertex := by
      simpa [separatedLoopsGraph] using (mem_incoming.1 hedge)
    subst edge
    rfl
  · refine Finset.le_sup'
      (fun edge : Bool => (separatedLoopsLabel edge).apply
        (x (separatedLoopsGraph.source edge))) (mem_incoming.2 ?_)
    rfl

/-- The relaxation levels of the separated loops are exactly the levels at least `1`. -/
theorem relaxationLevels_separatedLoopsLabel :
    relaxationLevels separatedLoopsGraph separatedLoopsLabel = Set.Ici 1 := by
  ext lam
  rw [mem_relaxationLevels_iff]
  simp only [Set.mem_Ici]
  constructor
  · rintro ⟨x, hx⟩
    have h := hx false
    simp only [separatedLoopsGraph, id_eq, apply_separatedLoopsLabel_false] at h
    linarith
  · intro hlam
    refine ⟨fun _ => 0, fun edge => ?_⟩
    cases edge <;> simp <;> linarith

/-- The separated loops have attained least relaxation level `1`. -/
theorem isLeast_relaxationLevels_separatedLoopsLabel :
    IsLeast (relaxationLevels separatedLoopsGraph separatedLoopsLabel) 1 := by
  rw [relaxationLevels_separatedLoopsLabel]
  exact ⟨le_rfl, fun _ => id⟩

/-- The separated loops admit no common additive eigenvalue: their equations force the level to
be both `1` and `0`. -/
theorem not_exists_isEigenvector_separatedLoopsLabel :
    ¬∃ (lam : ℝ) (x : Bool → ℝ),
      IsEigenvector separatedLoopsGraph separatedLoopsLabel lam x := by
  rintro ⟨lam, x, hx⟩
  have hfalse := hx false
  have htrue := hx true
  rw [vertexOperator_separatedLoopsLabel] at hfalse htrue
  simp only [apply_separatedLoopsLabel_false] at hfalse
  simp only [apply_separatedLoopsLabel_true] at htrue
  linarith

/-- The eigenvalue set of the separated-loop example is empty. -/
theorem eigenvalues_separatedLoopsLabel_eq_empty :
    eigenvalues separatedLoopsGraph separatedLoopsLabel = ∅ := by
  ext lam
  simp only [mem_eigenvalues_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx⟩
  exact not_exists_isEigenvector_separatedLoopsLabel ⟨lam, x, hx⟩

/-! ## Main results -/

/-- A loop at `false` together with one edge from `false` to `true`. -/
def feedingGraph : EdgeGraph Bool Bool where
  source := fun _ => false
  target := id

/-- The loop acts by `x ↦ 1 + x`; the edge to `true` acts by `x ↦ 2x`. -/
def feedingLabel : Bool → Label
  | false => ⟨⊥, 1, 1⟩
  | true => ⟨⊥, 0, 2⟩

/-- The loop in the feeding graph acts by translation by one. -/
@[simp] theorem apply_feedingLabel_false (x : ℝ) :
    (feedingLabel false).apply x = 1 + x := by
  simp [feedingLabel]

/-- The edge leaving the critical loop doubles its input. -/
@[simp] theorem apply_feedingLabel_true (x : ℝ) :
    (feedingLabel true).apply x = 2 * x := by
  simp [feedingLabel]

/-- Both slopes in the feeding example are nonnegative. -/
theorem slope_feedingLabel_nonneg (edge : Bool) : 0 ≤ (feedingLabel edge).slope := by
  cases edge <;> norm_num [feedingLabel]

/-- Each vertex of the feeding graph has an incoming edge. -/
theorem incoming_feedingGraph_nonempty (vertex : Bool) :
    (incoming feedingGraph vertex).Nonempty := by
  exact ⟨vertex, mem_incoming.2 rfl⟩

/-- Every walk starting at `true` is empty and therefore ends at `true`. -/
theorem eq_true_of_walk_feedingGraph {finish : Bool}
    (walk : feedingGraph.Walk true finish) : finish = true := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      have hfalse : false = true := by
        rw [feedingGraph] at legal
        exact legal.trans ih
      contradiction

/-- The feeding graph is not strongly connected at its loop vertex. -/
theorem not_isStronglyConnectedAt_feedingGraph :
    ¬IsStronglyConnectedAt feedingGraph false := by
  intro hconnected
  exact Bool.noConfusion (eq_true_of_walk_feedingGraph (hconnected true).2.some)

/-- The relaxation levels of the feeding example are exactly the levels at least `1`. -/
theorem relaxationLevels_feedingLabel :
    relaxationLevels feedingGraph feedingLabel = Set.Ici 1 := by
  ext lam
  rw [mem_relaxationLevels_iff]
  simp only [Set.mem_Ici]
  constructor
  · rintro ⟨x, hx⟩
    have h := hx false
    simp only [feedingGraph, id_eq, apply_feedingLabel_false] at h
    linarith
  · intro hlam
    refine ⟨fun vertex => if vertex then -1 else 0, fun edge => ?_⟩
    cases edge <;> simp [feedingGraph] <;> linarith

/-- The feeding example has attained least relaxation level `1`. -/
theorem isLeast_relaxationLevels_feedingLabel :
    IsLeast (relaxationLevels feedingGraph feedingLabel) 1 := by
  rw [relaxationLevels_feedingLabel]
  exact ⟨le_rfl, fun _ => id⟩

/-- The genuine branches of the floorless feeding labelling are its two affine branches. -/
def feedingBranchEquiv : Branch feedingLabel ≃ Bool where
  toFun := branchEdge feedingLabel
  invFun edge := ⟨Sum.inl edge, trivial⟩
  left_inv branch := by
    apply Subtype.ext
    obtain ⟨action, hgenuine⟩ := branch
    cases action with
    | inl edge => rfl
    | inr edge =>
        cases edge <;> simp [IsGenuineBranch, feedingLabel] at hgenuine
  right_inv _ := rfl

/-- The branch equivalence sends an affine branch to its edge. -/
@[simp] theorem feedingBranchEquiv_apply (edge : Bool) :
    feedingBranchEquiv ⟨Sum.inl edge, trivial⟩ = edge := rfl

/-- The inverse branch equivalence selects the affine branch of an edge. -/
@[simp] theorem feedingBranchEquiv_symm_apply (edge : Bool) :
    feedingBranchEquiv.symm edge = ⟨Sum.inl edge, trivial⟩ := by
  change feedingBranchEquiv.invFun edge = ⟨Sum.inl edge, trivial⟩
  rfl

/-- The normalized certificate concentrated on the unit-slope loop of the feeding graph. -/
def feedingCoefficient (branch : Branch feedingLabel) : ℝ :=
  if branch.1 = Sum.inl false then 1 else 0

/-- The loop-supported coefficient is a normalized gain-flow certificate. -/
theorem isNormalizedBranchCertificate_feedingCoefficient :
    IsNormalizedBranchCertificate (G := feedingGraph) (label := feedingLabel)
      feedingCoefficient := by
  classical
  constructor
  · intro branch
    unfold feedingCoefficient
    split <;> norm_num
  constructor
  · calc
      ∑ branch, feedingCoefficient branch =
          ∑ edge : Bool, feedingCoefficient (feedingBranchEquiv.symm edge) :=
        (feedingBranchEquiv.symm.sum_comp feedingCoefficient).symm
      _ = 1 := by simp [feedingCoefficient]
  · intro vertex
    rw [(feedingBranchEquiv.symm.sum_comp fun branch =>
      feedingCoefficient branch * branchDelta feedingGraph feedingLabel branch vertex).symm]
    simp only [feedingBranchEquiv_symm_apply]
    cases vertex <;>
      simp [feedingCoefficient, branchDelta_apply, branchEdge, branchSlope,
        feedingGraph, feedingLabel]

/-- The loop-supported certificate has value `1`, the shift of the critical loop. -/
theorem branchCertificateValue_feedingCoefficient :
    branchCertificateValue feedingCoefficient = 1 := by
  classical
  calc
    branchCertificateValue feedingCoefficient =
        ∑ edge : Bool, feedingCoefficient (feedingBranchEquiv.symm edge) *
          branchBase feedingLabel (feedingBranchEquiv.symm edge) :=
      (feedingBranchEquiv.symm.sum_comp fun branch =>
        feedingCoefficient branch * branchBase feedingLabel branch).symm
    _ = 1 := by
      simp [feedingCoefficient, branchBase, rowBase, feedingLabel]

/-- The critical loop reaches both vertices of the feeding graph. -/
theorem reachable_from_critical_feedingCoefficient (vertex : Bool) :
    ∃ start,
      start ∈ criticalVertices feedingGraph feedingLabel feedingCoefficient ∧
        Nonempty (feedingGraph.Walk start vertex) := by
  have hcritical :
      false ∈ criticalVertices feedingGraph feedingLabel feedingCoefficient := by
    refine ⟨⟨Sum.inl false, trivial⟩, ?_, rfl⟩
    simp [feedingCoefficient]
  refine ⟨false, hcritical, ?_⟩
  cases vertex
  · exact ⟨.nil⟩
  · exact ⟨.concat .nil true rfl⟩

/-- The potential `(0, -1)` is an eigenvector of the feeding example at level `1`. -/
theorem isEigenvector_feedingLabel :
    IsEigenvector feedingGraph feedingLabel 1 (fun vertex => if vertex then -1 else 0) := by
  rw [isEigenvector_iff feedingGraph feedingLabel 1 _ incoming_feedingGraph_nonempty]
  constructor
  · intro edge
    cases edge <;> simp [feedingGraph]
  · intro vertex
    refine ⟨vertex, rfl, ?_⟩
    cases vertex <;> simp [feedingGraph]

/-- **The reachable-certificate theorem recovers the least eigenvalue on a reducible graph.**
The normalized certificate freezes the loop coordinate, and its outgoing edge carries a lower
bound to the remaining vertex. -/
theorem isLeast_eigenvalues_feedingLabel :
    IsLeast (eigenvalues feedingGraph feedingLabel) 1 := by
  apply isLeast_eigenvalues_of_reachable_certificate slope_feedingLabel_nonneg
    incoming_feedingGraph_nonempty isNormalizedBranchCertificate_feedingCoefficient
    branchCertificateValue_feedingCoefficient
    (potential := fun vertex => if vertex then -1 else 0)
  · intro vertex
    rw [isEigenvector_feedingLabel vertex]
  · intro vertex
    obtain ⟨start, hcritical, walk⟩ := reachable_from_critical_feedingCoefficient vertex
    exact ⟨start, Or.inl hcritical, walk⟩

/-! ## Implementation notes -/

/-- The constant reset branch makes the sole vertex of the mixed reset-doubling example a
lower-bound vertex. -/
theorem unit_mem_lowerBoundVertices_loopLabel :
    () ∈ lowerBoundVertices loopGraph loopLabel := by
  left
  refine ⟨⟨Sum.inl false, trivial⟩, ?_, rfl⟩
  simp [branchSlope, loopLabel]

/-- **Every feasible level of the mixed reset-doubling example is an eigenvalue.**  The constant
reset supplies a lower bound for the descending relaxed orbit; since there is only one vertex,
the reachability hypothesis is immediate. -/
theorem eigenvalues_loopLabel_eq_relaxationLevels :
    eigenvalues loopGraph loopLabel = relaxationLevels loopGraph loopLabel := by
  apply eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds slope_loopLabel_nonneg
  · intro vertex
    exact ⟨false, mem_incoming.2 rfl⟩
  · intro vertex
    refine ⟨(), unit_mem_lowerBoundVertices_loopLabel, ?_⟩
    exact ⟨.nil⟩

end MaxAffineTransport

end

end Maths
