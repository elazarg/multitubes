/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.LeastEigenvalue
public import Maths.Multitubes.MaxAffine.CycleSlack

/-!
# Eigenvectors from reachable lower bounds

The descending relaxed iteration converges whenever each coordinate receives a lower bound.
Constant branches, contracting closed walks, and the critical coordinates of an optimal
certificate provide such bounds. Directed reachability propagates them to other coordinates;
strong connectivity is not required.

When every vertex is reachable from a constant branch or a contracting closed walk, every
feasible relaxation level is an eigenvalue. The full spectrum then equals the relaxation set.
For the least eigenvalue, the frozen critical coordinates of a normalized certificate can
also supply the required bounds.

## Main definitions

* `Maths.MaxAffineTransport.lowerBoundVertices`: targets of constant branches and vertices
  admitting a closed walk with slope product below one.

## Main results

* `Maths.MaxAffineTransport.holonomyApply_relax_le_iterate`: relaxed transport bounds later
  iterates along a walk.
* `Maths.MaxAffineTransport.bddBelow_relaxedStep_of_contractiveCycle`: a contracting cycle
  bounds a descending relaxed orbit below.
* `Maths.MaxAffineTransport.exists_isEigenvector_of_reachable_lowerBounds`: lower-bound
  vertices reaching the whole graph make each feasible level an eigenvalue.
* `Maths.MaxAffineTransport.eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds`: the
  resulting exact spectral classification.
* `Maths.MaxAffineTransport.mem_eigenvalues_of_le_of_reachable_lowerBounds`: every level
  above an eigenvalue is again an eigenvalue under the same reachability condition.
* `Maths.MaxAffineTransport.isLeast_eigenvalues_of_reachable_certificate`: optimal
  certificate criticality and reachable lower bounds replace strong connectivity.
-/

@[expose] public section

noncomputable section

namespace Maths.MaxAffineTransport

variable {V E : Type*} {G : EdgeGraph V E} {label : E → Label}

/-- Vertices whose descending relaxed orbit is bounded below by a constant branch or a
closed walk with slope product strictly below one. -/
def lowerBoundVertices (G : EdgeGraph V E) (label : E → Label) : Set V :=
  {vertex | (∃ branch : Branch label, branchSlope label branch = 0 ∧
      G.target (branchEdge label branch) = vertex) ∨
    ∃ cycle : G.Walk vertex vertex, Label.pathSlope (cycle.edges.map label) < 1}

variable [Fintype E] [DecidableEq V]

/-- A relaxed edge inequality propagates along a walk, with a time shift equal to its length. -/
theorem holonomyApply_relax_le_iterate (hslope : ∀ edge, 0 ≤ (label edge).slope)
    {level : ℝ} {orbit : ℕ → V → ℝ}
    (hstep : ∀ n vertex, vertexOperator G label (orbit n) vertex - level ≤ orbit (n + 1) vertex)
    {start finish : V} (walk : G.Walk start finish) (n : ℕ) :
    holonomyApply (fun edge => Label.relax level (label edge)) walk (orbit n start) ≤
      orbit (n + walk.length) finish := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      rw [holonomyApply_concat, EdgeGraph.Walk.length_concat]
      have hmono := Label.monotone_apply (f := Label.relax level (label edge))
        (by simpa using hslope edge) ih
      simp only [Label.apply_relax] at hmono
      have hedge : (label edge).apply (orbit (n + walk.length) (G.source edge)) ≤
          vertexOperator G label (orbit (n + walk.length)) (G.target edge) :=
        le_vertexOperator rfl
      rw [legal] at hedge
      have hnext := hstep (n + walk.length) (G.target edge)
      have hbound := (sub_le_sub_right hedge level).trans hnext
      simpa only [Nat.add_assoc, Label.apply_relax] using hmono.trans hbound

/-- In a descending orbit, a constant incoming branch supplies a uniform coordinate bound. -/
theorem bddBelow_relaxedStep_of_constantBranch {level : ℝ} {orbit : ℕ → V → ℝ}
    (hstep : ∀ n vertex, vertexOperator G label (orbit n) vertex - level ≤ orbit (n + 1) vertex)
    (hanti : Antitone orbit) (branch : Branch label) (hzero : branchSlope label branch = 0) :
    BddBelow (Set.range fun n => orbit n (G.target (branchEdge label branch))) := by
  refine ⟨branchBase label branch - level, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hbranch := branchBase_add_branchSlope_mul_le_apply label branch
    (orbit n (G.source (branchEdge label branch)))
  rw [hzero, zero_mul, add_zero] at hbranch
  have hedge : (label (branchEdge label branch)).apply
      (orbit n (G.source (branchEdge label branch))) ≤
      vertexOperator G label (orbit n) (G.target (branchEdge label branch)) :=
    le_vertexOperator rfl
  have hnext := hstep n (G.target (branchEdge label branch))
  have hdesc := hanti (Nat.le_succ n) (G.target (branchEdge label branch))
  linarith

/-- A contracting closed walk bounds a descending relaxed orbit below, even with no floors. -/
theorem bddBelow_relaxedStep_of_contractiveCycle (hslope : ∀ edge, 0 ≤ (label edge).slope)
    {level : ℝ} {orbit : ℕ → V → ℝ}
    (hstep : ∀ n vertex, vertexOperator G label (orbit n) vertex - level ≤ orbit (n + 1) vertex)
    (hanti : Antitone orbit) {vertex : V} (cycle : G.Walk vertex vertex)
    (hcycle : Label.pathSlope (cycle.edges.map label) < 1) :
    BddBelow (Set.range fun n => orbit n vertex) := by
  let composite := Label.compList (cycle.edges.map fun edge => Label.relax level (label edge))
  have hslope_eq : composite.slope = Label.pathSlope (cycle.edges.map label) := by
    simp [composite, Label.slope_compList_eq_pathSlope, Label.pathSlope, List.map_map,
      Function.comp_def]
  have hden : 0 < 1 - composite.slope := by rw [hslope_eq]; linarith
  refine ⟨composite.shift / (1 - composite.slope), ?_⟩
  rintro _ ⟨n, rfl⟩
  have hwalk := holonomyApply_relax_le_iterate hslope hstep cycle n
  have hcomp : composite.apply (orbit n vertex) ≤ orbit (n + cycle.length) vertex := by
    rwa [← apply_compList_edges (fun edge => by simpa using hslope edge)] at hwalk
  have haff := composite.affinePart_le_apply (orbit n vertex)
  have hdesc := hanti (Nat.le_add_right n cycle.length) vertex
  apply (div_le_iff₀ hden).mpr
  dsimp [Label.affinePart] at haff
  nlinarith

/-- A descending relaxed orbit is bounded below at every lower-bound vertex. -/
theorem bddBelow_relaxedStep_of_mem_lowerBoundVertices
    (hslope : ∀ edge, 0 ≤ (label edge).slope) {level : ℝ} {orbit : ℕ → V → ℝ}
    (hstep : ∀ n vertex, vertexOperator G label (orbit n) vertex - level ≤ orbit (n + 1) vertex)
    (hanti : Antitone orbit) {vertex : V} (hvertex : vertex ∈ lowerBoundVertices G label) :
    BddBelow (Set.range fun n => orbit n vertex) := by
  obtain ⟨branch, hzero, rfl⟩ | ⟨cycle, hcycle⟩ := hvertex
  · exact bddBelow_relaxedStep_of_constantBranch hstep hanti branch hzero
  · exact bddBelow_relaxedStep_of_contractiveCycle hslope hstep hanti cycle hcycle

/-- Directed walks propagate coordinate lower bounds throughout a descending relaxed orbit. -/
theorem bddBelow_relaxedStep_of_reachable (hslope : ∀ edge, 0 ≤ (label edge).slope)
    {level : ℝ} {orbit : ℕ → V → ℝ}
    (hstep : ∀ n vertex, vertexOperator G label (orbit n) vertex - level ≤ orbit (n + 1) vertex)
    (hanti : Antitone orbit) {start finish : V} (walk : G.Walk start finish)
    (hbound : BddBelow (Set.range fun n => orbit n start)) :
    BddBelow (Set.range fun n => orbit n finish) := by
  obtain ⟨bound, hbound⟩ := hbound
  obtain ⟨constant, hconstant⟩ := exists_lowerBound_of_walk hslope hstep walk
    (fun n => hbound ⟨n, rfl⟩)
  refine ⟨constant, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (hconstant n).trans (hanti (Nat.le_add_right n walk.length) finish)

/-- A feasible relaxed potential descends to an eigenvector when every vertex is reachable
from a constant branch or a contracting closed walk. -/
theorem exists_isEigenvector_of_reachable_lowerBounds
    (hslope : ∀ edge, 0 ≤ (label edge).slope)
    (hin : ∀ vertex, (incoming G vertex).Nonempty)
    (hreach : ∀ vertex, ∃ start ∈ lowerBoundVertices G label, Nonempty (G.Walk start vertex))
    {level : ℝ} {potential : V → ℝ}
    (hsub : ∀ vertex, vertexOperator G label potential vertex ≤ level + potential vertex) :
    ∃ vector : V → ℝ, IsEigenvector G label level vector ∧ vector ≤ potential := by
  let orbit : ℕ → V → ℝ :=
    fun n => (fun point vertex => vertexOperator G label point vertex - level)^[n] potential
  have hzero : orbit 0 = potential := rfl
  have hstep : ∀ n vertex,
      orbit (n + 1) vertex = vertexOperator G label (orbit n) vertex - level :=
    fun n vertex => congrFun (Function.iterate_succ_apply' _ n potential) vertex
  have hanti := antitone_of_relaxedStep hslope hstep (by rw [hzero]; exact hsub)
  have hbound (vertex : V) : BddBelow (Set.range fun n => orbit n vertex) := by
    obtain ⟨start, hstart, ⟨walk⟩⟩ := hreach vertex
    exact bddBelow_relaxedStep_of_reachable hslope (fun n v => (hstep n v).ge) hanti walk
      (bddBelow_relaxedStep_of_mem_lowerBoundVertices hslope
        (fun n v => (hstep n v).ge) hanti hstart)
  refine ⟨fun vertex => ⨅ n, orbit n vertex,
    isEigenvector_iInf_of_relaxedStep hin hstep hanti hbound, fun vertex => ?_⟩
  exact (ciInf_le (hbound vertex) 0).trans_eq (congrFun hzero vertex)

/-- If constant branches and contracting cycles reach every vertex, the spectrum equals all
feasible relaxation levels. No strong-connectivity or positive-slope hypothesis is needed. -/
theorem eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds
    (hslope : ∀ edge, 0 ≤ (label edge).slope)
    (hin : ∀ vertex, (incoming G vertex).Nonempty)
    (hreach : ∀ vertex, ∃ start ∈ lowerBoundVertices G label, Nonempty (G.Walk start vertex)) :
    eigenvalues G label = relaxationLevels G label := by
  apply Set.Subset.antisymm (eigenvalues_subset_relaxationLevels G label)
  intro level hlevel
  obtain ⟨potential, hpotential⟩ := (mem_relaxationLevels_iff G label level).mp hlevel
  have hsub (vertex : V) : vertexOperator G label potential vertex ≤ level + potential vertex := by
    rw [vertexOperator_eq_sup' (hin vertex)]
    refine Finset.sup'_le _ _ fun edge hedge => ?_
    simpa only [mem_incoming.mp hedge] using hpotential edge
  obtain ⟨vector, hvector, _⟩ :=
    exists_isEigenvector_of_reachable_lowerBounds hslope hin hreach hsub
  exact ⟨vector, hvector⟩

/-- Reachable lower-bound vertices make the spectrum upward closed. -/
theorem mem_eigenvalues_of_le_of_reachable_lowerBounds
    (hslope : ∀ edge, 0 ≤ (label edge).slope)
    (hin : ∀ vertex, (incoming G vertex).Nonempty)
    (hreach : ∀ vertex, ∃ start ∈ lowerBoundVertices G label, Nonempty (G.Walk start vertex))
    {level other : ℝ} (hlevel : level ∈ eigenvalues G label) (hle : level ≤ other) :
    other ∈ eigenvalues G label := by
  rw [eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds hslope hin hreach] at hlevel ⊢
  exact mem_relaxationLevels_of_le hlevel hle

/-- An attained least relaxation level determines the whole spectrum when lower-bound
vertices reach every vertex. -/
theorem eigenvalues_eq_Ici_of_reachable_lowerBounds
    (hslope : ∀ edge, 0 ≤ (label edge).slope)
    (hin : ∀ vertex, (incoming G vertex).Nonempty)
    (hreach : ∀ vertex, ∃ start ∈ lowerBoundVertices G label, Nonempty (G.Walk start vertex))
    {level : ℝ} (hleast : IsLeast (relaxationLevels G label) level) :
    eigenvalues G label = Set.Ici level := by
  rw [eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds hslope hin hreach]
  ext other
  exact ⟨fun hother => hleast.2 hother, fun hother =>
    mem_relaxationLevels_of_le hleast.1 hother⟩

variable [Fintype V]

/-- A feasible potential and a normalized certificate of the same value yield the least
eigenvalue if every vertex is reachable from a critical coordinate, a constant branch, or a
contracting closed walk. Strong connectivity is unnecessary. -/
theorem isLeast_eigenvalues_of_reachable_certificate
    (hslope : ∀ edge, 0 ≤ (label edge).slope)
    (hin : ∀ vertex, (incoming G vertex).Nonempty)
    {coefficient : Branch label → ℝ}
    (hcoefficient : IsNormalizedBranchCertificate (G := G) (label := label) coefficient)
    {level : ℝ} (hvalue : branchCertificateValue coefficient = level)
    {potential : V → ℝ}
    (hsub : ∀ vertex, vertexOperator G label potential vertex ≤ level + potential vertex)
    (hreach : ∀ vertex, ∃ start,
      (start ∈ criticalVertices G label coefficient ∨ start ∈ lowerBoundVertices G label) ∧
        Nonempty (G.Walk start vertex)) :
    IsLeast (eigenvalues G label) level := by
  have hedge (edge : E) : (label edge).apply (potential (G.source edge)) ≤
      level + potential (G.target edge) := (le_vertexOperator rfl).trans (hsub _)
  have hres := branchResidual_le_of_forall_apply_le hedge
  let orbit : ℕ → V → ℝ :=
    fun n => (fun point vertex => vertexOperator G label point vertex - level)^[n] potential
  have hzero : orbit 0 = potential := rfl
  have hstep : ∀ n vertex,
      orbit (n + 1) vertex = vertexOperator G label (orbit n) vertex - level :=
    fun n vertex => congrFun (Function.iterate_succ_apply' _ n potential) vertex
  have hanti := antitone_of_relaxedStep hslope hstep (by rw [hzero]; exact hsub)
  have hfrozen := relaxedStep_eq_of_mem_criticalVertices hslope hcoefficient hvalue hres
    hsub hzero hstep hanti
  have hbound (vertex : V) : BddBelow (Set.range fun n => orbit n vertex) := by
    obtain ⟨start, hstart, ⟨walk⟩⟩ := hreach vertex
    apply bddBelow_relaxedStep_of_reachable hslope (fun n v => (hstep n v).ge) hanti walk
    rcases hstart with hcritical | hconstant
    · refine ⟨potential start, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (hfrozen n start hcritical).ge
    · exact bddBelow_relaxedStep_of_mem_lowerBoundVertices hslope
        (fun n v => (hstep n v).ge) hanti hconstant
  refine ⟨⟨_, isEigenvector_iInf_of_relaxedStep hin hstep hanti hbound⟩, ?_⟩
  intro other hother
  have hdual := (mem_relaxationLevels_iff_forall_branchCertificateValue_le other).mp
    (eigenvalues_subset_relaxationLevels G label hother) coefficient hcoefficient
  rwa [hvalue] at hdual

end Maths.MaxAffineTransport
