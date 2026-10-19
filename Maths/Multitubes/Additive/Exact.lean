/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Potentials
public import Maths.Multitubes.Basic
public import Maths.Graph.EdgeGraph
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Additive exactness on a directed multigraph

An additive datum on the edges of a directed multigraph is a **coboundary** when
it is the difference of a vertex potential across each edge.  This file proves
the exactness criterion: on a strongly connected graph, edge data is a
coboundary exactly when every closed walk has sum zero.  It also gives the
quantitative obstruction supplied by a closed walk with nonzero sum.

The generic path semantics does not live here.  It is defined in
`Maths`; this file is its additive translation
specialization.  The edge datum `weight e` acts by `x ↦ x + weight e`, so a potential is
a section, a walk acts by translation by its walk sum, and zero cycle sums are
trivial holonomy.

A coboundary is also called an exact `1`-cochain, a potential difference, a
discrete gradient, or a tension.  Vanishing closed-walk sums are Kirchhoff's
voltage law, path independence, or conservativeness; in multiplicative form for
transition rates they are the Kolmogorov cycle criterion for reversibility.  A
nonzero cycle sum is a circulation, a first-cohomology class, a curvature, or a
holonomy obstruction.  Under the translation action, exactness is balance
(flatness) of the induced gain graph; for labels in a general group, balance is
equivalent to the existence of a switching function.  Only the
translation-labelled case is proved here.

`Maths` owns typed walk composition, constant-fiber actions,
monoid labels, and holonomy; the generic names live only there, and this file
opens them where the translation specialization needs them.

`Maths.Multitubes.Additive.Potentials` develops the one-sided inequality
`φ (source e) + weight e ≤ φ (target e)` and its positive-cycle duality.  Exactness
is its zero-defect case, and `Maths.Multitubes.Additive.Budget` characterizes the potentials of
bounded range.

## Main definitions

* `Maths.AdditiveTransport.IsCoboundary` - edge data that is the `Maths.coboundary` of a
  vertex potential.
* `Maths.translationTransport` - the direct additive reading as
  a `Maths.Transport`.

The walk sum `Maths.walkSum` that this file consumes lives in
`Maths.Multitubes.Basic`, and the reachability scopes
`Maths.LinkedTo`, `Maths.IsStronglyConnectedAt`, and
`Maths.EdgeEndpointsLinkedTo` live in
`Maths.EdgeGraph`; both are generic walk calculus.

## Main results

* `Maths.AdditiveTransport.exists_coboundary_of_baseCycleSums_eq_zero` - reconstruct
  a potential from path sums based at one vertex.
* `Maths.AdditiveTransport.isCoboundary_iff_hasZeroCycleSums` - exactness iff all
  cycle sums vanish on a strongly connected graph.
* `Maths.AdditiveTransport.isCoboundary_iff_exists_isSection` - exactness iff the
  translation transport has a section, without a connectivity hypothesis.
* `Maths.AdditiveTransport.hasZeroCycleSums_iff_hasTrivialHolonomy` - cycle sums are
  precisely translation holonomy.
* `Maths.monotone_edgeMap_translationTransport` - ordered
  translations are monotone edge maps.
* `Maths.AdditiveTransport.exists_edge_defect_ge_of_pos` and
  `Maths.AdditiveTransport.exists_edge_abs_defect_ge` - quantitative obstruction
  bounds from a positive cycle sum.

## Implementation notes

The file proves an exactness criterion, not a Hodge or cut-cycle decomposition.
It detects the vanishing of the first cohomology class but does not construct the
quotient or split arbitrary edge data into exact and circulating parts.

## References

* F. P. Kelly, *Reversibility and Stochastic Networks*, Wiley (1979), Chapter 1,
  for the Kolmogorov cycle criterion.
* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory
  Ser. B 47 (1989), 32-52, for balance and switching functions.

## Tags

coboundary, tension, potential difference, cycle sum, Kirchhoff voltage law, gain graph, holonomy,
path independence, graph cohomology
-/

@[expose] public section

namespace Maths

noncomputable section


namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Coboundaries and the cycle criterion

The sum of edge data along a walk is the generic fold `Maths.walkSum`, whose `simp` calculus
lives with the monoid walk label in `Maths.Graph.WalkLabel`. -/
section Coboundary

variable {A : Type*} [AddCommGroup A]

/-- Edge data is **exact** when it is the coboundary of some vertex potential. -/
def IsCoboundary (G : EdgeGraph V E) (weight : E → A) : Prop :=
  ∃ φ : V → A, ∀ edge : E, weight edge = coboundary G φ edge

variable {start finish : V}

theorem walkSum_eq_sub_of_isCoboundary {weight : E → A} (hweight : IsCoboundary G weight)
    (walk : G.Walk start finish) :
    ∃ φ : V → A, walkSum weight walk = φ finish - φ start := by
  obtain ⟨φ, hφ⟩ := hweight
  refine ⟨φ, ?_⟩
  rw [show weight = coboundary G φ from funext hφ, walkSum_coboundary]

/-- Exact edge data has vanishing cycle sums. -/
theorem IsCoboundary.hasZeroCycleSums {weight : E → A} (hweight : IsCoboundary G weight) :
    HasZeroCycleSums G weight := by
  obtain ⟨φ, hφ⟩ := hweight
  intro vertex cycle
  rw [show weight = coboundary G φ from funext hφ, walkSum_coboundary, sub_self]

end Coboundary

/-! ### Reachability scope
The converse construction needs the endpoints of every edge to lie on a closed
walk through a fixed base vertex: a walk out to the endpoint and a walk back.
In a directed graph neither direction follows from the other.  The scopes
themselves - `Maths.LinkedTo`,
`Maths.IsStronglyConnectedAt`, and
`Maths.EdgeEndpointsLinkedTo` - are walk-existence notions with no
additive content and live in `Maths.EdgeGraph`. -/

/-! ### The exactness criterion -/
section Reconstruction

variable {A : Type*} [AddCommGroup A]

/-- The potential built by summing edge data along a chosen walk from `base`,
and by `0` on the vertices `base` does not reach.  Well-definedness on the
reachable part is the content of
`exists_coboundary_of_baseCycleSums_eq_zero`. -/
def basePotential (G : EdgeGraph V E) (weight : E → A) (base vertex : V) : A :=
  @dite A (Nonempty (G.Walk base vertex)) (Classical.dec _)
    (fun hreach => walkSum weight hreach.some) (fun _ => 0)

theorem basePotential_eq_walkSum_of_baseCycleSums_eq_zero
    {weight : E → A} {base : V}
    (hzero : ∀ cycle : G.Walk base base, walkSum weight cycle = 0)
    {vertex : V} (walk : G.Walk base vertex)
    (hback : Nonempty (G.Walk vertex base)) :
    basePotential G weight base vertex = walkSum weight walk := by
  have hreach : Nonempty (G.Walk base vertex) := ⟨walk⟩
  have hchosen := hzero (hreach.some.append hback.some)
  have hgiven := hzero (walk.append hback.some)
  rw [walkSum_append] at hchosen hgiven
  rw [basePotential, dite_eq_left hreach]
  linear_combination (norm := abel) hchosen - hgiven

/-- **Reconstruction of a potential.**  If every closed walk at `base` has
cycle sum zero and every edge endpoint is linked to `base`, then the edge data
is a coboundary.  The potential is the path sum from `base`; the zero-cycle
hypothesis at `base` alone makes it well defined. -/
theorem exists_coboundary_of_baseCycleSums_eq_zero {weight : E → A} {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hzero : ∀ cycle : G.Walk base base, walkSum weight cycle = 0) :
    IsCoboundary G weight := by
  refine ⟨basePotential G weight base, fun edge => ?_⟩
  obtain ⟨⟨hout, hbackSource⟩, ⟨houtTarget, hbackTarget⟩⟩ := hlinked edge
  have hsource :
      basePotential G weight base (G.source edge) = walkSum weight hout.some :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero hout.some hbackSource
  have htarget :
      basePotential G weight base (G.target edge) =
        walkSum weight (hout.some.concat edge) :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero
      (hout.some.concat edge) hbackTarget
  rw [coboundary_apply, hsource, htarget, walkSum_concat]
  abel

/-- **Exactness criterion.**  On a strongly connected directed multigraph, edge
data valued in an additive commutative group is a coboundary exactly when every
closed walk has cycle sum zero.  Also known as Kirchhoff's voltage law, or as
the Kolmogorov cycle criterion in its multiplicative form. -/
theorem isCoboundary_iff_hasZeroCycleSums {weight : E → A} {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G weight ↔ HasZeroCycleSums G weight :=
  ⟨fun hweight => hweight.hasZeroCycleSums,
    fun hzero =>
      exists_coboundary_of_baseCycleSums_eq_zero
        hconnected.edgeEndpointsLinkedTo (hzero base)⟩

end Reconstruction

/-! ### The quantitative obstruction
A closed walk of positive cycle sum is not merely an obstruction to exactness:
it forces every candidate potential to be wrong on some edge of that walk, by
an amount inversely proportional to the walk's length.
The residual of a candidate potential at one edge is `Maths.AdditiveTransport.defect`,
and the one-sided existence statement is `Maths.AdditiveTransport.exists_edge_defect_ge`.
Exactness is the case where that residual vanishes on every edge. -/
section Quantitative

open Maths.AdditiveTransport

variable {weight : E → ℝ} {φ : V → ℝ} {vertex : V}

/-- Exactness is the vanishing-defect case of the one-sided potential
inequality. -/
theorem isCoboundary_iff_exists_defect_eq_zero :
    IsCoboundary G weight ↔ ∃ ψ : V → ℝ, ∀ edge : E, defect G weight ψ edge = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : weight edge = ψ (G.target edge) - ψ (G.source edge) := hψ edge
    simp only [defect]
    linarith
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : ψ (G.source edge) + weight edge - ψ (G.target edge) = 0 := hψ edge
    simp only [coboundary_apply]
    linarith

/-- Around a closed walk the candidate potential cancels: the defects of the
traversed edges sum to the cycle sum of the edge data. -/
theorem sum_defect_cycle (cycle : G.Walk vertex vertex) :
    (cycle.edges.map (defect G weight φ)).sum = walkSum weight cycle := by
  rw [sum_defect_eq, add_sub_cancel_right]

/-- A closed walk of cycle sum at least `γ > 0` has at least one edge. -/
theorem length_pos_of_le_cycleSum {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum weight cycle) :
    0 < cycle.length := by
  have hne : cycle.edges ≠ [] := by
    intro hnil
    rw [walkSum, hnil] at hcycle
    simp only [List.map_nil, List.sum_nil] at hcycle
    linarith
  have hpos : 0 < cycle.edges.length := List.length_pos_iff.mpr hne
  rwa [cycle.edges_length] at hpos

/-- A uniform one-sided bound on the defect caps every cycle sum by the walk's
length times the bound. -/
theorem cycleSum_le_length_mul_of_defect_le {δ : ℝ}
    (cycle : G.Walk vertex vertex)
    (hdefect : ∀ edge ∈ cycle.edges, defect G weight φ edge ≤ δ) :
    walkSum weight cycle ≤ (cycle.length : ℝ) * δ := by
  have hsum : (cycle.edges.map (defect G weight φ)).sum ≤ cycle.edges.length • δ := by
    have hbound := List.sum_le_length_nsmul (cycle.edges.map (defect G weight φ)) δ (by
      intro value hvalue
      obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
      exact hdefect edge hedge)
    rwa [List.length_map] at hbound
  rw [sum_defect_cycle] at hsum
  simpa [cycle.edges_length, nsmul_eq_mul] using hsum

/-- **One-sided obstruction class.**  A closed walk whose cycle sum is at least
`γ > 0` forces, for every candidate potential, some edge on that walk to exceed
the potential difference by at least `γ` divided by the walk's length.  This is
`Maths.AdditiveTransport.exists_edge_defect_ge` with the length hypothesis
supplied by positivity of `γ`. -/
theorem exists_edge_defect_ge_of_pos {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum weight cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ defect G weight φ edge :=
  exists_edge_defect_ge φ cycle (length_pos_of_le_cycleSum hγ cycle hcycle) hcycle

/-- **Absolute obstruction class.**  The same closed walk forces a deviation of
absolute value at least `γ` divided by its length. -/
theorem exists_edge_abs_defect_ge {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum weight cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ |defect G weight φ edge| := by
  obtain ⟨edge, hedge, hbound⟩ := exists_edge_defect_ge_of_pos (φ := φ) hγ cycle hcycle
  exact ⟨edge, hedge, hbound.trans (le_abs_self _)⟩

/-- A closed walk of strictly positive cycle sum excludes exactness outright. -/
theorem not_isCoboundary_of_cycleSum_pos (cycle : G.Walk vertex vertex)
    (hcycle : 0 < walkSum weight cycle) : ¬ IsCoboundary G weight := by
  intro hweight
  exact absurd (hweight.hasZeroCycleSums vertex cycle) hcycle.ne'

end Quantitative

/-! ### Translation transport

An additive edge datum `weight e` acts on one common fiber by the translation
`x ↦ x + weight e`.  Under this reading, a coboundary potential is exactly a section,
and zero cycle sums are exactly trivial holonomy. -/

section TranslationTransport

variable {A : Type*} [AddCommGroup A]

variable {weight : E → A} {start finish : V}

/-- The section equation for translation transport is the coboundary equation. -/
theorem isSection_translationTransport_iff (weight : E → A) (φ : V → A) :
    (translationTransport G weight).IsSection φ ↔
      ∀ edge : E, weight edge = coboundary G φ edge := by
  constructor
  · intro hsection edge
    have hedge := hsection edge
    change φ (G.source edge) + weight edge = φ (G.target edge) at hedge
    rw [coboundary_apply, eq_sub_iff_add_eq]
    simpa [add_comm] using hedge
  · intro h edge
    have hedge := h edge
    rw [coboundary_apply, eq_sub_iff_add_eq] at hedge
    change φ (G.source edge) + weight edge = φ (G.target edge)
    simpa [add_comm] using hedge

/-- Edge data is a coboundary exactly when its translation transport admits a
section.  No connectivity hypothesis is needed. -/
theorem isCoboundary_iff_exists_isSection (G : EdgeGraph V E) (weight : E → A) :
    IsCoboundary G weight ↔
      ∃ φ : V → A, (translationTransport G weight).IsSection φ := by
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ, (isSection_translationTransport_iff (G := G) weight φ).2 hφ⟩,
    fun ⟨φ, hφ⟩ => ⟨φ, (isSection_translationTransport_iff (G := G) weight φ).1 hφ⟩⟩

/-- Vanishing cycle sums are exactly trivial holonomy of translation
transport. -/
theorem hasZeroCycleSums_iff_hasTrivialHolonomy (G : EdgeGraph V E)
    (weight : E → A) :
    HasZeroCycleSums G weight ↔
      (translationTransport G weight).HasTrivialHolonomy := by
  constructor
  · intro hzero base cycle
    funext point
    change (translationTransport G weight).walkMap cycle point = id point
    rw [walkMap_translationTransport, hzero base cycle]
    simp
  · intro hflat base cycle
    have hpoint := congrFun (hflat base cycle) 0
    change (translationTransport G weight).walkMap cycle 0 = id 0 at hpoint
    rw [walkMap_translationTransport, zero_add] at hpoint
    simpa using hpoint

/-- On a strongly connected graph, additive exactness is equivalent to trivial
holonomy of the translation transport. -/
theorem isCoboundary_iff_hasTrivialHolonomy {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G weight ↔ (translationTransport G weight).HasTrivialHolonomy :=
  (isCoboundary_iff_hasZeroCycleSums hconnected).trans
    (hasZeroCycleSums_iff_hasTrivialHolonomy G weight)

end TranslationTransport

/-! ### Real edge data as translation labels -/
section Translation

open Maths

variable {weight : E → ℝ} {start finish : V}

/-- **Exactness as flatness.**  On a strongly connected graph, real edge data is
a potential difference exactly when the translation labelling it defines has
trivial cycle labels, that is, when its gain graph is balanced. -/
theorem isCoboundary_iff_hasTrivialCycleLabels {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G weight ↔
      HasTrivialCycleLabels G (fun edge => Multiplicative.ofAdd (weight edge)) := by
  rw [hasTrivialCycleLabels_ofAdd_iff]
  exact isCoboundary_iff_hasZeroCycleSums hconnected

end Translation

/-! ### The inequality form
A potential in the sense of `Maths.AdditiveTransport.IsPotential` is a vertex function whose
coboundary dominates the edge data; an exact potential is the equality case. -/
section Inequality

variable {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A] {weight : E → A}

/-- A potential is a vertex function whose coboundary dominates the edge data. -/
theorem isPotential_iff_le_coboundary (φ : V → A) :
    AdditiveTransport.IsPotential G weight φ ↔ ∀ edge : E, weight edge ≤ coboundary G φ edge :=
  AdditiveTransport.isPotential_iff.trans <|
    forall_congr' fun _ => by rw [coboundary_apply, le_sub_iff_add_le']

/-- A potential difference is a potential, with equality on every edge. -/
theorem isPotential_of_eq_coboundary {φ : V → A}
    (hφ : ∀ edge : E, weight edge = coboundary G φ edge) :
    AdditiveTransport.IsPotential G weight φ :=
  (isPotential_iff_le_coboundary φ).2 fun edge => (hφ edge).le

end Inequality

end AdditiveTransport

end

end Maths
