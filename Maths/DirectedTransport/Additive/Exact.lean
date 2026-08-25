/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Potentials
public import Maths.DirectedTransport.Basic
public import Maths.Graph.ChargedRelation
public import Maths.Graph.EdgeGraph
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Real.Basic
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
specialization.  The edge datum `w e` acts by `x ↦ x + w e`, so a potential is
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

`Maths.DirectedTransport.Additive.Potentials` develops the one-sided inequality
`φ (source e) + w e ≤ φ (target e)` and its positive-cycle duality.  Exactness
is its zero-defect case.  `Maths.Graph.ChargedRelation` uses the opposite decrement
orientation for nonnegative charges and bounded path budgets.

## Main definitions

* `Maths.CycleCoboundary.coboundary` and
  `Maths.CycleCoboundary.IsCoboundary`.
* `Maths.CycleCoboundary.HasZeroCycleSums`.
* `Maths.CycleCoboundary.translationTransport` - the direct additive reading as
  a `Maths.Transport`.

The walk sum `Maths.walkSum` that this file consumes lives in
`Maths.DirectedTransport.Basic`, and the reachability scopes
`Maths.LinkedTo`, `Maths.IsStronglyConnectedAt`, and
`Maths.EdgeEndpointsLinkedTo` live in
`Maths.EdgeGraph`; both are generic walk calculus.

## Main results

* `Maths.CycleCoboundary.exists_coboundary_of_baseCycleSums_eq_zero` - reconstruct
  a potential from path sums based at one vertex.
* `Maths.CycleCoboundary.isCoboundary_iff_hasZeroCycleSums` - exactness iff all
  cycle sums vanish on a strongly connected graph.
* `Maths.CycleCoboundary.isCoboundary_iff_exists_isSection` - exactness iff the
  translation transport has a section, without a connectivity hypothesis.
* `Maths.CycleCoboundary.hasZeroCycleSums_iff_hasTrivialHolonomy` - cycle sums are
  precisely translation holonomy.
* `Maths.CycleCoboundary.exists_edge_defect_ge_of_pos` and
  `Maths.CycleCoboundary.exists_edge_abs_defect_ge` - quantitative obstruction
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

coboundary, tension, potential difference, cycle sum, Kirchhoff voltage law,
gain graph, holonomy
-/

@[expose] public section

namespace Maths

noncomputable section


namespace CycleCoboundary

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Sums of edge data along walks

The generic fold `Maths.walkSum` and its `simp` calculus live with
the monoid walk label in `Maths.DirectedTransport.Basic`; this section relates it to
the real walk weight and records its subtraction rule. -/

/-- The real walk weight of `Maths.DirectedTransport.Additive.Potentials` is the real instance of
`walkSum`. -/
theorem walkWeight_eq_walkSum (weight : E → ℝ) {start finish : V}
    (walk : G.Walk start finish) :
    Maths.MaxPlusPotential.walkWeight weight walk = walkSum weight walk := rfl

theorem walkSum_sub {A : Type*} [AddCommGroup A] (w₁ w₂ : E → A)
    {start finish : V} (walk : G.Walk start finish) :
    walkSum (fun edge => w₁ edge - w₂ edge) walk =
      walkSum w₁ walk - walkSum w₂ walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkSum_concat, walkSum_concat, walkSum_concat, ih]
      abel

/-! ### Coboundaries and the cycle criterion -/
section Coboundary

variable {A : Type*} [AddCommGroup A]

/-- The edge data induced by a vertex potential: the difference of the
potential across each edge.  Also called an exact `1`-cochain, a potential
difference, a discrete gradient, or a tension. -/
def coboundary (G : EdgeGraph V E) (φ : V → A) : E → A :=
  fun edge => φ (G.target edge) - φ (G.source edge)

@[simp] theorem coboundary_apply (φ : V → A) (edge : E) :
    coboundary G φ edge = φ (G.target edge) - φ (G.source edge) := rfl

/-- Edge data is **exact** when it is the coboundary of some vertex potential. -/
def IsCoboundary (G : EdgeGraph V E) (w : E → A) : Prop :=
  ∃ φ : V → A, ∀ edge : E, w edge = coboundary G φ edge

/-- Every closed walk has cycle sum zero.  This is Kirchhoff's voltage law, or
path independence of the walk sum. -/
def HasZeroCycleSums (G : EdgeGraph V E) (w : E → A) : Prop :=
  ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum w cycle = 0

variable {start finish : V}

/-- Telescoping: the walk sum of a coboundary depends only on the endpoints. -/
@[simp] theorem walkSum_coboundary (φ : V → A) (walk : G.Walk start finish) :
    walkSum (coboundary G φ) walk = φ finish - φ start := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkSum_concat, ih, coboundary_apply, legal]
      abel

theorem walkSum_eq_sub_of_isCoboundary {w : E → A} (hw : IsCoboundary G w)
    (walk : G.Walk start finish) :
    ∃ φ : V → A, walkSum w walk = φ finish - φ start := by
  obtain ⟨φ, hφ⟩ := hw
  refine ⟨φ, ?_⟩
  rw [show w = coboundary G φ from funext hφ, walkSum_coboundary]

/-- Exact edge data has vanishing cycle sums. -/
theorem IsCoboundary.hasZeroCycleSums {w : E → A} (hw : IsCoboundary G w) :
    HasZeroCycleSums G w := by
  obtain ⟨φ, hφ⟩ := hw
  intro vertex cycle
  rw [show w = coboundary G φ from funext hφ, walkSum_coboundary, sub_self]

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
def basePotential (G : EdgeGraph V E) (w : E → A) (base vertex : V) : A :=
  @dite A (Nonempty (G.Walk base vertex)) (Classical.dec _)
    (fun hreach => walkSum w hreach.some) (fun _ => 0)

theorem basePotential_eq_walkSum_of_baseCycleSums_eq_zero
    {w : E → A} {base : V}
    (hzero : ∀ cycle : G.Walk base base, walkSum w cycle = 0)
    {vertex : V} (walk : G.Walk base vertex)
    (hback : Nonempty (G.Walk vertex base)) :
    basePotential G w base vertex = walkSum w walk := by
  have hreach : Nonempty (G.Walk base vertex) := ⟨walk⟩
  have hchosen := hzero (hreach.some.append hback.some)
  have hgiven := hzero (walk.append hback.some)
  rw [walkSum_append] at hchosen hgiven
  rw [basePotential, dif_pos hreach]
  linear_combination (norm := abel) hchosen - hgiven

/-- **Reconstruction of a potential.**  If every closed walk at `base` has
cycle sum zero and every edge endpoint is linked to `base`, then the edge data
is a coboundary.  The potential is the path sum from `base`; the zero-cycle
hypothesis at `base` alone makes it well defined. -/
theorem exists_coboundary_of_baseCycleSums_eq_zero {w : E → A} {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hzero : ∀ cycle : G.Walk base base, walkSum w cycle = 0) :
    IsCoboundary G w := by
  refine ⟨basePotential G w base, fun edge => ?_⟩
  obtain ⟨⟨hout, hbackSource⟩, ⟨houtTarget, hbackTarget⟩⟩ := hlinked edge
  have hsource :
      basePotential G w base (G.source edge) = walkSum w hout.some :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero hout.some hbackSource
  have htarget :
      basePotential G w base (G.target edge) =
        walkSum w (hout.some.concat edge rfl) :=
    basePotential_eq_walkSum_of_baseCycleSums_eq_zero hzero
      (hout.some.concat edge rfl) hbackTarget
  rw [coboundary_apply, hsource, htarget, walkSum_concat]
  abel

/-- **Exactness criterion.**  On a strongly connected directed multigraph, edge
data valued in an additive commutative group is a coboundary exactly when every
closed walk has cycle sum zero.  Also known as Kirchhoff's voltage law, or as
the Kolmogorov cycle criterion in its multiplicative form. -/
theorem isCoboundary_iff_hasZeroCycleSums {w : E → A} {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G w ↔ HasZeroCycleSums G w :=
  ⟨fun hw => hw.hasZeroCycleSums,
    fun hzero =>
      exists_coboundary_of_baseCycleSums_eq_zero
        hconnected.edgeEndpointsLinkedTo (hzero base)⟩

end Reconstruction

/-! ### The quantitative obstruction
A closed walk of positive cycle sum is not merely an obstruction to exactness:
it forces every candidate potential to be wrong on some edge of that walk, by
an amount inversely proportional to the walk's length.
The residual of a candidate potential at one edge is `Maths.MaxPlusPotential.defect`,
and the one-sided existence statement is `Maths.MaxPlusPotential.exists_edge_defect_ge`.
Exactness is the case where that residual vanishes on every edge. -/
section Quantitative

open Maths.MaxPlusPotential

variable {w : E → ℝ} {φ : V → ℝ} {vertex : V}

/-- Exactness is the vanishing-defect case of the one-sided potential
inequality. -/
theorem isCoboundary_iff_exists_defect_eq_zero :
    IsCoboundary G w ↔ ∃ ψ : V → ℝ, ∀ edge : E, defect G w ψ edge = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : w edge = ψ (G.target edge) - ψ (G.source edge) := hψ edge
    simp only [defect]
    linarith
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, fun edge => ?_⟩
    have h : ψ (G.source edge) + w edge - ψ (G.target edge) = 0 := hψ edge
    simp only [coboundary_apply]
    linarith

/-- An exact potential is in particular a one-sided potential. -/
theorem isPotential_of_isCoboundary (hφ : ∀ edge : E, w edge = coboundary G φ edge) :
    IsPotential G w φ := by
  intro edge
  have h : w edge = φ (G.target edge) - φ (G.source edge) := hφ edge
  linarith

/-- Around a closed walk the candidate potential cancels: the defects of the
traversed edges sum to the cycle sum of the edge data. -/
theorem sum_defect_cycle (cycle : G.Walk vertex vertex) :
    (cycle.edges.map (defect G w φ)).sum = walkSum w cycle := by
  rw [sum_defect_eq, add_sub_cancel_right]
  rfl

/-- A closed walk of cycle sum at least `γ > 0` has at least one edge. -/
theorem length_pos_of_le_cycleSum {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
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
    (hdefect : ∀ edge ∈ cycle.edges, defect G w φ edge ≤ δ) :
    walkSum w cycle ≤ (cycle.length : ℝ) * δ := by
  have hsum : (cycle.edges.map (defect G w φ)).sum ≤ cycle.edges.length • δ := by
    have hbound := List.sum_le_card_nsmul (cycle.edges.map (defect G w φ)) δ (by
      intro value hvalue
      obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
      exact hdefect edge hedge)
    rwa [List.length_map] at hbound
  rw [sum_defect_cycle] at hsum
  simpa [cycle.edges_length, nsmul_eq_mul] using hsum

/-- **One-sided obstruction class.**  A closed walk whose cycle sum is at least
`γ > 0` forces, for every candidate potential, some edge on that walk to exceed
the potential difference by at least `γ` divided by the walk's length.  This is
`Maths.MaxPlusPotential.exists_edge_defect_ge` with the length hypothesis
supplied by positivity of `γ`. -/
theorem exists_edge_defect_ge_of_pos {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ defect G w φ edge :=
  exists_edge_defect_ge φ cycle (length_pos_of_le_cycleSum hγ cycle hcycle) hcycle

/-- **Absolute obstruction class.**  The same closed walk forces a deviation of
absolute value at least `γ` divided by its length. -/
theorem exists_edge_abs_defect_ge {γ : ℝ} (hγ : 0 < γ)
    (cycle : G.Walk vertex vertex) (hcycle : γ ≤ walkSum w cycle) :
    ∃ edge ∈ cycle.edges, γ / (cycle.length : ℝ) ≤ |defect G w φ edge| := by
  obtain ⟨edge, hedge, hbound⟩ := exists_edge_defect_ge_of_pos (φ := φ) hγ cycle hcycle
  exact ⟨edge, hedge, hbound.trans (le_abs_self _)⟩

/-- A closed walk of strictly positive cycle sum excludes exactness outright. -/
theorem not_isCoboundary_of_cycleSum_pos (cycle : G.Walk vertex vertex)
    (hcycle : 0 < walkSum w cycle) : ¬ IsCoboundary G w := by
  intro hw
  exact absurd (hw.hasZeroCycleSums vertex cycle) hcycle.ne'

end Quantitative

/-! ### Translation transport

An additive edge datum `w e` acts on one common fiber by the translation
`x ↦ x + w e`.  Under this reading, a coboundary potential is exactly a section,
and zero cycle sums are exactly trivial holonomy. -/

section TranslationTransport

variable {A : Type*} [AddCommGroup A]

variable {w : E → A} {start finish : V}

/-- The constant-fiber directed transport whose edge `e` acts by translation by
`w e`. -/
def translationTransport (G : EdgeGraph V E) (w : E → A) :
    Maths.Transport G (fun _ : V => A) :=
  Maths.ofEdgeAct G A fun edge point => point + w edge

/-- Transport by additive edge data is translation by the walk sum. -/
@[simp] theorem walkMap_translationTransport (w : E → A)
    (walk : G.Walk start finish) (point : A) :
    (translationTransport G w).walkMap walk point = point + walkSum w walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [Maths.Transport.walkMap_concat,
        Maths.fiberCast_const, ih, walkSum_concat]
      change (point + walkSum w walkSoFar) + w edge =
        point + (walkSum w walkSoFar + w edge)
      exact add_assoc _ _ _

/-- The section equation for translation transport is the coboundary equation. -/
theorem isSection_translationTransport_iff (w : E → A) (φ : V → A) :
    (translationTransport G w).IsSection φ ↔
      ∀ edge : E, w edge = coboundary G φ edge := by
  constructor
  · intro hsection edge
    have hedge := hsection edge
    change φ (G.source edge) + w edge = φ (G.target edge) at hedge
    rw [coboundary_apply, eq_sub_iff_add_eq]
    simpa [add_comm] using hedge
  · intro h edge
    have hedge := h edge
    rw [coboundary_apply, eq_sub_iff_add_eq] at hedge
    change φ (G.source edge) + w edge = φ (G.target edge)
    simpa [add_comm] using hedge

/-- Edge data is a coboundary exactly when its translation transport admits a
section.  No connectivity hypothesis is needed. -/
theorem isCoboundary_iff_exists_isSection (G : EdgeGraph V E) (w : E → A) :
    IsCoboundary G w ↔
      ∃ φ : V → A, (translationTransport G w).IsSection φ := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, (isSection_translationTransport_iff (G := G) w φ).2 hφ⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, (isSection_translationTransport_iff (G := G) w φ).1 hφ⟩

/-- Vanishing cycle sums are exactly trivial holonomy of translation
transport. -/
theorem hasZeroCycleSums_iff_hasTrivialHolonomy (G : EdgeGraph V E)
    (w : E → A) :
    HasZeroCycleSums G w ↔
      (translationTransport G w).HasTrivialHolonomy := by
  constructor
  · intro hzero base cycle
    funext point
    change (translationTransport G w).walkMap cycle point = id point
    rw [walkMap_translationTransport, hzero base cycle]
    simp
  · intro hflat base cycle
    have hpoint := congrFun (hflat base cycle) 0
    change (translationTransport G w).walkMap cycle 0 = id 0 at hpoint
    rw [walkMap_translationTransport, zero_add] at hpoint
    simpa using hpoint

/-- On a strongly connected graph, additive exactness is equivalent to trivial
holonomy of the translation transport. -/
theorem isCoboundary_iff_hasTrivialHolonomy {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G w ↔ (translationTransport G w).HasTrivialHolonomy :=
  (isCoboundary_iff_hasZeroCycleSums hconnected).trans
    (hasZeroCycleSums_iff_hasTrivialHolonomy G w)

end TranslationTransport

/-! ### Real edge data as translation labels -/
section Translation

open Maths

variable {w : E → ℝ} {start finish : V}

/-- Real edge data labels the graph by translations of the line: the walk's
composite label is its walk sum, carried into the multiplicative encoding by
the type tag `Multiplicative.ofAdd` (no exponential is applied).  Translations
invert, so this labelling is a genuine gain graph. -/
@[simp] theorem walkLabel_ofAdd (walk : G.Walk start finish) :
    walkLabel (fun edge => Multiplicative.ofAdd (w edge)) walk =
      Multiplicative.ofAdd (walkSum w walk) := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkLabel_concat, ih, walkSum_concat, ← ofAdd_add, add_comm]

/-- Vanishing cycle sums is triviality of the cycle holonomy for the
translation labelling. -/
theorem hasTrivialCycleLabels_ofAdd_iff :
    HasTrivialCycleLabels G (fun edge => Multiplicative.ofAdd (w edge)) ↔
      HasZeroCycleSums G w := by
  constructor
  · intro hflat vertex cycle
    have := hflat vertex cycle
    rw [walkLabel_ofAdd] at this
    simpa using this
  · intro hzero vertex cycle
    rw [walkLabel_ofAdd, hzero vertex cycle]
    rfl

/-- **Exactness as flatness.**  On a strongly connected graph, real edge data is
a potential difference exactly when the translation labelling it defines has
trivial cycle labels, that is, when its gain graph is balanced. -/
theorem isCoboundary_iff_hasTrivialCycleLabels {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    IsCoboundary G w ↔
      HasTrivialCycleLabels G (fun edge => Multiplicative.ofAdd (w edge)) := by
  rw [hasTrivialCycleLabels_ofAdd_iff]
  exact isCoboundary_iff_hasZeroCycleSums hconnected

end Translation

/-! ### Bridge to the inequality form
`Maths.Graph.ChargedRelation` characterises finiteness of the path budget of
nonnegative edge data by existence of a **bounded** potential obeying the
one-sided decrement `Φ (tgt e) + w e ≤ Φ (src e)`.  With the sign convention
there, that inequality says exactly that the coboundary of `-Φ` dominates the
edge data.  An exact potential is the equality case. -/
section ChargedBridge

open Maths.ChargedPathBudget

/-- Nonnegative real edge data on an edge graph, read as a charged relation. -/
def chargedRelation (G : EdgeGraph V E) (w : E → ℝ) (hw : ∀ edge, 0 ≤ w edge) :
    ChargedRelation V E where
  src := G.source
  tgt := G.target
  charge := w
  charge_nonneg := hw

variable {w : E → ℝ} {hw : ∀ edge, 0 ≤ w edge}

/-- The decrement inequality of `ChargedPathBudget` is domination of the edge
data by a coboundary.  Its sign convention is the reverse of
`Maths.MaxPlusPotential.IsPotential`, hence the negation. -/
theorem chargedIsPotential_iff_le_coboundary (Φ : V → ℝ) :
    (chargedRelation G w hw).IsPotential Φ ↔
      ∀ edge : E, w edge ≤ coboundary G (fun vertex => -Φ vertex) edge := by
  constructor
  · intro hΦ edge
    have h : Φ (G.target edge) + w edge ≤ Φ (G.source edge) := hΦ edge
    change w edge ≤ -Φ (G.target edge) - -Φ (G.source edge)
    linarith
  · intro hΦ edge
    have h : w edge ≤ -Φ (G.target edge) - -Φ (G.source edge) := hΦ edge
    change Φ (G.target edge) + w edge ≤ Φ (G.source edge)
    linarith

/-- An exact potential is a charged-relation potential, with equality on every
edge. -/
theorem chargedIsPotential_neg_of_isCoboundary {φ : V → ℝ}
    (hφ : ∀ edge : E, w edge = coboundary G φ edge) :
    (chargedRelation G w hw).IsPotential (fun vertex => -φ vertex) := by
  intro edge
  have h : w edge = φ (G.target edge) - φ (G.source edge) := hφ edge
  change -φ (G.target edge) + w edge ≤ -φ (G.source edge)
  linarith

end ChargedBridge

end CycleCoboundary

end

end Maths
