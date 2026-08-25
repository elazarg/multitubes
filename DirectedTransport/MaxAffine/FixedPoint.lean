/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Eigenvector
public import DirectedTransport.MaxAffine.Basic

import DirectedTransport.Additive.CycleMean
import DirectedTransport.Additive.ShortCycles
import Mathlib.Tactic.Linarith

/-!
# The vertex operator of a max-affine transport graph and its fixed points

A max-affine labelling of a finite directed multigraph assembles into a single self-map of
`V → ℝ`, the **vertex operator**

`F x v = ⨆ {e // G.target e = v}, (label e).apply (x (G.source e))`,

whose value at a vertex is the best demand placed on that vertex by its incoming edges.  The
first result of this file is that a lax section is exactly a sub-fixed point of `F`:
`DirectedTransport.MaxAffineTransport.IsLaxSection` holds for `x` if and only if `F x ≤ x`
pointwise.  The obstruction theory already developed for lax sections is therefore the
sub-fixed-point theory of `F`, and what remains is the passage from `≤` to `=`.

`F` is monotone as soon as every slope is nonnegative, and *subhomogeneous*: raising the argument
by a nonnegative constant raises the value by at most that constant, provided the slopes lie in
`[0, 1]`.  Full additive homogeneity, `F (x + c) = F x + c`, needs more, and the extra hypothesis
is not cosmetic: a genuine floor destroys it, because `max e (t + x + c)` exceeds
`max e (t + x) + c` whenever the floor is active before the shift and not after.  Homogeneity is
proved exactly where it holds, on unit-slope floorless labels, that is on translations.  Monotone
together with additively homogeneous is the definition of a **topical** map, so it is on that
class, and only there, that this file calls the vertex operator topical.

For a topical vertex operator the eigenvalue equation `F x = lam + x` is solved.  The solution is
not reproved: a translation labelling is a max-plus weighting by the shifts, so
`DirectedTransport.MaxPlusPotential.maxRootedWeight` -- the column of the Kleene star of
`shift - lam` rooted at a critical vertex -- is an eigenvector, its subeigenvector half being the
potential property and its tightness half the last-edge argument of the max-plus eigenvector
theory.  The eigenvalue is the maximum cycle mean of the shifts.

The graph-level hypotheses are the ones the proof uses: every vertex reachable from the base of a
mean-maximizing closed walk, and no irreducibility beyond that.  Over the reals the maximizing
walk need not be assumed either.

Outside the translation regime additive homogeneity fails and the Perron--Frobenius theory of
topical maps no longer applies verbatim, but eigenvectors are still available.  Below unit slope
modulus `DirectedTransport.MaxAffine.Contraction` pins one down uniquely, for every real
eigenvalue, and at nonnegative slopes straddling one
`DirectedTransport.MaxAffine.Eigenproblem` produces one by Brouwer's theorem in exponential
coordinates, floors included, with
`DirectedTransport.MaxAffineTransport.not_exists_isEigenvector_flipLabel` showing the sign
condition sharp.  Existence is what those arguments settle; the eigenvalue at nonnegative slopes
straddling one is not settled anywhere.

## Main definitions

* `DirectedTransport.MaxAffineTransport.incoming`: the edges arriving at a vertex.
* `DirectedTransport.MaxAffineTransport.vertexOperatorBot`,
  `DirectedTransport.MaxAffineTransport.vertexOperator`: the vertex operator, valued in
  `WithBot ℝ` so that a vertex with no incoming edge is meaningful, and its real-valued form.
* `DirectedTransport.MaxAffineTransport.IsEigenvector`: the equation `F x = lam + x`.

## Main results

* `DirectedTransport.MaxAffineTransport.isLaxSection_iff_vertexOperatorBot_le` and
  `DirectedTransport.MaxAffineTransport.isLaxSection_iff_vertexOperator_le`: **a lax section is
  precisely a sub-fixed point of the vertex operator.**
* `DirectedTransport.MaxAffineTransport.monotone_vertexOperator`: monotonicity at nonnegative
  slopes.
* `DirectedTransport.MaxAffineTransport.vertexOperator_add_const_le`: subhomogeneity for slopes
  in `[0, 1]`.
* `DirectedTransport.MaxAffineTransport.vertexOperator_add_const`: additive homogeneity for
  unit-slope floorless labels, which with monotonicity makes the operator topical
  (`DirectedTransport.MaxAffineTransport.monotone_vertexOperator_of_translation`).
* `DirectedTransport.MaxAffineTransport.isEigenvector_iff`: the eigenvalue equation splits into
  the edgewise inequality and tightness at every vertex.
* `DirectedTransport.MaxAffineTransport.isEigenvector_maxRootedWeight_of_maximizing_cycle`:
  **a fixed point of the topical vertex operator**, relative to a given mean-maximizing closed
  walk whose base reaches every vertex.
* `DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_translation`: over the reals, on
  a finite strongly connected graph in which every vertex has an incoming edge, a topical vertex
  operator has an eigenvector, with the maximum cycle mean of the shifts as eigenvalue.

## Implementation notes

`DirectedTransport.MaxAffineTransport.vertexOperator` takes the junk value `0` at a vertex with
no incoming edge, in the manner of `DirectedTransport.MaxPlusPotential.maxRootedWeight`; the
`WithBot`-valued `DirectedTransport.MaxAffineTransport.vertexOperatorBot` is the honest object
there, and the two agree wherever an incoming edge exists.  The lax-section reformulation is
stated in both forms, and only the `WithBot` form is free of nonemptiness hypotheses.

Fixed points are obtained only in the topical regime.  Nothing here upgrades a lax section to a
section for mixed slopes; the sub-fixed-point theory of that case remains what
`DirectedTransport.MaxAffine.Farkas` and `DirectedTransport.MaxAffine.Slopes` provide.

## References

* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.
* J. Gunawardena, *From max-plus algebra to nonexpansive mappings: a nonlinear theory for
  discrete event systems*, Theoret. Comput. Sci. 293 (2003), 141-167.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992).

## Tags

topical map, vertex operator, fixed point, eigenvector, max-plus, lax section, cycle mean
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {label : E → Label} {x y : V → ℝ}

/-! ## The vertex operator -/

section Incoming

variable [Fintype E] [DecidableEq V]

/-- The edges arriving at a vertex. -/
def incoming (G : EdgeGraph V E) (vertex : V) : Finset E :=
  {e ∈ Finset.univ | G.target e = vertex}

/-- Membership in the incoming edges of a vertex is arrival at that vertex. -/
@[simp] theorem mem_incoming {vertex : V} {e : E} :
    e ∈ incoming G vertex ↔ G.target e = vertex := by
  simp [incoming]

/-- The **vertex operator** in `WithBot ℝ`: the best demand placed on a vertex by its incoming
edges, taking the value `⊥` at a vertex with no incoming edge. -/
def vertexOperatorBot (G : EdgeGraph V E) (label : E → Label) (x : V → ℝ) (vertex : V) :
    WithBot ℝ :=
  (incoming G vertex).sup fun e => (((label e).apply (x (G.source e)) : ℝ) : WithBot ℝ)

/-- The **vertex operator** on `V → ℝ`, with the junk value `0` at a vertex with no incoming
edge. -/
def vertexOperator (G : EdgeGraph V E) (label : E → Label) (x : V → ℝ) (vertex : V) : ℝ :=
  (vertexOperatorBot G label x vertex).unbotD 0

/-- Every incoming edge is dominated by the vertex operator. -/
theorem le_vertexOperatorBot {vertex : V} {e : E} (he : G.target e = vertex) :
    (((label e).apply (x (G.source e)) : ℝ) : WithBot ℝ) ≤ vertexOperatorBot G label x vertex :=
  Finset.le_sup (f := fun e => (((label e).apply (x (G.source e)) : ℝ) : WithBot ℝ))
    (mem_incoming.2 he)

/-- At a vertex with an incoming edge the vertex operator is the greatest incoming demand. -/
theorem vertexOperator_eq_sup' {vertex : V} (hne : (incoming G vertex).Nonempty) :
    vertexOperator G label x vertex =
      (incoming G vertex).sup' hne fun e => (label e).apply (x (G.source e)) := by
  have hcoe : ((((incoming G vertex).sup' hne fun e =>
        (label e).apply (x (G.source e))) : ℝ) : WithBot ℝ)
      = (incoming G vertex).sup fun e =>
        (((label e).apply (x (G.source e)) : ℝ) : WithBot ℝ) := by
    rw [Finset.coe_sup']
    rfl
  rw [vertexOperator, vertexOperatorBot, ← hcoe, WithBot.unbotD_coe]

/-- At a vertex with no incoming edge the vertex operator takes its junk value. -/
theorem vertexOperator_of_incoming_eq_empty {vertex : V} (hempty : incoming G vertex = ∅) :
    vertexOperator G label x vertex = 0 := by
  simp [vertexOperator, vertexOperatorBot, hempty]

/-- Every incoming edge is dominated by the real vertex operator. -/
theorem le_vertexOperator {vertex : V} {e : E} (he : G.target e = vertex) :
    (label e).apply (x (G.source e)) ≤ vertexOperator G label x vertex := by
  have hne : (incoming G vertex).Nonempty := ⟨e, mem_incoming.2 he⟩
  rw [vertexOperator_eq_sup' hne]
  exact Finset.le_sup' (fun e => (label e).apply (x (G.source e))) (mem_incoming.2 he)

/-- The vertex operator is attained along some incoming edge. -/
theorem exists_incoming_vertexOperator_eq {vertex : V} (hne : (incoming G vertex).Nonempty) :
    ∃ e : E, G.target e = vertex ∧
      (label e).apply (x (G.source e)) = vertexOperator G label x vertex := by
  obtain ⟨e, he, hvalue⟩ :=
    Finset.exists_mem_eq_sup' hne fun e => (label e).apply (x (G.source e))
  exact ⟨e, mem_incoming.1 he, by rw [vertexOperator_eq_sup' hne, hvalue]⟩

/-! ## Lax sections are sub-fixed points -/

/-- **A lax section is precisely a sub-fixed point of the vertex operator.**  Stated in
`WithBot ℝ`, so that vertices with no incoming edge need no hypothesis: there the operator is
`⊥` and the condition is vacuous, exactly as the edgewise condition is. -/
theorem isLaxSection_iff_vertexOperatorBot_le (G : EdgeGraph V E) (label : E → Label)
    (x : V → ℝ) :
    IsLaxSection G label x ↔
      ∀ vertex : V, vertexOperatorBot G label x vertex ≤ ((x vertex : ℝ) : WithBot ℝ) := by
  constructor
  · intro hx vertex
    refine Finset.sup_le fun e he => ?_
    rw [WithBot.coe_le_coe]
    exact (mem_incoming.1 he) ▸ hx e
  · intro hx e
    have := le_trans (le_vertexOperatorBot (x := x) (label := label) (rfl : G.target e = _))
      (hx (G.target e))
    exact_mod_cast this

/-- **A lax section is precisely a sub-fixed point of the vertex operator**, in real-valued
form.  Every vertex is asked to have an incoming edge, which is what makes the real-valued
operator faithful. -/
theorem isLaxSection_iff_vertexOperator_le (G : EdgeGraph V E) (label : E → Label) (x : V → ℝ)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    IsLaxSection G label x ↔ ∀ vertex : V, vertexOperator G label x vertex ≤ x vertex := by
  constructor
  · intro hx vertex
    rw [vertexOperator_eq_sup' (hin vertex)]
    exact Finset.sup'_le _ _ fun e he => (mem_incoming.1 he) ▸ hx e
  · exact fun hx e => le_trans (le_vertexOperator rfl) (hx (G.target e))

/-! ## Monotonicity and homogeneity -/

/-- The vertex operator is monotone as soon as every slope is nonnegative. -/
theorem monotone_vertexOperator (G : EdgeGraph V E) {label : E → Label}
    (hslope : ∀ e : E, 0 ≤ (label e).slope) : Monotone (vertexOperator G label) := by
  intro x y hxy
  rw [Pi.le_def]
  intro vertex
  rcases (incoming G vertex).eq_empty_or_nonempty with hempty | hne
  · rw [vertexOperator_of_incoming_eq_empty hempty, vertexOperator_of_incoming_eq_empty hempty]
  · rw [vertexOperator_eq_sup' hne, vertexOperator_eq_sup' hne]
    refine Finset.sup'_le _ _ fun e he => le_trans ?_ (Finset.le_sup' _ he)
    exact Label.monotone_apply (hslope e) (Pi.le_def.mp hxy _)

/-- **Subhomogeneity.**  With slopes in `[0, 1]`, raising the argument by a nonnegative constant
raises the value of the vertex operator by at most that constant.  This is the one-sided
Lipschitz estimate `DirectedTransport.MaxAffineTransport.Label.apply_add_le` read at a vertex. -/
theorem vertexOperator_add_const_le (G : EdgeGraph V E) {label : E → Label}
    (hnonneg : ∀ e : E, 0 ≤ (label e).slope) (hslope : ∀ e : E, (label e).slope ≤ 1)
    (x : V → ℝ) {c : ℝ} (hc : 0 ≤ c) (vertex : V) :
    vertexOperator G label (fun v => x v + c) vertex ≤ vertexOperator G label x vertex + c := by
  rcases (incoming G vertex).eq_empty_or_nonempty with hempty | hne
  · rw [vertexOperator_of_incoming_eq_empty hempty, vertexOperator_of_incoming_eq_empty hempty]
    linarith
  · rw [vertexOperator_eq_sup' hne, vertexOperator_eq_sup' hne]
    refine Finset.sup'_le _ _ fun e he => ?_
    have hedge := Label.apply_add_le (f := label e) (hnonneg e) (x (G.source e)) hc
    have hmul : (label e).slope * c ≤ c := by nlinarith [hslope e, hnonneg e]
    have hle : (label e).apply (x (G.source e))
        ≤ (incoming G vertex).sup' hne fun e => (label e).apply (x (G.source e)) :=
      Finset.le_sup' (fun e => (label e).apply (x (G.source e))) he
    linarith

/-- **Additive homogeneity on translations.**  When every label is a floorless unit-slope
label -- that is, a translation -- the vertex operator commutes with the addition of a constant.
A genuine floor destroys this: `max e (t + x + c)` exceeds `max e (t + x) + c` as soon as the
floor is active at `x` and not at `x + c`. -/
theorem vertexOperator_add_const (G : EdgeGraph V E) {label : E → Label}
    (hslope : ∀ e : E, (label e).slope = 1) (hfloor : ∀ e : E, (label e).floor = ⊥)
    (x : V → ℝ) (c : ℝ) {vertex : V} (hne : (incoming G vertex).Nonempty) :
    vertexOperator G label (fun v => x v + c) vertex = vertexOperator G label x vertex + c := by
  have hvalue (e : E) (z : ℝ) : (label e).apply z = (label e).shift + z := by
    rw [Label.apply_of_floor_bot (hfloor e), Label.affinePart, hslope e, one_mul]
  refine le_antisymm ?_ ?_
  · rw [vertexOperator_eq_sup' hne]
    refine Finset.sup'_le _ _ fun e he => ?_
    have hle : (label e).apply (x (G.source e)) ≤ vertexOperator G label x vertex :=
      le_vertexOperator (mem_incoming.1 he)
    rw [hvalue e] at hle
    rw [hvalue e]
    linarith
  · obtain ⟨e, he, hattained⟩ := exists_incoming_vertexOperator_eq (x := x) (label := label) hne
    have hle : (label e).apply (x (G.source e) + c)
        ≤ vertexOperator G label (fun v => x v + c) vertex :=
      le_vertexOperator (x := fun v => x v + c) he
    rw [hvalue e] at hle hattained
    linarith

/-- **The vertex operator of a translation labelling is topical**: monotone, and commuting with
the addition of a constant.  The two properties are
`DirectedTransport.MaxAffineTransport.monotone_vertexOperator` and
`DirectedTransport.MaxAffineTransport.vertexOperator_add_const`, and both hypotheses of the
latter are needed for the second. -/
theorem monotone_vertexOperator_of_translation (G : EdgeGraph V E) {label : E → Label}
    (hslope : ∀ e : E, (label e).slope = 1) (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    Monotone (vertexOperator G label) ∧
      ∀ (x : V → ℝ) (c : ℝ) (vertex : V),
        vertexOperator G label (fun v => x v + c) vertex
          = vertexOperator G label x vertex + c :=
  ⟨monotone_vertexOperator G fun e => (hslope e) ▸ zero_le_one,
    fun x c vertex => vertexOperator_add_const G hslope hfloor x c (hin vertex)⟩

/-! ## Fixed points -/

/-- An **eigenvector** of the vertex operator: `F x = lam + x` pointwise.  At `lam = 0` this is a
genuine fixed point, and the inequality `F x ≤ x` defining a lax section is its sub-fixed-point
relaxation. -/
def IsEigenvector (G : EdgeGraph V E) (label : E → Label) (lam : ℝ) (x : V → ℝ) : Prop :=
  ∀ vertex : V, vertexOperator G label x vertex = lam + x vertex

/-- The eigenvalue equation splits into the edgewise inequality and **tightness**: at every
vertex some incoming edge attains the value.  This is the max-affine form of
`DirectedTransport.MaxPlusPotential.isEigenvector_iff`. -/
theorem isEigenvector_iff (G : EdgeGraph V E) (label : E → Label) (lam : ℝ) (x : V → ℝ)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) :
    IsEigenvector G label lam x ↔
      (∀ e : E, (label e).apply (x (G.source e)) ≤ lam + x (G.target e)) ∧
        ∀ vertex : V, ∃ e : E, G.target e = vertex ∧
          (label e).apply (x (G.source e)) = lam + x vertex := by
  constructor
  · intro hx
    refine ⟨fun e => (hx (G.target e)) ▸ le_vertexOperator rfl, fun vertex => ?_⟩
    obtain ⟨e, he, hattained⟩ := exists_incoming_vertexOperator_eq (x := x) (label := label)
      (hin vertex)
    exact ⟨e, he, by rw [hattained, hx vertex]⟩
  · rintro ⟨hle, htight⟩ vertex
    refine le_antisymm ?_ ?_
    · rw [vertexOperator_eq_sup' (hin vertex)]
      exact Finset.sup'_le _ _ fun e he => (mem_incoming.1 he) ▸ hle e
    · obtain ⟨e, he, hattained⟩ := htight vertex
      exact hattained ▸ le_vertexOperator he

end Incoming

/-! ### The topical eigenvector -/

section Translation

variable [Fintype E] [DecidableEq V]

open MaxPlusPotential

/-- **A fixed point of the topical vertex operator.**  For a translation labelling -- every slope
one and every floor absent -- the column of the Kleene star of `shift - lam` rooted at the base
of a mean-maximizing closed walk is an eigenvector of the vertex operator, with that walk's mean
as eigenvalue.

The hypotheses are those the proof uses: a nonempty closed walk `best` whose mean dominates that
of every closed walk, and reachability of every vertex from its base.  Irreducibility is not
assumed; only the outward half of strong connectivity is. -/
theorem isEigenvector_maxRootedWeight_of_maximizing_cycle (G : EdgeGraph V E)
    {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    (hfloor : ∀ e : E, (label e).floor = ⊥) {base : V} (best : G.Walk base base)
    (hpos : 0 < best.length)
    (hbest : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight (fun e => (label e).shift) cycle
        ≤ cycle.length * (walkWeight (fun e => (label e).shift) best / best.length))
    (hreach : ∀ vertex : V, Nonempty (G.Walk base vertex)) :
    IsEigenvector G label (walkWeight (fun e => (label e).shift) best / best.length)
      (maxRootedWeight G
        (fun e => (label e).shift
          - walkWeight (fun e => (label e).shift) best / best.length) base) := by
  set weight : E → ℝ := fun e => (label e).shift with hweight
  set lam : ℝ := walkWeight weight best / best.length with hlam
  set shifted : E → ℝ := fun e => weight e - lam with hshifted
  set x : V → ℝ := maxRootedWeight G shifted base with hx
  have hlenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  have hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight shifted cycle ≤ 0 := by
    intro vertex cycle
    rw [hshifted, walkWeight_sub_const]
    linarith [hbest vertex cycle]
  have hzero : walkWeight shifted best = 0 := by
    rw [hshifted, walkWeight_sub_const, hlam]
    field_simp
    ring
  have hvalue (e : E) (z : ℝ) : (label e).apply z = weight e + z := by
    rw [Label.apply_of_floor_bot (hfloor e), Label.affinePart, hslope e, one_mul, hweight]
  have htight (vertex : V) : ∃ e : E, G.target e = vertex ∧
      x (G.source e) + shifted e = x vertex :=
    exists_tight_edge_maxRootedWeight hcyc hreach best hpos hzero vertex
  have hin (vertex : V) : (incoming G vertex).Nonempty := by
    obtain ⟨e, he, -⟩ := htight vertex
    exact ⟨e, mem_incoming.2 he⟩
  refine (isEigenvector_iff G label lam x hin).2 ⟨fun e => ?_, fun vertex => ?_⟩
  · have hpot := maxRootedWeight_isPotential hcyc hreach e
    rw [hvalue e]
    simp only [hshifted] at hpot
    linarith
  · obtain ⟨e, he, heq⟩ := htight vertex
    refine ⟨e, he, ?_⟩
    rw [hvalue e]
    simp only [hshifted] at heq
    linarith

/-- **Existence of an eigenvector of a topical vertex operator over the reals.**  On a finite
graph in which every vertex has an incoming edge and some vertex reaches every other, a
translation labelling has an eigenvector, and the eigenvalue is the maximum cycle mean of the
shifts, attained on a closed walk of length at most the number of vertices. -/
theorem exists_isEigenvector_of_translation [Fintype V] [Nonempty V] (G : EdgeGraph V E)
    {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hinEdge : ∀ vertex : V, ∃ e : E, G.target e = vertex)
    (hconnected : ∀ source target : V, Nonempty (G.Walk source target)) :
    ∃ (lam : ℝ) (base : V) (best : G.Walk base base),
      0 < best.length ∧ best.length ≤ Fintype.card V ∧
        lam = walkWeight (fun e => (label e).shift) best / best.length ∧
        (∀ (vertex : V) (cycle : G.Walk vertex vertex), 0 < cycle.length →
          walkWeight (fun e => (label e).shift) cycle / cycle.length ≤ lam) ∧
        ∃ x : V → ℝ, IsEigenvector G label lam x := by
  obtain ⟨base, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean G (fun e => (label e).shift)
      (exists_closedWalk_length_pos (G := G) hinEdge)
  set weight : E → ℝ := fun e => (label e).shift with hweight
  set lam : ℝ := walkWeight weight best / best.length with hlam
  have hlenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  have hbest : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam := by
    intro vertex cycle
    rcases Nat.eq_zero_or_pos cycle.length with hzero | hcyclePos
    · have hedges : cycle.edges = [] :=
        List.length_eq_zero_iff.mp (by rw [EdgeGraph.Walk.edges_length, hzero])
      simp [walkWeight, hedges, hzero]
    · have hlen : (0 : ℝ) < cycle.length := by exact_mod_cast hcyclePos
      have := (div_le_iff₀ hlen).mp (hmax vertex cycle hcyclePos)
      linarith
  exact ⟨lam, base, best, hpos, hcard, hlam, fun vertex cycle hlen => hmax vertex cycle hlen, _,
    isEigenvector_maxRootedWeight_of_maximizing_cycle G hslope hfloor best hpos hbest
      fun vertex => hconnected base vertex⟩

end Translation

end MaxAffineTransport

end

end DirectedTransport
