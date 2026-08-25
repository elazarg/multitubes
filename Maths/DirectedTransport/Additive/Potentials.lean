/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Real.Basic

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additive potentials on a weighted digraph

A directed multigraph is represented by `Maths.EdgeGraph`, so parallel
edges keep their identities, and its finite walks are endpoint-indexed typed
walks.  Here every edge additionally carries a weight in a linearly ordered
field `𝕜`, and the weight of a walk is the sum of the weights of its edges.

A **potential** is a `𝕜`-valued function on vertices satisfying the edge
increment inequality `φ (source e) + weight e ≤ φ (target e)`.  The central
result is the duality between potentials and closed walks: with finitely many
edges, a potential exists exactly when no closed walk has strictly positive
weight.  The vertex type is arbitrary - a walk visiting pairwise distinct
vertices traverses pairwise distinct edges, so the edge count already bounds
every pruned walk.  The scalars are arbitrary too: the witness is a maximum over
the finitely many walks that traverse pairwise distinct edges, so no supremum,
and hence no completeness, is involved.  The quantitative form of the duality
measures, for an arbitrary candidate function, how badly some edge of a positive
closed walk must fail the inequality.

A potential is also called a feasible node potential, a feasible price vector, a
subinvariant or superharmonic function, or a Lyapunov weighting; in the (max, +)
semiring the same object is a subeigenvector, and the duality below is variously
the Bellman--Ford criterion, mean-payoff feasibility, tropical linear-programming
duality, and Farkas' lemma in the (max, +) semiring.  The supremum of the cycle
means is the max cycle mean, the tropical spectral radius, or the max-plus Perron
root.

What this file develops is the potential (subeigenvector) side of max-plus
spectral theory.  The equality side is `Maths.DirectedTransport.Additive.Eigenvector`,
and the attained cycle-mean characterization is
`Maths.DirectedTransport.Additive.CycleMean`.  The critical graph as a subgraph in its
own right, the description of the whole eigenspace, and the Kleene-star
(all-pairs longest-walk) operator, of which `maxIncomingWeight` is one row by
`Maths.MaxPlusPotential.isGreatest_range_maxRootedWeight`, are
`Maths.DirectedTransport.Additive.CriticalGraph`, as are the strongly connected
components of the critical graph and both the sufficiency and the *minimality*
of one Kleene-star column per component, the latter once a vertex of the
component in question reaches the whole graph.

## Main definitions

- `Maths.MaxPlusPotential.walkWeight` - total weight of a finite typed walk
- `Maths.MaxPlusPotential.IsPotential` - the edge increment inequality
- `Maths.MaxPlusPotential.defect` - the amount by which one edge fails it
- `Maths.MaxPlusPotential.incomingWeights`,
  `Maths.MaxPlusPotential.nodupIncomingWeights` - the weights of the walks
  arriving at a vertex, and of those among them that repeat no edge
- `Maths.MaxPlusPotential.maxIncomingWeight` - the canonical potential, the
  greatest weight of a walk arriving at a vertex without repeating an edge
- `Maths.MaxPlusPotential.matrixGraph`,
  `Maths.MaxPlusPotential.matrixWeight`,
  `Maths.MaxPlusPotential.IsSubeigenvector` - the max-plus matrix reading

## Main results

- `Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` - the
  duality, for finitely many edges, an arbitrary vertex type and arbitrary
  linearly ordered field of weights
- `Maths.MaxPlusPotential.isGreatest_incomingWeights` - with no positive closed
  walk, `maxIncomingWeight` is the greatest weight of a walk arriving at a vertex
- `Maths.MaxPlusPotential.maxIncomingWeight_eq_sSup` - over `ℝ` it is therefore
  the supremum of the weights of all arriving walks
- `Maths.MaxPlusPotential.exists_edge_defect_ge` - a closed walk of weight at
  least `γ` forces some edge to fail the inequality by at least `γ` divided by
  the length of that walk, for every candidate function
- `Maths.MaxPlusPotential.exists_subeigenvector_iff_forall_closedWalk_le` - for a
  max-plus matrix, a subeigenvector for `lam` exists exactly when every cycle has
  mean weight at most `lam`

## Implementation notes

The increment orientation `φ (source e) + weight e ≤ φ (target e)` is used
throughout.  The opposite decrement orientation
`φ (target e) + weight e ≤ φ (source e)` is the same notion applied to the
reversed graph, and is the convention of `Maths.ChargedPathBudget`, which studies
nonnegative charges and the *oscillation* of a bounded potential rather than
signed weights and cycles.

The weights live in a linearly ordered field `𝕜`, matching the generality of
`Maths.LinearProgramming`.  Multiplication is used only where the
statements themselves involve it - rescaling an edge weighting by a constant, and
the cycle *means* of the quantitative and matrix sections; the duality itself is
purely additive.  The candidate potential is a `Finset.max'` over the weights of
the walks arriving at a vertex without repeating an edge, of which `[Finite E]`
leaves only finitely many.  Over `ℝ` this maximum is the supremum of the weights
of *all* arriving walks (`maxIncomingWeight_eq_sSup`), which is the shape the
conditionally complete lattice literature states; that identification is the only
place where completeness is used, and it is a corollary rather than a step.

## References

* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and
  Linearity*, Wiley (1992), for max-plus spectral theory.
* M. Akian, S. Gaubert and A. Guterman, *Tropical polyhedra are equivalent to
  mean payoff games*, Internat. J. Algebra Comput. 22 (2012), for the
  mean-payoff reading of the duality.
* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous,
  monotone functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950, for the
  fixed-point theory of topical maps.

## Tags

potential, subeigenvector, max-plus, tropical, mean payoff, Bellman-Ford,
cycle mean
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxPlusPotential

universe uV uE

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Weights of walks -/

/-- Total weight of a finite typed walk: the sum of the weights of its
edges, counted with multiplicity in chronological order. -/
def walkWeight (weight : E → 𝕜) {start finish : V} (walk : G.Walk start finish) : 𝕜 :=
  (walk.edges.map weight).sum

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem walkWeight_nil (weight : E → 𝕜) (start : V) :
    walkWeight weight (EdgeGraph.Walk.nil : G.Walk start start) = 0 := rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem walkWeight_concat (weight : E → 𝕜) {start finish : V}
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    walkWeight weight (walk.concat edge legal) = walkWeight weight walk + weight edge := by
  simp [walkWeight]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem walkWeight_append (weight : E → 𝕜) {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    walkWeight weight (first.append second)
      = walkWeight weight first + walkWeight weight second := by
  simp [walkWeight]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Negating a weighting negates every walk weight. -/
@[simp] theorem walkWeight_neg (weight : E → 𝕜) {start finish : V}
    (walk : G.Walk start finish) :
    walkWeight (fun edge => -weight edge) walk = -walkWeight weight walk := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih => simp [ih]; ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem walkWeight_castFinish (weight : E → 𝕜) {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    walkWeight weight (walk.castFinish hfinish) = walkWeight weight walk := by
  simp [walkWeight]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Shifting every edge weight by a constant shifts the weight of a walk by that
constant times the length of the walk. -/
theorem walkWeight_sub_const (weight : E → 𝕜) (lam : 𝕜) {start finish : V}
    (walk : G.Walk start finish) :
    walkWeight (fun e => weight e - lam) walk
      = walkWeight weight walk - walk.length * lam := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      simp only [walkWeight_concat, ih, EdgeGraph.Walk.length_concat, Nat.cast_add,
        Nat.cast_one]
      ring

/-! ### Potentials and their edge defects -/

/-- A potential for an edge weighting: traversing an edge increases it by at
least the weight of that edge.  Also called a feasible node potential, a feasible
price vector, a subinvariant function, or a Lyapunov weighting; in the (max, +)
semiring it is a subeigenvector of the weight matrix.  The opposite decrement
convention is the same notion on the reversed graph. -/
def IsPotential (G : EdgeGraph V E) (weight : E → 𝕜) (φ : V → 𝕜) : Prop :=
  ∀ e : E, φ (G.source e) + weight e ≤ φ (G.target e)

/-- The amount by which a candidate function fails the increment inequality at
one edge.  Also called the edge slack, the reduced weight, or the residual of the
edge; a potential is exactly a function whose defects are all nonpositive. -/
def defect (G : EdgeGraph V E) (weight : E → 𝕜) (φ : V → 𝕜) (e : E) : 𝕜 :=
  φ (G.source e) + weight e - φ (G.target e)

theorem isPotential_iff_forall_defect_nonpos (G : EdgeGraph V E) (weight : E → 𝕜)
    (φ : V → 𝕜) : IsPotential G weight φ ↔ ∀ e : E, defect G weight φ e ≤ 0 := by
  simp [IsPotential, defect]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Telescoping along a walk: the defects of the traversed edges sum to the
weight of the walk corrected by the endpoint values. -/
theorem sum_defect_eq (weight : E → 𝕜) (φ : V → 𝕜) {start finish : V}
    (walk : G.Walk start finish) :
    (walk.edges.map (defect G weight φ)).sum
      = walkWeight weight walk + φ start - φ finish := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      subst legal
      simp only [EdgeGraph.Walk.edges_concat, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih, defect,
        walkWeight_concat]
      ring

/-- A potential dominates the weight of every walk between its endpoints. -/
theorem IsPotential.walkWeight_le {weight : E → 𝕜} {φ : V → 𝕜}
    (hφ : IsPotential G weight φ) {start finish : V} (walk : G.Walk start finish) :
    walkWeight weight walk ≤ φ finish - φ start := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      have hedge := hφ edge
      subst legal
      simp only [walkWeight_concat]
      linarith

/-- Weak duality: a potential forbids closed walks of positive weight. -/
theorem IsPotential.closedWalk_nonpos {weight : E → 𝕜} {φ : V → 𝕜}
    (hφ : IsPotential G weight φ) {vertex : V} (cycle : G.Walk vertex vertex) :
    walkWeight weight cycle ≤ 0 := by
  simpa using hφ.walkWeight_le cycle

/-! ### The duality

The finite-walk calculus this rests on - the visited-vertex list
`Maths.EdgeGraph.Walk.visited`, the split at a visited vertex, and the
closed-subwalk extraction `Maths.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`
- lives in `Maths.EdgeGraph`. -/

/-- Weights of the finite walks arriving at a vertex. -/
def incomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex), walkWeight weight walk = r}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem zero_mem_incomingWeights (weight : E → 𝕜) (vertex : V) :
    (0 : 𝕜) ∈ incomingWeights G weight vertex :=
  ⟨vertex, .nil, rfl⟩

/-- Weights of the finite walks arriving at a vertex that traverse pairwise
distinct edges.  Pruning makes this subfamily cofinal in `incomingWeights`, and
with finitely many edges it is finite, so its maximum is attained without any
completeness assumption on the weights. -/
def nodupIncomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex),
    walk.edges.Nodup ∧ walkWeight weight walk = r}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem nodupIncomingWeights_subset (weight : E → 𝕜) (vertex : V) :
    nodupIncomingWeights G weight vertex ⊆ incomingWeights G weight vertex := by
  rintro r ⟨start, walk, -, rfl⟩
  exact ⟨start, walk, rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem zero_mem_nodupIncomingWeights (weight : E → 𝕜) (vertex : V) :
    (0 : 𝕜) ∈ nodupIncomingWeights G weight vertex :=
  ⟨vertex, .nil, by simp, rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With finitely many edges there are only finitely many weights of walks that
repeat no edge, since such a walk is determined by a duplicate-free list of
edges. -/
theorem finite_nodupIncomingWeights [Finite E] (weight : E → 𝕜) (vertex : V) :
    (nodupIncomingWeights G weight vertex).Finite := by
  cases nonempty_fintype E
  refine Set.Finite.subset
    (((List.finite_length_le E (Fintype.card E)).image fun l => (l.map weight).sum)) ?_
  rintro r ⟨start, walk, hnd, rfl⟩
  exact ⟨walk.edges, hnd.length_le_card, rfl⟩

/-- Pruning: with no closed walk of positive weight, every walk is dominated by
one that visits pairwise distinct vertices. -/
theorem exists_nodup_visited_walkWeight_le {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    ∀ (bound : ℕ) {start finish : V} (walk : G.Walk start finish), walk.length ≤ bound →
      ∃ pruned : G.Walk start finish,
        pruned.visited.Nodup ∧ walkWeight weight walk ≤ walkWeight weight pruned := by
  intro bound
  induction bound with
  | zero =>
      intro start finish walk hlen
      cases walk with
      | nil => exact ⟨.nil, by simp, le_rfl⟩
      | concat walkSoFar edge legal => simp at hlen
  | succ bound ih =>
      intro start finish walk hlen
      by_cases hnd : walk.visited.Nodup
      · exact ⟨walk, hnd, le_rfl⟩
      · obtain ⟨vertex, before, cycle, after, hcyclen, hedges⟩ :=
          walk.exists_closedSubwalk_of_not_nodup hnd
        have hlengths : walk.length = before.length + (cycle.length + after.length) := by
          have hcongr := congrArg List.length hedges
          simpa [EdgeGraph.Walk.edges_length] using hcongr
        have hshort : (before.append after).length ≤ bound := by
          simp only [EdgeGraph.Walk.length_append]
          omega
        have hweights : walkWeight weight walk
            = walkWeight weight before + walkWeight weight cycle
              + walkWeight weight after := by
          simp only [walkWeight, hedges, List.map_append, List.sum_append]
        obtain ⟨pruned, hpruned, hle⟩ := ih (before.append after) hshort
        refine ⟨pruned, hpruned, le_trans ?_ hle⟩
        have := hcyc vertex cycle
        simp only [walkWeight_append]
        linarith

section Finite

variable [Finite E]

/-- The canonical potential: the greatest weight of a walk arriving at a vertex
without repeating an edge.  With no closed walk of positive weight this is also
the greatest weight of *any* walk arriving there (`isGreatest_incomingWeights`),
so it is the value function of the Bellman--Ford longest-walk recursion; in
max-plus notation it is the largest entry of the row of the Kleene star of the
weight matrix indexed by that vertex.  Taking a maximum over a finite family
rather than a supremum is what keeps the duality free of any completeness
assumption on the weights. -/
def maxIncomingWeight (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : 𝕜 :=
  Finset.max' (Set.Finite.toFinset (finite_nodupIncomingWeights (G := G) weight vertex))
    ((Set.Finite.toFinset_nonempty (finite_nodupIncomingWeights (G := G) weight vertex)).2
      ⟨0, zero_mem_nodupIncomingWeights (G := G) weight vertex⟩)

omit [IsStrictOrderedRing 𝕜] in
/-- The canonical potential is itself the weight of a walk arriving at the
vertex without repeating an edge. -/
theorem maxIncomingWeight_mem (weight : E → 𝕜) (vertex : V) :
    maxIncomingWeight G weight vertex ∈ nodupIncomingWeights G weight vertex :=
  (Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).1
    (Finset.max'_mem _ _)

omit [IsStrictOrderedRing 𝕜] in
/-- The canonical potential dominates the weight of every walk arriving at the
vertex without repeating an edge. -/
theorem le_maxIncomingWeight {weight : E → 𝕜} {vertex : V} {r : 𝕜}
    (hr : r ∈ nodupIncomingWeights G weight vertex) :
    r ≤ maxIncomingWeight G weight vertex :=
  Finset.le_max' _ _
    ((Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).2 hr)

/-- Under the no-positive-cycle hypothesis the weights of all walks are bounded
above by one explicit constant. -/
theorem exists_bound_walkWeight (weight : E → 𝕜)
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    ∃ bound : 𝕜, ∀ (start finish : V) (walk : G.Walk start finish),
      walkWeight weight walk ≤ bound := by
  cases nonempty_fintype E
  obtain ⟨cap, hcap⟩ := Finite.exists_le weight
  refine ⟨Fintype.card E * max cap 0, ?_⟩
  intro start finish walk
  obtain ⟨pruned, hnd, hle⟩ :=
    exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
  refine hle.trans ?_
  have hlen : pruned.length ≤ Fintype.card E := by
    have hcard := (pruned.edges_nodup_of_visited_nodup hnd).length_le_card
    rwa [EdgeGraph.Walk.edges_length] at hcard
  have hsum : walkWeight weight pruned ≤ pruned.length * max cap 0 := by
    have hbound (x : 𝕜) (hx : x ∈ pruned.edges.map weight) : x ≤ max cap 0 := by
      rw [List.mem_map] at hx
      obtain ⟨e, _, rfl⟩ := hx
      exact (hcap e).trans (le_max_left _ _)
    have := List.sum_le_card_nsmul (pruned.edges.map weight) (max cap 0) hbound
    simpa [walkWeight, EdgeGraph.Walk.edges_length, nsmul_eq_mul] using this
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (le_max_right _ _))
  exact_mod_cast hlen

theorem bddAbove_incomingWeights {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (vertex : V) : BddAbove (incomingWeights G weight vertex) := by
  obtain ⟨bound, hbound⟩ := exists_bound_walkWeight weight hcyc
  refine ⟨bound, ?_⟩
  rintro r ⟨start, walk, rfl⟩
  exact hbound start vertex walk

/-- Pruning again: with no closed walk of positive weight the canonical
potential dominates the weight of *every* arriving walk, not only of those that
repeat no edge. -/
theorem walkWeight_le_maxIncomingWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {start finish : V} (walk : G.Walk start finish) :
    walkWeight weight walk ≤ maxIncomingWeight G weight finish := by
  obtain ⟨pruned, hnd, hle⟩ := exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
  exact hle.trans (le_maxIncomingWeight ⟨_, pruned, pruned.edges_nodup_of_visited_nodup hnd, rfl⟩)

/-- With no closed walk of positive weight, the canonical potential is the
greatest weight of a walk arriving at the vertex - the maximum over walks that
repeat no edge is attained on the whole family. -/
theorem isGreatest_incomingWeights {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (vertex : V) :
    IsGreatest (incomingWeights G weight vertex) (maxIncomingWeight G weight vertex) :=
  ⟨nodupIncomingWeights_subset weight vertex (maxIncomingWeight_mem weight vertex), by
    rintro r ⟨start, walk, rfl⟩
    exact walkWeight_le_maxIncomingWeight hcyc walk⟩

/-- Over the reals the canonical potential is the supremum of the weights of the
walks arriving at a vertex.  This is the only statement of the file that uses
completeness of `ℝ`, and it is a corollary of `isGreatest_incomingWeights`
rather than a step towards the duality. -/
theorem maxIncomingWeight_eq_sSup {weight : E → ℝ}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (vertex : V) :
    maxIncomingWeight G weight vertex = sSup (incomingWeights G weight vertex) :=
  ((isGreatest_incomingWeights hcyc vertex).csSup_eq).symm

theorem maxIncomingWeight_isPotential {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    IsPotential G weight (maxIncomingWeight G weight) := by
  intro e
  obtain ⟨start, walk, -, hwalk⟩ := maxIncomingWeight_mem weight (G.source e)
  have hle := walkWeight_le_maxIncomingWeight hcyc (walk.concat e rfl)
  rwa [walkWeight_concat, hwalk] at hle

/-- **Tropical Farkas duality.**  Over finitely many edges a potential exists
exactly when no closed walk has strictly positive weight; the vertex type and
the linearly ordered field of weights are arbitrary.  The witness in the forward
direction is `maxIncomingWeight`.  This is the Bellman--Ford criterion, and the
mean-payoff feasibility criterion. -/
theorem exists_isPotential_iff_forall_closedWalk_nonpos (weight : E → 𝕜) :
    (∃ φ : V → 𝕜, IsPotential G weight φ) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0 :=
  ⟨fun ⟨_, hφ⟩ _ cycle => hφ.closedWalk_nonpos cycle,
    fun hcyc => ⟨maxIncomingWeight G weight, maxIncomingWeight_isPotential hcyc⟩⟩

end Finite

/-! ### The quantitative obstruction -/

/-- **Quantitative infeasibility.**  A closed walk of weight at least `γ` forces
every candidate function to fail the increment inequality at one of its edges by
at least `γ` divided by the length of that walk.  No finiteness is needed. -/
theorem exists_edge_defect_ge {weight : E → 𝕜} (φ : V → 𝕜) {vertex : V}
    (cycle : G.Walk vertex vertex) (hlen : 0 < cycle.length) {γ : 𝕜}
    (hγ : γ ≤ walkWeight weight cycle) :
    ∃ e ∈ cycle.edges, γ / cycle.length ≤ defect G weight φ e := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hne : cycle.edges ≠ [] := by
    intro hnil
    rw [← EdgeGraph.Walk.edges_length, hnil] at hlen
    simp at hlen
  have hstrict : (cycle.edges.map (defect G weight φ)).sum
      < (cycle.edges.map (fun _ : E => γ / cycle.length)).sum :=
    List.sum_lt_sum_of_ne_nil hne _ _ hcon
  have hconst : (cycle.edges.map (fun _ : E => γ / cycle.length)).sum
      = cycle.length * (γ / cycle.length) := by
    simp [List.map_const', List.sum_replicate, EdgeGraph.Walk.edges_length,
      nsmul_eq_mul]
  have hpos : (0 : 𝕜) < cycle.length := by exact_mod_cast hlen
  rw [hconst, mul_div_cancel₀ _ hpos.ne'] at hstrict
  rw [sum_defect_eq] at hstrict
  simp only [add_sub_cancel_right] at hstrict
  linarith

/-- A closed walk of strictly positive weight excludes every potential. -/
theorem not_exists_isPotential_of_pos_closedWalk {weight : E → 𝕜} {vertex : V}
    (cycle : G.Walk vertex vertex) (hpos : 0 < walkWeight weight cycle) :
    ¬ ∃ φ : V → 𝕜, IsPotential G weight φ := by
  rintro ⟨φ, hφ⟩
  exact absurd (hφ.closedWalk_nonpos cycle) (not_le.mpr hpos)

/-! ### The max-plus matrix reading -/

section Matrix

universe uι

variable {ι : Type uι}

/-- The complete digraph on a vertex type, one edge for each ordered pair,
oriented so that the edge `(i, j)` carries the coefficient `A i j` of a max-plus
matrix from the coordinate `j` to the coordinate `i`. -/
def matrixGraph (ι : Type uι) : EdgeGraph ι (ι × ι) where
  source := Prod.snd
  target := Prod.fst

@[simp] theorem matrixGraph_source (e : ι × ι) : (matrixGraph ι).source e = e.2 := rfl

@[simp] theorem matrixGraph_target (e : ι × ι) : (matrixGraph ι).target e = e.1 := rfl

/-- The edge weighting of `matrixGraph` induced by a max-plus matrix, that is, by
a matrix of coefficients in the (max, +) semiring. -/
def matrixWeight (A : ι → ι → 𝕜) : ι × ι → 𝕜 := fun e => A e.1 e.2

/-- A subeigenvector of a max-plus matrix for the value `lam`: the max-plus
matrix-vector product `A ⊙ v`, whose `i`-th coordinate is the supremum over `j`
of `A i j + v j`, is dominated coordinatewise by `lam + v`.  Also called a
subinvariant vector, a subharmonic vector, or a super-solution of the max-plus
eigenvalue equation.  The infimum of the values `lam` for which a subeigenvector
exists is called the max cycle mean of `A`, the max-plus Perron root, or the
tropical spectral radius. -/
def IsSubeigenvector (A : ι → ι → 𝕜) (lam : 𝕜) (v : ι → 𝕜) : Prop :=
  ∀ i j : ι, A i j + v j ≤ lam + v i

theorem isSubeigenvector_iff_isPotential (A : ι → ι → 𝕜) (lam : 𝕜) (v : ι → 𝕜) :
    IsSubeigenvector A lam v ↔
      IsPotential (matrixGraph ι) (fun e => matrixWeight A e - lam) v := by
  constructor
  · intro hv e
    have := hv e.1 e.2
    simp only [matrixGraph_source, matrixGraph_target, matrixWeight]
    linarith
  · intro hv i j
    have := hv (i, j)
    simp only [matrixGraph_source, matrixGraph_target, matrixWeight] at this
    linarith

/-- **Max-plus subeigenvector criterion.**  A subeigenvector for `lam` exists
exactly when every closed walk has weight at most `lam` times its length, that
is, when every cycle of the matrix has mean weight at most `lam`.  The set of
admissible values of `lam` is thereby identified, so its infimum is the max cycle
mean of `A`. -/
theorem exists_subeigenvector_iff_forall_closedWalk_le [Finite ι]
    (A : ι → ι → 𝕜) (lam : 𝕜) :
    (∃ v : ι → 𝕜, IsSubeigenvector A lam v) ↔
      ∀ (i : ι) (cycle : (matrixGraph ι).Walk i i),
        walkWeight (matrixWeight A) cycle ≤ cycle.length * lam := by
  have hshift (i : ι) (cycle : (matrixGraph ι).Walk i i) :
      walkWeight (fun e => matrixWeight A e - lam) cycle
        = walkWeight (matrixWeight A) cycle - cycle.length * lam :=
    walkWeight_sub_const (matrixWeight A) lam cycle
  constructor
  · rintro ⟨v, hv⟩ i cycle
    have hpot := (isSubeigenvector_iff_isPotential A lam v).1 hv
    have := hpot.closedWalk_nonpos cycle
    rw [hshift i cycle] at this
    linarith
  · intro hmean
    have : Finite (ι × ι) := inferInstance
    obtain ⟨v, hv⟩ :=
      (exists_isPotential_iff_forall_closedWalk_nonpos
        (G := matrixGraph ι) (fun e => matrixWeight A e - lam)).2
        (by
          intro i cycle
          have := hmean i cycle
          rw [hshift i cycle]
          linarith)
    exact ⟨v, (isSubeigenvector_iff_isPotential A lam v).2 hv⟩

end Matrix

end MaxPlusPotential

end

end Maths
