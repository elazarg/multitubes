/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additive potentials on a weighted directed multigraph

A directed multigraph is represented by `Maths.EdgeGraph`, so parallel
edges keep their identities, and its finite walks are endpoint-indexed typed
walks.  Here every edge additionally carries a weight in an ordered additive
commutative monoid `𝕜`, and the weight of a walk is the sum of its edge weights.

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
spectral theory.  The equality side is `Maths.Multitubes.Additive.Eigenvector`,
and the attained cycle-mean characterization is
`Maths.Multitubes.Additive.CycleMean`.  The critical graph as a subgraph in its
own right, the description of the whole eigenspace, and the Kleene-star
(all-pairs longest-walk) operator, of which `maxIncomingWeight` is one row by
`Maths.AdditiveTransport.isGreatest_range_maxRootedWeight`, are
`Maths.Multitubes.Additive.CriticalGraph`, as are the strongly connected
components of the critical graph and both the sufficiency and the *minimality*
of one Kleene-star column per component, the latter once a vertex of the
component in question reaches the whole graph.

## Main definitions

- `Maths.translationTransport` - additive edge data acting by translation
- `Maths.AdditiveTransport.IsPotential` - the edge increment inequality, a lax section of the
  translation transport
- `Maths.AdditiveTransport.defect` - the amount by which one edge fails it
- `Maths.AdditiveTransport.incomingWeights`,
  `Maths.AdditiveTransport.nodupIncomingWeights` - the weights of the walks
  arriving at a vertex, and of those among them that repeat no edge
- `Maths.AdditiveTransport.maxIncomingWeight` - the canonical potential, the
  greatest weight of a walk arriving at a vertex without repeating an edge
- `Maths.AdditiveTransport.matrixGraph`,
  `Maths.AdditiveTransport.matrixWeight`,
  `Maths.AdditiveTransport.IsSubeigenvector` - the max-plus matrix reading

## Main results

- `Maths.AdditiveTransport.exists_isPotential_iff_forall_closedWalk_nonpos` - the
  duality, for finitely many edges, an arbitrary vertex type and ordered
  additive commutative monoid with cancellation of weights
- `Maths.AdditiveTransport.walkSum_add_le_of_forall_mem_edges` and
  `Maths.AdditiveTransport.IsPotential.walkSum_add_le` - the additive-monoid
  walk propagation inequality, from the edge inequality on one walk's edges
- `Maths.AdditiveTransport.isGreatest_incomingWeights` - with no positive closed
  walk, `maxIncomingWeight` is the greatest weight of a walk arriving at a vertex
- `Maths.AdditiveTransport.isLeast_nonnegativePotentials` - the same envelope is
  the least nonnegative potential
- `Maths.AdditiveTransport.maxIncomingWeight_eq_sSup` - over `ℝ` it is therefore
  the supremum of the weights of all arriving walks
- `Maths.AdditiveTransport.exists_edge_defect_ge` - a closed walk of weight at
  least `γ` forces some edge to fail the inequality by at least `γ` divided by
  the length of that walk, for every candidate function
- `Maths.AdditiveTransport.exists_subeigenvector_iff_forall_closedWalk_le` - for a
  max-plus matrix, a subeigenvector for `lam` exists exactly when every cycle has
  mean weight at most `lam`

## Implementation notes

The increment orientation `φ (source e) + weight e ≤ φ (target e)` is used
throughout.  The opposite decrement orientation
`φ (target e) + weight e ≤ φ (source e)` is the same notion applied to the
reversed graph.  `Maths.Multitubes.Additive.Budget` studies the potentials of
bounded range, whose existence needs no finiteness of the edge type.

The predicates `IsPotential` and `IsSubeigenvector` themselves need only
addition and a comparison relation. Walk propagation uses an ordered additive
commutative monoid `𝕜`, and cancellation is assumed only for the closed-walk
duality.
Multiplication is used only in the cycle *means* of the
quantitative and matrix sections; the duality itself is purely additive.  The
candidate potential is a `Finset.max'` over the weights of the walks arriving
at a vertex without repeating an edge, of which `[Finite E]` leaves only
finitely many.  Over `ℝ` this maximum is the supremum of the weights of *all*
arriving walks (`maxIncomingWeight_eq_sSup`), which is the shape the
conditionally complete lattice literature states; that identification is the
only place where completeness is used, and it is a corollary, not a step.

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

potential, subeigenvector, max-plus, tropical, mean payoff, Bellman-Ford, cycle mean,
difference constraints, shortest path, longest path, reduced cost, Johnson reweighting,
feasible potential
-/

@[expose] public section

namespace Maths

noncomputable section

universe uV uE

/-! ### Translation transport -/

section Translation

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {A : Type*}

/-- The constant-fiber transport whose edge `e` acts by translation by `weight e`. -/
def translationTransport [Add A] (G : EdgeGraph V E) (weight : E → A) :
    Transport G (fun _ : V => A) :=
  ofEdgeAct G A fun edge point => point + weight edge

@[simp] theorem translationTransport_edgeMap [Add A] (weight : E → A) (edge : E) (point : A) :
    (translationTransport G weight).edgeMap edge point = point + weight edge := rfl

/-- Transport by additive edge data is translation by the walk sum. -/
@[simp] theorem walkMap_translationTransport [AddMonoid A] (weight : E → A) {start finish : V}
    (walk : G.Walk start finish) (point : A) :
    (translationTransport G weight).walkMap walk point = point + walkSum weight walk := by
  induction walk with
  | nil => simp
  | concat edge walkSoFar ih =>
      rw [Transport.walkMap_concat, ih, walkSum_concat,
        translationTransport_edgeMap, add_assoc]

/-- Every edge map of an ordered translation transport is monotone. -/
theorem monotone_edgeMap_translationTransport [Add A] [Preorder A] [AddRightMono A]
    (weight : E → A) (edge : E) : Monotone ((translationTransport G weight).edgeMap edge) :=
  fun _ _ hle => add_le_add_left hle (weight edge)

end Translation

namespace AdditiveTransport

variable {𝕜 : Type*} [AddCommMonoid 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

section Potential

variable {𝕜p : Type*} [Add 𝕜p] [LE 𝕜p]

/-- A potential for an edge weighting: traversing an edge increases it by at
least the weight of that edge, `φ (source e) + weight e ≤ φ (target e)`.  It is a lax
section of the translation transport.  Also called a feasible node potential, a feasible
price vector, a subinvariant function, or a Lyapunov weighting; in the (max, +)
semiring it is a subeigenvector of the weight matrix.  The opposite decrement
convention is the same notion on the reversed graph. -/
def IsPotential (G : EdgeGraph V E) (weight : E → 𝕜p) (φ : V → 𝕜p) : Prop :=
  (translationTransport G weight).IsLaxSection φ

/-- The edge inequality of a potential. -/
theorem isPotential_iff {weight : E → 𝕜p} {φ : V → 𝕜p} :
    IsPotential G weight φ ↔ ∀ e : E, φ (G.source e) + weight e ≤ φ (G.target e) :=
  Iff.rfl

/-- The edge inequality of a potential at one edge. -/
theorem IsPotential.le {weight : E → 𝕜p} {φ : V → 𝕜p} (hφ : IsPotential G weight φ) (e : E) :
    φ (G.source e) + weight e ≤ φ (G.target e) :=
  hφ e

end Potential

/-! ### Potentials and their edge defects -/

section AddGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g] [Preorder 𝕜g] [IsOrderedAddMonoid 𝕜g]

/-- The amount by which a candidate function fails the increment inequality at
one edge.  Also called the reduced weight of the edge; it is the negative of the
slack of the edge inequality.  A potential is exactly a function whose defects are all
nonpositive. -/
def defect (G : EdgeGraph V E) (weight : E → 𝕜g) (φ : V → 𝕜g) (e : E) : 𝕜g :=
  φ (G.source e) + weight e - φ (G.target e)

theorem isPotential_iff_forall_defect_nonpos (G : EdgeGraph V E) (weight : E → 𝕜g)
    (φ : V → 𝕜g) : IsPotential G weight φ ↔ ∀ e : E, defect G weight φ e ≤ 0 := by
  simp [isPotential_iff, defect]

omit [Preorder 𝕜g] [IsOrderedAddMonoid 𝕜g] in
/-- Telescoping along a walk: the defects of the traversed edges sum to the
weight of the walk corrected by the endpoint values. -/
theorem sum_defect_eq (weight : E → 𝕜g) (φ : V → 𝕜g) {start finish : V}
    (walk : G.Walk start finish) :
    (walk.edges.map (defect G weight φ)).sum
      = walkSum weight walk + φ start - φ finish := by
  induction walk with
  | nil => simp
  | concat edge walkSoFar ih =>
      simp only [EdgeGraph.Walk.edges_concat, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih, defect,
        walkSum_concat]
      abel

end AddGroup

section OrderedMonoid

variable {𝕜o : Type*} [AddCommMonoid 𝕜o] [Preorder 𝕜o] [IsOrderedAddMonoid 𝕜o]

/-- A vertex function satisfying the edge inequality of a potential on the edges of one walk
bounds that walk after adding the value at its starting vertex: walk propagation of the lax
section along the translation transport, needed only on the edges the walk traverses. -/
theorem walkSum_add_le_of_forall_mem_edges {weight : E → 𝕜o} {φ : V → 𝕜o} {start finish : V}
    (walk : G.Walk start finish)
    (hedge : ∀ e ∈ walk.edges, φ (G.source e) + weight e ≤ φ (G.target e)) :
    walkSum weight walk + φ start ≤ φ finish := by
  have h := (translationTransport G weight).walkMap_rel_of_forall_mem_edges (family := φ)
    (R := fun _ => (· ≤ ·)) (fun _ => le_rfl) (fun _ => le_trans) walk
    (fun edge _ _ _ hxy => monotone_edgeMap_translationTransport weight edge hxy) hedge
  rwa [walkMap_translationTransport, add_comm] at h

/-- A potential bounds a walk after adding the value at its starting vertex: walk propagation
of the lax section along the translation transport. -/
theorem IsPotential.walkSum_add_le {weight : E → 𝕜o} {φ : V → 𝕜o}
    (hφ : IsPotential G weight φ) {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk + φ start ≤ φ finish :=
  walkSum_add_le_of_forall_mem_edges walk fun e _ => hφ e

/-- A potential dominates the weight of every walk between its endpoints. -/
theorem IsPotential.walkSum_le {𝕜g : Type*} [AddCommGroup 𝕜g] [Preorder 𝕜g]
    [IsOrderedAddMonoid 𝕜g] {weight : E → 𝕜g} {φ : V → 𝕜g}
    (hφ : IsPotential G weight φ) {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk ≤ φ finish - φ start :=
  le_sub_iff_add_le.2 (hφ.walkSum_add_le walk)

section CancelOrder

variable [IsOrderedCancelAddMonoid 𝕜o]

omit [IsOrderedAddMonoid 𝕜o] in
/-- Weak duality: a potential forbids closed walks of positive weight. -/
theorem IsPotential.closedWalk_nonpos {weight : E → 𝕜o} {φ : V → 𝕜o}
    (hφ : IsPotential G weight φ) {vertex : V} (cycle : G.Walk vertex vertex) :
    walkSum weight cycle ≤ 0 := by
  have h := hφ.walkSum_add_le cycle
  have h' : walkSum weight cycle + φ vertex ≤ 0 + φ vertex := by simpa using h
  exact le_of_add_le_add_right h'

end CancelOrder

end OrderedMonoid

/-! ### The duality

The finite-walk calculus this rests on - the visited-vertex list
`Maths.EdgeGraph.Walk.visited`, the split at a visited vertex, and the
closed-subwalk extraction `Maths.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`
- lives in `Maths.EdgeGraph`. -/

/-- Weights of the finite walks arriving at a vertex. -/
def incomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex), walkSum weight walk = r}

omit [LinearOrder 𝕜] in
theorem zero_mem_incomingWeights (weight : E → 𝕜) (vertex : V) :
    (0 : 𝕜) ∈ incomingWeights G weight vertex :=
  ⟨vertex, .nil, rfl⟩

/-- Weights of the finite walks arriving at a vertex that traverse pairwise
distinct edges.  Pruning makes this subfamily cofinal in `incomingWeights`, and
with finitely many edges it is finite, so its maximum is attained without any
completeness assumption on the weights. -/
def nodupIncomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex),
    walk.edges.Nodup ∧ walkSum weight walk = r}

omit [LinearOrder 𝕜] in
theorem nodupIncomingWeights_subset (weight : E → 𝕜) (vertex : V) :
    nodupIncomingWeights G weight vertex ⊆ incomingWeights G weight vertex := by
  rintro r ⟨start, walk, -, rfl⟩
  exact ⟨start, walk, rfl⟩

omit [LinearOrder 𝕜] in
theorem zero_mem_nodupIncomingWeights (weight : E → 𝕜) (vertex : V) :
    (0 : 𝕜) ∈ nodupIncomingWeights G weight vertex :=
  ⟨vertex, .nil, by simp, rfl⟩

omit [LinearOrder 𝕜] in
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
theorem exists_nodup_visited_walkSum_le {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0) :
    ∀ (bound : ℕ) {start finish : V} (walk : G.Walk start finish), walk.length ≤ bound →
      ∃ pruned : G.Walk start finish,
        pruned.visited.Nodup ∧ walkSum weight walk ≤ walkSum weight pruned := by
  intro bound
  induction bound with
  | zero =>
      intro start finish walk hlen
      cases walk with
      | nil => exact ⟨.nil, by simp, le_rfl⟩
      | concat edge walkSoFar => simp at hlen
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
        have hweights : walkSum weight walk
            = walkSum weight before + walkSum weight cycle
              + walkSum weight after := by
          simp only [walkSum, hedges, List.map_append, List.sum_append]
        obtain ⟨pruned, hpruned, hle⟩ := ih (before.append after) hshort
        refine ⟨pruned, hpruned, le_trans ?_ hle⟩
        have := hcyc vertex cycle
        calc
          walkSum weight walk = walkSum weight before + walkSum weight cycle
              + walkSum weight after := hweights
          _ ≤ walkSum weight before + walkSum weight after := by
            have h := add_le_add_right (add_le_add_right this (walkSum weight before))
                (walkSum weight after)
            simpa [add_assoc, add_comm, add_left_comm] using h
          _ ≤ walkSum weight (before.append after) := by
            rw [walkSum_append]

section Finite

variable [Finite E]

/-- The canonical potential: the greatest weight of a walk arriving at a vertex
without repeating an edge.  With no closed walk of positive weight this is also
the greatest weight of *any* walk arriving there (`isGreatest_incomingWeights`),
so it is the value function of the Bellman--Ford longest-walk recursion; in
max-plus notation it is the largest entry of the row of the Kleene star of the
weight matrix indexed by that vertex.  Taking a maximum over a finite family, not a
supremum, is what keeps the duality free of any completeness assumption on the weights. -/
def maxIncomingWeight (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : 𝕜 :=
  Finset.max' (Set.Finite.toFinset (finite_nodupIncomingWeights (G := G) weight vertex))
    ((Set.Finite.toFinset_nonempty (finite_nodupIncomingWeights (G := G) weight vertex)).2
      ⟨0, zero_mem_nodupIncomingWeights (G := G) weight vertex⟩)

omit [IsOrderedAddMonoid 𝕜] in
/-- The canonical potential is itself the weight of a walk arriving at the
vertex without repeating an edge. -/
theorem maxIncomingWeight_mem (weight : E → 𝕜) (vertex : V) :
    maxIncomingWeight G weight vertex ∈ nodupIncomingWeights G weight vertex :=
  (Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).1
    (Finset.max'_mem _ _)

omit [IsOrderedAddMonoid 𝕜] in
/-- The canonical potential dominates the weight of every walk arriving at the
vertex without repeating an edge. -/
theorem le_maxIncomingWeight {weight : E → 𝕜} {vertex : V} {r : 𝕜}
    (hr : r ∈ nodupIncomingWeights G weight vertex) :
    r ≤ maxIncomingWeight G weight vertex :=
  Finset.le_max' _ _
    ((Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).2 hr)

/-- Under the no-positive-cycle hypothesis the weights of all walks are bounded
above by one explicit constant. -/
theorem exists_bound_walkSum (weight : E → 𝕜)
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0) :
    ∃ bound : 𝕜, ∀ (start finish : V) (walk : G.Walk start finish),
      walkSum weight walk ≤ bound := by
  cases nonempty_fintype E
  obtain ⟨cap, hcap⟩ := Finite.exists_le weight
  refine ⟨Fintype.card E • max cap 0, ?_⟩
  intro start finish walk
  obtain ⟨pruned, hnd, hle⟩ :=
    exists_nodup_visited_walkSum_le hcyc walk.length walk le_rfl
  refine hle.trans ?_
  have hlen : pruned.length ≤ Fintype.card E := by
    have hcard := (pruned.edges_nodup_of_visited_nodup hnd).length_le_card
    rwa [EdgeGraph.Walk.edges_length] at hcard
  have hsum : walkSum weight pruned ≤ pruned.length • max cap 0 := by
    have hbound (x : 𝕜) (hx : x ∈ pruned.edges.map weight) : x ≤ max cap 0 := by
      rw [List.mem_map] at hx
      obtain ⟨e, _, rfl⟩ := hx
      exact (hcap e).trans (le_max_left _ _)
    have := List.sum_le_length_nsmul (pruned.edges.map weight) (max cap 0) hbound
    simpa [walkSum, EdgeGraph.Walk.edges_length] using this
  refine hsum.trans (nsmul_le_nsmul_left (le_max_right _ _) hlen)

theorem bddAbove_incomingWeights {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0)
    (vertex : V) : BddAbove (incomingWeights G weight vertex) := by
  obtain ⟨bound, hbound⟩ := exists_bound_walkSum weight hcyc
  refine ⟨bound, ?_⟩
  rintro r ⟨start, walk, rfl⟩
  exact hbound start vertex walk

/-- Pruning again: with no closed walk of positive weight the canonical
potential dominates the weight of *every* arriving walk, not only of those that
repeat no edge. -/
theorem walkSum_le_maxIncomingWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0)
    {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk ≤ maxIncomingWeight G weight finish := by
  obtain ⟨pruned, hnd, hle⟩ := exists_nodup_visited_walkSum_le hcyc walk.length walk le_rfl
  exact hle.trans (le_maxIncomingWeight ⟨_, pruned, pruned.edges_nodup_of_visited_nodup hnd, rfl⟩)

/-- With no closed walk of positive weight, the canonical potential is the
greatest weight of a walk arriving at the vertex - the maximum over walks that
repeat no edge is attained on the whole family. -/
theorem isGreatest_incomingWeights {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0)
    (vertex : V) :
    IsGreatest (incomingWeights G weight vertex) (maxIncomingWeight G weight vertex) :=
  ⟨nodupIncomingWeights_subset weight vertex (maxIncomingWeight_mem weight vertex), by
    rintro r ⟨start, walk, rfl⟩
    exact walkSum_le_maxIncomingWeight hcyc walk⟩

/-- Over the reals the canonical potential is the supremum of the weights of the
walks arriving at a vertex.  This is the only statement of the file that uses
completeness of `ℝ`, and it is a corollary of `isGreatest_incomingWeights`,
not a step towards the duality. -/
theorem maxIncomingWeight_eq_sSup {weight : E → ℝ}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0)
    (vertex : V) :
    maxIncomingWeight G weight vertex = sSup (incomingWeights G weight vertex) :=
  ((isGreatest_incomingWeights hcyc vertex).csSup_eq).symm

theorem maxIncomingWeight_isPotential {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0) :
    IsPotential G weight (maxIncomingWeight G weight) := by
  intro e
  obtain ⟨start, walk, -, hwalk⟩ := maxIncomingWeight_mem weight (G.source e)
  have hle := walkSum_le_maxIncomingWeight hcyc (walk.concat e)
  rwa [walkSum_concat, hwalk] at hle

/-- The incoming path closure is the least nonnegative potential.  Thus its
maximum-over-paths description and its minimum-over-feasible-potentials
description are two sides of the same normalization. -/
theorem isLeast_nonnegativePotentials {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0) :
    IsLeast {potential : V → 𝕜 | (0 : V → 𝕜) ≤ potential ∧ IsPotential G weight potential}
      (maxIncomingWeight G weight) := by
  constructor
  · exact ⟨fun vertex ↦ le_maxIncomingWeight
      (zero_mem_nodupIncomingWeights weight vertex),
      maxIncomingWeight_isPotential hcyc⟩
  · rintro potential ⟨hnonnegative, hpotential⟩ vertex
    obtain ⟨start, walk, -, hwalk⟩ := maxIncomingWeight_mem weight vertex
    rw [← hwalk]
    calc
      walkSum weight walk = walkSum weight walk + 0 := (add_zero _).symm
      _ ≤ walkSum weight walk + potential start :=
        by
          simpa [add_comm] using
            add_le_add_left (hnonnegative start) (walkSum weight walk)
      _ ≤ potential vertex := hpotential.walkSum_add_le walk

section CancelOrder

variable [IsOrderedCancelAddMonoid 𝕜]

omit [IsOrderedAddMonoid 𝕜] in
/-- **Tropical Farkas duality.**  Over finitely many edges a potential exists
exactly when no closed walk has strictly positive weight; the vertex type and
the ordered cancellative additive commutative monoid of weights are arbitrary.
The witness in the forward direction is `maxIncomingWeight`.  This is the
Bellman--Ford criterion and the mean-payoff feasibility criterion. -/
theorem exists_isPotential_iff_forall_closedWalk_nonpos (weight : E → 𝕜) :
    (∃ φ : V → 𝕜, IsPotential G weight φ) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkSum weight cycle ≤ 0 :=
  ⟨fun ⟨_, hφ⟩ _ cycle => hφ.closedWalk_nonpos cycle,
    fun hcyc => ⟨maxIncomingWeight G weight, maxIncomingWeight_isPotential hcyc⟩⟩

end CancelOrder

end Finite

/-! ### The quantitative obstruction -/

section Quantitative

variable {𝕜q : Type*} [Field 𝕜q] [LinearOrder 𝕜q] [IsStrictOrderedRing 𝕜q]

/-- **Quantitative infeasibility.**  A closed walk of weight at least `γ` forces
every candidate function to fail the increment inequality at one of its edges by
at least `γ` divided by the length of that walk.  No finiteness is needed. -/
theorem exists_edge_defect_ge {weight : E → 𝕜q} (φ : V → 𝕜q) {vertex : V}
    (cycle : G.Walk vertex vertex) (hlen : 0 < cycle.length) {γ : 𝕜q}
    (hγ : γ ≤ walkSum weight cycle) :
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
  have hpos : (0 : 𝕜q) < cycle.length := by exact_mod_cast hlen
  rw [hconst, mul_div_cancel₀ _ hpos.ne'] at hstrict
  rw [sum_defect_eq] at hstrict
  simp only [add_sub_cancel_right] at hstrict
  linarith

end Quantitative

section CancelPreorder

variable {𝕜c : Type*} [AddCommMonoid 𝕜c] [Preorder 𝕜c]
variable [IsOrderedCancelAddMonoid 𝕜c]

/-- A closed walk of strictly positive weight excludes every potential. -/
theorem not_exists_isPotential_of_pos_closedWalk {weight : E → 𝕜c} {vertex : V}
    (cycle : G.Walk vertex vertex) (hpos : 0 < walkSum weight cycle) :
    ¬ ∃ φ : V → 𝕜c, IsPotential G weight φ := by
  rintro ⟨φ, hφ⟩
  exact (not_le_of_gt hpos) (hφ.closedWalk_nonpos cycle)

end CancelPreorder

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

section MatrixGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g] [LinearOrder 𝕜g] [IsOrderedAddMonoid 𝕜g]

/-- The edge weighting of `matrixGraph` induced by a max-plus matrix, that is, by
a matrix of coefficients in the (max, +) semiring. -/
def matrixWeight (A : ι → ι → 𝕜g) : ι × ι → 𝕜g := fun e => A e.1 e.2

end MatrixGroup

section Subeigenvector

variable {𝕜m : Type*} [Add 𝕜m] [LE 𝕜m]

/-- A subeigenvector of a max-plus matrix for the value `lam`: the max-plus
matrix-vector product `A ⊙ v`, whose `i`-th coordinate is the supremum over `j`
of `A i j + v j`, is dominated coordinatewise by `lam + v`.  Also called a
subinvariant or superharmonic vector.  The infimum of the values `lam` for which a subeigenvector
exists is called the max cycle mean of `A`, the max-plus Perron root, or the
tropical spectral radius. -/
def IsSubeigenvector (A : ι → ι → 𝕜m) (lam : 𝕜m) (v : ι → 𝕜m) : Prop :=
  ∀ i j : ι, A i j + v j ≤ lam + v i

end Subeigenvector

section MatrixGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g] [LinearOrder 𝕜g] [IsOrderedAddMonoid 𝕜g]

theorem isSubeigenvector_iff_isPotential (A : ι → ι → 𝕜g) (lam : 𝕜g) (v : ι → 𝕜g) :
    IsSubeigenvector A lam v ↔
      IsPotential (matrixGraph ι) (fun e => matrixWeight A e - lam) v := by
  constructor
  · intro hv e
    have := hv e.1 e.2
    simp only [translationTransport_edgeMap, matrixGraph_source, matrixGraph_target,
      matrixWeight]
    rw [show v e.2 + (A e.1 e.2 - lam) =
      (A e.1 e.2 + v e.2) - lam by abel]
    apply (sub_le_iff_le_add).2
    simpa [add_assoc, add_comm, add_left_comm] using this
  · intro hv i j
    have := hv.le (i, j)
    simp only [matrixGraph_source, matrixGraph_target, matrixWeight] at this
    have h' : (A i j + v j) - lam ≤ v i := by
      calc
        (A i j + v j) - lam = v j + (A i j - lam) := by abel
        _ ≤ v i := this
    have h := (sub_le_iff_le_add.mp h')
    simpa [add_assoc, add_comm, add_left_comm] using h

end MatrixGroup

section MatrixQuantitative

variable {𝕜q : Type*} [Field 𝕜q] [LinearOrder 𝕜q] [IsStrictOrderedRing 𝕜q]

/-- **Max-plus subeigenvector criterion.**  A subeigenvector for `lam` exists
exactly when every closed walk has weight at most `lam` times its length, that
is, when every cycle of the matrix has mean weight at most `lam`.  The set of
admissible values of `lam` is thereby identified, so its infimum is the max cycle
mean of `A`. -/
theorem exists_subeigenvector_iff_forall_closedWalk_le [Finite ι]
    (A : ι → ι → 𝕜q) (lam : 𝕜q) :
    (∃ v : ι → 𝕜q, IsSubeigenvector A lam v) ↔
      ∀ (i : ι) (cycle : (matrixGraph ι).Walk i i),
        walkSum (matrixWeight A) cycle ≤ cycle.length * lam := by
  have hshift (i : ι) (cycle : (matrixGraph ι).Walk i i) :
    walkSum (fun e => matrixWeight A e - lam) cycle
      = walkSum (matrixWeight A) cycle - cycle.length * lam :=
    by simpa [nsmul_eq_mul] using walkSum_sub_const (matrixWeight A) lam cycle
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

end MatrixQuantitative

end Matrix

end AdditiveTransport

end

end Maths
