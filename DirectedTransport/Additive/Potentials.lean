/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.EdgeGraph
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additive potentials on a real-weighted digraph

A directed multigraph is represented by `DirectedTransport.EdgeGraph`, so parallel
edges keep their identities, and its finite walks are endpoint-indexed typed
walks.  Here every edge additionally carries a real weight, and the weight of a
walk is the sum of the weights of its edges.

A **potential** is a real function on vertices satisfying the edge increment
inequality `φ (source e) + weight e ≤ φ (target e)`.  The central result is the
duality between potentials and closed walks: with finitely many edges, a
potential exists exactly when no closed walk has strictly positive weight.  The
vertex type is arbitrary — a walk visiting pairwise distinct vertices traverses
pairwise distinct edges, so the edge count already bounds every pruned walk.
The quantitative form of the duality measures, for an arbitrary candidate
function, how badly some edge of a positive closed walk must fail the
inequality.

A potential is also called a feasible node potential, a feasible price vector, a
subinvariant or superharmonic function, or a Lyapunov weighting; in the (max, +)
semiring the same object is a subeigenvector, and the duality below is variously
the Bellman--Ford criterion, mean-payoff feasibility, tropical linear-programming
duality, and Farkas' lemma in the (max, +) semiring.  The supremum of the cycle
means is the max cycle mean, the tropical spectral radius, or the max-plus Perron
root.

## Main definitions

- `DirectedTransport.MaxPlusPotential.walkWeight` — total real weight of a finite typed walk
- `DirectedTransport.MaxPlusPotential.IsPotential` — the edge increment inequality
- `DirectedTransport.MaxPlusPotential.defect` — the amount by which one edge fails it
- `DirectedTransport.MaxPlusPotential.maxIncomingWeight` — the canonical potential, the
  supremum of the weights of the walks arriving at a vertex
- `DirectedTransport.MaxPlusPotential.matrixGraph`,
  `DirectedTransport.MaxPlusPotential.matrixWeight`,
  `DirectedTransport.MaxPlusPotential.IsSubeigenvector` — the max-plus matrix reading

## Main results

- `DirectedTransport.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` — the
  duality, for finitely many edges and an arbitrary vertex type
- `DirectedTransport.MaxPlusPotential.exists_edge_defect_ge` — a closed walk of weight at
  least `γ` forces some edge to fail the inequality by at least `γ` divided by
  the length of that walk, for every candidate function
- `DirectedTransport.MaxPlusPotential.exists_subeigenvector_iff_forall_closedWalk_le` — for a
  max-plus matrix, a subeigenvector for `lam` exists exactly when every cycle has
  mean weight at most `lam`

## Implementation notes

The increment orientation `φ (source e) + weight e ≤ φ (target e)` is used
throughout.  The opposite decrement orientation
`φ (target e) + weight e ≤ φ (source e)` is the same notion applied to the
reversed graph, and is the convention of `DirectedTransport.ChargedPathBudget`, which studies
nonnegative charges and the *oscillation* of a bounded potential rather than
signed weights and cycles.

## TODO

This file develops the potential (subeigenvector) side of max-plus spectral
theory only.  Not developed here: existence of genuine eigenvectors, the
Collatz--Wielandt characterization of the max cycle mean as an attained
maximum over cycles, the critical graph, and the Kleene-star (all-pairs
longest-walk) operator, of which `maxIncomingWeight` is one row.  The natural
common setting for those is the fixed-point theory of topical maps.

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

namespace DirectedTransport

noncomputable section

namespace MaxPlusPotential

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Weights of walks -/

/-- Total real weight of a finite typed walk: the sum of the weights of its
edges, counted with multiplicity in chronological order. -/
def walkWeight (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) : ℝ :=
  (walk.edges.map weight).sum

@[simp] theorem walkWeight_nil (weight : E → ℝ) (start : V) :
    walkWeight weight (EdgeGraph.Walk.nil : G.Walk start start) = 0 := rfl

@[simp] theorem walkWeight_concat (weight : E → ℝ) {start finish : V}
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    walkWeight weight (walk.concat edge legal) = walkWeight weight walk + weight edge := by
  simp [walkWeight]

@[simp] theorem walkWeight_append (weight : E → ℝ) {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    walkWeight weight (first.append second)
      = walkWeight weight first + walkWeight weight second := by
  simp [walkWeight]

@[simp] theorem walkWeight_castFinish (weight : E → ℝ) {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    walkWeight weight (walk.castFinish hfinish) = walkWeight weight walk := by
  simp [walkWeight]

/-- Shifting every edge weight by a constant shifts the weight of a walk by that
constant times the length of the walk. -/
theorem walkWeight_sub_const (weight : E → ℝ) (lam : ℝ) {start finish : V}
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

/-- A potential for a real edge weighting: traversing an edge increases it by at
least the weight of that edge.  Also called a feasible node potential, a feasible
price vector, a subinvariant function, or a Lyapunov weighting; in the (max, +)
semiring it is a subeigenvector of the weight matrix.  The opposite decrement
convention is the same notion on the reversed graph. -/
def IsPotential (G : EdgeGraph V E) (weight : E → ℝ) (φ : V → ℝ) : Prop :=
  ∀ e : E, φ (G.source e) + weight e ≤ φ (G.target e)

/-- The amount by which a candidate function fails the increment inequality at
one edge.  Also called the edge slack, the reduced weight, or the residual of the
edge; a potential is exactly a function whose defects are all nonpositive. -/
def defect (G : EdgeGraph V E) (weight : E → ℝ) (φ : V → ℝ) (e : E) : ℝ :=
  φ (G.source e) + weight e - φ (G.target e)

theorem isPotential_iff_forall_defect_nonpos (G : EdgeGraph V E) (weight : E → ℝ)
    (φ : V → ℝ) : IsPotential G weight φ ↔ ∀ e : E, defect G weight φ e ≤ 0 := by
  simp [IsPotential, defect]

/-- Telescoping along a walk: the defects of the traversed edges sum to the
weight of the walk corrected by the endpoint values. -/
theorem sum_defect_eq (weight : E → ℝ) (φ : V → ℝ) {start finish : V}
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
theorem IsPotential.walkWeight_le {weight : E → ℝ} {φ : V → ℝ}
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
theorem IsPotential.closedWalk_nonpos {weight : E → ℝ} {φ : V → ℝ}
    (hφ : IsPotential G weight φ) {vertex : V} (cycle : G.Walk vertex vertex) :
    walkWeight weight cycle ≤ 0 := by
  simpa using hφ.walkWeight_le cycle

/-! ### The duality

The finite-walk calculus this rests on — the visited-vertex list
`DirectedTransport.EdgeGraph.Walk.visited`, the split at a visited vertex, and the
closed-subwalk extraction `DirectedTransport.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`
— lives in `DirectedTransport.EdgeGraph`. -/

/-- Weights of the finite walks arriving at a vertex. -/
def incomingWeights (G : EdgeGraph V E) (weight : E → ℝ) (vertex : V) : Set ℝ :=
  {r | ∃ (start : V) (walk : G.Walk start vertex), walkWeight weight walk = r}

theorem zero_mem_incomingWeights (weight : E → ℝ) (vertex : V) :
    (0 : ℝ) ∈ incomingWeights G weight vertex :=
  ⟨vertex, .nil, by simp⟩

/-- The canonical potential: the largest weight of a walk arriving at a vertex.
This is the value function of the Bellman--Ford longest-walk recursion; in
max-plus notation it is the largest entry of the row of the Kleene star of the
weight matrix indexed by that vertex. -/
def maxIncomingWeight (G : EdgeGraph V E) (weight : E → ℝ) (vertex : V) : ℝ :=
  sSup (incomingWeights G weight vertex)

/-- Pruning: with no closed walk of positive weight, every walk is dominated by
one that visits pairwise distinct vertices. -/
theorem exists_nodup_visited_walkWeight_le {weight : E → ℝ}
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

/-- Under the no-positive-cycle hypothesis the weights of all walks are bounded
above by one explicit constant. -/
theorem exists_bound_walkWeight (weight : E → ℝ)
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    ∃ bound : ℝ, ∀ (start finish : V) (walk : G.Walk start finish),
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
    have hbound (x : ℝ) (hx : x ∈ pruned.edges.map weight) : x ≤ max cap 0 := by
      rw [List.mem_map] at hx
      obtain ⟨e, _, rfl⟩ := hx
      exact (hcap e).trans (le_max_left _ _)
    have := List.sum_le_card_nsmul (pruned.edges.map weight) (max cap 0) hbound
    simpa [walkWeight, EdgeGraph.Walk.edges_length, nsmul_eq_mul] using this
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (le_max_right _ _))
  exact_mod_cast hlen

theorem bddAbove_incomingWeights {weight : E → ℝ}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (vertex : V) : BddAbove (incomingWeights G weight vertex) := by
  obtain ⟨bound, hbound⟩ := exists_bound_walkWeight weight hcyc
  refine ⟨bound, ?_⟩
  rintro r ⟨start, walk, rfl⟩
  exact hbound start vertex walk

theorem maxIncomingWeight_isPotential {weight : E → ℝ}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    IsPotential G weight (maxIncomingWeight G weight) := by
  intro e
  have hbdd := bddAbove_incomingWeights hcyc (G.target e)
  have hstep : ∀ r ∈ incomingWeights G weight (G.source e),
      r ≤ sSup (incomingWeights G weight (G.target e)) - weight e := by
    rintro r ⟨start, walk, rfl⟩
    have hmem : walkWeight weight (walk.concat e rfl)
        ∈ incomingWeights G weight (G.target e) := ⟨start, _, rfl⟩
    have hle := le_csSup hbdd hmem
    rw [walkWeight_concat] at hle
    linarith
  have hsup := csSup_le ⟨0, zero_mem_incomingWeights weight (G.source e)⟩ hstep
  simp only [maxIncomingWeight]
  linarith

/-- **Tropical Farkas duality.**  Over finitely many edges a potential exists
exactly when no closed walk has strictly positive weight; the vertex type is
arbitrary.  The witness in the forward direction is `maxIncomingWeight`.  This
is the Bellman--Ford criterion, and the mean-payoff feasibility criterion. -/
theorem exists_isPotential_iff_forall_closedWalk_nonpos (weight : E → ℝ) :
    (∃ φ : V → ℝ, IsPotential G weight φ) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0 :=
  ⟨fun ⟨_, hφ⟩ _ cycle => hφ.closedWalk_nonpos cycle,
    fun hcyc => ⟨maxIncomingWeight G weight, maxIncomingWeight_isPotential hcyc⟩⟩

end Finite

/-! ### The quantitative obstruction -/

/-- **Quantitative infeasibility.**  A closed walk of weight at least `γ` forces
every candidate function to fail the increment inequality at one of its edges by
at least `γ` divided by the length of that walk.  No finiteness is needed. -/
theorem exists_edge_defect_ge {weight : E → ℝ} (φ : V → ℝ) {vertex : V}
    (cycle : G.Walk vertex vertex) (hlen : 0 < cycle.length) {γ : ℝ}
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
  have hpos : (0 : ℝ) < cycle.length := by exact_mod_cast hlen
  rw [hconst, mul_div_cancel₀ _ hpos.ne'] at hstrict
  rw [sum_defect_eq] at hstrict
  simp only [add_sub_cancel_right] at hstrict
  linarith

/-- A closed walk of strictly positive weight excludes every potential. -/
theorem not_exists_isPotential_of_pos_closedWalk {weight : E → ℝ} {vertex : V}
    (cycle : G.Walk vertex vertex) (hpos : 0 < walkWeight weight cycle) :
    ¬ ∃ φ : V → ℝ, IsPotential G weight φ := by
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
def matrixWeight (A : ι → ι → ℝ) : ι × ι → ℝ := fun e => A e.1 e.2

/-- A subeigenvector of a max-plus matrix for the value `lam`: the max-plus
matrix-vector product `A ⊙ v`, whose `i`-th coordinate is the supremum over `j`
of `A i j + v j`, is dominated coordinatewise by `lam + v`.  Also called a
subinvariant vector, a subharmonic vector, or a super-solution of the max-plus
eigenvalue equation.  The infimum of the values `lam` for which a subeigenvector
exists is called the max cycle mean of `A`, the max-plus Perron root, or the
tropical spectral radius. -/
def IsSubeigenvector (A : ι → ι → ℝ) (lam : ℝ) (v : ι → ℝ) : Prop :=
  ∀ i j : ι, A i j + v j ≤ lam + v i

theorem isSubeigenvector_iff_isPotential (A : ι → ι → ℝ) (lam : ℝ) (v : ι → ℝ) :
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
    (A : ι → ι → ℝ) (lam : ℝ) :
    (∃ v : ι → ℝ, IsSubeigenvector A lam v) ↔
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

end DirectedTransport
