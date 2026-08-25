/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Potentials
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finset.Lattice.Fold

import Maths.DirectedTransport.Additive.ShortCycles
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Linarith

/-!
# Max-plus eigenvectors

`Maths.DirectedTransport.Additive.Potentials` produces *sub*eigenvectors: functions with
`A i j + v j ≤ lam + v i` for all `i` and `j`, which exist exactly when every cycle has mean
weight at most `lam`.  This file upgrades the inequality to the max-plus eigenvalue equation

`∀ i, max_j (A i j + v j) = lam + v i`,

at the one value of `lam` where that is possible, namely the maximum cycle mean.

The construction is the classical one.  Fix a **critical** vertex, that is a vertex carrying a
closed walk of mean weight exactly `lam`, and let `v` be the greatest weight of a walk from that
vertex, measured in the shifted weighting `weight - lam`.  This is the column of the Kleene star
of `A - lam` rooted at the critical vertex.  The subeigenvector inequality is the potential
property of that maximum, already available from the pruning argument of the potential file.  The
new content is **tightness**: at every vertex some incoming edge achieves equality.  A greatest
walk arriving at a vertex has, if it is nonempty, a last edge whose prefix must already be a
greatest walk to that edge's source, so that last edge is tight; and a nonempty greatest walk is
available at every vertex, at the root because the critical cycle is one.

Consequently the equality holds at *every* coordinate, not only on the critical graph - the
critical vertex enters as the root of the construction, not as a restriction on where the
eigenvector equation holds.

## Main definitions

* `Maths.MaxPlusPotential.rootedWeights`,
  `Maths.MaxPlusPotential.nodupRootedWeights`: the weights of the walks issuing from
  a fixed base vertex and arriving at a given vertex, and of those among them that repeat no
  edge.
* `Maths.MaxPlusPotential.maxRootedWeight`: the greatest such weight, the rooted
  analogue of `Maths.MaxPlusPotential.maxIncomingWeight` and the row of the Kleene
  star indexed by the base.
* `Maths.MaxPlusPotential.IsCriticalVertex`: a vertex carrying a closed walk of mean
  weight exactly `lam`.
* `Maths.MaxPlusPotential.IsEigenvector`: the max-plus eigenvalue equation
  `A ⊗ v = lam ⊗ v`.

## Main results

* `Maths.MaxPlusPotential.maxRootedWeight_isPotential`: the rooted maximum is a
  potential, that is, a subeigenvector.
* `Maths.MaxPlusPotential.exists_tight_edge_maxRootedWeight`: **tightness**, the new
  content.  Rooted at a vertex of a closed walk of weight zero, the rooted maximum has, at every
  vertex, an incoming edge along which the potential inequality is an equality.
* `Maths.MaxPlusPotential.isEigenvector_iff`: the eigenvalue equation splits into the
  subeigenvector inequality and tightness at every coordinate.
* `Maths.MaxPlusPotential.exists_isEigenvector_of_maximizing_cycle`: **existence of a
  max-plus eigenvector**, over an arbitrary linearly ordered field, relative to a given
  mean-maximizing cycle; the eigenvalue is that cycle's mean.
* `Maths.MaxPlusPotential.exists_isEigenvector`: over the reals the maximizing cycle
  need not be assumed, so every real max-plus matrix on a nonempty finite index type has an
  eigenvector, with the maximum cycle mean as eigenvalue.

## Implementation notes

The graph-level results are stated for an arbitrary `Maths.EdgeGraph` and ask
explicitly for the reachability they use: `∀ vertex, Nonempty (G.Walk base vertex)`, one half of
`Maths.IsStronglyConnectedAt`.  Only walks *out of* the base occur, so the
return direction is never needed.  For the matrix reading no reachability hypothesis survives:
`Maths.MaxPlusPotential.matrixGraph` is the complete digraph, since a matrix with
entries in a field has no `-∞` entries, so it is automatically irreducible.  This is why
irreducibility, which the classical statement assumes, appears nowhere in the matrix theorems
below; it is discharged, not dropped.

`Maths.MaxPlusPotential.maxRootedWeight` is total, taking the junk value `0` when no
walk from the base arrives, in the manner of
`Maths.MaxPlusPotential.stepValue`; every result about it assumes reachability, under
which that case never occurs.

Following `Maths.DirectedTransport.Additive.CycleMean`, the general-field theorem takes the
mean-maximizing cycle as a hypothesis and only the real version invokes attainment, which is
available over `ℝ` alone.

The critical *graph* plays no role in existence: since the eigenvalue equation is proved at every
coordinate, no such restriction is needed, and only the critical *vertex* used as the root appears
here, as `Maths.MaxPlusPotential.IsCriticalVertex`.  The subgraph itself, and the
description of the whole eigenspace as generated by the Kleene-star columns rooted at critical
vertices, are `Maths.DirectedTransport.Additive.CriticalGraph`.  So are the critical *classes* - the
strongly connected components of the critical graph, the fact that two Kleene-star columns rooted
in the same critical class differ by a constant, and the resulting sufficiency of one column per
class - together with the minimality of that family, which holds once a vertex of the class in
question reaches the whole graph.

## References

* R. A. Cuninghame-Green, *Minimax Algebra*, Lecture Notes in Economics and Mathematical Systems
  166, Springer (1979), Chapter 24, for the eigenvector of an irreducible max-plus matrix.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992), Theorem 3.23, for the maximum cycle mean as the unique eigenvalue and the critical
  graph.
* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.

## Tags

max-plus, tropical, eigenvector, Perron root, cycle mean, critical graph, Kleene star
-/

@[expose] public section

namespace Maths

noncomputable section

namespace EdgeGraph.Walk

variable {V : Type*} {E : Type*} {G : EdgeGraph V E} {start finish : V}

/-- A walk with no edges does not move. -/
theorem eq_of_length_eq_zero (walk : G.Walk start finish) (hlen : walk.length = 0) :
    start = finish := by
  cases walk with
  | nil => rfl
  | concat walkSoFar edge legal => simp at hlen

/-- A nonempty walk ends with an edge, after a walk to that edge's source. -/
theorem exists_last_edge (walk : G.Walk start finish) (hlen : 0 < walk.length) :
    ∃ (edge : E) (before : G.Walk start (G.source edge)),
      G.target edge = finish ∧ walk.edges = before.edges ++ [edge] := by
  cases walk with
  | nil => simp at hlen
  | concat walkSoFar edge legal =>
      exact ⟨edge, walkSoFar.castFinish legal.symm, rfl, by simp⟩

end EdgeGraph.Walk

namespace MaxPlusPotential

universe uV uE

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### The rooted maximum walk weight -/

/-- Weights of the finite walks from a fixed base vertex to a given vertex. -/
def rootedWeights (G : EdgeGraph V E) (weight : E → 𝕜) (base vertex : V) : Set 𝕜 :=
  {r | ∃ walk : G.Walk base vertex, walkWeight weight walk = r}

/-- Weights of the finite walks from a fixed base vertex to a given vertex that traverse
pairwise distinct edges.  With finitely many edges there are only finitely many of these, so
their maximum is attained without any completeness assumption on the weights. -/
def nodupRootedWeights (G : EdgeGraph V E) (weight : E → 𝕜) (base vertex : V) : Set 𝕜 :=
  {r | ∃ walk : G.Walk base vertex, walk.edges.Nodup ∧ walkWeight weight walk = r}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem nodupRootedWeights_subset (weight : E → 𝕜) (base vertex : V) :
    nodupRootedWeights G weight base vertex ⊆ rootedWeights G weight base vertex := by
  rintro r ⟨walk, -, rfl⟩
  exact ⟨walk, rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With finitely many edges only finitely many weights are realized by walks that repeat no
edge, since such a walk is determined by a duplicate-free list of edges. -/
theorem finite_nodupRootedWeights [Finite E] (weight : E → 𝕜) (base vertex : V) :
    (nodupRootedWeights G weight base vertex).Finite := by
  cases nonempty_fintype E
  refine Set.Finite.subset
    ((List.finite_length_le E (Fintype.card E)).image fun l => (l.map weight).sum) ?_
  rintro r ⟨walk, hnd, rfl⟩
  exact ⟨walk.edges, hnd.length_le_card, rfl⟩

/-- The greatest weight of a walk from the base to a vertex that repeats no edge.  With no
closed walk of positive weight this is the greatest weight of *any* walk from the base
(`walkWeight_le_maxRootedWeight`), that is, the entry of the Kleene star of the weight matrix
indexed by the pair.  It takes the junk value `0` when the vertex is unreachable from the base,
which the reachability hypothesis of every result below rules out. -/
def maxRootedWeight [Finite E] (G : EdgeGraph V E) (weight : E → 𝕜) (base vertex : V) : 𝕜 :=
  ((finite_nodupRootedWeights (G := G) weight base vertex).toFinset.max).unbotD 0

section Finite

variable [Finite E]

omit [IsStrictOrderedRing 𝕜] in
/-- The rooted maximum dominates the weight of every walk from the base that repeats no
edge. -/
theorem le_maxRootedWeight {weight : E → 𝕜} {base vertex : V} {r : 𝕜}
    (hr : r ∈ nodupRootedWeights G weight base vertex) :
    r ≤ maxRootedWeight G weight base vertex := by
  have hfin := finite_nodupRootedWeights (G := G) weight base vertex
  have hmem : r ∈ hfin.toFinset := hfin.mem_toFinset.2 hr
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty ⟨r, hmem⟩
  have hle : (r : WithBot 𝕜) ≤ (a : WithBot 𝕜) := ha ▸ Finset.le_max hmem
  simpa [maxRootedWeight, ha] using (WithBot.coe_le_coe.mp hle)

/-- Under the reachability hypothesis, and with no closed walk of positive weight, the rooted
maximum is itself the weight of a walk from the base that repeats no edge. -/
theorem maxRootedWeight_mem {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base vertex : V} (hreach : Nonempty (G.Walk base vertex)) :
    maxRootedWeight G weight base vertex ∈ nodupRootedWeights G weight base vertex := by
  have hfin := finite_nodupRootedWeights (G := G) weight base vertex
  obtain ⟨walk⟩ := hreach
  obtain ⟨pruned, hnd, -⟩ := exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
  have hne : hfin.toFinset.Nonempty :=
    hfin.toFinset_nonempty.2
      ⟨walkWeight weight pruned, pruned, pruned.edges_nodup_of_visited_nodup hnd, rfl⟩
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty hne
  have hmem := Finset.mem_of_max ha
  simpa [maxRootedWeight, ha] using hfin.mem_toFinset.1 hmem

/-- Pruning: with no closed walk of positive weight the rooted maximum dominates the weight of
*every* walk from the base, not only of those that repeat no edge. -/
theorem walkWeight_le_maxRootedWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base vertex : V} (walk : G.Walk base vertex) :
    walkWeight weight walk ≤ maxRootedWeight G weight base vertex := by
  obtain ⟨pruned, hnd, hle⟩ :=
    exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
  exact hle.trans
    (le_maxRootedWeight ⟨pruned, pruned.edges_nodup_of_visited_nodup hnd, rfl⟩)

/-- With no closed walk of positive weight, the rooted maximum is the greatest weight of a walk
from the base to the vertex. -/
theorem isGreatest_rootedWeights {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base vertex : V} (hreach : Nonempty (G.Walk base vertex)) :
    IsGreatest (rootedWeights G weight base vertex) (maxRootedWeight G weight base vertex) :=
  ⟨nodupRootedWeights_subset weight base vertex (maxRootedWeight_mem hcyc hreach), by
    rintro r ⟨walk, rfl⟩
    exact walkWeight_le_maxRootedWeight hcyc walk⟩

/-- The rooted maximum is a potential: it is the rooted analogue of
`Maths.MaxPlusPotential.maxIncomingWeight_isPotential`, and needs the source of every
edge to be reachable from the base. -/
theorem maxRootedWeight_isPotential {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base : V} (hreach : ∀ vertex : V, Nonempty (G.Walk base vertex)) :
    IsPotential G weight (maxRootedWeight G weight base) := by
  intro e
  obtain ⟨walk, -, hwalk⟩ := maxRootedWeight_mem hcyc (hreach (G.source e))
  have hle := walkWeight_le_maxRootedWeight hcyc (walk.concat e rfl)
  rwa [walkWeight_concat, hwalk] at hle

/-- The weight of the base itself is zero: the empty walk realizes it, and every walk from the
base back to the base is a closed walk, hence of nonpositive weight. -/
theorem maxRootedWeight_self {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (base : V) : maxRootedWeight G weight base base = 0 := by
  refine le_antisymm ?_ (le_maxRootedWeight ⟨.nil, by simp, rfl⟩)
  obtain ⟨walk, -, hwalk⟩ := maxRootedWeight_mem hcyc ⟨(.nil : G.Walk base base)⟩
  exact hwalk ▸ hcyc base walk

/-! ### Critical vertices and tightness -/

/-- A vertex is **critical** for the value `lam` when it carries a nonempty closed walk of mean
weight exactly `lam`.  The maximum cycle mean is the unique value for which a critical vertex can
exist alongside the subeigenvector inequality, and the critical vertices are exactly the vertices
of the critical graph. -/
def IsCriticalVertex (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) (base : V) : Prop :=
  ∃ cycle : G.Walk base base, 0 < cycle.length ∧ walkWeight weight cycle = cycle.length * lam

/-- A nonempty walk from the base realizing the rooted maximum exists at every reachable vertex,
provided the base carries a nonempty closed walk of weight zero: away from the base every walk is
already nonempty, and at the base that closed walk is a maximizer. -/
theorem exists_pos_length_walkWeight_eq_maxRootedWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base : V} (best : G.Walk base base) (hpos : 0 < best.length)
    (hzero : walkWeight weight best = 0) {vertex : V} (hreach : Nonempty (G.Walk base vertex)) :
    ∃ walk : G.Walk base vertex,
      0 < walk.length ∧ walkWeight weight walk = maxRootedWeight G weight base vertex := by
  obtain ⟨walk, -, hwalk⟩ := maxRootedWeight_mem hcyc hreach
  rcases Nat.eq_zero_or_pos walk.length with hlen | hlen
  · obtain rfl := walk.eq_of_length_eq_zero hlen
    exact ⟨best, hpos, by rw [hzero, maxRootedWeight_self hcyc]⟩
  · exact ⟨walk, hlen, hwalk⟩

/-- **Tightness, the eigenvector step.**  With no closed walk of positive weight, and rooted at a
vertex carrying a nonempty closed walk of weight zero, the rooted maximum satisfies the potential
inequality *with equality* along some incoming edge of every vertex.  The witness is the last
edge of a greatest walk arriving at the vertex: its prefix is dominated by the rooted maximum at
that edge's source, while the potential inequality forces the reverse. -/
theorem exists_tight_edge_maxRootedWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base : V} (hreach : ∀ vertex : V, Nonempty (G.Walk base vertex))
    (best : G.Walk base base) (hpos : 0 < best.length) (hzero : walkWeight weight best = 0)
    (vertex : V) :
    ∃ e : E, G.target e = vertex ∧
      maxRootedWeight G weight base (G.source e) + weight e
        = maxRootedWeight G weight base vertex := by
  obtain ⟨walk, hlen, hwalk⟩ :=
    exists_pos_length_walkWeight_eq_maxRootedWeight hcyc best hpos hzero (hreach vertex)
  obtain ⟨e, before, htarget, hedges⟩ := walk.exists_last_edge hlen
  refine ⟨e, htarget, le_antisymm ?_ ?_⟩
  · have := maxRootedWeight_isPotential hcyc hreach e
    rwa [htarget] at this
  · have hsplit : walkWeight weight walk = walkWeight weight before + weight e := by
      simp [walkWeight, hedges]
    have hbefore : walkWeight weight before ≤ maxRootedWeight G weight base (G.source e) :=
      walkWeight_le_maxRootedWeight hcyc before
    linarith [hwalk, hsplit]

end Finite

/-! ### The max-plus matrix reading -/

section Matrix

universe uι

variable {ι : Type uι}

/-- An eigenvector of a max-plus matrix for the value `lam`: the max-plus matrix-vector product
`A ⊙ v`, whose `i`-th coordinate is the maximum over `j` of `A i j + v j`, equals `lam + v`
coordinatewise.  This is `Maths.MaxPlusPotential.IsSubeigenvector` with the
inequality replaced by an equation. -/
def IsEigenvector [Fintype ι] [Nonempty ι] (A : ι → ι → 𝕜) (lam : 𝕜) (v : ι → 𝕜) : Prop :=
  ∀ i : ι, (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun j => A i j + v j) = lam + v i

omit [IsStrictOrderedRing 𝕜] in
/-- The eigenvalue equation splits into the subeigenvector inequality and the attainment of the
maximum at every coordinate. -/
theorem isEigenvector_iff [Fintype ι] [Nonempty ι] (A : ι → ι → 𝕜) (lam : 𝕜) (v : ι → 𝕜) :
    IsEigenvector A lam v ↔
      IsSubeigenvector A lam v ∧ ∀ i : ι, ∃ j : ι, A i j + v j = lam + v i := by
  constructor
  · intro hv
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · exact (hv i) ▸ Finset.le_sup' (fun j => A i j + v j) (Finset.mem_univ j)
    · obtain ⟨j, -, hj⟩ :=
        Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun j => A i j + v j)
      exact ⟨j, by rw [← hj, hv i]⟩
  · rintro ⟨hle, htight⟩ i
    refine le_antisymm (Finset.sup'_le _ _ fun j _ => hle i j) ?_
    obtain ⟨j, hj⟩ := htight i
    exact hj ▸ Finset.le_sup' (fun j => A i j + v j) (Finset.mem_univ j)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Every vertex of the matrix graph is reachable from every other in one edge: a matrix with
entries in a field has no `-∞` entries, so its graph is complete, hence strongly connected. -/
theorem nonempty_walk_matrixGraph (base vertex : ι) :
    Nonempty ((matrixGraph ι).Walk base vertex) :=
  ⟨EdgeGraph.Walk.singleton (G := matrixGraph ι) (vertex, base)⟩

/-- **Existence of a max-plus eigenvector**, over an arbitrary linearly ordered field, relative to
a given mean-maximizing cycle.  If `best` is a nonempty closed walk of the matrix graph whose mean
weight dominates that of every closed walk, then that mean is an eigenvalue: the column of the
Kleene star of `A - lam` rooted at the base of `best` is an eigenvector.

No irreducibility hypothesis appears because none is needed here: the graph of a matrix with
entries in a field is complete. -/
theorem exists_isEigenvector_of_maximizing_cycle [Fintype ι] [Nonempty ι] (A : ι → ι → 𝕜)
    {base : ι} (best : (matrixGraph ι).Walk base base) (hpos : 0 < best.length)
    (hbest : ∀ (i : ι) (cycle : (matrixGraph ι).Walk i i),
      walkWeight (matrixWeight A) cycle
        ≤ cycle.length * (walkWeight (matrixWeight A) best / best.length)) :
    IsEigenvector A (walkWeight (matrixWeight A) best / best.length)
      (maxRootedWeight (matrixGraph ι)
        (fun e => matrixWeight A e - walkWeight (matrixWeight A) best / best.length) base) := by
  classical
  set lam := walkWeight (matrixWeight A) best / best.length with hlam
  set shifted : ι × ι → 𝕜 := fun e => matrixWeight A e - lam with hshifted
  have hlenPos : (0 : 𝕜) < best.length := by exact_mod_cast hpos
  have hcyc : ∀ (i : ι) (cycle : (matrixGraph ι).Walk i i), walkWeight shifted cycle ≤ 0 := by
    intro i cycle
    rw [hshifted, walkWeight_sub_const]
    linarith [hbest i cycle]
  have hzero : walkWeight shifted best = 0 := by
    rw [hshifted, walkWeight_sub_const, hlam]
    field_simp
    ring
  have hreach := nonempty_walk_matrixGraph (ι := ι) base
  refine (isEigenvector_iff A lam _).2 ⟨?_, fun i => ?_⟩
  · exact (isSubeigenvector_iff_isPotential A lam _).2 (maxRootedWeight_isPotential hcyc hreach)
  · obtain ⟨e, htarget, htight⟩ :=
      exists_tight_edge_maxRootedWeight hcyc hreach best hpos hzero i
    have hfst : e.1 = i := htarget
    have hsource : (matrixGraph ι).source e = e.2 := rfl
    have hvalue : shifted e = A i e.2 - lam := by
      simp only [hshifted, matrixWeight, hfst]
    rw [hsource, hvalue] at htight
    exact ⟨e.2, by linarith [htight]⟩

/-- **Max-plus eigenvector existence over the reals.**  Every real max-plus matrix on a nonempty
finite index type has an eigenvector, and the eigenvalue is the maximum cycle mean, attained on a
closed walk of length at most the cardinality of the index type.  The eigenvector is the column
of the Kleene star of `A - lam` rooted at the base of that critical cycle. -/
theorem exists_isEigenvector {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → ι → ℝ) :
    ∃ (lam : ℝ) (base : ι) (best : (matrixGraph ι).Walk base base),
      0 < best.length ∧ best.length ≤ Fintype.card ι ∧
        IsCriticalVertex (matrixGraph ι) (matrixWeight A) lam base ∧
        (∀ (i : ι) (cycle : (matrixGraph ι).Walk i i), 0 < cycle.length →
          walkWeight (matrixWeight A) cycle / cycle.length ≤ lam) ∧
        ∃ v : ι → ℝ, IsEigenvector A lam v := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hexists : ∃ (vertex : ι) (cycle : (matrixGraph ι).Walk vertex vertex),
      0 < cycle.length :=
    ⟨i, ((EdgeGraph.Walk.nil : (matrixGraph ι).Walk i i).concat (i, i)
      (matrixGraph_source _)).castFinish (matrixGraph_target _), by
      rw [EdgeGraph.Walk.length_castFinish, EdgeGraph.Walk.length_concat]
      exact Nat.succ_pos _⟩
  obtain ⟨base, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean
      (matrixGraph ι) (matrixWeight A) hexists
  have hlenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  set lam := walkWeight (matrixWeight A) best / best.length with hlam
  have hbest : ∀ (j : ι) (cycle : (matrixGraph ι).Walk j j),
      walkWeight (matrixWeight A) cycle ≤ cycle.length * lam := by
    intro j cycle
    rcases Nat.eq_zero_or_pos cycle.length with hzero | hposCycle
    · have hedges : cycle.edges = [] :=
        List.length_eq_zero_iff.mp (by rw [EdgeGraph.Walk.edges_length, hzero])
      simp [walkWeight, hedges, hzero]
    · have hlen : (0 : ℝ) < cycle.length := by exact_mod_cast hposCycle
      have := (div_le_iff₀ hlen).mp (hmax j cycle hposCycle)
      linarith
  refine ⟨lam, base, best, hpos, hcard, ⟨best, hpos, ?_⟩, fun j cycle hlen => hmax j cycle hlen,
    _, exists_isEigenvector_of_maximizing_cycle A best hpos hbest⟩
  rw [hlam]
  field_simp

end Matrix

end MaxPlusPotential

end

end Maths
