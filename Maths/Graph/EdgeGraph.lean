/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Set.CoeSort

import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Directed multigraphs with edge identities and their typed walks

A directed multigraph is represented by a vertex type, an edge type, and source and target
maps. Edges are data, not mere related vertex pairs, so parallel edges retain their
identities.

`EdgeGraph.Walk G start finish` is an endpoint-indexed finite walk. It stores the edge
identities in chronological order and makes endpoint compatibility part of the type: an edge
extends a walk ending at its source, and the extension ends at its target, so reading a walk
never requires an endpoint coercion. This file supplies the reusable finite-walk calculus:
length, edge and visited-vertex lists, endpoint facts, concatenation, singleton walks, edge
multiplicity, splitting at an edge, and splicing at a visited vertex.

The file deliberately assigns no labels or weights to edges. Transport, charges, discrepancy,
circulations, and application-specific semantics belong in files that import this one.

## Main definitions

* `Maths.EdgeGraph`: a directed multigraph as vertex and edge types with `source`
  and `target` maps.
* `Maths.EdgeGraph.reverse`: the graph obtained by reversing every edge while
  retaining its identity.
* `Maths.EdgeGraph.restrictEdges` and `Maths.EdgeGraph.induce`: the subgraphs on a set of
  edges and on a set of vertices.
* `Maths.EdgeGraph.Walk.ofRestrictEdges`: a walk of an edge subgraph read in the ambient
  graph.
* `Maths.EdgeGraph.symmetrization`: the graph carrying both orientations of every edge.
* `Maths.EdgeGraph.Walk`: an endpoint-indexed finite walk.
* `Maths.EdgeGraph.Walk.edges`, `length`, `visited`, `edgeMultiplicity`: the
  basic measurements of a walk.
* `Maths.EdgeGraph.Walk.append`, `singleton`, `iterate`, `castStart`, `castFinish`,
  `reverse`: walk constructors.
* `Maths.EdgeGraph.Walk.IsSimpleCycle`: a nonempty closed walk with no decomposition into two
  nonempty closed walks at a repeated vertex, the decomposition-invariant form of a simple
  directed cycle.
* `Maths.EdgeGraph.Walk.VertexSplit`: a witness that a walk visits a vertex,
  together with `splice` for inserting a closed walk there.
* `Maths.RootReaches`, `Maths.LinkedTo`, `Maths.IsStronglyConnectedAt`,
  `Maths.EdgeEndpointsLinkedTo`, and `Maths.HasEdgeReturns`: walk-existence reachability
  conditions.

## Main results

* `Maths.EdgeGraph.Walk.ext`: a walk is determined by its edge list.
* `Maths.EdgeGraph.Walk.edges_isChain`: consecutive edges have matching endpoints.
* `Maths.EdgeGraph.Walk.reverse_nil`, `reverse_concat`, and `reverse_append`: reversal
  distributes over the basic walk constructors.
* `Maths.EdgeGraph.Walk.length_reverse`, `edges_reverse`, and `reverse_reverse`:
  reversal preserves length, reverses the edge list, and is involutive.
* `Maths.EdgeGraph.Walk.edges_nodup_of_visited_nodup`: pairwise distinct visited
  vertices force pairwise distinct edges.
* `Maths.EdgeGraph.Walk.exists_splitAtEdge`: a walk splits at any edge it uses.
* `Maths.EdgeGraph.Walk.exists_split_of_length_le`: a walk splits after any
  prescribed number of its edges.
* `Maths.EdgeGraph.Walk.exists_split_of_mem_visited`: a walk splits at any vertex
  it visits.
* `Maths.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`: a walk revisiting a
  vertex contains a nonempty closed subwalk.
* `Maths.EdgeGraph.Walk.IsSimpleCycle.length_le_card`: a simple cycle on finitely many
  vertices has at most one edge per vertex.
* `Maths.EdgeGraph.exists_walk_length_eq_forall_mem_edges` and
  `Maths.EdgeGraph.exists_walk_length_eq`: when every vertex has an incoming edge of some
  kind, every vertex ends walks of every length along edges of that kind.
* `Maths.EdgeGraph.exists_source_eq`: a vertex with an incoming edge that reaches every vertex
  has an outgoing edge.
* `Maths.linkedTo_source_of_mem_edges` and `Maths.linkedTo_target_of_mem_edges`: a closed
  walk stays inside the strongly connected component of its base.
* `Maths.EdgeGraph.Walk.VertexSplit.length_splice`: splicing adds lengths.
* `Maths.EdgeGraph.reverse_reverse`: reversing every edge twice recovers the
  original graph.
* `Maths.EdgeGraph.symmetrization_hasEdgeReturns`: every edge of the symmetrization
  returns along its opposite orientation.

## Implementation notes

A *cycle* in a declaration name, as in `Maths.HasTrivialCycleLabels` or
`Maths.HasZeroCycleSums`, means an arbitrary closed walk, which may repeat vertices and edges.
This differs from mathlib's `SimpleGraph.Walk.IsCycle`.  The simple cycles, closed walks with
no proper closed subwalk, are `Maths.EdgeGraph.Walk.IsSimpleCycle`.

## Tags

directed multigraph, quiver, walk, path, parallel edges, edge multiplicity
-/

@[expose] public section

namespace Maths

universe uV uE

/-- A directed multigraph, given by `source` and `target` maps on an edge type. Edges are
data, so parallel edges retain their identities. -/
structure EdgeGraph (V : Type uV) (E : Type uE) where
  /-- The vertex an edge starts at. -/
  source : E → V
  /-- The vertex an edge ends at. -/
  target : E → V

namespace EdgeGraph

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-- Reverse every edge while retaining its identity. -/
abbrev reverse : EdgeGraph V E where
  source := G.target
  target := G.source

/-- The source of an edge in the reversed graph is its original target. -/
@[simp] theorem reverse_source (edge : E) : G.reverse.source edge = G.target edge :=
  rfl

/-- The target of an edge in the reversed graph is its original source. -/
@[simp] theorem reverse_target (edge : E) : G.reverse.target edge = G.source edge :=
  rfl

/-- Reversing every edge twice recovers the original graph. -/
@[simp] theorem reverse_reverse : G.reverse.reverse = G :=
  rfl

/-- The subgraph on a set of edges: the vertices are those of the ambient graph and the edges are
the members of the set, with the ambient endpoints.  This is the edge-indexed analogue of
`Maths.EdgeGraph.induce`, which selects a set of vertices instead. -/
abbrev restrictEdges (S : Set E) : EdgeGraph V S where
  source edge := G.source edge.1
  target edge := G.target edge.1

/-- The source map of an edge subgraph restricts the ambient source map. -/
@[simp] theorem restrictEdges_source (S : Set E) (edge : S) :
    (G.restrictEdges S).source edge = G.source edge.1 := rfl

/-- The target map of an edge subgraph restricts the ambient target map. -/
@[simp] theorem restrictEdges_target (S : Set E) (edge : S) :
    (G.restrictEdges S).target edge = G.target edge.1 := rfl

/-- The induced subgraph on a set of vertices: its vertices are the members of the set,
and its edges are the ambient edges whose endpoints both belong to the set. -/
def induce (G : EdgeGraph V E) (S : Set V) :
    EdgeGraph S {edge : E // G.source edge ∈ S ∧ G.target edge ∈ S} where
  source edge := ⟨G.source edge.1, edge.2.1⟩
  target edge := ⟨G.target edge.1, edge.2.2⟩

/-- The source map of an induced subgraph restricts the ambient source map. -/
@[simp] theorem induce_source (G : EdgeGraph V E) (S : Set V)
    (edge : {edge : E // G.source edge ∈ S ∧ G.target edge ∈ S}) :
    (G.induce S).source edge = ⟨G.source edge.1, edge.2.1⟩ := rfl

/-- The target map of an induced subgraph restricts the ambient target map. -/
@[simp] theorem induce_target (G : EdgeGraph V E) (S : Set V)
    (edge : {edge : E // G.source edge ∈ S ∧ G.target edge ∈ S}) :
    (G.induce S).target edge = ⟨G.target edge.1, edge.2.2⟩ := rfl

/-- The graph carrying both orientations of every edge identity: `(edge, false)` runs
forward and `(edge, true)` runs backward.  Directed walks in it are the undirected walks
of `G`, so it is the carrier of classical, undirected gain-graph notions. -/
def symmetrization : EdgeGraph V (E × Bool) where
  source
    | (edge, false) => G.source edge
    | (edge, true) => G.target edge
  target
    | (edge, false) => G.target edge
    | (edge, true) => G.source edge

@[simp] theorem symmetrization_source_false (edge : E) :
    G.symmetrization.source (edge, false) = G.source edge := rfl

@[simp] theorem symmetrization_source_true (edge : E) :
    G.symmetrization.source (edge, true) = G.target edge := rfl

@[simp] theorem symmetrization_target_false (edge : E) :
    G.symmetrization.target (edge, false) = G.target edge := rfl

@[simp] theorem symmetrization_target_true (edge : E) :
    G.symmetrization.target (edge, true) = G.source edge := rfl

/-- The opposite orientation of an edge of the symmetrization. -/
@[simp] theorem symmetrization_source_not (edge : E × Bool) :
    G.symmetrization.source (edge.1, !edge.2) = G.symmetrization.target edge := by
  rcases edge with ⟨edge, _ | _⟩ <;> rfl

/-- The opposite orientation of an edge of the symmetrization. -/
@[simp] theorem symmetrization_target_not (edge : E × Bool) :
    G.symmetrization.target (edge.1, !edge.2) = G.symmetrization.source edge := by
  rcases edge with ⟨edge, _ | _⟩ <;> rfl

/-- A finite directed walk, retaining the list of edge identities.  An edge extends a walk
exactly when the walk ends at the edge's source, and this is enforced by the index rather than
by a proof argument, so no endpoint coercion is ever needed to read a walk. -/
inductive Walk (start : V) : V → Type (max uV uE)
  | /-- The empty walk at `start`. -/
    nil : Walk start start
  | /-- Extend a walk ending at the source of an edge by that edge. -/
    concat (edge : E) (walkSoFar : Walk start (G.source edge)) : Walk start (G.target edge)

namespace Walk

variable {G} {start finish middle : V}

/-- Number of edges in a finite walk. -/
def length {start : V} : {finish : V} → G.Walk start finish → ℕ
  | _, .nil => 0
  | _, .concat _ walkSoFar => walkSoFar.length + 1

/-- Edge identities in chronological order. -/
def edges {start : V} : {finish : V} → G.Walk start finish → List E
  | _, .nil => []
  | _, .concat edge walkSoFar => walkSoFar.edges ++ [edge]

@[simp] theorem length_nil : (Walk.nil : G.Walk start start).length = 0 := rfl

@[simp] theorem length_concat (edge : E) (walkSoFar : G.Walk start (G.source edge)) :
    (walkSoFar.concat edge).length = walkSoFar.length + 1 := rfl

@[simp] theorem edges_nil : (Walk.nil : G.Walk start start).edges = [] := rfl

@[simp] theorem edges_concat (edge : E) (walkSoFar : G.Walk start (G.source edge)) :
    (walkSoFar.concat edge).edges = walkSoFar.edges ++ [edge] := rfl

@[simp] theorem edges_length (walk : G.Walk start finish) :
    walk.edges.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih => simp [edges, length, ih]

/-- The vertices visited by a typed walk, in chronological order, starting with
its initial vertex.  A walk with `n` edges visits `n + 1` vertices. -/
def visited {start : V} : {finish : V} → G.Walk start finish → List V
  | _, .nil => [start]
  | _, .concat edge walkSoFar => walkSoFar.visited ++ [G.target edge]

@[simp] theorem visited_nil : (Walk.nil : G.Walk start start).visited = [start] := rfl

@[simp] theorem visited_concat (edge : E) (walkSoFar : G.Walk start (G.source edge)) :
    (walkSoFar.concat edge).visited = walkSoFar.visited ++ [G.target edge] := rfl

@[simp] theorem length_visited (walk : G.Walk start finish) :
    walk.visited.length = walk.length + 1 := by
  induction walk with
  | nil => simp
  | concat edge walkSoFar ih => simp [ih]

/-- An edge used by a walk has its target among the walk's visited vertices. -/
theorem mem_visited_of_mem_edges (walk : G.Walk start finish)
    {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ walk.visited := by
  induction walk with
  | nil => simp at hmem
  | concat e walkSoFar ih =>
      rw [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rw [visited_concat]
      rcases hmem with hmem | rfl
      · exact List.mem_append_left _ (ih hmem)
      · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A walk whose visited vertices are pairwise distinct traverses pairwise
distinct edges: a repeated edge would revisit its target vertex.  This lets
walk bounds count edges, not vertices. -/
theorem edges_nodup_of_visited_nodup (walk : G.Walk start finish)
    (hnd : walk.visited.Nodup) : walk.edges.Nodup := by
  induction walk with
  | nil => simp
  | concat e walkSoFar ih =>
      rw [visited_concat, List.nodup_append] at hnd
      obtain ⟨hvisited, -, hdisjoint⟩ := hnd
      rw [edges_concat, List.nodup_append]
      refine ⟨ih hvisited, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hdisjoint (G.target a) (walkSoFar.mem_visited_of_mem_edges ha)
        (G.target a) (List.mem_singleton_self _) rfl

/-- A walk splits at every vertex it visits. -/
theorem exists_split_of_mem_visited (walk : G.Walk start finish)
    {vertex : V} (hmem : vertex ∈ walk.visited) :
    ∃ (before : G.Walk start vertex) (after : G.Walk vertex finish),
      walk.edges = before.edges ++ after.edges := by
  induction walk with
  | nil =>
      rw [visited_nil, List.mem_singleton] at hmem
      subst hmem
      exact ⟨.nil, .nil, by simp⟩
  | concat edge walkSoFar ih =>
      rw [visited_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨before, after, hedges⟩ := ih hmem
        refine ⟨before, after.concat edge, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]
      · subst hmem
        exact ⟨walkSoFar.concat edge, .nil, by simp⟩

/-- A walk that revisits a vertex contains a nonempty closed subwalk. -/
theorem exists_closedSubwalk_of_not_nodup
    (walk : G.Walk start finish) (hdup : ¬ walk.visited.Nodup) :
    ∃ (vertex : V) (before : G.Walk start vertex) (cycle : G.Walk vertex vertex)
      (after : G.Walk vertex finish),
      0 < cycle.length ∧
        walk.edges = before.edges ++ cycle.edges ++ after.edges := by
  induction walk with
  | nil => exact absurd (List.nodup_singleton start) hdup
  | concat edge walkSoFar ih =>
      rw [visited_concat] at hdup
      by_cases hmem : G.target edge ∈ walkSoFar.visited
      · obtain ⟨before, after, hedges⟩ :=
          walkSoFar.exists_split_of_mem_visited hmem
        refine ⟨G.target edge, before, after.concat edge, .nil, by simp, ?_⟩
        simp only [edges_concat, edges_nil, hedges,
          List.append_assoc, List.append_nil]
      · have hnodup : ¬ walkSoFar.visited.Nodup := by
          intro hnd
          refine hdup ?_
          rw [List.nodup_append]
          refine ⟨hnd, List.nodup_singleton _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          rintro rfl
          exact hmem ha
        obtain ⟨vertex, before, cycle, after, hlen, hedges⟩ := ih hnodup
        refine ⟨vertex, before, cycle, after.concat edge, hlen, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]

/-- A walk is determined by its start and its edge list, even across terminal indices: walks
with equal edge lists end at the same vertex and are heterogeneously equal. -/
theorem heq_of_edges_eq {finish' : V} (first : G.Walk start finish)
    (second : G.Walk start finish') (hedges : first.edges = second.edges) :
    finish = finish' ∧ first ≍ second := by
  induction first generalizing finish' with
  | nil =>
      cases second with
      | nil => exact ⟨rfl, .rfl⟩
      | concat edge second => simp at hedges
  | concat edge first ih =>
      cases second with
      | nil => simp at hedges
      | concat edge' second =>
          rw [edges_concat, edges_concat] at hedges
          obtain ⟨hprefix, hlast⟩ := List.append_inj' hedges rfl
          rw [List.singleton_inj] at hlast
          subst hlast
          cases eq_of_heq (ih second hprefix).2
          exact ⟨rfl, .rfl⟩

/-- **Walks are determined by their edges.** -/
@[ext] theorem ext {first second : G.Walk start finish} (hedges : first.edges = second.edges) :
    first = second :=
  eq_of_heq (heq_of_edges_eq first second hedges).2

/-- An empty walk has equal endpoints. -/
theorem eq_of_length_eq_zero (walk : G.Walk start finish) (hlength : walk.length = 0) :
    start = finish := by
  cases walk with
  | nil => rfl
  | concat _ _ => simp at hlength

/-- An empty closed walk is the empty walk. -/
theorem eq_nil_of_length_eq_zero {walk : G.Walk start start} (hlength : walk.length = 0) :
    walk = .nil :=
  Walk.ext (List.eq_nil_of_length_eq_zero ((edges_length walk).trans hlength))

/-- A nonempty walk ends with an edge, after a walk to that edge's source. -/
theorem exists_last_edge (walk : G.Walk start finish) (hlen : 0 < walk.length) :
    ∃ (edge : E) (before : G.Walk start (G.source edge)),
      G.target edge = finish ∧ walk.edges = before.edges ++ [edge] := by
  cases walk with
  | nil => simp at hlen
  | concat edge walkSoFar => exact ⟨edge, walkSoFar, rfl, rfl⟩

/-- The last edge of a walk ending at `finish` ends at `finish`, stated for `List.getLast?` so
that no nonemptiness proof appears in the statement. -/
theorem target_of_mem_getLast? (walk : G.Walk start finish) {edge : E}
    (hlast : walk.edges.getLast? = some edge) : G.target edge = finish := by
  induction walk with
  | nil => simp at hlast
  | concat finalEdge walkSoFar =>
      rw [edges_concat, List.getLast?_concat, Option.some_inj] at hlast
      rw [hlast]

/-- Consecutive edge identities in a typed walk have matching endpoints. -/
theorem edges_isChain (walk : G.Walk start finish) :
    walk.edges.IsChain fun first second => G.target first = G.source second := by
  induction walk with
  | nil => exact List.isChain_nil
  | concat edge walkSoFar ih =>
      rw [edges_concat, List.isChain_append]
      refine ⟨ih, List.isChain_singleton edge, fun last hlast first hfirst => ?_⟩
      rw [List.head?_singleton, Option.mem_def, Option.some_inj] at hfirst
      subst hfirst
      exact walkSoFar.target_of_mem_getLast? hlast

/-- The first edge of a nonempty typed walk starts at its initial vertex, stated for
`List.head?` so that no nonemptiness proof appears in the statement. -/
theorem source_of_mem_head? (walk : G.Walk start finish) {edge : E}
    (hhead : walk.edges.head? = some edge) : G.source edge = start := by
  induction walk with
  | nil => simp at hhead
  | concat finalEdge walkSoFar ih =>
      rw [edges_concat] at hhead
      rcases List.eq_nil_or_concat walkSoFar.edges with hnil | ⟨_, _, hsnoc⟩
      · have hstart : walkSoFar.length = 0 := by rw [← edges_length, hnil, List.length_nil]
        rw [hnil, List.nil_append, List.head?_cons, Option.some_inj] at hhead
        subst hhead
        exact (walkSoFar.eq_of_length_eq_zero hstart).symm
      · rw [List.head?_append_of_ne_nil _ (by simp [hsnoc])] at hhead
        exact ih hhead

/-- A closed walk with no proper nonempty closed subwalk whose removal leaves
a nonempty closed walk.  This is the decomposition-invariant form of a simple
directed cycle and includes one-edge loops. -/
def IsSimpleCycle {base : V} (cycle : G.Walk base base) : Prop :=
  0 < cycle.length ∧
    ∀ (vertex : V) (before : G.Walk base vertex)
      (inner : G.Walk vertex vertex) (after : G.Walk vertex base),
      cycle.edges = before.edges ++ inner.edges ++ after.edges →
      0 < inner.length → 0 < before.length + after.length → False

/-- A simple cycle on finitely many vertices has at most one edge per vertex. -/
theorem IsSimpleCycle.length_le_card [Fintype V] {base : V} {cycle : G.Walk base base}
    (hsimple : cycle.IsSimpleCycle) : cycle.length ≤ Fintype.card V := by
  classical
  by_contra hcard
  cases cycle with
  | nil => exact (Nat.not_lt_zero _ hsimple.1)
  | concat edge initial =>
      have hinitialDup : ¬initial.visited.Nodup := by
        intro hnodup
        have hlengthCard := hnodup.length_le_card
        rw [length_visited] at hlengthCard
        simp only [length_concat] at hcard
        exact hcard hlengthCard
      obtain ⟨middle, before, inner, after, hinnerPos, hedges⟩ :=
        initial.exists_closedSubwalk_of_not_nodup hinitialDup
      have hcycleEdges :
          (initial.concat edge).edges =
            before.edges ++ inner.edges ++ (after.concat edge).edges := by
        simp only [edges_concat, hedges, List.append_assoc]
      exact hsimple.2 middle before inner (after.concat edge)
        hcycleEdges hinnerPos (by rw [length_concat]; omega)

/-- The first edge of a nonempty typed walk starts at its initial vertex. -/
theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.source (walk.edges.head hne) = start :=
  source_of_mem_head? walk (List.head?_eq_some_head hne)

/-- The last edge of a nonempty typed walk ends at its terminal vertex. -/
theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.target (walk.edges.getLast hne) = finish :=
  target_of_mem_getLast? walk (List.getLast?_eq_some_getLast hne)

/-- Multiplicity of an edge identity in a finite walk. -/
def edgeMultiplicity [DecidableEq E] {start : V} :
    {finish : V} → G.Walk start finish → E → ℕ
  | _, .nil => fun _ => 0
  | _, .concat edge walkSoFar => fun candidate =>
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0

@[simp] theorem edgeMultiplicity_nil [DecidableEq E] (candidate : E) :
    (Walk.nil : G.Walk start start).edgeMultiplicity candidate = 0 := rfl

@[simp] theorem edgeMultiplicity_concat [DecidableEq E] (edge : E)
    (walkSoFar : G.Walk start (G.source edge)) (candidate : E) :
    (walkSoFar.concat edge).edgeMultiplicity candidate =
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0 := rfl

theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges := by
  induction walk with
  | nil => simp [edgeMultiplicity, edges]
  | concat finalEdge walkSoFar ih =>
      by_cases h : edge = finalEdge <;> simp [edgeMultiplicity, edges, ih, h]

theorem edgeMultiplicity_eq_count [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    walk.edgeMultiplicity edge = walk.edges.count edge := by
  induction walk with
  | nil => rfl
  | concat finalEdge walkSoFar ih =>
      by_cases h : edge = finalEdge
      · subst edge
        simp [edgeMultiplicity, edges, List.count_append, ih]
      · simp [edgeMultiplicity, edges, List.count_append, ih, h, eq_comm]

theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges := by
  grind [walk.edgeMultiplicity_eq_count]

theorem edgeMultiplicity_le_one [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge ≤ 1 := by
  rw [walk.edgeMultiplicity_eq_count]
  exact (List.nodup_iff_count_le_one.mp hnodup) edge

/-- Change only the terminal index of a typed walk along an equality. -/
def castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') : G.Walk start finish' :=
  hfinish ▸ walk

@[simp] theorem castFinish_rfl (walk : G.Walk start finish) : walk.castFinish rfl = walk :=
  rfl

@[simp] theorem length_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).length = walk.length := by
  subst finish'
  rfl

@[simp] theorem edges_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).edges = walk.edges := by
  subst finish'
  rfl

@[simp] theorem castFinish_castFinish {finish' finish'' : V} (walk : G.Walk start finish)
    (hfirst : finish = finish') (hsecond : finish' = finish'') :
    (walk.castFinish hfirst).castFinish hsecond = walk.castFinish (hfirst.trans hsecond) := by
  subst hfirst hsecond
  rfl

/-- Extending heterogeneously equal walks by equal edges gives heterogeneously equal walks. -/
theorem concat_heq_concat {edge edge' : E} (hedge : edge = edge')
    {first : G.Walk start (G.source edge)} {second : G.Walk start (G.source edge')}
    (hwalk : first ≍ second) : first.concat edge ≍ second.concat edge' := by
  subst hedge
  cases eq_of_heq hwalk
  rfl

/-- Change only the initial index of a typed walk along an equality. -/
def castStart {start start' finish : V} (walk : G.Walk start finish)
    (hstart : start = start') : G.Walk start' finish :=
  hstart ▸ walk

@[simp] theorem castStart_rfl (walk : G.Walk start finish) : walk.castStart rfl = walk :=
  rfl

/-- Changing the initial index leaves the length unchanged. -/
@[simp] theorem length_castStart {start start' finish : V}
    (walk : G.Walk start finish) (hstart : start = start') :
    (walk.castStart hstart).length = walk.length := by
  subst start'
  rfl

/-- Changing the initial index leaves the edge list unchanged. -/
@[simp] theorem edges_castStart {start start' finish : V}
    (walk : G.Walk start finish) (hstart : start = start') :
    (walk.castStart hstart).edges = walk.edges := by
  subst start'
  rfl

/-- Concatenate two typed walks at their common endpoint. -/
def append {start middle : V} (first : G.Walk start middle) :
    {finish : V} → G.Walk middle finish → G.Walk start finish
  | _, .nil => first
  | _, .concat edge second => (first.append second).concat edge

@[simp] theorem append_nil (first : G.Walk start middle) :
    first.append (.nil : G.Walk middle middle) = first := rfl

/-- Prepending an empty walk leaves a walk unchanged. -/
@[simp] theorem nil_append (second : G.Walk middle finish) :
    (.nil : G.Walk middle middle).append second = second := by
  induction second with
  | nil => rfl
  | concat edge second ih => simp [append, ih]

@[simp] theorem append_concat (first : G.Walk start middle) (edge : E)
    (second : G.Walk middle (G.source edge)) :
    first.append (second.concat edge) = (first.append second).concat edge := rfl

/-- Associativity of typed walk concatenation. -/
theorem append_assoc {finish' : V} (first : G.Walk start middle) (second : G.Walk middle finish)
    (third : G.Walk finish finish') :
    (first.append second).append third = first.append (second.append third) := by
  induction third with
  | nil => rfl
  | concat edge third ih =>
      simp only [append_concat, ih]

/-- Appending to a walk with a retyped terminal index retypes the appended walk's start. -/
theorem castFinish_append {finish' : V} (first : G.Walk start middle)
    (second : G.Walk finish finish') (hmiddle : middle = finish) :
    (first.castFinish hmiddle).append second = first.append (second.castStart hmiddle.symm) := by
  subst hmiddle
  rfl

/-- Appending a walk with a retyped terminal index retypes the composite's terminal index. -/
theorem append_castFinish {finish' : V} (first : G.Walk start middle)
    (second : G.Walk middle finish) (hfinish : finish = finish') :
    first.append (second.castFinish hfinish) = (first.append second).castFinish hfinish := by
  subst hfinish
  rfl

@[simp] theorem edges_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).edges = first.edges ++ second.edges := by
  induction second with
  | nil => simp
  | concat edge second ih => simp [ih, List.append_assoc]

@[simp] theorem length_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp
  | concat edge second ih => simp [ih, Nat.add_assoc]

/-- Traverse a closed walk `n` times. -/
def iterate {base : V} (cycle : G.Walk base base) : ℕ → G.Walk base base
  | 0 => .nil
  | n + 1 => (cycle.iterate n).append cycle

@[simp] theorem iterate_zero {base : V} (cycle : G.Walk base base) : cycle.iterate 0 = .nil :=
  rfl

@[simp] theorem iterate_succ {base : V} (cycle : G.Walk base base) (n : ℕ) :
    cycle.iterate (n + 1) = (cycle.iterate n).append cycle := rfl

@[simp] theorem length_iterate {base : V} (cycle : G.Walk base base) (n : ℕ) :
    (cycle.iterate n).length = n * cycle.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul]

/-- The one-edge walk carrying a prescribed edge identity. -/
def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) :=
  .concat edge .nil

@[simp] theorem edges_singleton (edge : E) : (singleton (G := G) edge).edges = [edge] := rfl

@[simp] theorem length_singleton (edge : E) : (singleton (G := G) edge).length = 1 := rfl

/-- Prepending a one-edge walk. -/
theorem singleton_append_concat (first : E) (edge : E)
    (walk : G.Walk (G.target first) (G.source edge)) :
    (singleton first).append (walk.concat edge) = ((singleton first).append walk).concat edge :=
  rfl

/-- Reverse a typed walk, changing its graph orientation and endpoint order. -/
def reverse {start : V} : {finish : V} → G.Walk start finish → G.reverse.Walk finish start
  | _, .nil => .nil
  | _, .concat edge walkSoFar => (singleton (G := G.reverse) edge).append (reverse walkSoFar)

/-- Reversal turns a change of initial index into a change of terminal index. -/
theorem reverse_castStart {start start' finish : V} (walk : G.Walk start finish)
    (hstart : start = start') :
    reverse (walk.castStart hstart) = (reverse walk).castFinish hstart := by
  subst start'
  rfl

/-- Reversal turns a change of terminal index into a change of initial index. -/
theorem reverse_castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    reverse (walk.castFinish hfinish) = (reverse walk).castStart hfinish := by
  subst finish'
  rfl

/-- Reversing a one-edge walk gives the same edge in the reversed graph. -/
@[simp] theorem reverse_singleton (edge : E) :
    reverse (singleton (G := G) edge) = singleton (G := G.reverse) edge :=
  rfl

/-- Reversal leaves an empty walk empty. -/
@[simp] theorem reverse_nil : (reverse (G := G) (.nil : G.Walk start start)) = .nil :=
  rfl

/-- Reversal of a walk extended by an edge starts with the reversed edge. -/
@[simp] theorem reverse_concat (edge : E) (walkSoFar : G.Walk start (G.source edge)) :
    reverse (walkSoFar.concat edge) =
      (singleton (G := G.reverse) edge).append (reverse walkSoFar) :=
  rfl

/-- Reversal preserves the number of edges in a walk. -/
@[simp] theorem length_reverse (walk : G.Walk start finish) :
    walk.reverse.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      rw [reverse_concat, length_append, length_singleton, length_concat, ih]
      omega

/-- Reversal reverses the chronological edge list of a walk. -/
@[simp] theorem edges_reverse (walk : G.Walk start finish) :
    walk.reverse.edges = walk.edges.reverse := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      rw [reverse_concat, edges_append, edges_singleton, edges_concat, ih]
      simp

/-- Reversal distributes over typed walk concatenation. -/
theorem reverse_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).reverse = second.reverse.append first.reverse := by
  induction second with
  | nil => simp [nil_append]
  | concat edge second ih =>
      rw [append_concat, reverse_concat, ih, reverse_concat, append_assoc]

/-- Reversing a typed walk twice recovers the original walk. -/
@[simp] theorem reverse_reverse (walk : G.Walk start finish) :
    walk.reverse.reverse = walk := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      rw [reverse_concat, reverse_append, ih]
      rfl

/-- A typed decomposition of a walk at an occurrence of an edge. -/
theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E) (hmem : edge ∈ walk.edges) :
    ∃ (before : G.Walk start (G.source edge)) (after : G.Walk (G.target edge) finish),
      walk.edges = before.edges ++ edge :: after.edges := by
  induction walk with
  | nil => simp at hmem
  | concat finalEdge walkSoFar ih =>
      simp only [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | heq
      · obtain ⟨before, after, hsplit⟩ := ih hmem
        refine ⟨before, after.concat finalEdge, ?_⟩
        simp only [edges_concat, hsplit]
        simp [List.append_assoc]
      · subst finalEdge
        exact ⟨walkSoFar, .nil, by simp⟩

/-- A walk splits after any prescribed number of its edges. -/
theorem exists_split_of_length_le {start finish : V} (walk : G.Walk start finish)
    {count : ℕ} (hcount : count ≤ walk.length) :
    ∃ (middle : V) (before : G.Walk start middle) (after : G.Walk middle finish),
      before.length = count ∧ walk.edges = before.edges ++ after.edges := by
  induction walk with
  | nil =>
      have hzero : count = 0 := Nat.le_zero.mp hcount
      exact ⟨start, .nil, .nil, hzero.symm ▸ rfl, by simp⟩
  | concat edge walkSoFar ih =>
      rcases Nat.lt_or_ge count (walkSoFar.length + 1) with hlt | hge
      · obtain ⟨mid, before, after, hlen, hedges⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨mid, before, after.concat edge, hlen, by
          simp only [edges_concat, hedges, List.append_assoc]⟩
      · have hEq : count = walkSoFar.length + 1 := by
          simp only [length_concat] at hcount
          omega
        exact ⟨_, walkSoFar.concat edge, .nil, by simp [hEq], by simp⟩

/-- A witness that a typed walk passes through a specified vertex. -/
structure VertexSplit (walk : G.Walk start finish) (vertex : V) where
  /-- The portion of the walk before the visit. -/
  before : G.Walk start vertex
  /-- The portion of the walk after the visit. -/
  after : G.Walk vertex finish
  /-- The two portions recover the original edge list. -/
  edges_eq : walk.edges = before.edges ++ after.edges

/-- The source of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtSource (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.source edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before, (singleton (G := G) edge).append after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

/-- The target of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtTarget (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.target edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before.concat edge, after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

namespace VertexSplit

/-- Insert a closed walk at a visited vertex. -/
def splice {walk : G.Walk start finish} {vertex : V} (split : walk.VertexSplit vertex)
    (inserted : G.Walk vertex vertex) : G.Walk start finish :=
  (split.before.append inserted).append split.after

@[simp] theorem edges_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges =
      split.before.edges ++ inserted.edges ++ split.after.edges := by
  simp [splice, List.append_assoc]

theorem edges_splice_perm {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges.Perm (walk.edges ++ inserted.edges) := by
  rw [split.edges_eq]
  simpa [List.append_assoc] using
    (List.Perm.refl split.before.edges).append
      (List.perm_append_comm :
        (inserted.edges ++ split.after.edges).Perm (split.after.edges ++ inserted.edges))

@[simp] theorem length_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).length = walk.length + inserted.length := by
  rw [← Walk.edges_length, ← Walk.edges_length, ← Walk.edges_length]
  simpa using (split.edges_splice_perm inserted).length_eq

end VertexSplit

/-- A walk of an edge subgraph read as a walk of the ambient graph, by forgetting the membership
proof carried by each edge. -/
def ofRestrictEdges {S : Set E} {start : V} :
    {finish : V} → (G.restrictEdges S).Walk start finish → G.Walk start finish
  | _, .nil => .nil
  | _, .concat edge walkSoFar => (ofRestrictEdges walkSoFar).concat edge.1

@[simp] theorem ofRestrictEdges_nil {S : Set E} {start : V} :
    ofRestrictEdges (G := G) (S := S) (.nil : (G.restrictEdges S).Walk start start) = .nil := rfl

/-- Reading a walk of an edge subgraph in the ambient graph forgets the membership proofs of its
edges and nothing else. -/
@[simp] theorem edges_ofRestrictEdges {S : Set E} {start finish : V}
    (walk : (G.restrictEdges S).Walk start finish) :
    (ofRestrictEdges walk).edges = walk.edges.map Subtype.val := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      change (ofRestrictEdges walkSoFar).edges ++ [edge.1] = (walkSoFar.edges ++ [edge]).map _
      rw [ih, List.map_append, List.map_singleton]

/-- The converse reading: a walk of the ambient graph all of whose edges belong to the set is a
walk of the edge subgraph.  It is stated as an existence because the walk of the subgraph carries
the membership proofs, which the ambient walk does not determine. -/
theorem nonempty_restrictEdges_of_forall_mem {S : Set E} {start finish : V}
    (walk : G.Walk start finish) (hmem : ∀ e ∈ walk.edges, e ∈ S) :
    Nonempty ((G.restrictEdges S).Walk start finish) := by
  induction walk with
  | nil => exact ⟨.nil⟩
  | concat edge walkSoFar ih =>
      obtain ⟨before⟩ := ih fun e he => hmem e (by simp [he])
      exact ⟨before.concat (G := G.restrictEdges S) ⟨edge, hmem edge (by simp)⟩⟩

/-- Reading a walk of an edge subgraph in the ambient graph preserves its length. -/
@[simp] theorem length_ofRestrictEdges {S : Set E} {start finish : V}
    (walk : (G.restrictEdges S).Walk start finish) :
    (ofRestrictEdges walk).length = walk.length := by
  rw [← edges_length, ← edges_length, edges_ofRestrictEdges, List.length_map]

end Walk

variable {G}

/-- **Backward walks of every length.**  If every vertex is the target of an edge with
property `P`, then every vertex ends a walk of any prescribed length all of whose edges have
property `P`: such edges can be prepended indefinitely. -/
theorem exists_walk_length_eq_forall_mem_edges (P : E → Prop)
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex ∧ P e) (count : ℕ) (vertex : V) :
    ∃ (start : V) (walk : G.Walk start vertex), walk.length = count ∧ ∀ e ∈ walk.edges, P e := by
  induction count generalizing vertex with
  | zero => exact ⟨vertex, .nil, rfl, by simp⟩
  | succ count ih =>
      obtain ⟨edge, htarget, hedge⟩ := hin vertex
      obtain ⟨start, walk, hlen, hall⟩ := ih (G.source edge)
      refine ⟨start, (walk.concat edge).castFinish htarget, by simp [hlen], fun e hmem => ?_⟩
      rw [Walk.edges_castFinish, Walk.edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact hall e hmem
      · exact hedge

/-- Every vertex is the endpoint of a walk with any prescribed number of edges, as soon as
every vertex has an incoming edge. -/
theorem exists_walk_length_eq (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex)
    (count : ℕ) (vertex : V) :
    ∃ (start : V) (walk : G.Walk start vertex), walk.length = count :=
  let ⟨start, walk, hlen, _⟩ := exists_walk_length_eq_forall_mem_edges (fun _ => True)
    (fun vertex => (hin vertex).imp fun _ h => ⟨h, trivial⟩) count vertex
  ⟨start, walk, hlen⟩

/-- **A vertex with an incoming edge that reaches every vertex has an outgoing edge.**  If no edge
left the vertex, no walk could leave it either, so the source of its incoming edge would be the
vertex itself.  On a strongly connected graph in which every vertex has an incoming edge, every
vertex therefore has an outgoing edge. -/
theorem exists_source_eq {vertex : V} (hin : ∃ e : E, G.target e = vertex)
    (hreach : ∀ finish : V, Nonempty (G.Walk vertex finish)) :
    ∃ e : E, G.source e = vertex := by
  by_contra hcon
  have hne : ∀ e : E, G.source e ≠ vertex := fun e he => hcon ⟨e, he⟩
  have hstay : ∀ {finish : V}, G.Walk vertex finish → finish = vertex := by
    intro finish walk
    induction walk with
    | nil => rfl
    | concat e _ ih => exact absurd ih (hne e)
  obtain ⟨e, he⟩ := hin
  obtain ⟨walk⟩ := hreach (G.source e)
  exact hne e (hstay walk)

end EdgeGraph

/-! ## Reachability scope

Walk-existence hypotheses consumed by the potential and normal-form theory.
In a directed graph a walk out to a vertex and a walk back from it are
independent, so both directions are demanded explicitly. -/

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- Every vertex is reachable from `base` by a directed walk. -/
def RootReaches (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ vertex : V, Nonempty (G.Walk base vertex)

/-- `base` reaches `vertex` and `vertex` reaches `base`.  Equivalently, the two
vertices lie in a common strongly connected component. -/
def LinkedTo (G : EdgeGraph V E) (base vertex : V) : Prop :=
  Nonempty (G.Walk base vertex) ∧ Nonempty (G.Walk vertex base)

/-- Every vertex is linked to `base`: the graph is strongly connected. -/
def IsStronglyConnectedAt (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ vertex : V, LinkedTo G base vertex

theorem IsStronglyConnectedAt.nonempty_walk {base : V}
    (hconnected : IsStronglyConnectedAt G base) (source target : V) :
    Nonempty (G.Walk source target) :=
  ⟨((hconnected source).2.some).append ((hconnected target).1.some)⟩

/-- The endpoints of every edge are linked to `base`.  This is all the
reachability the coboundary reconstruction consumes. -/
def EdgeEndpointsLinkedTo (G : EdgeGraph V E) (base : V) : Prop :=
  ∀ edge : E, LinkedTo G base (G.source edge) ∧ LinkedTo G base (G.target edge)

theorem IsStronglyConnectedAt.edgeEndpointsLinkedTo {base : V}
    (hconnected : IsStronglyConnectedAt G base) :
    EdgeEndpointsLinkedTo G base :=
  fun _ => ⟨hconnected _, hconnected _⟩

/-- Every vertex is linked to itself by the empty walk. -/
theorem LinkedTo.refl (vertex : V) : LinkedTo G vertex vertex :=
  ⟨⟨.nil⟩, ⟨.nil⟩⟩

/-- Linking is symmetric. -/
theorem LinkedTo.symm {first second : V} (h : LinkedTo G first second) :
    LinkedTo G second first :=
  ⟨h.2, h.1⟩

/-- Linking is transitive. -/
theorem LinkedTo.trans {first second third : V} (h₁ : LinkedTo G first second)
    (h₂ : LinkedTo G second third) : LinkedTo G first third :=
  ⟨⟨h₁.1.some.append h₂.1.some⟩, ⟨h₂.2.some.append h₁.2.some⟩⟩

/-- A closed walk stays inside the strongly connected component of its base: the source of
every traversed edge is linked to the base. -/
theorem linkedTo_source_of_mem_edges {base : V} (cycle : G.Walk base base) {edge : E}
    (hmem : edge ∈ cycle.edges) : LinkedTo G base (G.source edge) :=
  let split := cycle.vertexSplitAtSource edge hmem
  ⟨⟨split.before⟩, ⟨split.after⟩⟩

/-- A closed walk stays inside the strongly connected component of its base: the target of
every traversed edge is linked to the base. -/
theorem linkedTo_target_of_mem_edges {base : V} (cycle : G.Walk base base) {edge : E}
    (hmem : edge ∈ cycle.edges) : LinkedTo G base (G.target edge) :=
  let split := cycle.vertexSplitAtTarget edge hmem
  ⟨⟨split.before⟩, ⟨split.after⟩⟩

/-- Every edge lies on a closed walk: its target walks back to its source.  This is the
local reachability that component-wise coboundary reconstruction consumes; it imposes no
connectivity between different strongly connected components. -/
def HasEdgeReturns (G : EdgeGraph V E) : Prop :=
  ∀ edge : E, Nonempty (G.Walk (G.target edge) (G.source edge))

/-- With edge returns, the endpoints of every edge are linked to each other. -/
theorem HasEdgeReturns.linkedTo (hreturn : HasEdgeReturns G) (edge : E) :
    LinkedTo G (G.source edge) (G.target edge) :=
  ⟨⟨EdgeGraph.Walk.singleton edge⟩, hreturn edge⟩

/-- A graph whose every edge lies in the strongly connected component of `base` has edge
returns. -/
theorem EdgeEndpointsLinkedTo.hasEdgeReturns {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base) : HasEdgeReturns G :=
  fun edge => ((hlinked edge).2.symm.trans (hlinked edge).1).1

/-- In the symmetrization every edge returns along its opposite orientation. -/
theorem EdgeGraph.symmetrization_hasEdgeReturns : HasEdgeReturns G.symmetrization := by
  rintro ⟨edge, orientation⟩
  refine ⟨(EdgeGraph.Walk.singleton (G := G.symmetrization) (edge, !orientation)).castStart
    ?_ |>.castFinish ?_⟩ <;> cases orientation <;> rfl

end Maths
