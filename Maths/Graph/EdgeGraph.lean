/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.List.Chain

import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Directed multigraphs with edge identities and their typed walks

A directed multigraph is represented by a vertex type, an edge type, and source and target
maps. Edges are data rather than mere related vertex pairs, so parallel edges retain their
identities.

`EdgeGraph.Walk G start finish` is an endpoint-indexed finite walk. It stores the edge
identities in chronological order and makes endpoint compatibility part of the type. This
file supplies the reusable finite-walk calculus: length, edge and visited-vertex lists,
endpoint facts, concatenation, singleton walks, edge multiplicity, splitting at an edge,
and splicing at a visited vertex.

The file deliberately assigns no labels or weights to edges. Transport, charges, discrepancy,
circulations, and application-specific semantics belong in files that import this one.

## Main definitions

* `Maths.EdgeGraph`: a directed multigraph as vertex and edge types with `source`
  and `target` maps.
* `Maths.EdgeGraph.Walk`: an endpoint-indexed finite walk.
* `Maths.EdgeGraph.Walk.edges`, `length`, `visited`, `edgeMultiplicity`: the
  basic measurements of a walk.
* `Maths.EdgeGraph.Walk.append`, `singleton`, `castFinish`: walk constructors.
* `Maths.EdgeGraph.Walk.VertexSplit`: a witness that a walk visits a vertex,
  together with `splice` for inserting a closed walk there.
* `Maths.LinkedTo`, `Maths.IsStronglyConnectedAt`, and
  `Maths.EdgeEndpointsLinkedTo`: the walk-existence reachability scopes
  consumed by the potential and normal-form theory.

## Main results

* `Maths.EdgeGraph.Walk.edges_isChain`: consecutive edges have matching endpoints.
* `Maths.EdgeGraph.Walk.edges_nodup_of_visited_nodup`: pairwise distinct visited
  vertices force pairwise distinct edges.
* `Maths.EdgeGraph.Walk.exists_splitAtEdge`: a walk splits at any edge it uses.
* `Maths.EdgeGraph.Walk.exists_split_of_length_le`: a walk splits after any
  prescribed number of its edges.
* `Maths.EdgeGraph.Walk.exists_split_of_mem_visited`: a walk splits at any vertex
  it visits.
* `Maths.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`: a walk revisiting a
  vertex contains a nonempty closed subwalk.
* `Maths.EdgeGraph.Walk.VertexSplit.length_splice`: splicing adds lengths.

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

/-- A finite directed walk, retaining the list of edge identities. -/
inductive Walk (start : V) : V → Type (max uV uE)
  | /-- The empty walk at `start`. -/
    nil : Walk start start
  | /-- Extend a walk by one edge whose source is the current endpoint. -/
    concat {finish : V} (walkSoFar : Walk start finish) (edge : E)
      (legal : G.source edge = finish) : Walk start (G.target edge)

namespace Walk

variable {G} {start finish middle : V}

/-- Number of edges in a finite walk. -/
def length {start : V} : {finish : V} → G.Walk start finish → ℕ
  | _, .nil => 0
  | _, .concat walkSoFar _ _ => walkSoFar.length + 1

/-- Edge identities in chronological order. -/
def edges {start : V} : {finish : V} → G.Walk start finish → List E
  | _, .nil => []
  | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]

@[simp] theorem length_nil : (Walk.nil : G.Walk start start).length = 0 := rfl

@[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1 := rfl

@[simp] theorem edges_nil : (Walk.nil : G.Walk start start).edges = [] := rfl

@[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge] := rfl

@[simp] theorem edges_length (walk : G.Walk start finish) :
    walk.edges.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [edges, length, ih]

/-- The vertices visited by a typed walk, in chronological order, starting with
its initial vertex.  A walk with `n` edges visits `n + 1` vertices. -/
def visited {start : V} : {finish : V} → G.Walk start finish → List V
  | _, .nil => [start]
  | _, .concat walkSoFar edge _ => walkSoFar.visited ++ [G.target edge]

@[simp] theorem visited_nil : (Walk.nil : G.Walk start start).visited = [start] := rfl

@[simp] theorem visited_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).visited = walkSoFar.visited ++ [G.target edge] := rfl

@[simp] theorem length_visited (walk : G.Walk start finish) :
    walk.visited.length = walk.length + 1 := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih => simp [ih]

/-- An edge used by a walk has its target among the walk's visited vertices. -/
theorem mem_visited_of_mem_edges (walk : G.Walk start finish)
    {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ walk.visited := by
  induction walk with
  | nil => simp at hmem
  | concat walkSoFar e legal ih =>
      rw [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rw [visited_concat]
      rcases hmem with hmem | rfl
      · exact List.mem_append_left _ (ih hmem)
      · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A walk whose visited vertices are pairwise distinct traverses pairwise
distinct edges: a repeated edge would revisit its target vertex.  This lets
walk bounds count edges instead of vertices. -/
theorem edges_nodup_of_visited_nodup (walk : G.Walk start finish)
    (hnd : walk.visited.Nodup) : walk.edges.Nodup := by
  induction walk with
  | nil => simp
  | concat walkSoFar e legal ih =>
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
  | concat walkSoFar edge legal ih =>
      rw [visited_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨before, after, hedges⟩ := ih hmem
        refine ⟨before, after.concat edge legal, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]
      · subst hmem
        exact ⟨walkSoFar.concat edge legal, .nil, by simp⟩

/-- A walk that revisits a vertex contains a nonempty closed subwalk. -/
theorem exists_closedSubwalk_of_not_nodup
    (walk : G.Walk start finish) (hdup : ¬ walk.visited.Nodup) :
    ∃ (vertex : V) (before : G.Walk start vertex) (cycle : G.Walk vertex vertex)
      (after : G.Walk vertex finish),
      0 < cycle.length ∧
        walk.edges = before.edges ++ cycle.edges ++ after.edges := by
  induction walk with
  | nil => exact absurd (List.nodup_singleton start) hdup
  | concat walkSoFar edge legal ih =>
      rw [visited_concat] at hdup
      by_cases hmem : G.target edge ∈ walkSoFar.visited
      · obtain ⟨before, after, hedges⟩ :=
          walkSoFar.exists_split_of_mem_visited hmem
        refine ⟨G.target edge, before, after.concat edge legal, .nil, by simp, ?_⟩
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
        refine ⟨vertex, before, cycle, after.concat edge legal, hlen, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]

/-- Consecutive edge identities in a typed walk have matching endpoints. -/
theorem edges_isChain (walk : G.Walk start finish) :
    walk.edges.IsChain fun first second => G.target first = G.source second := by
  induction walk with
  | nil => exact List.isChain_nil
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => exact List.isChain_singleton edge
      | @concat previous walkBefore finalEdge finalLegal =>
          rw [edges, List.isChain_append]
          refine ⟨ih, List.isChain_singleton edge, ?_⟩
          simp [edges, legal]

/-- The first edge of a nonempty typed walk starts at its initial vertex, stated for
`List.head?` so that no nonemptiness proof appears in the statement. -/
theorem source_of_mem_head? (walk : G.Walk start finish) {edge : E}
    (hhead : walk.edges.head? = some edge) : G.source edge = start := by
  induction walk with
  | nil => simp [edges] at hhead
  | @concat middle walkSoFar finalEdge legal ih =>
      cases walkSoFar with
      | nil =>
          rw [edges_concat, edges_nil, List.nil_append, List.head?_cons,
            Option.some_inj] at hhead
          exact hhead ▸ legal
      | @concat previous walkBefore edge' legal' =>
          have hne : (walkBefore.concat edge' legal').edges ≠ [] := by simp [edges]
          rw [edges_concat, List.head?_append_of_ne_nil _ hne] at hhead
          exact ih hhead

/-- The first edge of a nonempty typed walk starts at its initial vertex. -/
theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.source (walk.edges.head hne) = start :=
  source_of_mem_head? walk (List.head?_eq_some_head hne)

/-- The last edge of a nonempty typed walk ends at its terminal vertex. -/
theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.target (walk.edges.getLast hne) = finish := by
  cases walk with
  | nil => simp [edges] at hne
  | concat walkSoFar edge legal => simp [edges]

/-- Multiplicity of an edge identity in a finite walk. -/
def edgeMultiplicity [DecidableEq E] {start : V} :
    {finish : V} → G.Walk start finish → E → ℕ
  | _, .nil => fun _ => 0
  | _, .concat walkSoFar edge _ => fun candidate =>
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0

@[simp] theorem edgeMultiplicity_nil [DecidableEq E] (candidate : E) :
    (Walk.nil : G.Walk start start).edgeMultiplicity candidate = 0 := rfl

@[simp] theorem edgeMultiplicity_concat [DecidableEq E]
    (walkSoFar : G.Walk start finish) (edge candidate : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edgeMultiplicity candidate =
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0 := rfl

theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges := by
  induction walk with
  | nil => simp [edgeMultiplicity, edges]
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge <;> simp [edgeMultiplicity, edges, ih, h]

theorem edgeMultiplicity_eq_count [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    walk.edgeMultiplicity edge = walk.edges.count edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge
      · subst edge
        simp [edgeMultiplicity, edges, List.count_append, ih]
      · simp [edgeMultiplicity, edges, List.count_append, ih, h, eq_comm]

theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges := by
  rw [walk.edgeMultiplicity_eq_count]
  exact ⟨fun h => List.count_pos_iff.mp (by omega),
    fun h => List.count_eq_one_of_mem hnodup h⟩

theorem edgeMultiplicity_le_one [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge ≤ 1 := by
  rw [walk.edgeMultiplicity_eq_count]
  exact (List.nodup_iff_count_le_one.mp hnodup) edge

/-- Change only the terminal index of a typed walk along an equality. -/
def castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') : G.Walk start finish' :=
  hfinish ▸ walk

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

/-- Concatenate two typed walks at their common endpoint. -/
def append {start middle : V} (first : G.Walk start middle) :
    {finish : V} → G.Walk middle finish → G.Walk start finish
  | _, .nil => first
  | _, .concat second edge legal => .concat (first.append second) edge legal

@[simp] theorem append_nil (first : G.Walk start middle) :
    first.append (.nil : G.Walk middle middle) = first := rfl

@[simp] theorem append_concat (first : G.Walk start middle)
    (second : G.Walk middle finish) (edge : E) (legal : G.source edge = finish) :
    first.append (.concat second edge legal) = .concat (first.append second) edge legal := rfl

@[simp] theorem edges_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).edges = first.edges ++ second.edges := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, List.append_assoc]

@[simp] theorem length_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, Nat.add_assoc]

/-- The one-edge walk carrying a prescribed edge identity. -/
def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) :=
  .concat .nil edge rfl

@[simp] theorem edges_singleton (edge : E) : (singleton (G := G) edge).edges = [edge] := rfl

@[simp] theorem length_singleton (edge : E) : (singleton (G := G) edge).length = 1 := rfl

/-- A typed decomposition of a walk at an occurrence of an edge. -/
theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E) (hmem : edge ∈ walk.edges) :
    ∃ (before : G.Walk start (G.source edge)) (after : G.Walk (G.target edge) finish),
      walk.edges = before.edges ++ edge :: after.edges := by
  induction walk with
  | nil => simp at hmem
  | @concat middle walkSoFar finalEdge legal ih =>
      simp only [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | heq
      · obtain ⟨before, after, hsplit⟩ := ih hmem
        refine ⟨before, after.concat finalEdge legal, ?_⟩
        simp only [edges_concat, hsplit]
        simp [List.append_assoc]
      · subst finalEdge
        exact ⟨walkSoFar.castFinish legal.symm, .nil, by simp⟩

/-- A walk splits after any prescribed number of its edges. -/
theorem exists_split_of_length_le {start finish : V} (walk : G.Walk start finish)
    {count : ℕ} (hcount : count ≤ walk.length) :
    ∃ (middle : V) (before : G.Walk start middle) (after : G.Walk middle finish),
      before.length = count ∧ walk.edges = before.edges ++ after.edges := by
  induction walk with
  | nil =>
      have hzero : count = 0 := Nat.le_zero.mp hcount
      exact ⟨start, .nil, .nil, hzero.symm ▸ rfl, by simp⟩
  | @concat middle walkSoFar edge legal ih =>
      rcases Nat.lt_or_ge count (walkSoFar.length + 1) with hlt | hge
      · obtain ⟨mid, before, after, hlen, hedges⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨mid, before, after.concat edge legal, hlen, by
          simp only [edges_concat, hedges, List.append_assoc]⟩
      · have hEq : count = walkSoFar.length + 1 := by
          simp only [length_concat] at hcount
          omega
        exact ⟨_, walkSoFar.concat edge legal, .nil, by simp [hEq], by simp⟩

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
  refine ⟨⟨before.append (singleton (G := G) edge), after, ?_⟩⟩
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

end Walk

end EdgeGraph

/-! ## Reachability scope

Walk-existence hypotheses consumed by the potential and normal-form theory.
In a directed graph a walk out to a vertex and a walk back from it are
independent, so both directions are demanded explicitly. -/

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

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

end Maths
