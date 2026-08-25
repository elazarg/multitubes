/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Circulation

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn

/-!
# Eulerian trails and the realization of connected circulations

A trail is a walk that uses no edge twice. Inside a prescribed finite edge set, a longest
trail exists, and if the edge set is balanced then that longest trail is closed. If in
addition the edge set is weakly connected, Hierholzer's augmentation shows the longest closed
trail already uses every allowed edge: this is the directed Euler theorem for a finite set of
distinguishable edges.

A nonnegative integer multiplicity is turned into such an edge set by splitting each edge
into as many distinguishable tokens as its multiplicity prescribes. Balance and weak
connectivity lift to the token graph, the Euler theorem produces a closed trail through all
tokens, and forgetting token indices returns a closed walk whose edge multiplicities are
exactly the prescribed ones. Consequently every connected integer circulation is realized
exactly by a nonempty closed walk based at any vertex incident to its support, and that walk
carries the circulation's charge.

## Main definitions

* `DirectedTransport.EdgeGraph.Walk.IsTrailWithin`: a walk with pairwise distinct edges, all
  drawn from a prescribed finite edge set.
* `DirectedTransport.EdgeGraph.MultiplicityToken`: the distinguishable copies of an edge under
  a nonnegative integer multiplicity.
* `DirectedTransport.EdgeGraph.tokenGraph`: the multigraph on those tokens.
* `DirectedTransport.EdgeGraph.Walk.detokenize`: forget token indices along a walk.

## Main results

* `DirectedTransport.EdgeGraph.Walk.exists_maximalTrailWithin`: a longest allowed trail from a
  prescribed vertex exists.
* `DirectedTransport.EdgeGraph.Walk.maximalTrailWithin_isClosed`: in a balanced edge set a
  longest trail returns to its start.
* `DirectedTransport.EdgeGraph.Walk.exists_closedTrail_covering_of_balanced_connected`: the
  directed Euler theorem for a balanced, weakly connected finite edge set.
* `DirectedTransport.EdgeGraph.ConnectedIntegerCirculation.exists_closedWalk_exactMultiplicity_at`:
  every connected integer circulation is the exact edge count of a nonempty zero-charge closed
  walk based at any vertex incident to its support.

## Tags

Eulerian trail, Euler circuit, Hierholzer, circulation, directed multigraph
-/

@[expose] public section

namespace DirectedTransport

namespace EdgeGraph

universe uV uE uκ

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-! ### Trails inside a finite edge set -/

namespace Walk

variable {G} {start finish base : V}

/-- A trail whose distinct edge identities all belong to `allowed`. -/
def IsTrailWithin [DecidableEq E] (walk : G.Walk start finish)
    (allowed : Finset E) : Prop :=
  walk.edges.Nodup ∧ ∀ edge ∈ walk.edges, edge ∈ allowed

/-- Splicing a residual closed trail into a trail preserves edge uniqueness and the original
allowed-edge bound. -/
theorem VertexSplit.isTrailWithin_splice [DecidableEq E]
    {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex)
    (allowed : Finset E) (hwalk : walk.IsTrailWithin allowed)
    (hinserted : inserted.IsTrailWithin (allowed \ walk.edges.toFinset)) :
    (split.splice inserted).IsTrailWithin allowed := by
  have hdisjoint : walk.edges.Disjoint inserted.edges := by
    rw [List.disjoint_left]
    intro edge hedgeWalk hedgeInserted
    have hresidual := hinserted.2 edge hedgeInserted
    exact (Finset.mem_sdiff.mp hresidual).2 (List.mem_toFinset.mpr hedgeWalk)
  have hconcatNodup : (walk.edges ++ inserted.edges).Nodup :=
    List.nodup_append'.2 ⟨hwalk.1, hinserted.1, hdisjoint⟩
  refine ⟨(split.edges_splice_perm inserted).symm.nodup hconcatNodup, ?_⟩
  intro edge hedge
  have hmem : edge ∈ walk.edges ++ inserted.edges :=
    (split.edges_splice_perm inserted).mem_iff.mp hedge
  rcases List.mem_append.mp hmem with hedgeWalk | hedgeInserted
  · exact hwalk.2 edge hedgeWalk
  · exact (Finset.mem_sdiff.mp (hinserted.2 edge hedgeInserted)).1

/-- Splicing a nonempty closed walk strictly lengthens a walk. -/
theorem VertexSplit.length_lt_splice
    {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex)
    (hne : 0 < inserted.length) :
    walk.length < (split.splice inserted).length := by
  rw [split.length_splice]
  omega

/-- A trail uses at most as many edges as the allowed set contains. -/
theorem length_le_card_of_isTrailWithin [DecidableEq E]
    (walk : G.Walk start finish) (allowed : Finset E)
    (htrail : walk.IsTrailWithin allowed) :
    walk.length ≤ allowed.card := by
  have hsubset : walk.edges.toFinset ⊆ allowed := fun edge hedge =>
    htrail.2 edge (List.mem_toFinset.mp hedge)
  calc
    walk.length = walk.edges.length := walk.edges_length.symm
    _ = walk.edges.toFinset.card := (List.toFinset_card_of_nodup htrail.1).symm
    _ ≤ allowed.card := Finset.card_le_card hsubset

/-- A longest allowed trail from a prescribed starting vertex exists because no trail can use
more than `allowed.card` distinct edges. -/
theorem exists_maximalTrailWithin [DecidableEq E]
    (allowed : Finset E) (start : V) :
    ∃ (finish : V) (walk : G.Walk start finish),
      walk.IsTrailWithin allowed ∧
      ∀ (finish' : V) (other : G.Walk start finish'),
        other.IsTrailWithin allowed → other.length ≤ walk.length := by
  classical
  let feasible : ℕ → Prop := fun length =>
    ∃ (finish : V) (walk : G.Walk start finish),
      walk.IsTrailWithin allowed ∧ walk.length = length
  have hzero : feasible 0 :=
    ⟨start, Walk.nil, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨finish, walk, htrail, hlength⟩ :
      feasible (Nat.findGreatest feasible allowed.card) :=
    Nat.findGreatest_spec (Nat.zero_le _) hzero
  refine ⟨finish, walk, htrail, ?_⟩
  intro finish' other hother
  rw [hlength]
  exact Nat.le_findGreatest (other.length_le_card_of_isTrailWithin allowed hother)
    ⟨finish', other, hother, rfl⟩

/-- A trail uses each allowed edge at most as often as the allowed-edge indicator permits. -/
theorem edgeMultiplicity_le_edgeSetMultiplicity [DecidableEq E]
    (walk : G.Walk start finish) (allowed : Finset E)
    (htrail : walk.IsTrailWithin allowed) (edge : E) :
    walk.edgeMultiplicity edge ≤ edgeSetMultiplicity allowed edge := by
  by_cases hedge : edge ∈ walk.edges
  · have hallowed : edge ∈ allowed := htrail.2 edge hedge
    rw [(walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hedge]
    simp [edgeSetMultiplicity, hallowed]
  · have hzero : walk.edgeMultiplicity edge = 0 :=
      Nat.eq_zero_of_not_pos fun hpos =>
        hedge ((walk.edgeMultiplicity_pos_iff_mem_edges edge).1 hpos)
    simp [hzero]

/-- An edge unused by a trail contributes no multiplicity. -/
theorem edgeMultiplicity_eq_zero_of_notMem [DecidableEq E]
    (walk : G.Walk start finish) {edge : E} (hedge : edge ∉ walk.edges) :
    walk.edgeMultiplicity edge = 0 :=
  Nat.eq_zero_of_not_pos fun hpos =>
    hedge ((walk.edgeMultiplicity_pos_iff_mem_edges edge).1 hpos)

/-- A longest allowed trail cannot leave an unused allowed edge at its terminal vertex. -/
theorem edge_mem_of_maximalTrailWithin_of_source_eq
    [DecidableEq E] (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length)
    (edge : E) (hedgeAllowed : edge ∈ allowed)
    (hsource : G.source edge = finish) :
    edge ∈ walk.edges := by
  by_contra hedgeUnused
  have hlongerTrail : (Walk.concat walk edge hsource).IsTrailWithin allowed := by
    refine ⟨?_, ?_⟩
    · rw [edges_concat]
      exact List.nodup_append'.2 ⟨htrail.1, List.nodup_singleton edge,
        List.disjoint_singleton.mpr hedgeUnused⟩
    · intro candidate hcandidate
      rw [edges_concat, List.mem_append, List.mem_singleton] at hcandidate
      rcases hcandidate with hcandidate | rfl
      · exact htrail.2 candidate hcandidate
      · exact hedgeAllowed
  have hle := hmaximal _ (Walk.concat walk edge hsource) hlongerTrail
  rw [length_concat] at hle
  omega

/-- On outgoing edges of the terminal vertex, maximality identifies the trail multiplicity
with the allowed-edge indicator. -/
theorem outgoingMultiplicity_eq_edgeSetMultiplicity_of_maximal
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    G.outgoingMultiplicity walk.edgeMultiplicity finish =
      G.outgoingMultiplicity (edgeSetMultiplicity allowed) finish := by
  classical
  unfold outgoingMultiplicity
  refine Finset.sum_congr rfl ?_
  intro edge hedge
  have hsource : G.source edge = finish := (Finset.mem_filter.mp hedge).2
  by_cases hallowed : edge ∈ allowed
  · have hmem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
      allowed htrail hmaximal edge hallowed hsource
    rw [(walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hmem]
    simp [edgeSetMultiplicity, hallowed]
  · have hnotmem : edge ∉ walk.edges := fun hmem => hallowed (htrail.2 edge hmem)
    simp [edgeSetMultiplicity, hallowed, walk.edgeMultiplicity_eq_zero_of_notMem hnotmem]

/-- A trail never enters a vertex more often than the allowed edge set permits. -/
theorem incomingMultiplicity_le_edgeSetMultiplicity_of_trail
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed) (vertex : V) :
    G.incomingMultiplicity walk.edgeMultiplicity vertex ≤
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex := by
  classical
  unfold incomingMultiplicity
  exact Finset.sum_le_sum fun edge _ =>
    walk.edgeMultiplicity_le_edgeSetMultiplicity allowed htrail edge

/-- A maximal trail in a balanced allowed edge set returns to its start. -/
theorem maximalTrailWithin_isClosed
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk start finish) (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    finish = start := by
  by_contra hfinish
  have hflow := walk.edgeMultiplicity_flow_with_endpoints finish
  have hout := walk.outgoingMultiplicity_eq_edgeSetMultiplicity_of_maximal
    allowed htrail hmaximal
  have hin := walk.incomingMultiplicity_le_edgeSetMultiplicity_of_trail
    allowed htrail finish
  have hallowedBalance := hbalanced finish
  rw [if_pos rfl, if_neg (Ne.symm hfinish)] at hflow
  omega

/-- From any vertex with an allowed outgoing edge, a balanced finite edge set contains a
nonempty closed trail based at that vertex. -/
theorem exists_nonempty_closedTrailWithin_of_exists_outgoing
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (start : V)
    (houtgoing : ∃ edge, edge ∈ allowed ∧ G.source edge = start) :
    ∃ walk : G.Walk start start,
      walk.IsTrailWithin allowed ∧ 0 < walk.length := by
  obtain ⟨finish, walk, htrail, hmaximal⟩ :=
    Walk.exists_maximalTrailWithin (G := G) allowed start
  have hclosed : finish = start :=
    walk.maximalTrailWithin_isClosed allowed hbalanced htrail hmaximal
  subst hclosed
  obtain ⟨edge, hedgeAllowed, hsource⟩ := houtgoing
  have hedgeMem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
    allowed htrail hmaximal edge hedgeAllowed hsource
  refine ⟨walk, htrail, ?_⟩
  rw [← walk.edges_length, List.length_pos_iff]
  exact List.ne_nil_of_mem hedgeMem

/-- The allowed-edge indicator splits into the multiplicity of a trail and the indicator of
the residual edge set. -/
theorem edgeSetMultiplicity_decompose_trail
    [DecidableEq E] (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed) (edge : E) :
    edgeSetMultiplicity allowed edge =
      walk.edgeMultiplicity edge +
        edgeSetMultiplicity (allowed \ walk.edges.toFinset) edge := by
  by_cases hmem : edge ∈ walk.edges
  · have hallowed := htrail.2 edge hmem
    have hone := (walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hmem
    simp [edgeSetMultiplicity, hallowed, hmem, hone]
  · simp [edgeSetMultiplicity, hmem, walk.edgeMultiplicity_eq_zero_of_notMem hmem]

/-- Removing the edges of a closed allowed trail preserves balance of the remaining
distinguishable edge set. -/
theorem isBalancedEdgeSet_sdiff_closedTrail
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed) :
    G.IsBalancedEdgeSet (allowed \ walk.edges.toFinset) := by
  intro vertex
  have houtDecompose :
      G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex =
        G.outgoingMultiplicity walk.edgeMultiplicity vertex +
          G.outgoingMultiplicity
            (edgeSetMultiplicity (allowed \ walk.edges.toFinset)) vertex := by
    unfold outgoingMultiplicity
    simp_rw [edgeSetMultiplicity_decompose_trail allowed walk htrail]
    exact Finset.sum_add_distrib
  have hinDecompose :
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex =
        G.incomingMultiplicity walk.edgeMultiplicity vertex +
          G.incomingMultiplicity
            (edgeSetMultiplicity (allowed \ walk.edges.toFinset)) vertex := by
    unfold incomingMultiplicity
    simp_rw [edgeSetMultiplicity_decompose_trail allowed walk htrail]
    exact Finset.sum_add_distrib
  have hwalkBalance := walk.edgeMultiplicity_balanced vertex
  have hallowedBalance := hbalanced vertex
  omega

/-- If an unused allowed edge shares an endpoint with a closed trail, residual balance
supplies a nonempty residual closed trail at a vertex visited by the old trail. This is the
local augmentation step in Hierholzer's argument. -/
theorem exists_residualClosedTrailAt_of_sharesEndpoint
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed)
    (used unused : E) (hused : used ∈ walk.edges)
    (hunusedAllowed : unused ∈ allowed) (hunused : unused ∉ walk.edges)
    (hshares : G.SharesEndpoint used unused) :
    ∃ (vertex : V) (_split : walk.VertexSplit vertex)
      (inserted : G.Walk vertex vertex),
      inserted.IsTrailWithin (allowed \ walk.edges.toFinset) ∧
        0 < inserted.length := by
  set residual := allowed \ walk.edges.toFinset with hresidualDef
  have hresidualBalanced : G.IsBalancedEdgeSet residual :=
    walk.isBalancedEdgeSet_sdiff_closedTrail allowed hbalanced htrail
  have hunusedResidual : unused ∈ residual := by
    simp [hresidualDef, hunusedAllowed, hunused]
  /- In each case pick the vertex of `used` that `unused` meets, then follow a residual
  closed trail there; when `unused` only enters that vertex, balance supplies a residual
  edge leaving it. -/
  rcases hshares with hsourceSource | hsourceTarget | htargetSource | htargetTarget
  · obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.source used)
        ⟨unused, hunusedResidual, hsourceSource.symm⟩
    exact ⟨G.source used, walk.vertexSplitAtSource used hused, inserted, hinserted, hpositive⟩
  · obtain ⟨outgoing, houtgoingResidual, hsource⟩ :=
      IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := G) residual hresidualBalanced unused hunusedResidual
          (G.source used) hsourceTarget.symm
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.source used)
        ⟨outgoing, houtgoingResidual, hsource⟩
    exact ⟨G.source used, walk.vertexSplitAtSource used hused, inserted, hinserted, hpositive⟩
  · obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.target used)
        ⟨unused, hunusedResidual, htargetSource.symm⟩
    exact ⟨G.target used, walk.vertexSplitAtTarget used hused, inserted, hinserted, hpositive⟩
  · obtain ⟨outgoing, houtgoingResidual, hsource⟩ :=
      IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := G) residual hresidualBalanced unused hunusedResidual
          (G.target used) htargetTarget.symm
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.target used)
        ⟨outgoing, houtgoingResidual, hsource⟩
    exact ⟨G.target used, walk.vertexSplitAtTarget used hused, inserted, hinserted, hpositive⟩

/-- A longest nonempty closed trail in a walk-connected balanced support uses every allowed
distinguishable edge. -/
theorem all_edges_mem_of_maximal_closedTrailWithin_of_connected
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (hconnected : G.HasWalkConnectedSupport (edgeSetMultiplicity allowed))
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed)
    (hnonempty : 0 < walk.length)
    (hmaximal : ∀ (finish : V) (other : G.Walk base finish),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    ∀ edge, edge ∈ allowed → edge ∈ walk.edges := by
  intro unused hunusedAllowed
  by_contra hunused
  have hwalkEdges : walk.edges ≠ [] := walk.edges_ne_nil_of_length_pos hnonempty
  have husedMem : walk.edges.head hwalkEdges ∈ walk.edges := List.head_mem hwalkEdges
  have hmarked : ∃ edge, 0 < edgeSetMultiplicity allowed edge ∧
      edge ∈ walk.edges.toFinset :=
    ⟨walk.edges.head hwalkEdges,
      (edgeSetMultiplicity_pos_iff allowed _).2 (htrail.2 _ husedMem),
      List.mem_toFinset.mpr husedMem⟩
  have hunmarked : ∃ edge, 0 < edgeSetMultiplicity allowed edge ∧
      edge ∉ walk.edges.toFinset :=
    ⟨unused, (edgeSetMultiplicity_pos_iff allowed unused).2 hunusedAllowed, by simpa using hunused⟩
  obtain ⟨usedBoundary, unusedBoundary, -, husedBoundary,
    hunusedBoundaryPositive, hunusedBoundary, hshares⟩ :=
      HasWalkConnectedSupport.exists_boundary (G := G)
        (edgeSetMultiplicity allowed) hconnected walk.edges.toFinset hmarked hunmarked
  obtain ⟨vertex, split, inserted, hinserted, hinsertedPositive⟩ :=
    walk.exists_residualClosedTrailAt_of_sharesEndpoint allowed hbalanced htrail
      usedBoundary unusedBoundary (List.mem_toFinset.mp husedBoundary)
      ((edgeSetMultiplicity_pos_iff allowed unusedBoundary).1 hunusedBoundaryPositive)
      (by simpa using hunusedBoundary) hshares
  have hle := hmaximal base (split.splice inserted)
    (split.isTrailWithin_splice inserted allowed htrail hinserted)
  have hlt := split.length_lt_splice inserted hinsertedPositive
  omega

/-- **Directed Euler theorem** for a finite set of distinguishable edge tokens: a nonempty
walk-connected balanced support has a closed trail using every allowed token exactly once.
The base may be any vertex with an allowed outgoing token. -/
theorem exists_closedTrail_covering_of_balanced_connected
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (hconnected : G.HasWalkConnectedSupport (edgeSetMultiplicity allowed))
    (base : V) (houtgoing : ∃ edge, edge ∈ allowed ∧ G.source edge = base) :
    ∃ walk : G.Walk base base,
      walk.IsTrailWithin allowed ∧
      ∀ edge, edge ∈ walk.edges ↔ edge ∈ allowed := by
  obtain ⟨finish, walk, htrail, hmaximal⟩ :=
    Walk.exists_maximalTrailWithin (G := G) allowed base
  have hclosed : finish = base :=
    walk.maximalTrailWithin_isClosed allowed hbalanced htrail hmaximal
  subst hclosed
  obtain ⟨initialEdge, hinitialAllowed, hinitialSource⟩ := houtgoing
  have hinitialMem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
    allowed htrail hmaximal initialEdge hinitialAllowed hinitialSource
  have hnonempty : 0 < walk.length := by
    rw [← walk.edges_length, List.length_pos_iff]
    exact List.ne_nil_of_mem hinitialMem
  have hcover := walk.all_edges_mem_of_maximal_closedTrailWithin_of_connected
    allowed hbalanced hconnected htrail hnonempty hmaximal
  exact ⟨walk, htrail, fun edge => ⟨htrail.2 edge, hcover edge⟩⟩

end Walk

/-! ### Distinguishable copies of an edge -/

/-- Distinguishable copies of an edge under a finite integer multiplicity. -/
abbrev MultiplicityToken (multiplicity : E → ℕ) :=
  Σ edge : E, Fin (multiplicity edge)

namespace MultiplicityToken

/-- The original edge a token is a copy of. -/
def edge {multiplicity : E → ℕ} (token : MultiplicityToken multiplicity) : E :=
  token.1

/-- Counting tokens over a predicate on their underlying edges sums the multiplicity. -/
theorem card_filter_edge_eq_sum_filter [Fintype E]
    (multiplicity : E → ℕ) (predicate : E → Prop) [DecidablePred predicate] :
    (Finset.univ.filter
        (fun token : MultiplicityToken multiplicity => predicate token.edge)).card =
      ∑ edge with predicate edge, multiplicity edge := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [show (∑ token ∈ (Finset.univ : Finset (MultiplicityToken multiplicity)),
      if predicate token.edge then 1 else 0) =
      ∑ token : MultiplicityToken multiplicity,
        if predicate token.edge then 1 else 0 from rfl]
  rw [Fintype.sum_sigma]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro edge _
  by_cases hedge : predicate edge <;> simp [MultiplicityToken.edge, hedge]

/-- All distinguishable copies of one original edge. -/
def listForEdge (multiplicity : E → ℕ) (edge : E) :
    List (MultiplicityToken multiplicity) :=
  List.ofFn fun index : Fin (multiplicity edge) => ⟨edge, index⟩

/-- An edge of positive multiplicity has at least one copy. -/
theorem listForEdge_ne_nil_of_pos (multiplicity : E → ℕ) (edge : E)
    (hpositive : 0 < multiplicity edge) :
    listForEdge multiplicity edge ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  simp only [listForEdge, List.length_ofFn, List.length_nil] at hlength
  omega

/-- Every copy in `listForEdge multiplicity edge` is a copy of `edge`. -/
theorem edge_eq_of_mem_listForEdge {multiplicity : E → ℕ} {edge : E}
    {token : MultiplicityToken multiplicity}
    (hmem : token ∈ listForEdge multiplicity edge) :
    token.edge = edge := by
  rw [listForEdge, List.mem_ofFn'] at hmem
  obtain ⟨index, rfl⟩ := hmem
  rfl

/-- A token occurs among the copies of its own underlying edge. -/
theorem self_mem_listForEdge {multiplicity : E → ℕ}
    (token : MultiplicityToken multiplicity) :
    token ∈ listForEdge multiplicity token.edge := by
  obtain ⟨edge, index⟩ := token
  rw [listForEdge, List.mem_ofFn']
  exact ⟨index, rfl⟩

/-- The copies of a given edge are exactly as many as its multiplicity. -/
theorem sum_ite_edge_eq (multiplicity : E → ℕ) [Fintype E] [DecidableEq E] (edge : E) :
    (∑ token : MultiplicityToken multiplicity,
      if token.edge = edge then 1 else 0) = multiplicity edge := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single edge]
  · simp [MultiplicityToken.edge]
  · intro other _ hne
    simp [MultiplicityToken.edge, hne]
  · simp

end MultiplicityToken

/-- Expand an integer edge multiplicity into a directed graph of distinguishable edge
tokens. -/
def tokenGraph (multiplicity : E → ℕ) :
    EdgeGraph V (MultiplicityToken multiplicity) where
  source token := G.source token.edge
  target token := G.target token.edge

@[simp] theorem tokenGraph_source (multiplicity : E → ℕ)
    (token : MultiplicityToken multiplicity) :
    (G.tokenGraph multiplicity).source token = G.source token.edge := rfl

@[simp] theorem tokenGraph_target (multiplicity : E → ℕ)
    (token : MultiplicityToken multiplicity) :
    (G.tokenGraph multiplicity).target token = G.target token.edge := rfl

/-- Outgoing token counts recover the original outgoing multiplicity. -/
theorem tokenGraph_outgoingMultiplicity_univ
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) :
    (G.tokenGraph multiplicity).outgoingMultiplicity
        (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
      G.outgoingMultiplicity multiplicity vertex := by
  unfold outgoingMultiplicity
  rw [← MultiplicityToken.card_filter_edge_eq_sum_filter multiplicity
      fun edge => G.source edge = vertex,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun token _ => ?_
  simp only [tokenGraph_source]
  by_cases hsource : G.source token.edge = vertex
  · simp [hsource, edgeSetMultiplicity]
  · simp [hsource]

/-- Incoming token counts recover the original incoming multiplicity. -/
theorem tokenGraph_incomingMultiplicity_univ
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) :
    (G.tokenGraph multiplicity).incomingMultiplicity
        (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
      G.incomingMultiplicity multiplicity vertex := by
  unfold incomingMultiplicity
  rw [← MultiplicityToken.card_filter_edge_eq_sum_filter multiplicity
      fun edge => G.target edge = vertex,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun token _ => ?_
  simp only [tokenGraph_target]
  by_cases htarget : G.target token.edge = vertex
  · simp [htarget, edgeSetMultiplicity]
  · simp [htarget]

/-- A balanced multiplicity expands to a balanced set of all its tokens. -/
theorem tokenGraph_univ_balanced_of_balanced
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ)
    (hbalanced : ∀ vertex,
      G.outgoingMultiplicity multiplicity vertex =
        G.incomingMultiplicity multiplicity vertex) :
    (G.tokenGraph multiplicity).IsBalancedEdgeSet Finset.univ := by
  intro vertex
  rw [G.tokenGraph_outgoingMultiplicity_univ multiplicity vertex,
    G.tokenGraph_incomingMultiplicity_univ multiplicity vertex]
  exact hbalanced vertex

/-- Copies of a single edge form a chain in the token incidence graph. -/
theorem tokenGraph_listForEdge_isChain (multiplicity : E → ℕ) (edge : E) :
    (MultiplicityToken.listForEdge multiplicity edge).IsChain
      (G.tokenGraph multiplicity).SharesEndpoint := by
  rw [MultiplicityToken.listForEdge, List.isChain_ofFn]
  intro index hindex
  exact Or.inl rfl

/-- Copies of edges that share an endpoint themselves share an endpoint. -/
theorem tokenGraph_sharesEndpoint_of_mem_listForEdge
    (multiplicity : E → ℕ) {first second : E}
    (hshares : G.SharesEndpoint first second)
    {firstToken secondToken : MultiplicityToken multiplicity}
    (hfirst : firstToken ∈ MultiplicityToken.listForEdge multiplicity first)
    (hsecond : secondToken ∈ MultiplicityToken.listForEdge multiplicity second) :
    (G.tokenGraph multiplicity).SharesEndpoint firstToken secondToken := by
  have hfirstEdge := MultiplicityToken.edge_eq_of_mem_listForEdge hfirst
  have hsecondEdge := MultiplicityToken.edge_eq_of_mem_listForEdge hsecond
  simpa [SharesEndpoint, hfirstEdge, hsecondEdge] using hshares

/-- A chain of blocks, each nonempty and internally chained, with all cross pairs related, is
itself a chain. -/
private theorem isChain_flatMap_of_nonempty
    {α β : Type*} (relation : α → α → Prop)
    (liftedRelation : β → β → Prop) (block : α → List β)
    (items : List α) (hitems : items.IsChain relation)
    (hnonempty : ∀ item ∈ items, block item ≠ [])
    (hblock : ∀ item ∈ items, (block item).IsChain liftedRelation)
    (hcross : ∀ {first second}, relation first second →
      ∀ x ∈ block first, ∀ y ∈ block second, liftedRelation x y) :
    (items.flatMap block).IsChain liftedRelation := by
  induction items with
  | nil => exact List.isChain_nil
  | cons first tail ih =>
      match tail with
      | [] => simpa using hblock first (by simp)
      | second :: rest =>
          have hrelation : relation first second := (List.isChain_cons_cons.mp hitems).1
          have htailChain : (second :: rest).IsChain relation :=
            (List.isChain_cons_cons.mp hitems).2
          have hsecondNonempty : block second ≠ [] := hnonempty second (by simp)
          have htailResult :
              ((second :: rest).flatMap block).IsChain liftedRelation :=
            ih htailChain (fun item hitem => hnonempty item (by simp [hitem]))
              (fun item hitem => hblock item (by simp [hitem]))
          rw [List.flatMap_cons]
          refine (hblock first (by simp)).append htailResult ?_
          intro x hx y hy
          have hyInHead : y ∈ (block second).head? := by
            rw [List.flatMap_cons, List.head?_append_of_ne_nil _ hsecondNonempty] at hy
            exact hy
          exact hcross hrelation x (List.mem_of_mem_getLast? hx) y
            (List.mem_of_mem_head? hyInHead)

/-- Weak connectivity of the original positive support lifts to weak connectivity of all
distinguishable multiplicity tokens. -/
theorem tokenGraph_univ_hasWalkConnectedSupport
    [Fintype E] [DecidableEq E] (multiplicity : E → ℕ)
    (hnonzero : ∃ edge, 0 < multiplicity edge)
    (hconnected : G.HasWalkConnectedSupport multiplicity) :
    (G.tokenGraph multiplicity).HasWalkConnectedSupport
      (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) := by
  obtain ⟨traversal, -, hsupport, hchain⟩ := hconnected
  set block : E → List (MultiplicityToken multiplicity) :=
    MultiplicityToken.listForEdge multiplicity with hblockDef
  have htokenChain :
      (traversal.flatMap block).IsChain (G.tokenGraph multiplicity).SharesEndpoint :=
    isChain_flatMap_of_nonempty G.SharesEndpoint
      (G.tokenGraph multiplicity).SharesEndpoint block traversal hchain
      (fun edge hedge => MultiplicityToken.listForEdge_ne_nil_of_pos multiplicity edge
        ((hsupport edge).1 hedge))
      (fun edge _ => G.tokenGraph_listForEdge_isChain multiplicity edge)
      fun hshares firstToken hfirst secondToken hsecond =>
        G.tokenGraph_sharesEndpoint_of_mem_listForEdge multiplicity hshares hfirst hsecond
  have hall : ∀ token : MultiplicityToken multiplicity, token ∈ traversal.flatMap block :=
    fun token => List.mem_flatMap.mpr
      ⟨token.edge, (hsupport token.edge).2 (Nat.zero_lt_of_lt token.2.isLt),
        MultiplicityToken.self_mem_listForEdge token⟩
  have htokenNonempty : traversal.flatMap block ≠ [] := by
    obtain ⟨edge, hpositive⟩ := hnonzero
    exact List.ne_nil_of_mem (hall ⟨edge, ⟨0, hpositive⟩⟩)
  refine ⟨traversal.flatMap block, htokenNonempty, fun token => ⟨fun _ => ?_, fun _ => ?_⟩,
    htokenChain⟩
  · exact (edgeSetMultiplicity_pos_iff Finset.univ token).2 (Finset.mem_univ token)
  · exact hall token

/-! ### Forgetting token indices -/

namespace Walk

variable {G} {start finish : V}

/-- Forget token indices in a typed walk through the multiplicity-expanded graph. -/
def detokenize (multiplicity : E → ℕ) {start : V} : {finish : V} →
    (G.tokenGraph multiplicity).Walk start finish → G.Walk start finish
  | _, .nil => .nil
  | _, .concat walkSoFar token legal =>
      (Walk.concat (detokenize multiplicity walkSoFar) token.edge
        ((G.tokenGraph_source multiplicity token).symm.trans legal)).castFinish
          (G.tokenGraph_target multiplicity token).symm

@[simp] theorem edges_detokenize (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).edges = walk.edges.map MultiplicityToken.edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar token legal ih =>
      rw [detokenize, edges_castFinish, edges_concat, edges_concat, ih, List.map_append]
      rfl

@[simp] theorem length_detokenize (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).length = walk.length := by
  rw [← Walk.edges_length, ← Walk.edges_length, edges_detokenize, List.length_map]

@[simp] theorem charge_detokenize {κ : Type uκ}
    (multiplicity : E → ℕ) (edgeCharge : E → κ → ℤ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).charge edgeCharge =
      walk.charge fun token => edgeCharge token.edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar token legal ih =>
      rw [detokenize, charge_castFinish, charge_concat, charge_concat, ih]

/-- Counting the values of an injectively indexed list is a sum of indicators. -/
private theorem count_map_eq_sum_toFinset_ite
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (mapValue : α → β) (items : List α) (hnodup : items.Nodup) (value : β) :
    (items.map mapValue).count value =
      ∑ item ∈ items.toFinset, if mapValue item = value then 1 else 0 := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.count_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hnodup.1), ih hnodup.2]
      by_cases hvalue : mapValue first = value
      · simp only [hvalue, beq_self_eq_true, if_true]
        omega
      · simp [hvalue, beq_iff_eq]

/-- A token trail containing every distinguishable token detokenizes to the prescribed
original integer edge multiplicity. -/
theorem edgeMultiplicity_detokenize_of_nodup_all
    [Finite E] [DecidableEq E] (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish)
    (hnodup : walk.edges.Nodup)
    (hall : ∀ token : MultiplicityToken multiplicity, token ∈ walk.edges)
    (edge : E) :
    (walk.detokenize multiplicity).edgeMultiplicity edge = multiplicity edge := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  rw [(walk.detokenize multiplicity).edgeMultiplicity_eq_count, edges_detokenize,
    count_map_eq_sum_toFinset_ite MultiplicityToken.edge walk.edges hnodup edge]
  have hfinset : walk.edges.toFinset = Finset.univ := by
    ext token
    simp [hall token]
  rw [hfinset]
  exact MultiplicityToken.sum_ite_edge_eq multiplicity edge

end Walk

/-! ### Exact realization of a connected circulation -/

namespace ConnectedIntegerCirculation

variable {G} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- A connected integer circulation has an exact closed-walk realization at any incident
support vertex. Integer multiplicities are expanded to distinguishable tokens, traversed by
the finite directed Euler theorem, and then detokenized. -/
theorem exists_closedWalk_exactMultiplicity_at
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (circulation : G.ConnectedIntegerCirculation edgeCharge) (base : V)
    (hbase : ∃ edge, 0 < circulation.multiplicity edge ∧
      (G.source edge = base ∨ G.target edge = base)) :
    ∃ walk : G.Walk base base,
      0 < walk.length ∧
      (∀ edge, walk.edgeMultiplicity edge = circulation.multiplicity edge) ∧
      walk.charge edgeCharge = 0 := by
  set multiplicity := circulation.multiplicity with hmultiplicityDef
  set tokenG := G.tokenGraph multiplicity with htokenGDef
  have htokenBalanced :
      tokenG.IsBalancedEdgeSet (Finset.univ : Finset (MultiplicityToken multiplicity)) :=
    G.tokenGraph_univ_balanced_of_balanced multiplicity circulation.balanced
  have htokenConnected : tokenG.HasWalkConnectedSupport
      (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) :=
    G.tokenGraph_univ_hasWalkConnectedSupport multiplicity
      circulation.nonzero circulation.connected
  have htokenOutgoing : ∃ token : MultiplicityToken multiplicity,
      token ∈ (Finset.univ : Finset (MultiplicityToken multiplicity)) ∧
        tokenG.source token = base := by
    obtain ⟨edge, hpositive, hsource | htarget⟩ := hbase
    · exact ⟨⟨edge, ⟨0, hpositive⟩⟩, Finset.mem_univ _, hsource⟩
    · exact IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := tokenG) Finset.univ htokenBalanced ⟨edge, ⟨0, hpositive⟩⟩
          (Finset.mem_univ _) base htarget
  obtain ⟨tokenWalk, htokenTrail, htokenCover⟩ :=
    Walk.exists_closedTrail_covering_of_balanced_connected
      (G := tokenG) Finset.univ htokenBalanced htokenConnected base htokenOutgoing
  refine ⟨tokenWalk.detokenize multiplicity, ?_, ?_, ?_⟩
  · rw [Walk.length_detokenize, ← tokenWalk.edges_length, List.length_pos_iff]
    obtain ⟨edge, hpositive⟩ := circulation.nonzero
    exact List.ne_nil_of_mem ((htokenCover ⟨edge, ⟨0, hpositive⟩⟩).2 (Finset.mem_univ _))
  · exact fun edge => tokenWalk.edgeMultiplicity_detokenize_of_nodup_all multiplicity
      htokenTrail.1 (fun token => (htokenCover token).2 (Finset.mem_univ token)) edge
  · have hexact : ∀ edge, (tokenWalk.detokenize multiplicity).edgeMultiplicity edge =
        circulation.multiplicity edge :=
      fun edge => tokenWalk.edgeMultiplicity_detokenize_of_nodup_all multiplicity
        htokenTrail.1 (fun token => (htokenCover token).2 (Finset.mem_univ token)) edge
    calc
      (tokenWalk.detokenize multiplicity).charge edgeCharge =
          G.multiplicityCharge edgeCharge
            (tokenWalk.detokenize multiplicity).edgeMultiplicity :=
        ((tokenWalk.detokenize multiplicity).multiplicityCharge_edgeMultiplicity
          edgeCharge).symm
      _ = G.multiplicityCharge edgeCharge circulation.multiplicity := by
        congr 1
        funext edge
        exact hexact edge
      _ = 0 := circulation.charge_zero

end ConnectedIntegerCirculation

end EdgeGraph

end DirectedTransport
