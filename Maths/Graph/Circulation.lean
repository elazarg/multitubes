/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.Algebra.BigOperators.Pi

public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Walk multiplicities as circulations

A finite walk of an `Maths.EdgeGraph` records how often it uses each edge, and
that edge multiplicity vector is a flow: at every vertex, the multiplicity leaving the vertex
matches the multiplicity entering it, up to a correction at the two endpoints of the walk. For
a closed walk the correction cancels and the multiplicity vector is an honest circulation.

A nonnegative integer circulation is packaged together with the two side conditions its
Eulerian realization needs: its total charge vanishes, and its positive support is weakly
connected, certified by a finite traversal in which consecutive edges share an endpoint. The
reachable variant adds an explicit finite route from a prescribed start vertex into that
support.

## Main definitions

* `Maths.EdgeGraph.Walk.charge`: the total integer charge of a finite walk.
* `Maths.EdgeGraph.outgoingMultiplicity`,
  `Maths.EdgeGraph.incomingMultiplicity`: the multiplicity leaving and entering a
  vertex.
* `Maths.EdgeGraph.multiplicityCharge`: the charge carried by an edge multiplicity
  vector.
* `Maths.EdgeGraph.SharesEndpoint`,
  `Maths.EdgeGraph.HasWalkConnectedSupport`: weak connectivity of a positive edge
  support, certified by a finite traversal.
* `Maths.EdgeGraph.edgeSetMultiplicity`,
  `Maths.EdgeGraph.IsBalancedEdgeSet`: the `0`-`1` multiplicity of a finite edge
  set and its flow balance.
* `Maths.EdgeGraph.ConnectedIntegerCirculation`,
  `Maths.EdgeGraph.ReachableConnectedIntegerCirculation`: nonzero balanced
  zero-charge multiplicities with a connected support, and their reachable refinement.

## Main results

* `Maths.EdgeGraph.Walk.edgeMultiplicity_flow_with_endpoints`: endpoint-corrected
  flow conservation for every finite typed walk.
* `Maths.EdgeGraph.Walk.edgeMultiplicity_balanced`: the edge multiplicities of a
  closed walk are balanced at every vertex.
* `Maths.EdgeGraph.Walk.multiplicityCharge_edgeMultiplicity`: the charge of a walk
  is the charge of its multiplicity vector.
* `Maths.EdgeGraph.HasWalkConnectedSupport.exists_boundary`: a connected support
  admits no nontrivial split without a shared endpoint across it.
* `Maths.EdgeGraph.Walk.toConnectedIntegerCirculation`: a nonempty zero-charge
  closed walk is a connected integer circulation.

## Tags

circulation, flow conservation, walk, edge multiplicity, directed multigraph
-/

@[expose] public section

namespace Maths

namespace EdgeGraph

universe uV uE uκ

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

namespace Walk

variable {G} {start finish middle : V}

/-- Total integer charge of a finite walk. -/
def charge {κ : Type uκ} (edgeCharge : E → κ → ℤ) {start : V} :
    {finish : V} → G.Walk start finish → κ → ℤ
  | _, .nil => 0
  | _, .concat walkSoFar edge _ => walkSoFar.charge edgeCharge + edgeCharge edge

@[simp] theorem charge_nil {κ : Type uκ} (edgeCharge : E → κ → ℤ) :
    (Walk.nil : G.Walk start start).charge edgeCharge = 0 := rfl

@[simp] theorem charge_concat {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).charge edgeCharge =
      walkSoFar.charge edgeCharge + edgeCharge edge := rfl

/-- The recursive charge agrees with summing the chronological edge list. -/
theorem charge_eq_sum_map {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walk : G.Walk start finish) :
    walk.charge edgeCharge = (walk.edges.map edgeCharge).sum := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [charge, edges, ih]

@[simp] theorem charge_castFinish {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    (walk.castFinish hfinish).charge edgeCharge = walk.charge edgeCharge := by
  subst hfinish
  rfl

@[simp] theorem charge_append {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).charge edgeCharge =
      first.charge edgeCharge + second.charge edgeCharge := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, add_assoc]

end Walk

/-- Total multiplicity leaving a vertex. -/
def outgoingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.source edge = vertex, multiplicity edge

/-- Total multiplicity entering a vertex. -/
def incomingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.target edge = vertex, multiplicity edge

/-- Total charge carried by an integer edge multiplicity. -/
def multiplicityCharge (_G : EdgeGraph V E) [Fintype E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (multiplicity : E → ℕ) : κ → ℤ :=
  ∑ edge, multiplicity edge • edgeCharge edge

/-- Two edge identities meet in the underlying undirected support graph. -/
def SharesEndpoint (first second : E) : Prop :=
  G.source first = G.source second ∨ G.source first = G.target second ∨
    G.target first = G.source second ∨ G.target first = G.target second

/-- Sharing an endpoint is a symmetric relation on edge identities. -/
theorem sharesEndpoint_symm {first second : E} (hshares : G.SharesEndpoint first second) :
    G.SharesEndpoint second first := by
  rcases hshares with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- A finite traversal certificate for weak connectivity of a nonempty edge support.
Repetitions are allowed; every positive-support edge must occur. -/
def HasWalkConnectedSupport (multiplicity : E → ℕ) : Prop :=
  ∃ traversal : List E,
    traversal ≠ [] ∧
    (∀ edge, edge ∈ traversal ↔ 0 < multiplicity edge) ∧
    traversal.IsChain G.SharesEndpoint

/-- A chain that meets both a marked and an unmarked item contains a related pair straddling
the mark. -/
private theorem exists_boundary_of_isChain
    {α : Type*} (relation : α → α → Prop)
    (hsymmetric : ∀ {first second}, relation first second → relation second first)
    (marked : α → Prop) (items : List α)
    (hchain : items.IsChain relation)
    (hmarked : ∃ item ∈ items, marked item)
    (hunmarked : ∃ item ∈ items, ¬ marked item) :
    ∃ first ∈ items, ∃ second ∈ items,
      marked first ∧ ¬ marked second ∧ relation first second := by
  induction items with
  | nil => simp at hmarked
  | cons first tail ih =>
      match tail with
      | [] => simp_all
      | second :: rest =>
          have hrelation : relation first second :=
            (List.isChain_cons_cons.mp hchain).1
          have htailChain : (second :: rest).IsChain relation :=
            (List.isChain_cons_cons.mp hchain).2
          by_cases hfirst : marked first
          · by_cases hsecond : marked second
            · have htailUnmarked : ∃ item ∈ second :: rest, ¬ marked item := by
                obtain ⟨item, hitem, hunmarkedItem⟩ := hunmarked
                simp only [List.mem_cons] at hitem
                rcases hitem with rfl | hitem
                · exact (hunmarkedItem hfirst).elim
                · exact ⟨item, by simpa only [List.mem_cons] using hitem, hunmarkedItem⟩
              obtain ⟨markedItem, hmarkedMem, unmarkedItem, hunmarkedMem,
                hmarkedItem, hunmarkedItem, hboundary⟩ :=
                  ih htailChain ⟨second, by simp, hsecond⟩ htailUnmarked
              exact ⟨markedItem, by simp [hmarkedMem], unmarkedItem,
                by simp [hunmarkedMem], hmarkedItem, hunmarkedItem, hboundary⟩
            · exact ⟨first, by simp, second, by simp, hfirst, hsecond, hrelation⟩
          · by_cases hsecond : marked second
            · exact ⟨second, by simp, first, by simp, hsecond, hfirst, hsymmetric hrelation⟩
            · have htailMarked : ∃ item ∈ second :: rest, marked item := by
                obtain ⟨item, hitem, hmarkedItem⟩ := hmarked
                simp only [List.mem_cons] at hitem
                rcases hitem with rfl | hitem
                · exact (hfirst hmarkedItem).elim
                · exact ⟨item, by simpa only [List.mem_cons] using hitem, hmarkedItem⟩
              obtain ⟨markedItem, hmarkedMem, unmarkedItem, hunmarkedMem,
                hmarkedItem, hunmarkedItem, hboundary⟩ :=
                  ih htailChain htailMarked ⟨second, by simp, hsecond⟩
              exact ⟨markedItem, by simp [hmarkedMem], unmarkedItem,
                by simp [hunmarkedMem], hmarkedItem, hunmarkedItem, hboundary⟩

/-- A walk-connected positive support cannot be split into two nonempty edge sets without a
pair of positive-support edges sharing an endpoint across the split. -/
theorem HasWalkConnectedSupport.exists_boundary
    (multiplicity : E → ℕ) (hconnected : G.HasWalkConnectedSupport multiplicity)
    (marked : Finset E)
    (hmarked : ∃ edge, 0 < multiplicity edge ∧ edge ∈ marked)
    (hunmarked : ∃ edge, 0 < multiplicity edge ∧ edge ∉ marked) :
    ∃ first second,
      0 < multiplicity first ∧ first ∈ marked ∧
       0 < multiplicity second ∧ second ∉ marked ∧
       G.SharesEndpoint first second := by
  classical
  obtain ⟨traversal, -, hsupport, hchain⟩ := hconnected
  have hmarkedTraversal : ∃ edge ∈ traversal, edge ∈ marked := by
    obtain ⟨edge, hpositive, hedgeMarked⟩ := hmarked
    exact ⟨edge, (hsupport edge).2 hpositive, hedgeMarked⟩
  have hunmarkedTraversal : ∃ edge ∈ traversal, edge ∉ marked := by
    obtain ⟨edge, hpositive, hedgeUnmarked⟩ := hunmarked
    exact ⟨edge, (hsupport edge).2 hpositive, hedgeUnmarked⟩
  obtain ⟨first, hfirstTraversal, second, hsecondTraversal,
    hfirstMarked, hsecondUnmarked, hshares⟩ :=
      exists_boundary_of_isChain G.SharesEndpoint (fun h => G.sharesEndpoint_symm h)
        (fun edge => edge ∈ marked) traversal hchain
        hmarkedTraversal hunmarkedTraversal
  exact ⟨first, second, (hsupport first).1 hfirstTraversal, hfirstMarked,
    (hsupport second).1 hsecondTraversal, hsecondUnmarked, hshares⟩

/-- The `0`-`1` multiplicity of a finite edge set. -/
def edgeSetMultiplicity [DecidableEq E] (allowed : Finset E) : E → ℕ :=
  fun edge => if edge ∈ allowed then 1 else 0

@[simp] theorem edgeSetMultiplicity_pos_iff [DecidableEq E]
    (allowed : Finset E) (edge : E) :
    0 < edgeSetMultiplicity allowed edge ↔ edge ∈ allowed := by
  by_cases hedge : edge ∈ allowed <;> simp [edgeSetMultiplicity, hedge]

/-- Flow balance for a finite set of distinguishable edge tokens. -/
def IsBalancedEdgeSet [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) : Prop :=
  ∀ vertex,
    G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex =
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex

/-- In a balanced edge set, any edge entering a vertex certifies that some allowed edge also
leaves that vertex. -/
theorem IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (edge : E) (hedge : edge ∈ allowed) (vertex : V)
    (htarget : G.target edge = vertex) :
    ∃ outgoing, outgoing ∈ allowed ∧ G.source outgoing = vertex := by
  have hincomingPositive :
      0 < G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex := by
    unfold incomingMultiplicity
    rw [Finset.sum_pos_iff]
    refine ⟨edge, ?_, ?_⟩
    · simp [htarget]
    · simp [edgeSetMultiplicity, hedge]
  have houtgoingPositive :
      0 < G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex := by
    rw [hbalanced vertex]
    exact hincomingPositive
  unfold outgoingMultiplicity at houtgoingPositive
  rw [Finset.sum_pos_iff] at houtgoingPositive
  obtain ⟨outgoing, houtgoingFilter, houtgoingPositive⟩ := houtgoingPositive
  have hsource : G.source outgoing = vertex :=
    (Finset.mem_filter.mp houtgoingFilter).2
  have hallowed : outgoing ∈ allowed := by
    by_contra hnotAllowed
    simp [edgeSetMultiplicity, hnotAllowed] at houtgoingPositive
  exact ⟨outgoing, hallowed, hsource⟩

/-- A nonzero nonnegative integer circulation with zero total charge and a finite certificate
that its positive support is weakly connected. -/
structure ConnectedIntegerCirculation {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) [Fintype E] [DecidableEq V] where
  /-- How often each edge is used. -/
  multiplicity : E → ℕ
  /-- At least one edge is used. -/
  nonzero : ∃ edge, 0 < multiplicity edge
  /-- Flow conservation at every vertex. -/
  balanced : ∀ vertex,
    G.outgoingMultiplicity multiplicity vertex =
      G.incomingMultiplicity multiplicity vertex
  /-- The multiplicity carries no net charge. -/
  charge_zero : G.multiplicityCharge edgeCharge multiplicity = 0
  /-- The positive support is weakly connected. -/
  connected : G.HasWalkConnectedSupport multiplicity

/-- A connected circulation together with an explicit finite route from the prescribed start
into its positive support. -/
structure ReachableConnectedIntegerCirculation {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) [Fintype E] [DecidableEq V]
    (start : V) extends G.ConnectedIntegerCirculation edgeCharge where
  /-- The vertex at which the route meets the support. -/
  entry : V
  /-- The route from `start` to `entry`. -/
  initialWalk : G.Walk start entry
  /-- Some used edge is incident to `entry`. -/
  entry_mem_support : ∃ edge, 0 < multiplicity edge ∧
    (G.source edge = entry ∨ G.target edge = entry)

namespace Walk

variable {G} {start finish : V}

@[simp] theorem outgoingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.outgoingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [outgoingMultiplicity]

@[simp] theorem incomingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.incomingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [incomingMultiplicity]

/-- Extending a walk by one edge adds one unit of outgoing multiplicity at that edge's
source. -/
theorem outgoingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.source edge = vertex then 1 else 0 := by
  classical
  simp [outgoingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

/-- Extending a walk by one edge adds one unit of incoming multiplicity at that edge's
target. -/
theorem incomingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.incomingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.incomingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.target edge = vertex then 1 else 0 := by
  classical
  simp [incomingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

/-- The charge of a walk is the charge carried by its edge multiplicity vector. -/
theorem multiplicityCharge_edgeMultiplicity
    [Fintype E] [DecidableEq E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk start finish) :
    G.multiplicityCharge edgeCharge walk.edgeMultiplicity =
      walk.charge edgeCharge := by
  induction walk with
  | nil => simp [multiplicityCharge]
  | concat walkSoFar edge legal ih =>
      funext coordinate
      simp only [multiplicityCharge, edgeMultiplicity, Walk.charge_concat,
        Pi.add_apply, Finset.sum_apply, nsmul_eq_mul]
      simp_rw [Nat.cast_add, add_mul, Pi.add_apply, Pi.mul_apply]
      have ihCoordinate := congrFun ih coordinate
      simp only [multiplicityCharge, Finset.sum_apply, nsmul_eq_mul,
        Pi.mul_apply] at ihCoordinate
      rw [Finset.sum_add_distrib, ihCoordinate]
      simp

/-- Endpoint-corrected flow conservation for every finite typed walk. -/
theorem edgeMultiplicity_flow_with_endpoints
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walk : G.Walk start finish) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex +
        (if finish = vertex then 1 else 0) =
      G.incomingMultiplicity walk.edgeMultiplicity vertex +
        (if start = vertex then 1 else 0) := by
  induction walk with
  | nil => simp
  | @concat middle walkSoFar edge legal ih =>
      rw [outgoingMultiplicity_edgeMultiplicity_concat,
        incomingMultiplicity_edgeMultiplicity_concat, legal]
      omega

/-- Edge multiplicities of a closed typed walk are balanced at every vertex. -/
theorem edgeMultiplicity_balanced [Fintype E] [DecidableEq E] [DecidableEq V]
    {base : V} (walk : G.Walk base base) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex =
      G.incomingMultiplicity walk.edgeMultiplicity vertex := by
  have hflow := walk.edgeMultiplicity_flow_with_endpoints vertex
  omega

/-- The edge list of a nonempty walk is nonempty. -/
theorem edges_ne_nil_of_length_pos (walk : G.Walk start finish) (hne : 0 < walk.length) :
    walk.edges ≠ [] := by
  rw [← List.length_pos_iff, walk.edges_length]
  exact hne

/-- The positive edge support of a nonempty walk is walk-connected in the underlying
undirected incidence graph. -/
theorem edgeMultiplicity_hasWalkConnectedSupport [DecidableEq E]
    (walk : G.Walk start finish) (hne : 0 < walk.length) :
    G.HasWalkConnectedSupport walk.edgeMultiplicity := by
  refine ⟨walk.edges, walk.edges_ne_nil_of_length_pos hne, ?_, ?_⟩
  · intro edge
    exact (walk.edgeMultiplicity_pos_iff_mem_edges edge).symm
  · exact walk.edges_isChain.imp fun _ _ hmatch => Or.inr (Or.inr (Or.inl hmatch))

/-- A nonempty zero-charge closed walk induces its exact connected integer circulation of edge
occurrence counts. -/
def toConnectedIntegerCirculation
    [Fintype E] [DecidableEq E] [DecidableEq V] {κ : Type uκ} {base : V}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk base base)
    (hne : 0 < walk.length) (hzero : walk.charge edgeCharge = 0) :
    G.ConnectedIntegerCirculation edgeCharge where
  multiplicity := walk.edgeMultiplicity
  nonzero :=
    ⟨walk.edges.head (walk.edges_ne_nil_of_length_pos hne),
      (walk.edgeMultiplicity_pos_iff_mem_edges _).2 (List.head_mem _)⟩
  balanced := walk.edgeMultiplicity_balanced
  charge_zero := by
    rw [walk.multiplicityCharge_edgeMultiplicity]
    exact hzero
  connected := walk.edgeMultiplicity_hasWalkConnectedSupport hne

end Walk

end EdgeGraph

end Maths
