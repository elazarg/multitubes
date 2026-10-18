/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.Order.Antisymmetrization

/-!
# Strongly connected components and the condensation

Directed reachability is a preorder on the vertices of a directed multigraph.  Its
antisymmetrization is the partial order of strongly connected components, and the edges
between distinct components form the condensation graph, which is acyclic: every nonempty
walk in it strictly increases the component order.

## Main definitions

* `Maths.ReachabilityVertex`: the vertex type carrying the reachability preorder.
* `Maths.SCC` and `Maths.toSCC`: the strongly connected components as the
  antisymmetrization of that preorder, and the quotient map.
* `Maths.InterSCCEdge` and `Maths.sccCondensation`: the condensation graph on components.
* `Maths.sccSet`: the vertex set of a strongly connected component, as the fiber of
  `Maths.toSCC` over it.

## Main results

* `Maths.toSCC_eq_toSCC_iff_linkedTo`: two vertices lie in one component exactly when they
  are mutually reachable.
* `Maths.sccCondensation_edge_strict` and `Maths.sccCondensation_no_nonempty_closedWalk`:
  the condensation is acyclic.
* `Maths.source_mem_sccSet_of_mem_edges` and `Maths.target_mem_sccSet_of_mem_edges`: a
  closed walk stays inside the strongly connected component of its base vertex.

## Tags

strongly connected component, condensation, reachability, directed acyclic graph
-/

@[expose] public section

namespace Maths

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ## The condensation partial order -/

/-- Vertices equipped with the directed reachability preorder. -/
def ReachabilityVertex (_G : EdgeGraph V E) := V

instance ReachabilityVertex.instPreorder : Preorder (ReachabilityVertex G) where
  le source target := Nonempty (G.Walk source target)
  le_refl vertex := ⟨.nil⟩
  le_trans _ _ _ first second := ⟨first.some.append second.some⟩

/-- Strongly connected components, ordered by directed reachability.  This is
the antisymmetrization of the vertex reachability preorder. -/
def SCC (G : EdgeGraph V E) :=
  Antisymmetrization (ReachabilityVertex G) (· ≤ ·)

instance SCC.instPartialOrder : PartialOrder (SCC G) :=
  inferInstanceAs (PartialOrder
    (Antisymmetrization (ReachabilityVertex G) (· ≤ ·)))

/-- The strongly connected component containing a vertex. -/
def toSCC (G : EdgeGraph V E) (vertex : V) : SCC G :=
  toAntisymmetrization (· ≤ ·) (vertex : ReachabilityVertex G)

theorem toSCC_le_toSCC_iff {source target : V} :
    toSCC G source ≤ toSCC G target ↔ Nonempty (G.Walk source target) :=
  toAntisymmetrization_le_toAntisymmetrization_iff

/-- Two vertices determine the same component exactly when they are mutually
reachable. -/
theorem toSCC_eq_toSCC_iff_linkedTo {source target : V} :
    toSCC G source = toSCC G target ↔ LinkedTo G source target := by
  constructor
  · intro hequal
    constructor
    · apply toSCC_le_toSCC_iff.mp
      rw [hequal]
    · apply toSCC_le_toSCC_iff.mp
      rw [hequal]
  · rintro ⟨hforward, hbackward⟩
    apply le_antisymm
    · exact toSCC_le_toSCC_iff.mpr hforward
    · exact toSCC_le_toSCC_iff.mpr hbackward

/-- Edges that cross between distinct strongly connected components. -/
def InterSCCEdge (G : EdgeGraph V E) :=
  {edge : E // ¬LinkedTo G (G.source edge) (G.target edge)}

/-- The condensation graph keeps precisely the inter-component edges and
replaces their endpoints by strongly connected components. -/
def sccCondensation (G : EdgeGraph V E) : EdgeGraph (SCC G) (InterSCCEdge G) where
  source edge := toSCC G (G.source edge.1)
  target edge := toSCC G (G.target edge.1)

/-- Every condensation edge strictly increases the component reachability
order. -/
theorem sccCondensation_edge_strict (edge : InterSCCEdge G) :
    (sccCondensation G).source edge < (sccCondensation G).target edge := by
  rw [lt_iff_le_and_ne]
  refine ⟨toSCC_le_toSCC_iff.mpr
    ⟨EdgeGraph.Walk.singleton edge.1⟩, ?_⟩
  exact fun hequal => edge.2 (toSCC_eq_toSCC_iff_linkedTo.mp hequal)

private theorem sccCondensation_walk_le {start finish : SCC G}
    (walk : (sccCondensation G).Walk start finish) : start ≤ finish := by
  induction walk with
  | nil => exact le_rfl
  | @concat _ walk edge legal ih =>
      subst legal
      exact ih.trans (sccCondensation_edge_strict edge).le

/-- Every nonempty condensation walk strictly increases the component order.
In particular, the condensation graph is acyclic. -/
theorem sccCondensation_walk_lt_of_pos {start finish : SCC G}
    (walk : (sccCondensation G).Walk start finish)
    (hpositive : 0 < walk.length) : start < finish := by
  cases walk with
  | nil => simp at hpositive
  | @concat _ walk edge legal =>
      subst legal
      exact lt_of_le_of_lt (sccCondensation_walk_le walk)
        (sccCondensation_edge_strict edge)

/-- The condensation graph has no nonempty closed directed walk. -/
theorem sccCondensation_no_nonempty_closedWalk
    (base : SCC G) (cycle : (sccCondensation G).Walk base base) :
    cycle.length = 0 := by
  by_contra hnonzero
  have hpositive : 0 < cycle.length := Nat.pos_of_ne_zero hnonzero
  exact (lt_irrefl base) (sccCondensation_walk_lt_of_pos cycle hpositive)

/-! ## The vertex set of a component -/

/-- The vertex set of a strongly connected component: the fiber of
`Maths.toSCC` over it. -/
def sccSet (G : EdgeGraph V E) (component : SCC G) : Set V :=
  {vertex | toSCC G vertex = component}

/-- Membership in the vertex set of a component is membership in the fiber of
`Maths.toSCC`. -/
@[simp] theorem mem_sccSet {component : SCC G} {vertex : V} :
    vertex ∈ sccSet G component ↔ toSCC G vertex = component :=
  Iff.rfl

/-- The component of a marked vertex consists of the vertices mutually reachable
with it. -/
theorem mem_sccSet_toSCC_iff_linkedTo {base vertex : V} :
    vertex ∈ sccSet G (toSCC G base) ↔ LinkedTo G base vertex := by
  rw [mem_sccSet, toSCC_eq_toSCC_iff_linkedTo]
  exact ⟨fun hlinked => ⟨hlinked.2, hlinked.1⟩, fun hlinked => ⟨hlinked.2, hlinked.1⟩⟩

/-- A closed walk stays inside the strongly connected component of its base vertex:
the source of every traversed edge lies in that component. -/
theorem source_mem_sccSet_of_mem_edges {base : V} (cycle : G.Walk base base)
    {edge : E} (hmem : edge ∈ cycle.edges) :
    G.source edge ∈ sccSet G (toSCC G base) :=
  mem_sccSet_toSCC_iff_linkedTo.2 (linkedTo_source_of_mem_edges cycle hmem)

/-- A closed walk stays inside the strongly connected component of its base vertex:
the target of every traversed edge lies in that component. -/
theorem target_mem_sccSet_of_mem_edges {base : V} (cycle : G.Walk base base)
    {edge : E} (hmem : edge ∈ cycle.edges) :
    G.target edge ∈ sccSet G (toSCC G base) :=
  mem_sccSet_toSCC_iff_linkedTo.2 (linkedTo_target_of_mem_edges cycle hmem)

end Maths
