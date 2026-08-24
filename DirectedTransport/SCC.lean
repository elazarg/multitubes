/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Exact
public import Mathlib.Order.Antisymmetrization

/-!
# Strongly connected normal forms for directed transport

An arbitrary type-valued transport has trivial holonomy exactly when its
restriction to every strongly connected component is equivalent to constant
transport.  The equivalences identify every edge map inside the component
with change of coordinates between its endpoint fibers.  No algebraic
structure on the fibers is required, and inter-component edges are
unconstrained.

## Main definitions

* `DirectedTransport.ReachabilityVertex`: the vertex type carrying the reachability
  preorder.
* `DirectedTransport.SCC` and `DirectedTransport.toSCC`: the strongly connected components
  as the antisymmetrization of that preorder, and the quotient map.
* `DirectedTransport.InterSCCEdge` and `DirectedTransport.sccCondensation`: the acyclic
  condensation graph on components.
* `DirectedTransport.Transport.HasSCCTrivializationAt` and
  `DirectedTransport.Transport.HasSCCTrivializations`: fiberwise equivalences identifying
  every edge map inside a component with a change of coordinates.
* `DirectedTransport.Transport.sccTrivialization`: the trivialization built from trivial
  holonomy.

## Main results

* `DirectedTransport.sccCondensation_edge_strict` and
  `DirectedTransport.sccCondensation_no_nonempty_closedWalk`: the condensation is acyclic.
* `DirectedTransport.Transport.hasTrivialHolonomy_iff_hasSCCTrivializations`: trivial
  holonomy is exactly componentwise triviality.
-/

@[expose] public section

noncomputable section

namespace DirectedTransport

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} {T : Transport G Fiber}

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

/-! ## Componentwise transport trivializations -/

/-- A constant-transport normal form on the strongly connected component of
`base`.  Only vertices and edges in that component enter the interface. -/
def Transport.HasSCCTrivializationAt (T : Transport G Fiber)
    (base : V) : Prop :=
  ∃ trivialization :
      ∀ vertex, LinkedTo G base vertex → Fiber base ≃ Fiber vertex,
    ∀ (edge : E)
      (hsource : LinkedTo G base (G.source edge))
      (htarget : LinkedTo G base (G.target edge)),
      T.edgeMap edge =
        (trivialization (G.target edge) htarget :
            Fiber base → Fiber (G.target edge)) ∘
          (trivialization (G.source edge) hsource).symm

/-- Componentwise constant-transport normal forms on the whole graph. -/
def Transport.HasSCCTrivializations (T : Transport G Fiber) : Prop :=
  ∀ base, T.HasSCCTrivializationAt base

/-- The equivalence induced by chosen forward and return walks inside a flat
strongly connected component. -/
def Transport.sccTrivialization (hflat : T.HasTrivialHolonomy)
    (base vertex : V) (hlinked : LinkedTo G base vertex) :
    Fiber base ≃ Fiber vertex :=
  T.walkMapEquivOfTrivialHolonomy hflat hlinked.1.some hlinked.2.some

theorem Transport.sccTrivialization_edgeMap
    (hflat : T.HasTrivialHolonomy) (base : V) (edge : E)
    (hsource : LinkedTo G base (G.source edge))
    (htarget : LinkedTo G base (G.target edge)) :
    T.edgeMap edge =
      (T.sccTrivialization hflat base (G.target edge) htarget :
          Fiber base → Fiber (G.target edge)) ∘
        (T.sccTrivialization hflat base (G.source edge) hsource).symm := by
  funext point
  change T.walkMap (EdgeGraph.Walk.singleton edge) point =
    T.walkMap htarget.1.some (T.walkMap hsource.2.some point)
  rw [← T.walkMap_append]
  exact congrFun
    (T.walkMap_eq_of_trivialHolonomy_of_return hflat
      (EdgeGraph.Walk.singleton edge)
      (hsource.2.some.append htarget.1.some)
      (htarget.2.some.append hsource.1.some)) point

private theorem linkedTo_of_mem_cycle_source {base : V}
    (cycle : G.Walk base base) {edge : E} (hedge : edge ∈ cycle.edges) :
    LinkedTo G base (G.source edge) := by
  let split := cycle.vertexSplitAtSource edge hedge
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

private theorem linkedTo_of_mem_cycle_target {base : V}
    (cycle : G.Walk base base) {edge : E} (hedge : edge ∈ cycle.edges) :
    LinkedTo G base (G.target edge) := by
  let split := cycle.vertexSplitAtTarget edge hedge
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

private theorem Transport.walkMap_eq_of_edgeTrivializations
    {base start finish : V}
    (trivialization :
      ∀ vertex, LinkedTo G base vertex → Fiber base ≃ Fiber vertex)
    (walk : G.Walk start finish)
    (hstart : LinkedTo G base start)
    (hfinish : LinkedTo G base finish)
    (hedge : ∀ edge ∈ walk.edges,
      ∃ (hsource : LinkedTo G base (G.source edge))
        (htarget : LinkedTo G base (G.target edge)),
        T.edgeMap edge =
          (trivialization (G.target edge) htarget :
              Fiber base → Fiber (G.target edge)) ∘
            (trivialization (G.source edge) hsource).symm) :
    T.walkMap walk =
      (trivialization finish hfinish : Fiber base → Fiber finish) ∘
        (trivialization start hstart).symm := by
  induction walk with
  | nil =>
      funext point
      simp
  | @concat middle walk edge legal ih =>
      have hbefore (candidate : E) (hcandidate : candidate ∈ walk.edges) :
          ∃ (hsource : LinkedTo G base (G.source candidate))
            (htarget : LinkedTo G base (G.target candidate)),
            T.edgeMap candidate =
              (trivialization (G.target candidate) htarget :
                  Fiber base → Fiber (G.target candidate)) ∘
                (trivialization (G.source candidate) hsource).symm :=
        hedge candidate (by simp [hcandidate])
      obtain ⟨hmiddle, htarget, hlast⟩ := hedge edge (by simp)
      subst legal
      funext point
      rw [T.walkMap_concat, hlast, Function.comp_apply,
        congrFun (ih hmiddle hbefore) point]
      simp

/-- **Type-valued SCC normal form.**  Trivial holonomy is equivalent to a
constant-transport trivialization on every strongly connected component.
This is the fiber-valued counterpart of the unit-potential normal form for
monoid labels. -/
theorem Transport.hasTrivialHolonomy_iff_hasSCCTrivializations :
    T.HasTrivialHolonomy ↔ T.HasSCCTrivializations := by
  constructor
  · intro hflat base
    refine ⟨T.sccTrivialization hflat base, ?_⟩
    exact T.sccTrivialization_edgeMap hflat base
  · intro hcomponents base cycle
    obtain ⟨trivialization, htrivialization⟩ := hcomponents base
    have hbase : LinkedTo G base base := ⟨⟨.nil⟩, ⟨.nil⟩⟩
    have hedge (edge : E) (hmem : edge ∈ cycle.edges) :
        ∃ (hsource : LinkedTo G base (G.source edge))
          (htarget : LinkedTo G base (G.target edge)),
          T.edgeMap edge =
            (trivialization (G.target edge) htarget :
                Fiber base → Fiber (G.target edge)) ∘
              (trivialization (G.source edge) hsource).symm := by
      let hsource := linkedTo_of_mem_cycle_source cycle hmem
      let htarget := linkedTo_of_mem_cycle_target cycle hmem
      exact ⟨hsource, htarget, htrivialization edge hsource htarget⟩
    have hwalk := T.walkMap_eq_of_edgeTrivializations
      trivialization cycle hbase hbase hedge
    funext point
    change T.walkMap cycle point = point
    rw [hwalk]
    simp

end DirectedTransport

end
