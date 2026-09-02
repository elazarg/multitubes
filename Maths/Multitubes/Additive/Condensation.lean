/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Potentials
public import Maths.Multitubes.SCC

import Mathlib.Tactic.Linarith

/-!
# Condensation decomposition of additive lax feasibility

A potential for a real edge weighting exists exactly when every strongly connected
component admits one on its induced subgraph.  Closed walks never leave a component:
splitting a closed walk at any traversed edge links the endpoints of that edge to the
base vertex.  The closed-walk test of the tropical Farkas duality
`Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` is
therefore intrinsically componentwise, and edges between distinct components are never
an obstruction.  No topological stitching along the acyclic condensation
`Maths.sccCondensation` is performed: the componentwise potentials certify
that no closed walk is positive, and the duality then rebuilds one global potential,
absorbing every inter-component edge.

This is the lax additive analogue of the exact componentwise normal form
`Maths.hasTrivialCycleLabels_iff_hasSCCUnitPotentials`, and a preprocessing
statement beside the simple-cycle reduction
`Maths.AdditiveTransport.worstDirectedResidualAtMost_iff_simpleCycles_le`:
additive lax feasibility may be decided one strongly connected component at a time.
As in the duality itself, `Finite E` is the only hypothesis and the vertex type is
arbitrary.  `Finite E` is also necessary, by the counterexample that makes it necessary
for the duality: two vertices joined by infinitely many parallel edges of unbounded
weight admit no potential, yet every component is a single vertex and the componentwise
condition holds vacuously.

## Main definitions

* `Maths.EdgeGraph.induce`: the induced subgraph on a set of vertices; an
  edge belongs to it exactly when both of its endpoints do.
* `Maths.sccSet`: the vertex set of a strongly connected component, as the
  fiber of `Maths.toSCC` over it.
* `Maths.MaxPlusPotential.HasSCCPotentialAt` and
  `Maths.MaxPlusPotential.HasSCCPotentials`: a potential on one strongly
  connected component, respectively on every component.

## Main results

* `Maths.MaxPlusPotential.exists_isPotential_iff_forall_scc_induce`: a
  potential exists exactly when the induced subgraph of every strongly connected
  component admits one.
* `Maths.MaxPlusPotential.exists_isPotential_iff_hasSCCPotentials`: the
  same decomposition phrased through componentwise constrained potentials.
* `Maths.MaxPlusPotential.hasSCCPotentialAt_iff_exists_isPotential_induce`:
  the two componentwise phrasings agree, without any finiteness hypothesis.
* `Maths.source_mem_sccSet_of_mem_edges` and
  `Maths.target_mem_sccSet_of_mem_edges`: a closed walk stays inside the
  strongly connected component of its base vertex.
-/

@[expose] public section

namespace Maths

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## Induced subgraphs -/

namespace EdgeGraph

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

end EdgeGraph

/-! ## The vertex set of a component -/

variable {G : EdgeGraph V E}

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
    G.source edge ∈ sccSet G (toSCC G base) := by
  rw [mem_sccSet_toSCC_iff_linkedTo]
  let split := cycle.vertexSplitAtSource edge hmem
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

/-- A closed walk stays inside the strongly connected component of its base vertex:
the target of every traversed edge lies in that component. -/
theorem target_mem_sccSet_of_mem_edges {base : V} (cycle : G.Walk base base)
    {edge : E} (hmem : edge ∈ cycle.edges) :
    G.target edge ∈ sccSet G (toSCC G base) := by
  rw [mem_sccSet_toSCC_iff_linkedTo]
  let split := cycle.vertexSplitAtTarget edge hmem
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

/-! ## Componentwise potentials -/

namespace MaxPlusPotential

/-- A potential restricts to a potential on every induced subgraph. -/
theorem IsPotential.induce {weight : E → ℝ} {φ : V → ℝ}
    (hφ : IsPotential G weight φ) (S : Set V) :
    IsPotential (G.induce S) (fun edge => weight edge.1) (fun vertex => φ vertex.1) :=
  fun edge => hφ edge.1

/-- A potential on the strongly connected component of `base`: a vertex function whose
increment inequality is imposed exactly on the edges with both endpoints in that
component. -/
def HasSCCPotentialAt (G : EdgeGraph V E) (weight : E → ℝ) (base : V) : Prop :=
  ∃ φ : V → ℝ, ∀ edge : E,
    LinkedTo G base (G.source edge) → LinkedTo G base (G.target edge) →
      φ (G.source edge) + weight edge ≤ φ (G.target edge)

/-- Componentwise lax feasibility: a potential on every strongly connected
component. -/
def HasSCCPotentials (G : EdgeGraph V E) (weight : E → ℝ) : Prop :=
  ∀ base : V, HasSCCPotentialAt G weight base

/-- The componentwise feasibility predicate at `base` is feasibility of the induced
subgraph of the component of `base`.  No finiteness is involved: a potential of the
induced subgraph extends by zero outside the component. -/
theorem hasSCCPotentialAt_iff_exists_isPotential_induce (weight : E → ℝ) (base : V) :
    HasSCCPotentialAt G weight base ↔
      ∃ ψ, IsPotential (G.induce (sccSet G (toSCC G base)))
        (fun edge => weight edge.1) ψ := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨fun vertex => φ vertex.1, ?_⟩
    rintro ⟨edge, hsource, htarget⟩
    exact hφ edge (mem_sccSet_toSCC_iff_linkedTo.mp hsource)
      (mem_sccSet_toSCC_iff_linkedTo.mp htarget)
  · rintro ⟨ψ, hψ⟩
    classical
    let φ : V → ℝ := fun vertex =>
      if hmem : vertex ∈ sccSet G (toSCC G base) then ψ ⟨vertex, hmem⟩ else 0
    refine ⟨φ, fun edge hsource htarget => ?_⟩
    have hs : G.source edge ∈ sccSet G (toSCC G base) :=
      mem_sccSet_toSCC_iff_linkedTo.mpr hsource
    have ht : G.target edge ∈ sccSet G (toSCC G base) :=
      mem_sccSet_toSCC_iff_linkedTo.mpr htarget
    have hedge := hψ ⟨edge, hs, ht⟩
    simp only [φ, dif_pos hs, dif_pos ht]
    exact hedge

private theorem walkWeight_le_of_forall_mem_edges {weight : E → ℝ} {φ : V → ℝ}
    {start finish : V} (walk : G.Walk start finish)
    (hedge : ∀ e ∈ walk.edges, φ (G.source e) + weight e ≤ φ (G.target e)) :
    walkWeight weight walk ≤ φ finish - φ start := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      have hlast := hedge edge (by simp)
      have hrest := ih fun e hmem => hedge e (by simp [hmem])
      subst legal
      simp only [walkWeight_concat]
      linarith

/-- **Componentwise decomposition of lax feasibility.**  Over finitely many edges a
potential exists exactly when every strongly connected component carries a vertex
function satisfying the increment inequalities on the edges of that component.
Inter-component edges impose no condition: they occur in no closed walk. -/
theorem exists_isPotential_iff_hasSCCPotentials [Finite E] (weight : E → ℝ) :
    (∃ φ : V → ℝ, IsPotential G weight φ) ↔ HasSCCPotentials G weight := by
  constructor
  · rintro ⟨φ, hφ⟩ base
    exact ⟨φ, fun edge _ _ => hφ edge⟩
  · intro hcomponents
    rw [exists_isPotential_iff_forall_closedWalk_nonpos]
    intro base cycle
    obtain ⟨φ, hφ⟩ := hcomponents base
    have hedge (e : E) (hmem : e ∈ cycle.edges) :
        φ (G.source e) + weight e ≤ φ (G.target e) :=
      hφ e
        (mem_sccSet_toSCC_iff_linkedTo.mp (source_mem_sccSet_of_mem_edges cycle hmem))
        (mem_sccSet_toSCC_iff_linkedTo.mp (target_mem_sccSet_of_mem_edges cycle hmem))
    simpa using walkWeight_le_of_forall_mem_edges cycle hedge

/-- **Condensation decomposition of lax feasibility.**  Over finitely many edges a
potential for a weighted digraph exists exactly when the induced subgraph of every
strongly connected component admits one.  Feasibility is thereby decided one component
at a time, and no compatibility between the componentwise potentials is required. -/
theorem exists_isPotential_iff_forall_scc_induce [Finite E] (weight : E → ℝ) :
    (∃ φ : V → ℝ, IsPotential G weight φ) ↔
      ∀ component : SCC G, ∃ ψ,
        IsPotential (G.induce (sccSet G component)) (fun edge => weight edge.1) ψ := by
  constructor
  · rintro ⟨φ, hφ⟩ component
    exact ⟨fun vertex => φ vertex.1, hφ.induce (sccSet G component)⟩
  · intro hcomponents
    rw [exists_isPotential_iff_hasSCCPotentials]
    intro base
    exact (hasSCCPotentialAt_iff_exists_isPotential_induce weight base).mpr
      (hcomponents (toSCC G base))

end MaxPlusPotential

end Maths
