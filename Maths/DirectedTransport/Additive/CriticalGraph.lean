/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Eigenvector
public import Maths.DirectedTransport.SCC

import Mathlib.Tactic.Linarith

/-!
# The critical graph and the max-plus eigenspace

`Maths.DirectedTransport.Additive.Eigenvector` produces one max-plus eigenvector for the maximum
cycle mean `lam`: the column of the Kleene star of `weight - lam` rooted at a critical vertex.  This
file develops the two structures that organize *all* of them.

The **critical graph** is the subgraph kept by the edges that lie on a closed walk of mean weight
exactly `lam`.  Its characteristic property is that on it the mean is not merely bounded by `lam`
but equal to it: every closed walk of the critical subgraph has mean exactly `lam`.  The proof
does not use attainment of the maximum cycle mean.  Fix any potential `φ` for the shifted
weighting `weight - lam`, which exists as soon as no closed walk exceeds the mean `lam`.  Along a
closed walk the edge defects of `φ` telescope to the shifted weight of the walk, so on a walk of
mean exactly `lam` a family of nonpositive numbers sums to zero: every edge of such a walk has
defect zero.  Criticality of an edge is therefore *tightness* for every such `φ` simultaneously,
and a closed walk of tight edges has shifted weight zero, that is, mean `lam`.

The **eigenspace** is described by the same tightness argument run backwards.  A max-plus
eigenvector is a potential for `weight - lam` that is tight at some incoming edge of every vertex.
Walking backwards along tight edges from a vertex, with finitely many vertices, must revisit a
vertex; the closed walk so traversed consists of tight edges, hence is critical, and the remaining
tight walk from that critical vertex certifies that the eigenvector's value there, plus the
Kleene-star entry, recovers its value at the original vertex.  Every eigenvector is thus the
max-plus combination of the critical Kleene-star columns with its own values as coefficients, and
each critical column is itself an eigenvector.

Columns rooted in one strongly connected component of the critical graph differ by a constant, so
one column per component already generates.  That family is also **minimal**: evaluating a
supposed expression of the column rooted at a vertex first at that vertex, where the column
vanishes, and then at the root attaining the maximum forces the two Kleene-star entries between
the two roots to be opposite, which happens only inside a single component.

## Main definitions

* `Maths.EdgeGraph.restrictEdges`: the subgraph on a set of edges, the edge-indexed
  analogue of `Maths.EdgeGraph.induce`.
* `Maths.EdgeGraph.Walk.ofRestrictEdges`: a walk of an edge subgraph read as a walk
  of the ambient graph.
* `Maths.MaxPlusPotential.IsCriticalEdge`,
  `Maths.MaxPlusPotential.criticalEdges`: an edge lying on a closed walk of mean
  weight `lam`, and the set of these.
* `Maths.MaxPlusPotential.criticalGraph`,
  `Maths.MaxPlusPotential.criticalWeight`: the critical subgraph and the restriction
  of the weighting to it, with `Maths.MaxPlusPotential.liftCriticalWalk` reading a
  walk of the former in the ambient graph.
* `Maths.MaxPlusPotential.IsGraphEigenvector`: the max-plus eigenvalue equation on a
  weighted digraph, namely the subeigenvector inequality together with an incoming tight edge at
  every vertex.
* `Maths.MaxPlusPotential.CriticalClass`,
  `Maths.MaxPlusPotential.toCriticalClass`: the critical classes, that is the strongly
  connected components of the critical graph, and the class of a vertex.
* `Maths.MaxPlusPotential.GeneratesEigenspace`: a set of vertices whose Kleene-star
  columns express every eigenvector.

## Main results

* `Maths.MaxPlusPotential.defect_eq_zero_of_isCriticalEdge`: a critical edge is tight
  for *every* potential of the shifted weighting.
* `Maths.MaxPlusPotential.walkWeight_criticalGraph_eq`: **the characteristic property
  of the critical graph**, every closed walk of it has mean exactly `lam`.
* `Maths.MaxPlusPotential.isCriticalVertex_of_criticalGraph_closedWalk`: consequently
  every vertex of a nonempty closed walk of the critical graph is a critical vertex.
* `Maths.MaxPlusPotential.add_maxRootedWeight_le_maxRootedWeight`: the triangle
  inequality of the Kleene star, and
  `Maths.MaxPlusPotential.isGreatest_range_maxRootedWeight`: the canonical potential
  `Maths.MaxPlusPotential.maxIncomingWeight` is the largest Kleene-star entry in its
  column, so it is one row of the all-pairs operator.
* `Maths.MaxPlusPotential.isGraphEigenvector_maxRootedWeight`: **every critical
  Kleene-star column is an eigenvector.**
* `Maths.MaxPlusPotential.isGreatest_criticalColumns`: **every eigenvector is the
  max-plus combination of the critical Kleene-star columns**, with its own values as
  coefficients; with finitely many vertices and edges and no further hypothesis.
* `Maths.MaxPlusPotential.isGreatest_criticalColumns_matrix`: the same for a max-plus
  matrix, where the reachability side conditions are automatic.
* `Maths.MaxPlusPotential.isCriticalVertex_of_toCriticalClass_eq`: criticality is a
  property of a whole critical class.
* `Maths.MaxPlusPotential.maxRootedWeight_eq_add_of_toCriticalClass_eq`: **two
  Kleene-star columns rooted in the same critical class differ by a constant**, namely by
  `Maths.MaxPlusPotential.maxRootedWeight_add_maxRootedWeight_eq_zero`, the Kleene-star
  entry between the two roots.
* `Maths.MaxPlusPotential.isGreatest_criticalClassColumns`: **one column per critical
  class suffices** to express every eigenvector, restated as
  `Maths.MaxPlusPotential.generatesEigenspace_of_forall_exists_mem`.
* `Maths.MaxPlusPotential.toCriticalClass_eq_of_maxRootedWeight_add_eq_zero`:
  conversely, two mutually reachable vertices whose Kleene-star entries are opposite lie in one
  critical class.
* `Maths.MaxPlusPotential.not_isGreatest_criticalColumns_of_forall_toCriticalClass_ne`:
  **a column is not the max-plus combination of the columns rooted in other critical classes**,
  whatever coefficients are used.
* `Maths.MaxPlusPotential.exists_mem_toCriticalClass_eq_of_generatesEigenspace`:
  **minimality**, every generating set meets the critical class of every critical vertex reaching
  the whole graph; with
  `Maths.MaxPlusPotential.generatesEigenspace_iff` identifying the generating sets, in
  that situation, with the transversals of the critical classes.

## Implementation notes

`Maths.EdgeGraph.restrictEdges` is placed here, beside its only use, exactly as
`Maths.EdgeGraph.induce` is placed beside its own in
`Maths.DirectedTransport.Additive.Condensation`; both are one-line reindexings of an ambient graph
along a subtype of its edges or vertices.

The hypothesis carried through the critical-graph results is that `lam` bounds every cycle mean,
`walkWeight weight cycle ≤ cycle.length * lam`, and never that `lam` is *attained*.  With no
critical cycle the critical graph is empty and the statements are vacuous, which is the correct
reading; attainment is available over `ℝ` alone and is imported only in the corollaries that need
a specific eigenvalue.

The eigenspace description asks for finitely many vertices and finitely many edges and nothing
else - no irreducibility, no strong connectivity, and no attainment.  Reachability enters only as
the side condition `Nonempty (G.Walk base vertex)` attached to a Kleene-star entry, which is what
keeps `Maths.MaxPlusPotential.maxRootedWeight` away from its junk value; the critical
vertex produced by the backward tight walk always satisfies it, so the description is a genuine
`IsGreatest` and not a conditional one.

`Maths.MaxPlusPotential.CriticalClass` is `Maths.SCC` of the critical
graph, so the reachability order on classes and the acyclicity of their condensation come with it
and mutual reachability inside the critical graph is not redefined here.

The family indexed by the critical classes is *sufficient* and *minimal*.  Sufficiency asks for
nothing beyond finiteness.  Minimality asks, for the class being recovered, that one of its
vertices reach every vertex of the graph: that reachability is exactly what makes the column
rooted there an eigenvector, by
`Maths.MaxPlusPotential.isGraphEigenvector_maxRootedWeight`, and without an
eigenvector attached to a class there is nothing a generating family could fail to express.
Nothing further is assumed - in particular the generating set is not required to consist of
critical vertices, and the walks from its members back to the class are read off the generating
hypothesis itself, not assumed.

## References

* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992), Theorem 3.23 and Section 3.7, for the critical graph and the eigenspace of an
  irreducible max-plus matrix.
* R. A. Cuninghame-Green, *Minimax Algebra*, Lecture Notes in Economics and Mathematical Systems
  166, Springer (1979), Chapter 24.
* B. Heidergott, G. J. Olsder and J. van der Woude, *Max Plus at Work*, Princeton University Press
  (2006), Chapter 2, for the critical graph and the star operator.
* P. Butkovič, *Max-linear Systems: Theory and Algorithms*, Springer (2010), Chapter 4, for the
  eigenspace as generated by the critical columns.

## Tags

max-plus, tropical, critical graph, eigenspace, Kleene star, cycle mean, Perron root
-/

@[expose] public section

namespace Maths

noncomputable section

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ### Edge subgraphs -/

namespace EdgeGraph

/-- The subgraph on a set of edges: the vertices are those of the ambient graph and the edges are
the members of the set, with the ambient endpoints.  This is the edge-indexed analogue of
`Maths.EdgeGraph.induce`, which selects a set of vertices instead. -/
def restrictEdges (G : EdgeGraph V E) (S : Set E) : EdgeGraph V S where
  source edge := G.source edge.1
  target edge := G.target edge.1

/-- The source map of an edge subgraph restricts the ambient source map. -/
@[simp] theorem restrictEdges_source (G : EdgeGraph V E) (S : Set E) (edge : S) :
    (G.restrictEdges S).source edge = G.source edge.1 := rfl

/-- The target map of an edge subgraph restricts the ambient target map. -/
@[simp] theorem restrictEdges_target (G : EdgeGraph V E) (S : Set E) (edge : S) :
    (G.restrictEdges S).target edge = G.target edge.1 := rfl

namespace Walk

variable {G : EdgeGraph V E}

/-- A walk of an edge subgraph read as a walk of the ambient graph, by forgetting the membership
proof carried by each edge. -/
def ofRestrictEdges {S : Set E} {start : V} :
    {finish : V} → (G.restrictEdges S).Walk start finish → G.Walk start finish
  | _, .nil => .nil
  | _, .concat walkSoFar edge legal => (ofRestrictEdges walkSoFar).concat edge.1 legal

@[simp] theorem ofRestrictEdges_nil {S : Set E} {start : V} :
    ofRestrictEdges (G := G) (S := S) (.nil : (G.restrictEdges S).Walk start start) = .nil := rfl

/-- Reading a walk of an edge subgraph in the ambient graph forgets the membership proofs of its
edges and nothing else. -/
@[simp] theorem edges_ofRestrictEdges {S : Set E} {start finish : V}
    (walk : (G.restrictEdges S).Walk start finish) :
    (ofRestrictEdges walk).edges = walk.edges.map Subtype.val := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      have hunfold : ofRestrictEdges (walkSoFar.concat edge legal)
          = (ofRestrictEdges walkSoFar).concat edge.1 legal := rfl
      have hstep := edges_concat (G := G) (ofRestrictEdges walkSoFar) edge.1 legal
      have htail : (ofRestrictEdges walkSoFar).edges ++ [edge.1]
          = List.map Subtype.val (walkSoFar.concat edge legal).edges := by
        rw [ih, edges_concat]
        simp
      rw [hunfold]
      exact hstep.trans htail

/-- The converse reading: a walk of the ambient graph all of whose edges belong to the set is a
walk of the edge subgraph.  It is stated as an existence because the walk of the subgraph carries
the membership proofs, which the ambient walk does not determine. -/
theorem nonempty_restrictEdges_of_forall_mem {S : Set E} {start finish : V}
    (walk : G.Walk start finish) (hmem : ∀ e ∈ walk.edges, e ∈ S) :
    Nonempty ((G.restrictEdges S).Walk start finish) := by
  induction walk with
  | nil => exact ⟨.nil⟩
  | concat walkSoFar edge legal ih =>
      obtain ⟨before⟩ := ih fun e he => hmem e (by simp [he])
      exact ⟨before.concat ⟨edge, hmem edge (by simp)⟩ legal⟩

/-- Reading a walk of an edge subgraph in the ambient graph preserves its length. -/
@[simp] theorem length_ofRestrictEdges {S : Set E} {start finish : V}
    (walk : (G.restrictEdges S).Walk start finish) :
    (ofRestrictEdges walk).length = walk.length := by
  rw [← edges_length, ← edges_length, edges_ofRestrictEdges, List.length_map]

end Walk

end EdgeGraph

namespace MaxPlusPotential

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {G : EdgeGraph V E}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Reading a walk of an edge subgraph in the ambient graph preserves its weight. -/
@[simp] theorem walkWeight_ofRestrictEdges {weight : E → 𝕜} {S : Set E} {start finish : V}
    (walk : (G.restrictEdges S).Walk start finish) :
    walkWeight weight walk.ofRestrictEdges = walkWeight (fun edge => weight edge.1) walk := by
  simp [walkWeight]

/-! ### The critical graph -/

/-- An edge is **critical** for the value `lam` when it is traversed by some nonempty closed walk
of mean weight exactly `lam`.  The critical edges are the edges the maximum cycle mean is actually
witnessed on, and they carry the whole max-plus spectral structure. -/
def IsCriticalEdge (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) (edge : E) : Prop :=
  ∃ (vertex : V) (cycle : G.Walk vertex vertex), 0 < cycle.length ∧
    walkWeight weight cycle = cycle.length * lam ∧ edge ∈ cycle.edges

/-- The set of critical edges for the value `lam`. -/
def criticalEdges (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) : Set E :=
  {edge | IsCriticalEdge G weight lam edge}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Membership in the critical edge set is criticality. -/
@[simp] theorem mem_criticalEdges {weight : E → 𝕜} {lam : 𝕜} {edge : E} :
    edge ∈ criticalEdges G weight lam ↔ IsCriticalEdge G weight lam edge := Iff.rfl

/-- The **critical graph**: the subgraph kept by the critical edges, on the ambient vertex
type. -/
def criticalGraph (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) :
    EdgeGraph V (criticalEdges G weight lam) :=
  G.restrictEdges (criticalEdges G weight lam)

/-- The ambient weighting restricted to the critical edges. -/
def criticalWeight (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) :
    criticalEdges G weight lam → 𝕜 :=
  fun edge => weight edge.1

/-- A walk of the critical graph read as a walk of the ambient graph. -/
def liftCriticalWalk {weight : E → 𝕜} {lam : 𝕜} {start finish : V}
    (walk : (criticalGraph G weight lam).Walk start finish) : G.Walk start finish :=
  walk.ofRestrictEdges

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Reading a walk of the critical graph in the ambient graph preserves its length. -/
@[simp] theorem length_liftCriticalWalk {weight : E → 𝕜} {lam : 𝕜} {start finish : V}
    (walk : (criticalGraph G weight lam).Walk start finish) :
    (liftCriticalWalk walk).length = walk.length :=
  EdgeGraph.Walk.length_ofRestrictEdges walk

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Reading a walk of the critical graph in the ambient graph forgets only the criticality proofs
of its edges. -/
@[simp] theorem edges_liftCriticalWalk {weight : E → 𝕜} {lam : 𝕜} {start finish : V}
    (walk : (criticalGraph G weight lam).Walk start finish) :
    (liftCriticalWalk walk).edges = walk.edges.map Subtype.val :=
  EdgeGraph.Walk.edges_ofRestrictEdges walk

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Reading a walk of the critical graph in the ambient graph preserves its weight. -/
@[simp] theorem walkWeight_liftCriticalWalk {weight : E → 𝕜} {lam : 𝕜} {start finish : V}
    (walk : (criticalGraph G weight lam).Walk start finish) :
    walkWeight weight (liftCriticalWalk walk) = walkWeight (criticalWeight G weight lam) walk :=
  walkWeight_ofRestrictEdges walk

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Every edge of a nonempty closed walk of mean weight `lam` is critical. -/
theorem isCriticalEdge_of_mem_edges {weight : E → 𝕜} {lam : 𝕜} {vertex : V}
    (cycle : G.Walk vertex vertex) (hpos : 0 < cycle.length)
    (hmean : walkWeight weight cycle = cycle.length * lam) {edge : E} (hmem : edge ∈ cycle.edges) :
    IsCriticalEdge G weight lam edge :=
  ⟨vertex, cycle, hpos, hmean, hmem⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The source of a critical edge is a critical vertex: rotating the closed walk that witnesses
the edge to start at that source changes neither its weight nor its length. -/
theorem isCriticalVertex_source_of_isCriticalEdge {weight : E → 𝕜} {lam : 𝕜} {edge : E}
    (hedge : IsCriticalEdge G weight lam edge) :
    IsCriticalVertex G weight lam (G.source edge) := by
  obtain ⟨vertex, cycle, hpos, hmean, hmem⟩ := hedge
  let split := cycle.vertexSplitAtSource edge hmem
  refine ⟨split.after.append split.before, ?_, ?_⟩
  · have hlen : cycle.length = split.before.length + split.after.length := by
      have hcongr := congrArg List.length split.edges_eq
      simpa [EdgeGraph.Walk.edges_length] using hcongr
    rw [EdgeGraph.Walk.length_append]
    omega
  · have hlen : (split.after.append split.before).length = cycle.length := by
      have hcongr := congrArg List.length split.edges_eq
      rw [EdgeGraph.Walk.length_append]
      simp only [EdgeGraph.Walk.edges_length, List.length_append] at hcongr
      omega
    have hweight : walkWeight weight (split.after.append split.before)
        = walkWeight weight cycle := by
      rw [walkWeight_append]
      simp only [walkWeight, split.edges_eq, List.map_append, List.sum_append]
      ring
    rw [hweight, hlen, hmean]

/-! ### Criticality is tightness -/

/-- A list of nonpositive scalars summing to zero has all its entries zero. -/
private theorem eq_zero_of_nonpos_of_sum_eq_zero (l : List 𝕜)
    (hle : ∀ x ∈ l, x ≤ 0) (heq : l.sum = 0) : ∀ x ∈ l, x = 0 := by
  have hsum : ∀ l : List 𝕜, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0 := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        intro hle
        have := ih fun x hx => hle x (List.mem_cons_of_mem a hx)
        have ha := hle a List.mem_cons_self
        rw [List.sum_cons]
        linarith
  induction l with
  | nil => simp
  | cons a t ih =>
      intro x hx
      have hta := hsum t fun y hy => hle y (List.mem_cons_of_mem a hy)
      have ha := hle a List.mem_cons_self
      rw [List.sum_cons] at heq
      have hazero : a = 0 := by linarith
      have htzero : t.sum = 0 := by linarith
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hazero
      · exact ih (fun y hy => hle y (List.mem_cons_of_mem a hy)) htzero x hx

/-- **Criticality is tightness.**  A critical edge has zero defect for *every* potential of the
shifted weighting `weight - lam`: along the closed walk of mean `lam` that witnesses the edge, the
defects are nonpositive and telescope to zero, so each of them vanishes. -/
theorem defect_eq_zero_of_isCriticalEdge {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsPotential G (fun e => weight e - lam) φ) {edge : E}
    (hedge : IsCriticalEdge G weight lam edge) :
    defect G (fun e => weight e - lam) φ edge = 0 := by
  obtain ⟨vertex, cycle, -, hmean, hmem⟩ := hedge
  have hzero : walkWeight (fun e => weight e - lam) cycle = 0 := by
    rw [walkWeight_sub_const, nsmul_eq_mul, hmean, sub_self]
  have hsum : (cycle.edges.map (defect G (fun e => weight e - lam) φ)).sum = 0 := by
    rw [sum_defect_eq, hzero]
    ring
  refine eq_zero_of_nonpos_of_sum_eq_zero _ ?_ hsum _ (List.mem_map_of_mem hmem)
  rintro x hx
  rw [List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  exact (isPotential_iff_forall_defect_nonpos G _ φ).1 hφ e

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A walk all of whose edges are tight realizes the difference of the potential at its
endpoints. -/
theorem walkWeight_eq_of_forall_defect_eq_zero {weight : E → 𝕜} {φ : V → 𝕜} {start finish : V}
    (walk : G.Walk start finish) (h : ∀ e ∈ walk.edges, defect G weight φ e = 0) :
    walkWeight weight walk = φ finish - φ start := by
  have hsum : (walk.edges.map (defect G weight φ)).sum = 0 :=
    List.sum_eq_zero <| by
      rintro x hx
      rw [List.mem_map] at hx
      obtain ⟨e, hmem, rfl⟩ := hx
      exact h e hmem
  rw [sum_defect_eq, sub_eq_zero] at hsum
  exact eq_sub_of_add_eq hsum

/-- **The characteristic property of the critical graph.**  Provided `lam` bounds every cycle
mean, every closed walk of the critical subgraph has mean weight exactly `lam` - it can neither
exceed `lam`, since it is a closed walk of the ambient graph, nor fall short of it, since all of
its edges are tight for a common potential of the shifted weighting.  Attainment of the maximum
cycle mean is not used; if `lam` is not attained the critical graph is empty. -/
theorem walkWeight_criticalGraph_eq [Finite E] {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {vertex : V} (cycle : (criticalGraph G weight lam).Walk vertex vertex) :
    walkWeight (criticalWeight G weight lam) cycle = cycle.length * lam := by
  have hshift : ∀ (v : V) (c : G.Walk v v), walkWeight (fun e => weight e - lam) c ≤ 0 := by
    intro v c
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v c]
  obtain ⟨φ, hφ⟩ :=
    (exists_isPotential_iff_forall_closedWalk_nonpos (G := G) (fun e => weight e - lam)).2 hshift
  have htight : ∀ e ∈ (liftCriticalWalk cycle).edges,
      defect G (fun e => weight e - lam) φ e = 0 := by
    intro e hmem
    rw [edges_liftCriticalWalk, List.mem_map] at hmem
    obtain ⟨⟨e, hcrit⟩, -, rfl⟩ := hmem
    exact defect_eq_zero_of_isCriticalEdge hφ hcrit
  have hzero : walkWeight (fun e => weight e - lam) (liftCriticalWalk cycle) = 0 := by
    rw [walkWeight_eq_of_forall_defect_eq_zero _ htight, sub_self]
  rw [walkWeight_sub_const, nsmul_eq_mul, length_liftCriticalWalk,
    walkWeight_liftCriticalWalk] at hzero
  linarith

/-- Every vertex carrying a nonempty closed walk of the critical subgraph is a critical vertex of
the ambient graph. -/
theorem isCriticalVertex_of_criticalGraph_closedWalk [Finite E] {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {vertex : V} (cycle : (criticalGraph G weight lam).Walk vertex vertex)
    (hpos : 0 < cycle.length) : IsCriticalVertex G weight lam vertex := by
  refine ⟨liftCriticalWalk cycle, by rw [length_liftCriticalWalk]; exact hpos, ?_⟩
  rw [length_liftCriticalWalk, walkWeight_liftCriticalWalk]
  exact walkWeight_criticalGraph_eq hcyc cycle

/-! ### The Kleene star

`Maths.MaxPlusPotential.maxRootedWeight` is the all-pairs longest-walk operator, the
Kleene star of the weight matrix, read as a function of both its base and its endpoint.  Its
max-plus algebra is the following: the diagonal is zero
(`Maths.MaxPlusPotential.maxRootedWeight_self`), composition is subadditive, and
`Maths.MaxPlusPotential.maxIncomingWeight` is the largest entry of a column. -/

section Kleene

variable [Finite E]

/-- **The triangle inequality of the Kleene star.**  Concatenating a greatest walk from the base
to an intermediate vertex with a greatest walk from there onwards produces a walk from the base,
so the max-plus product of two entries is dominated by the entry of the composite pair. -/
theorem add_maxRootedWeight_le_maxRootedWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base mid vertex : V} (hfirst : Nonempty (G.Walk base mid))
    (hsecond : Nonempty (G.Walk mid vertex)) :
    maxRootedWeight G weight base mid + maxRootedWeight G weight mid vertex
      ≤ maxRootedWeight G weight base vertex := by
  obtain ⟨first, -, hfirstWeight⟩ := maxRootedWeight_mem hcyc hfirst
  obtain ⟨second, -, hsecondWeight⟩ := maxRootedWeight_mem hcyc hsecond
  have hle := walkWeight_le_maxRootedWeight hcyc (first.append second)
  rwa [walkWeight_append, hfirstWeight, hsecondWeight] at hle

/-- The canonical potential dominates every Kleene-star entry of its column: a greatest walk from
a base is in particular a walk arriving at the endpoint. -/
theorem maxRootedWeight_le_maxIncomingWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {base vertex : V} (hreach : Nonempty (G.Walk base vertex)) :
    maxRootedWeight G weight base vertex ≤ maxIncomingWeight G weight vertex := by
  obtain ⟨walk, hnd, hwalk⟩ := maxRootedWeight_mem hcyc hreach
  exact hwalk ▸ le_maxIncomingWeight ⟨base, walk, hnd, rfl⟩

/-- **`maxIncomingWeight` is one row of the all-pairs operator.**  The canonical potential at a
vertex is the greatest Kleene-star entry in that vertex's column, the maximum being taken over the
bases the vertex is reachable from and being attained. -/
theorem isGreatest_range_maxRootedWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    (vertex : V) :
    IsGreatest {r : 𝕜 | ∃ base : V, Nonempty (G.Walk base vertex) ∧
        r = maxRootedWeight G weight base vertex} (maxIncomingWeight G weight vertex) := by
  obtain ⟨base, walk, hnd, hwalk⟩ := maxIncomingWeight_mem (G := G) weight vertex
  refine ⟨⟨base, ⟨walk⟩, le_antisymm ?_ ?_⟩, ?_⟩
  · exact hwalk ▸ le_maxRootedWeight ⟨walk, hnd, rfl⟩
  · exact maxRootedWeight_le_maxIncomingWeight hcyc ⟨walk⟩
  · rintro r ⟨root, hroot, rfl⟩
    exact maxRootedWeight_le_maxIncomingWeight hcyc hroot

end Kleene

/-! ### The eigenspace -/

/-- The max-plus eigenvalue equation on a weighted digraph: the shifted weighting `weight - lam`
admits `φ` as a potential, and at every vertex some incoming edge makes the inequality an
equality.  On the complete digraph of a matrix this is
`Maths.MaxPlusPotential.IsEigenvector`, by
`Maths.MaxPlusPotential.isEigenvector_iff_isGraphEigenvector`. -/
def IsGraphEigenvector (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) (φ : V → 𝕜) : Prop :=
  IsPotential G (fun e => weight e - lam) φ ∧
    ∀ vertex : V, ∃ edge : E, G.target edge = vertex ∧
      φ (G.source edge) + weight edge = lam + φ vertex

/-- An eigenvector forbids closed walks of mean above `lam`, since it is a potential for the
shifted weighting. -/
theorem IsGraphEigenvector.closedWalk_nonpos {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) (vertex : V) (cycle : G.Walk vertex vertex) :
    walkWeight (fun e => weight e - lam) cycle ≤ 0 :=
  hφ.1.closedWalk_nonpos cycle

/-- **Every critical Kleene-star column is an eigenvector.**  Rooted at a critical vertex, the
greatest weight of a walk in the shifted weighting is a potential by the pruning argument and is
tight at every vertex by the last edge of a greatest arriving walk.  The eigenvalue is `lam`, and
`lam` is only assumed to bound every cycle mean and to be attained at the root. -/
theorem isGraphEigenvector_maxRootedWeight [Finite E] {weight : E → 𝕜} {lam : 𝕜} {base : V}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    (hbase : IsCriticalVertex G weight lam base)
    (hreach : ∀ vertex : V, Nonempty (G.Walk base vertex)) :
    IsGraphEigenvector G weight lam (maxRootedWeight G (fun e => weight e - lam) base) := by
  have hshift : ∀ (v : V) (c : G.Walk v v), walkWeight (fun e => weight e - lam) c ≤ 0 := by
    intro v c
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v c]
  obtain ⟨best, hpos, hmean⟩ := hbase
  have hzero : walkWeight (fun e => weight e - lam) best = 0 := by
    rw [walkWeight_sub_const, nsmul_eq_mul, hmean, sub_self]
  refine ⟨maxRootedWeight_isPotential hshift hreach, fun vertex => ?_⟩
  obtain ⟨e, htarget, htight⟩ :=
    exists_tight_edge_maxRootedWeight hshift hreach best hpos hzero vertex
  exact ⟨e, htarget, by linarith⟩

omit [IsStrictOrderedRing 𝕜] in
/-- Backward tight walks of every length: from any vertex, tightness at every vertex lets one
prepend tight edges indefinitely. -/
theorem exists_walk_length_eq_forall_tight {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) (count : ℕ) (vertex : V) :
    ∃ (base : V) (walk : G.Walk base vertex), walk.length = count ∧
      ∀ e ∈ walk.edges, φ (G.source e) + weight e = lam + φ (G.target e) := by
  induction count generalizing vertex with
  | zero => exact ⟨vertex, .nil, rfl, by simp⟩
  | succ count ih =>
      obtain ⟨edge, htarget, htight⟩ := hφ.2 vertex
      obtain ⟨base, walk, hlen, hall⟩ := ih (G.source edge)
      refine ⟨base, (walk.concat edge rfl).castFinish htarget, by simp [hlen], ?_⟩
      intro e hmem
      rw [EdgeGraph.Walk.edges_castFinish, EdgeGraph.Walk.edges_concat, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact hall e hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        rw [htarget]
        exact htight

/-- **The backward tight walk reaches a critical vertex.**  With finitely many vertices, walking
backwards along tight edges of an eigenvector must revisit a vertex; the closed walk so traversed
is made of tight edges, hence has mean exactly `lam`, so that vertex is critical, and the
remaining tight walk joins it to the vertex one started from. -/
theorem exists_isCriticalVertex_walk_tight [Fintype V] {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) (vertex : V) :
    ∃ (base : V) (walk : G.Walk base vertex), IsCriticalVertex G weight lam base ∧
      ∀ e ∈ walk.edges, φ (G.source e) + weight e = lam + φ (G.target e) := by
  obtain ⟨root, walk, hlen, hall⟩ := exists_walk_length_eq_forall_tight hφ (Fintype.card V) vertex
  have hdup : ¬ walk.visited.Nodup := by
    intro hnd
    have hcard := hnd.length_le_card
    rw [EdgeGraph.Walk.length_visited, hlen] at hcard
    omega
  obtain ⟨base, before, cycle, after, hpos, hedges⟩ := walk.exists_closedSubwalk_of_not_nodup hdup
  have hsub : ∀ e ∈ cycle.edges ++ after.edges, e ∈ walk.edges := by
    intro e hmem
    rw [hedges, List.append_assoc]
    exact List.mem_append_right _ hmem
  have htightCycle : ∀ e ∈ cycle.edges, defect G (fun e => weight e - lam) φ e = 0 := by
    intro e hmem
    have := hall e (hsub e (List.mem_append_left _ hmem))
    simp only [defect]
    linarith
  refine ⟨base, after, ⟨cycle, hpos, ?_⟩, fun e hmem => hall e (hsub e ?_)⟩
  · have := walkWeight_eq_of_forall_defect_eq_zero cycle htightCycle
    rw [walkWeight_sub_const, nsmul_eq_mul, sub_self] at this
    linarith
  · exact List.mem_append_right _ hmem

/-- An eigenvector dominates the max-plus product of any of its values with the corresponding
Kleene-star entry: the entry is realized by a walk, and a potential dominates the weight of every
walk between its endpoints. -/
theorem add_maxRootedWeight_le [Finite E] {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) {base vertex : V}
    (hreach : Nonempty (G.Walk base vertex)) :
    φ base + maxRootedWeight G (fun e => weight e - lam) base vertex ≤ φ vertex := by
  obtain ⟨walk, -, hwalk⟩ := maxRootedWeight_mem hφ.closedWalk_nonpos hreach
  have := hφ.1.walkWeight_le walk
  rw [hwalk] at this
  linarith

/-- **The eigenspace is generated by the critical Kleene-star columns.**  Every eigenvector for
`lam` is, at every vertex, the max-plus combination of the columns of the Kleene star of
`weight - lam` rooted at the critical vertices, with the eigenvector's own values as coefficients;
and the maximum is attained.  Only finiteness of the vertex and edge types is assumed: no
irreducibility, no strong connectivity, and no attainment of the maximum cycle mean. -/
theorem isGreatest_criticalColumns [Fintype V] [Finite E] {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) (vertex : V) :
    IsGreatest {r : 𝕜 | ∃ base : V, IsCriticalVertex G weight lam base ∧
        Nonempty (G.Walk base vertex) ∧
        r = φ base + maxRootedWeight G (fun e => weight e - lam) base vertex} (φ vertex) := by
  obtain ⟨base, walk, hbase, htight⟩ := exists_isCriticalVertex_walk_tight hφ vertex
  refine ⟨⟨base, hbase, ⟨walk⟩, le_antisymm ?_ (add_maxRootedWeight_le hφ ⟨walk⟩)⟩, ?_⟩
  · have hrealize : walkWeight (fun e => weight e - lam) walk = φ vertex - φ base := by
      refine walkWeight_eq_of_forall_defect_eq_zero walk fun e hmem => ?_
      have := htight e hmem
      simp only [defect]
      linarith
    have hle := walkWeight_le_maxRootedWeight hφ.closedWalk_nonpos walk
    rw [hrealize] at hle
    linarith
  · rintro r ⟨root, -, hroot, rfl⟩
    exact add_maxRootedWeight_le hφ hroot

/-! ### The critical classes -/

section CriticalClass

variable [Finite E]

/-- The **critical classes**: the strongly connected components of the critical graph.  This is
`Maths.SCC` of `Maths.MaxPlusPotential.criticalGraph`, so it carries the
reachability partial order of the components and the acyclicity of their condensation. -/
def CriticalClass (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) : Type uV :=
  SCC (criticalGraph G weight lam)

instance CriticalClass.instPartialOrder {weight : E → 𝕜} {lam : 𝕜} :
    PartialOrder (CriticalClass G weight lam) :=
  inferInstanceAs (PartialOrder (SCC (criticalGraph G weight lam)))

/-- The critical class of a vertex. -/
def toCriticalClass (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) (vertex : V) :
    CriticalClass G weight lam :=
  toSCC (criticalGraph G weight lam) vertex

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Finite E] in
/-- Two vertices lie in the same critical class exactly when each is reachable from the other by
a walk of the critical graph. -/
theorem toCriticalClass_eq_iff {weight : E → 𝕜} {lam : 𝕜} {base base' : V} :
    toCriticalClass G weight lam base = toCriticalClass G weight lam base' ↔
      LinkedTo (criticalGraph G weight lam) base base' :=
  toSCC_eq_toSCC_iff_linkedTo

/-- Criticality is a property of the whole class: a vertex in the class of a critical vertex is
itself critical, since joining the two connecting walks of the critical graph produces a nonempty
closed walk of the critical graph, whose mean is exactly `lam`. -/
theorem isCriticalVertex_of_toCriticalClass_eq {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base base' : V} (hbase : IsCriticalVertex G weight lam base)
    (hclass : toCriticalClass G weight lam base = toCriticalClass G weight lam base') :
    IsCriticalVertex G weight lam base' := by
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := toCriticalClass_eq_iff.1 hclass
  rcases Nat.eq_zero_or_pos (backward.append forward).length with hlen | hlen
  · rw [EdgeGraph.Walk.length_append] at hlen
    obtain rfl : base' = base := backward.eq_of_length_eq_zero (by omega)
    exact hbase
  · exact isCriticalVertex_of_criticalGraph_closedWalk hcyc (backward.append forward) hlen

/-- **The two Kleene-star entries between vertices of one critical class are opposite.**  A walk
of the critical graph from one to the other and back is a closed walk of the critical graph, so its
shifted weight is zero; that bounds the sum of the two entries from below, while the triangle
inequality and the vanishing diagonal bound it from above. -/
theorem maxRootedWeight_add_maxRootedWeight_eq_zero {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base base' : V}
    (hclass : toCriticalClass G weight lam base = toCriticalClass G weight lam base') :
    maxRootedWeight G (fun e => weight e - lam) base base'
      + maxRootedWeight G (fun e => weight e - lam) base' base = 0 := by
  have hshift : ∀ (v : V) (c : G.Walk v v), walkWeight (fun e => weight e - lam) c ≤ 0 := by
    intro v c
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v c]
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := toCriticalClass_eq_iff.1 hclass
  set first := liftCriticalWalk forward with hfirst
  set second := liftCriticalWalk backward with hsecond
  have hedges : (liftCriticalWalk (forward.append backward)).edges
      = first.edges ++ second.edges := by
    rw [hfirst, hsecond, edges_liftCriticalWalk, edges_liftCriticalWalk, edges_liftCriticalWalk,
      EdgeGraph.Walk.edges_append, List.map_append]
  have hsplit : walkWeight (fun e => weight e - lam) (liftCriticalWalk (forward.append backward))
      = walkWeight (fun e => weight e - lam) first
        + walkWeight (fun e => weight e - lam) second := by
    simp [walkWeight, hedges]
  have hzero : walkWeight (fun e => weight e - lam) (liftCriticalWalk (forward.append backward))
      = 0 := by
    rw [walkWeight_sub_const, nsmul_eq_mul, walkWeight_liftCriticalWalk,
      length_liftCriticalWalk, walkWeight_criticalGraph_eq hcyc (forward.append backward),
      sub_self]
  have hle := add_maxRootedWeight_le_maxRootedWeight hshift (G := G)
    (weight := fun e => weight e - lam) ⟨first⟩ ⟨second⟩
  rw [maxRootedWeight_self hshift] at hle
  have hfirstLe := walkWeight_le_maxRootedWeight hshift (weight := fun e => weight e - lam) first
  have hsecondLe := walkWeight_le_maxRootedWeight hshift (weight := fun e => weight e - lam) second
  linarith [hsplit ▸ hzero]

/-- **Opposite Kleene-star entries detect the critical class.**  This is the converse of
`Maths.MaxPlusPotential.maxRootedWeight_add_maxRootedWeight_eq_zero`: if the two
entries between two mutually reachable vertices sum to zero, then greatest walks realizing them
concatenate to a closed walk of shifted weight zero, hence of mean exactly `lam`; every edge of
that closed walk is critical, so each of the two walks is a walk of the critical graph and the
vertices lie in one critical class. -/
theorem toCriticalClass_eq_of_maxRootedWeight_add_eq_zero {weight : E → 𝕜}
    {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base base' : V} (hforward : Nonempty (G.Walk base base'))
    (hbackward : Nonempty (G.Walk base' base))
    (hzero : maxRootedWeight G (fun e => weight e - lam) base base'
      + maxRootedWeight G (fun e => weight e - lam) base' base = 0) :
    toCriticalClass G weight lam base = toCriticalClass G weight lam base' := by
  have hshift : ∀ (v : V) (c : G.Walk v v), walkWeight (fun e => weight e - lam) c ≤ 0 := by
    intro v c
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v c]
  obtain ⟨first, -, hfirst⟩ := maxRootedWeight_mem hshift hforward
  obtain ⟨second, -, hsecond⟩ := maxRootedWeight_mem hshift hbackward
  have hcycle : walkWeight (fun e => weight e - lam) (first.append second) = 0 := by
    rw [walkWeight_append, hfirst, hsecond]
    exact hzero
  have hmean : walkWeight weight (first.append second)
      = (first.append second).length * lam := by
    rw [walkWeight_sub_const, nsmul_eq_mul] at hcycle
    linarith
  rcases Nat.eq_zero_or_pos (first.append second).length with hlen | hpos
  · rw [EdgeGraph.Walk.length_append] at hlen
    obtain rfl : base = base' := first.eq_of_length_eq_zero (by omega)
    rfl
  · have hcrit : ∀ e ∈ (first.append second).edges, e ∈ criticalEdges G weight lam :=
      fun e he => isCriticalEdge_of_mem_edges (first.append second) hpos hmean he
    rw [EdgeGraph.Walk.edges_append] at hcrit
    exact toCriticalClass_eq_iff.2
      ⟨EdgeGraph.Walk.nonempty_restrictEdges_of_forall_mem first
        fun e he => hcrit e (List.mem_append_left _ he),
       EdgeGraph.Walk.nonempty_restrictEdges_of_forall_mem second
        fun e he => hcrit e (List.mem_append_right _ he)⟩

/-- **Two Kleene-star columns rooted in the same critical class differ by a constant.**  The
constant is the Kleene-star entry between the two roots, and it does not depend on the vertex at
which the columns are compared.  Only the reachability actually used appears: the vertex has to be
reachable from one of the roots, and the critical graph carries the roots to one another. -/
theorem maxRootedWeight_eq_add_of_toCriticalClass_eq {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base base' vertex : V}
    (hclass : toCriticalClass G weight lam base = toCriticalClass G weight lam base')
    (hreach : Nonempty (G.Walk base vertex)) :
    maxRootedWeight G (fun e => weight e - lam) base' vertex
      = maxRootedWeight G (fun e => weight e - lam) base' base
        + maxRootedWeight G (fun e => weight e - lam) base vertex := by
  have hshift : ∀ (v : V) (c : G.Walk v v), walkWeight (fun e => weight e - lam) c ≤ 0 := by
    intro v c
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v c]
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := toCriticalClass_eq_iff.1 hclass
  have hforward : Nonempty (G.Walk base base') := ⟨liftCriticalWalk forward⟩
  have hbackward : Nonempty (G.Walk base' base) := ⟨liftCriticalWalk backward⟩
  have hreach' : Nonempty (G.Walk base' vertex) :=
    ⟨hbackward.some.append hreach.some⟩
  have hlower := add_maxRootedWeight_le_maxRootedWeight hshift
    (weight := fun e => weight e - lam) hbackward hreach
  have hupper := add_maxRootedWeight_le_maxRootedWeight hshift
    (weight := fun e => weight e - lam) hforward hreach'
  linarith [maxRootedWeight_add_maxRootedWeight_eq_zero hcyc hclass]

/-- Within one critical class the value of an eigenvector at a vertex is recovered exactly from
its value at any other vertex of the class: the inequality of
`Maths.MaxPlusPotential.add_maxRootedWeight_le` holds in both directions, because the
two Kleene-star entries between the roots are opposite. -/
theorem add_maxRootedWeight_eq_of_toCriticalClass_eq {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) {base base' : V}
    (hclass : toCriticalClass G weight lam base = toCriticalClass G weight lam base') :
    φ base' + maxRootedWeight G (fun e => weight e - lam) base' base = φ base := by
  have hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam := by
    intro v c
    have := hφ.closedWalk_nonpos v c
    rw [walkWeight_sub_const, nsmul_eq_mul] at this
    linarith
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := toCriticalClass_eq_iff.1 hclass
  have hfrom := add_maxRootedWeight_le hφ (weight := weight) ⟨liftCriticalWalk backward⟩
  have hto := add_maxRootedWeight_le hφ (weight := weight) ⟨liftCriticalWalk forward⟩
  linarith [maxRootedWeight_add_maxRootedWeight_eq_zero hcyc hclass]

/-- **One Kleene-star column per critical class suffices to generate the eigenspace.**  If `reps`
is a set of critical vertices meeting every critical class that contains a critical vertex, then
every eigenvector is already, at every vertex, the max-plus combination of the columns rooted at
`reps`, with its own values as coefficients, and the maximum is attained.  This is sufficiency of
the family; its minimality is
`Maths.MaxPlusPotential.exists_mem_toCriticalClass_eq_of_generatesEigenspace`. -/
theorem isGreatest_criticalClassColumns [Fintype V] {weight : E → 𝕜} {lam : 𝕜} {φ : V → 𝕜}
    (hφ : IsGraphEigenvector G weight lam φ) {reps : Set V}
    (hreps : ∀ base : V, IsCriticalVertex G weight lam base →
      ∃ root ∈ reps, toCriticalClass G weight lam base = toCriticalClass G weight lam root)
    (vertex : V) :
    IsGreatest {r : 𝕜 | ∃ root ∈ reps, Nonempty (G.Walk root vertex) ∧
        r = φ root + maxRootedWeight G (fun e => weight e - lam) root vertex} (φ vertex) := by
  have hcyc : ∀ (v : V) (cycle : G.Walk v v), walkWeight weight cycle ≤ cycle.length * lam := by
    intro v c
    have := hφ.closedWalk_nonpos v c
    rw [walkWeight_sub_const, nsmul_eq_mul] at this
    linarith
  obtain ⟨⟨base, hbase, hreachBase, hvalue⟩, -⟩ := isGreatest_criticalColumns hφ vertex
  obtain ⟨root, hmem, hclass⟩ := hreps base hbase
  obtain ⟨-, ⟨backward⟩⟩ := toCriticalClass_eq_iff.1 hclass
  refine ⟨⟨root, hmem, ⟨(liftCriticalWalk backward).append hreachBase.some⟩, ?_⟩, ?_⟩
  · rw [maxRootedWeight_eq_add_of_toCriticalClass_eq hcyc hclass hreachBase, hvalue,
      ← add_maxRootedWeight_eq_of_toCriticalClass_eq hφ hclass]
    ring
  · rintro r ⟨root', -, hroot', rfl⟩
    exact add_maxRootedWeight_le hφ hroot'

/-! ### Generating families and their minimality -/

/-- A set of vertices **generates the eigenspace** for `lam` when every eigenvector is, at every
vertex, the max-plus combination of the Kleene-star columns of `weight - lam` rooted at that set,
with the eigenvector's own values as coefficients, the maximum being attained. -/
def GeneratesEigenspace (G : EdgeGraph V E) (weight : E → 𝕜) (lam : 𝕜) (reps : Set V) : Prop :=
  ∀ φ : V → 𝕜, IsGraphEigenvector G weight lam φ → ∀ vertex : V,
    IsGreatest {r : 𝕜 | ∃ root ∈ reps, Nonempty (G.Walk root vertex) ∧
      r = φ root + maxRootedWeight G (fun e => weight e - lam) root vertex} (φ vertex)

/-- **Sufficiency.**  A set of vertices meeting every critical class generates the eigenspace.
This is `Maths.MaxPlusPotential.isGreatest_criticalClassColumns` read through
`Maths.MaxPlusPotential.GeneratesEigenspace`. -/
theorem generatesEigenspace_of_forall_exists_mem [Fintype V] {weight : E → 𝕜} {lam : 𝕜}
    {reps : Set V}
    (hreps : ∀ base : V, IsCriticalVertex G weight lam base →
      ∃ root ∈ reps, toCriticalClass G weight lam base = toCriticalClass G weight lam root) :
    GeneratesEigenspace G weight lam reps :=
  fun _ hφ vertex => isGreatest_criticalClassColumns hφ hreps vertex

/-- **A Kleene-star column is not dominated by the columns rooted outside its own critical
class.**  Whatever coefficients are used, the column rooted at `base` is not the max-plus
combination of the columns rooted at vertices of other critical classes, provided `base` reaches
those vertices.  Evaluating the combination at `base` itself makes some coefficient the negative of
the Kleene-star entry from that root to `base`; evaluating it at the root then forces the two
entries between the root and `base` to be opposite, which puts the root in the critical class of
`base`.

This is the separation the minimality of the family indexed by the critical classes rests on; no
criticality of `base` is used. -/
theorem not_isGreatest_criticalColumns_of_forall_toCriticalClass_ne {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base : V} {reps : Set V} (c : V → 𝕜)
    (hreach : ∀ root ∈ reps, Nonempty (G.Walk base root))
    (hne : ∀ root ∈ reps,
      toCriticalClass G weight lam root ≠ toCriticalClass G weight lam base) :
    ¬ ∀ vertex : V, IsGreatest {r : 𝕜 | ∃ root ∈ reps, Nonempty (G.Walk root vertex) ∧
        r = c root + maxRootedWeight G (fun e => weight e - lam) root vertex}
      (maxRootedWeight G (fun e => weight e - lam) base vertex) := by
  intro hgen
  have hshift : ∀ (v : V) (cycle : G.Walk v v), walkWeight (fun e => weight e - lam) cycle ≤ 0 := by
    intro v cycle
    rw [walkWeight_sub_const, nsmul_eq_mul]
    linarith [hcyc v cycle]
  obtain ⟨⟨root, hmem, hrootBase, hvalue⟩, -⟩ := hgen base
  rw [maxRootedWeight_self hshift] at hvalue
  have hupper := (hgen root).2 ⟨root, hmem, ⟨.nil⟩, rfl⟩
  rw [maxRootedWeight_self hshift] at hupper
  have htriangle := add_maxRootedWeight_le_maxRootedWeight hshift
    (weight := fun e => weight e - lam) hrootBase (hreach root hmem)
  rw [maxRootedWeight_self hshift] at htriangle
  exact hne root hmem <| toCriticalClass_eq_of_maxRootedWeight_add_eq_zero hcyc
    hrootBase (hreach root hmem) (by linarith)

/-- **Minimality of the family indexed by the critical classes.**  Every generating set contains a
vertex of the critical class of `base`, for every critical vertex `base` that reaches the whole
graph.  Together with
`Maths.MaxPlusPotential.generatesEigenspace_of_forall_exists_mem` this says that no
proper subfamily of the one-column-per-critical-class family generates: dropping the class of
`base` costs the eigenvector rooted at `base`.

The reachability hypothesis is what makes the column rooted at `base` an eigenvector at all, by
`Maths.MaxPlusPotential.isGraphEigenvector_maxRootedWeight`, and it is the only
hypothesis beyond finiteness and the bound on the cycle means; neither strong connectivity nor
attainment of the maximum cycle mean is used. -/
theorem exists_mem_toCriticalClass_eq_of_generatesEigenspace {weight : E → 𝕜}
    {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    {reps : Set V} (hreps : GeneratesEigenspace G weight lam reps) {base : V}
    (hbase : IsCriticalVertex G weight lam base)
    (hreach : ∀ vertex : V, Nonempty (G.Walk base vertex)) :
    ∃ root ∈ reps, toCriticalClass G weight lam base = toCriticalClass G weight lam root := by
  by_contra hcon
  push Not at hcon
  exact not_isGreatest_criticalColumns_of_forall_toCriticalClass_ne hcyc
    (maxRootedWeight G (fun e => weight e - lam) base) (fun root _ => hreach root)
    (fun root hmem hclass => hcon root hmem hclass.symm)
    (hreps _ (isGraphEigenvector_maxRootedWeight hcyc hbase hreach))

/-- **The generating sets are exactly the transversals of the critical classes**, once every
critical vertex reaches every vertex.  Sufficiency needs no such hypothesis; minimality does, and
uses it only through the critical vertex whose class is being recovered. -/
theorem generatesEigenspace_iff [Fintype V] {weight : E → 𝕜} {lam : 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle ≤ cycle.length * lam)
    (hreach : ∀ base : V, IsCriticalVertex G weight lam base →
      ∀ vertex : V, Nonempty (G.Walk base vertex))
    (reps : Set V) :
    GeneratesEigenspace G weight lam reps ↔
      ∀ base : V, IsCriticalVertex G weight lam base →
        ∃ root ∈ reps, toCriticalClass G weight lam base = toCriticalClass G weight lam root :=
  ⟨fun hreps base hbase =>
    exists_mem_toCriticalClass_eq_of_generatesEigenspace hcyc hreps hbase (hreach base hbase),
   generatesEigenspace_of_forall_exists_mem⟩

end CriticalClass

/-! ### The max-plus matrix reading -/

section Matrix

universe uι

variable {ι : Type uι}

/-- On the complete digraph of a matrix the two eigenvalue equations agree: the max-plus
eigenvector equation is the graph eigenvalue equation of the matrix weighting. -/
theorem isEigenvector_iff_isGraphEigenvector [Fintype ι] [Nonempty ι] (A : ι → ι → 𝕜) (lam : 𝕜)
    (v : ι → 𝕜) :
    IsEigenvector A lam v ↔ IsGraphEigenvector (matrixGraph ι) (matrixWeight A) lam v := by
  rw [isEigenvector_iff, IsGraphEigenvector, ← isSubeigenvector_iff_isPotential]
  refine and_congr Iff.rfl ⟨fun htight i => ?_, fun htight i => ?_⟩
  · obtain ⟨j, hj⟩ := htight i
    refine ⟨(i, j), rfl, ?_⟩
    simp only [matrixGraph_source, matrixWeight]
    linarith
  · obtain ⟨edge, htarget, hedge⟩ := htight i
    refine ⟨edge.2, ?_⟩
    have hfst : edge.1 = i := htarget
    simp only [matrixGraph_source, matrixWeight, hfst] at hedge
    linarith

/-- **The eigenspace of a max-plus matrix is generated by the critical Kleene-star columns.**
Every eigenvector is the max-plus combination of the columns of the Kleene star of `A - lam`
rooted at the critical vertices, with its own values as coefficients.  No reachability side
condition survives: the graph of a matrix with entries in a field is complete. -/
theorem isGreatest_criticalColumns_matrix [Fintype ι] [Nonempty ι] {A : ι → ι → 𝕜} {lam : 𝕜}
    {v : ι → 𝕜} (hv : IsEigenvector A lam v) (i : ι) :
    IsGreatest {r : 𝕜 | ∃ base : ι, IsCriticalVertex (matrixGraph ι) (matrixWeight A) lam base ∧
        r = v base + maxRootedWeight (matrixGraph ι)
          (fun e => matrixWeight A e - lam) base i} (v i) := by
  obtain ⟨⟨base, hbase, -, hbaseValue⟩, hupper⟩ :=
    isGreatest_criticalColumns ((isEigenvector_iff_isGraphEigenvector A lam v).1 hv) i
  refine ⟨⟨base, hbase, hbaseValue⟩, ?_⟩
  rintro r ⟨root, hroot, rfl⟩
  exact hupper ⟨root, hroot, nonempty_walk_matrixGraph root i, rfl⟩

end Matrix

end MaxPlusPotential

end

end Maths
