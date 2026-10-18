# Gain-graph connections in computer science

Baseline: `20d22aa`. Checked on 2026-10-18.
This reviews a survey of where Zaslavsky gain graphs appear in computer science: Unique Games,
relational abstract domains, graph lifts, parameterized algorithms, and group synchronization.
It records what the library already proved, which survey claims are inaccurate, and four
additions. Their mathematics is classical; no literature novelty is claimed.

**Status.** All four are implemented; see [Implementation](#implementation). Proposal C was
placed in `Applications/ProgramSemantics` instead of the core: octagon constraints are an
abstract-interpretation domain using the additive potential theory, not new transport theory.

## Current coverage

| Survey concept | Status | Declarations |
| --- | --- | --- |
| Gain, switching by `ζ : V → G` | Generalized to monoid labels and unit-valued switching functions. | `Maths.switch`, `Maths.switch_switch`, `Maths.switch_one` |
| Balanced ⇔ switching of the trivial gain | Proved when every edge endpoint is linked to one base. | `Maths.hasTrivialCycleLabels_iff_exists_switch_one` |
| Satisfying assignment unique after fixing a root | Proved; potentials form a torsor for the unit group. | `Maths.existsUnique_normalizedUnitPotential_of_trivialCycleLabels` |
| Spanning-tree balance test | Proved as a finite test: chosen root and return walks, one loop per edge. No algorithm. | `Maths.trivialCycleLabels_iff_chosen_root_return_tests` |
| Difference constraints, Bellman-Ford potentials | Proved, with SCC decomposition and finite certificates. | `Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos`, `Maths/Multitubes/Additive/Condensation.lean` |
| Cycle consistency of noisy measurements | Additive, unit-scale case only. | `CellularSheaves.RationalSensorNetwork.exists_isConsistent_uniform_iff_closedWalk_le` |
| Frustration index, Unique Games beyond exact satisfiability | Absent. | |
| Octagon / UTVPI constraints | Absent. Max-affine labels are monotone and cannot express `x ↦ -x + c`. | |
| Derived (covering) graph, k-lifts | Absent. | |
| Frame and lift matroids | Absent. | |
| Noisy non-abelian synchronization, connection Laplacian | Absent. The exact theory covers any group. | |

## Corrections to the survey

These matter before any of the survey is quoted in documentation.

1. **Unique Games satisfiability is not balance.** A Unique Games assignment is `ζ : V → Σ`, a
   *section* of the transport whose fiber is `Σ` and whose edge maps are the permutations
   `π_uv`. Balance asks for a *switching* `ζ : V → S_k`, which is strictly stronger. One vertex,
   one loop labelled by the transposition `(0 1)` on `Σ = {0, 1, 2}`: the assignment `2`
   satisfies it, yet the gain is unbalanced. The two notions agree when the group acts
   simply transitively on the alphabet, as in Max-2-Lin(k) over `ℤ/k`.
   The correct criterion is already in the library. On a strongly connected graph with
   injective edge maps, satisfying assignments through `a` at the base exist exactly when every
   base holonomy fixes `a`, and are then unique
   (`Maths.Transport.existsUnique_section_of_base_fixed_of_injective_returns`).
   So full satisfiability means the holonomy group at the base has a fixed point.
2. **Signed-graph frustration is Max-Cut only for all-negative signs.** In general it is a
   correlation-clustering style objective. The Goemans-Williamson ratio applies to the
   Max-Cut special case.
3. **Linear-time balance testing** assumes constant-time group operations and equality tests.
4. **The octagon doubled graph is not the derived graph of the sign gain.** See proposal C.
5. **The library's balance is directed.** `Maths.HasTrivialCycleLabels` quantifies over
   directed closed walks. Classical gain graphs are undirected: an edge may be traversed
   backwards with the inverse gain. On a directed acyclic graph, every gain is vacuously
   balanced in the library's sense, while the underlying undirected graph may contain
   unbalanced cycles. Proposal A closes this gap.

## Proposed additions

### A. Classical gain graphs and component-wise switching

*Priority: first. It is small, and every undirected application in the survey depends on it.*

**Symmetrization.** `Maths.AdditiveTransport.signedGraph` in
`Maths/Multitubes/Additive/Circuits.lean` already builds the graph with both orientations of
every edge identity. It mentions only graphs, so it belongs in `Maths/Graph/EdgeGraph.lean`.
Its name also collides with Zaslavsky's *signed graph* (a `ℤ/2`-gain graph), which proposal C
needs. Move it as `Maths.EdgeGraph.symmetrization : EdgeGraph V (E × Bool)`, and keep the
additive name as an abbreviation if the applications' churn is not wanted.

For a unit- or group-valued gain `φ`, the symmetric gain gives `φ e` forward and `(φ e)⁻¹`
backward. Classical balance of `(G, φ)` is then `Maths.HasTrivialCycleLabels` of the
symmetric gain on the symmetrization. No new predicate is needed.

**Component-wise switching.** The rooted theorem requires one base linked to every edge
endpoint, which excludes disconnected graphs. The hypothesis the proof actually uses is
local:

```text
theorem hasTrivialCycleLabels_iff_exists_switch_one_of_edge_return
    (hreturn : ∀ edge, Nonempty (G.Walk (G.target edge) (G.source edge))) :
    HasTrivialCycleLabels G label ↔ ∃ η : V → Mˣ, label = switch G η 1
```

The hypothesis says every edge lies on a closed walk. Proof: choose a representative in each
strongly connected component, take the rooted unit potential there, and glue the pieces. Every
edge has both endpoints in one component, so each edge condition is checked inside a single
component. The monoid hypotheses are the same as for the rooted theorem. A symmetrization
satisfies `hreturn` trivially, using the reverse edge.

**Corollaries.**
- Classical Zaslavsky balance: for any graph `G` and group gain, balance of the symmetric gain
  holds exactly when the gain is a switching of the trivial gain. There is no connectivity
  hypothesis.
- Max-2-Lin(k) and difference equations: an instance is fully satisfiable exactly when it is
  balanced. This is the simply transitive case.
- Unique Games, stated correctly: on the symmetrization of a weakly connected constraint graph,
  satisfying assignments correspond bijectively to the points fixed by the base holonomy group.
  The bijection is evaluation at the base. Both directions are corollaries of existing section
  theorems.

**Placement.** `symmetrization` goes in `Maths/Graph/EdgeGraph.lean`. The gluing theorem goes in
`Maths/Multitubes/Switching.lean`. The Unique Games corollary is a short application-style
statement and can live beside the switching results or in `Applications/`.

### B. The graph of elements of a transport

*Priority: second. It is the construction behind lifts, covers, and state-space unfolding.*

For `T : Transport G Fiber`, define

```text
Transport.elementsGraph T : EdgeGraph (Σ v, Fiber v) (Σ e, Fiber (G.source e))
  source ⟨e, x⟩ = ⟨G.source e, x⟩
  target ⟨e, x⟩ = ⟨G.target e, T.edgeMap e x⟩
```

The name follows mathlib's `CategoryTheory.Functor.Elements`, which is the same construction
for a functor out of the free category. With group gains acting on the group itself, this graph
is the Gross-Tucker derived graph `Γ ×_φ 𝔊`. With a finite permutation action it is a k-lift.
With `ℤ/2` it is the 2-lift of the Bilu-Linial and Marcus-Spielman-Srivastava papers.

**Main results.**
- `Walk.lift T w x : (elementsGraph T).Walk ⟨s, x⟩ ⟨t, T.walkMap w x⟩` and
  `project_lift : (lift T w x).project = w`.
- Unique path lifting, stated without dependent equalities: every walk of the elements graph
  out of `⟨s, x⟩` finishes at `⟨_, T.walkMap p.project x⟩`, and it equals the lift of its
  projection as an element of `Σ finish, Walk ⟨s, x⟩ finish`.
- Holonomy as monodromy: a closed walk `w` lifts to a closed walk from `x` exactly when
  `T.holonomy w x = x`.
- Balance as triviality of the cover: for monoid labels acting on `M` by left multiplication,
  `Maths.HasTrivialCycleLabels G label` holds exactly when every closed walk lifts to a closed
  walk from `1`. No group hypothesis is needed. If `m * 1 = 1` then `m = 1`.
- Sections as sheets: `T.IsSection σ` holds exactly when `{⟨v, σ v⟩}` is closed under the
  out-edges of the elements graph.
- Switching acts by isomorphism: `⟨v, x⟩ ↦ ⟨v, η v * x⟩` on vertices and
  `⟨e, x⟩ ↦ ⟨e, η (G.source e) * x⟩` on edges is an isomorphism from the elements graph of
  `label` to that of `switch G η label`. This is the classical statement that switching
  equivalent gains have isomorphic derived graphs.
- Relational version: `RelationTransport.elementsGraph` has edges
  `Σ e, {p // R e p.1 p.2}`. `walkRelation w x y` holds exactly when some walk of this graph
  from `⟨s, x⟩` to `⟨t, y⟩` projects to `w`. Lifting exists but is not unique. This is the
  state-space unfolding used by the program-semantics and model-checking applications.

**Implementation notes.** `EdgeGraph` has no morphism or isomorphism notion yet. Add a minimal
`Maths.EdgeGraph.Iso`, made of vertex and edge equivalences commuting with source and target,
in `Maths/Graph/` because it mentions only graphs. Walk lifting will hit the same
`fiberCast` transport as `Maths.Transport.walkMap`. Follow the CLAUDE.md advice and state
endpoint identities through sigma types instead of forcing casts.

**Not included.** The adjacency splitting `A(Γ ×_φ ℤ/2) ≅ A(Γ) ⊕ A_φ(Γ)` and the interlacing
argument of Marcus, Spielman, and Srivastava are linear algebra and spectral theory. They are
plausible later work on top of the elements graph, but this note does not propose them.

### C. Real UTVPI (octagon) feasibility by skew-symmetric doubling

*Priority: third. It extends the additive potential theory to the octagon abstract domain.*

Write every unit two-variable constraint as `σ_v x_v - σ_u x_u ≤ c` with signs `σ ∈ {±1}`.
This covers `x_v - x_u ≤ c`, `x_u + x_v ≤ c`, and `-x_u - x_v ≤ c`. A unary bound `x_v ≤ c`
is the case `u = v`, `σ_u = -1` with bound `2c`.

The doubled graph has vertices `V × {±1}`. Each constraint contributes two edges, both of
weight `-c` under the `Maths.MaxPlusPotential.IsPotential` convention
`φ (source) + weight ≤ φ (target)`:

```text
(v, σ_v)  → (u, σ_u)
(u, -σ_u) → (v, -σ_v)
```

**Theorem.** Over a linearly ordered field, the UTVPI system is feasible exactly when the
doubled graph admits a potential. Under the hypotheses of
`Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos`, this holds exactly when
no closed walk of the doubled graph has positive weight.

*Proof.* For the forward direction, put `φ (w, σ) = σ x_w`. Conversely, put
`x_w = (φ (w, 1) - φ (w, -1)) / 2`. Add the two edge inequalities of one constraint and use
`φ (w, σ) - φ (w, -σ) = 2 σ x_w`. Every cancellation is in pairs. The argument needs division
by two and nothing else.

The doubled graph is invariant under the involution `(v, σ) ↦ (v, -σ)` with edge reversal.
It is the skew-symmetric double cover of a bidirected graph, not the elements graph of
proposal B. The elements graph of a sign gain sends both sheets in the edge's own direction;
the octagon cover reverses one of them. Bidirected graphs are Zaslavsky's oriented signed
graphs, so this remains gain-graph theory, but the two constructions should not be identified.

**Follow-ups.**
- Tightest implied bounds, the correctness of strong closure, come from path weights in the
  doubled graph. Check first whether the additive layer already exposes least or greatest
  potentials in this form.
- The integer case is a genuine TODO. `2x ≤ 1` and `-2x ≤ -1`, entered as two unary
  constraints, are feasible over `ℚ`, infeasible over `ℤ`, and the doubled graph has no
  positive cycle. Integer feasibility needs the tightening step `⌊c / 2⌋` on unary bounds.
  Its correctness is the theorem of Lahiri and Musuvathi, and of Bagnara, Hill, and Zaffanella.

**Placement.** The constraint system, doubled graph and feasibility theorem form one domain
client of `Maths.MaxPlusPotential`, so they live together in
`Applications/ProgramSemantics/ProgramSemantics/Octagon.lean`. Nothing in them is reused by the
core.

### D. Frustration certificates

*Priority: optional. Depends on A.*

For a group gain on a finite edge type, let the frustration index be
`min over η of #{e | switch G η φ e ≠ 1}` on the symmetrization.

- **Deletion equals switching.** The frustration index equals the least number of edges whose
  deletion leaves a classically balanced gain. Given a balancing deletion set, component-wise
  switching from proposal A trivializes the remaining edges. Conversely, the edges that a
  switching makes trivial carry a balanced gain.
- **Packing lower bound.** Any `k` edge-disjoint unbalanced closed walks certify a frustration
  index of at least `k`. This is the lower-bound half of a certificate pair, matching the
  library's existing cycle-mean certificates.

These are exact combinatorial statements. Approximation ratios and hardness belong elsewhere.

## Out of scope

- The Unique Games Conjecture, Goemans-Williamson, and any approximation or hardness claim.
  These concern complexity classes, not the structure of sections.
- Frame and lift matroids, representative sets, and FPT kernels for Odd Cycle Transversal and
  Group Feedback Vertex Set. There is no matroid layer, and building one only for this
  connection would not serve the rest of the library.
- Half-integrality of signed-graph LPs. The LP layer exists, but total dual half-integrality
  is a separate polyhedral project.
- Noisy synchronization over `SO(3)`: connection Laplacians, spectral and SDP relaxations.
  The exact cycle-consistency statement is already covered by proposal A's corollaries over
  any group.

## Implementation

| Proposal | Declarations | Notes |
| --- | --- | --- |
| A | `Maths.EdgeGraph.symmetrization`, `Maths.HasEdgeReturns`, `Maths.exists_unitPotential_of_trivialCycleLabels_of_hasEdgeReturns`, `Maths.hasTrivialCycleLabels_iff_exists_switch_one_of_hasEdgeReturns`, `Maths.hasTrivialCycleLabels_symmetricGain_iff`, `Maths.Transport.ofEquivsSectionEquiv` | `AdditiveTransport.signedGraph` is now an abbreviation of the symmetrization. The rooted switching theorem is a corollary of the component-wise one. The per-edge argument is shared through `Maths.label_eq_linkedUnit`. |
| B | `Maths.EdgeGraph.Hom`, `Maths.EdgeGraph.Iso`, `Maths.EdgeGraph.Walk.map`, `Maths.Transport.elementsGraph`, `Maths.Transport.liftWalk`, `Maths.Transport.heq_liftWalk`, `Maths.Transport.holonomy_eq_iff_exists_closed_lift`, `Maths.hasTrivialCycleLabels_iff_forall_closed_lift`, `Maths.Transport.sheet`, `Maths.switchElementsIso`, `Maths.RelationTransport.mem_walkRelation_iff_exists_walk` | Unique lifting is stated as an endpoint equation plus heterogeneous equality of walks. The elements graph is reducible so that endpoint retyping stays type-correct during rewriting. |
| C | `ProgramSemantics.Octagon.feasible_iff_exists_isPotential`, `ProgramSemantics.Octagon.feasible_iff_forall_closedWalk_nonneg`, `ProgramSemantics.Octagon.integer_gap` | Over any linearly ordered field. The integer counterexample is checked. |
| D | `Maths.frustrationIndex`, `Maths.frustrationIndex_eq_sInf_deletion`, `Maths.le_frustrationIndex_of_disjoint` | For gains in the unit group of any monoid on a finite edge type. |

`Maths.EdgeGraph.restrictEdges` moved from `Additive/CriticalGraph.lean` to the graph layer,
since frustration needs it and it mentions only graphs.

## TODO

1. Integer octagon feasibility: tightening of unary bounds and its correctness.
2. Tightest implied octagon bounds as path weights in the doubled graph, that is, correctness
   of strong closure.
3. The adjacency splitting of 2-lifts, on top of the elements graph, if a spectral layer is ever
   wanted.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory Ser. B 47
  (1989), 32-52.
* J. L. Gross and T. W. Tucker, *Topological Graph Theory*, Wiley (1987), chapter 2, for
  voltage graphs and derived graphs.
* S. Khot, *On the power of unique 2-prover 1-round games*, STOC 2002.
* A. Marcus, D. A. Spielman, and N. Srivastava, *Interlacing families I: bipartite Ramanujan
  graphs of all degrees*, Ann. of Math. 182 (2015), 307-325.
* A. Miné, *The octagon abstract domain*, Higher-Order and Symbolic Computation 19 (2006),
  31-100.
* S. K. Lahiri and M. Musuvathi, *An efficient decision procedure for UTVPI constraints*,
  FroCoS 2005.
* R. Bagnara, P. M. Hill, and E. Zaffanella, *An improved tight closure algorithm for integer
  octagonal constraints*, VMCAI 2008.
* A. Singer, *Angular synchronization by eigenvectors and semidefinite programming*, Appl.
  Comput. Harmon. Anal. 30 (2011), 20-36.
