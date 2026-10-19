# Terminology

The canonical vocabulary of the library. Docstrings, comments, and the README use these terms
and avoid the ones marked *not*. When a domain or a classical source uses another name, a
docstring may mention it once as a gloss ("also called …") without adopting it.

## Graphs and walks

| Term | Meaning | Not |
| --- | --- | --- |
| directed multigraph | An `EdgeGraph`: edges are objects with a `source` and a `target`, so parallel edges stay distinct. | digraph (mathlib's `Digraph` has no parallel edges), edge graph |
| vertex, edge | The objects of the graph. | node, arc, transition, state |
| source, target | The endpoints of an edge. | head, tail |
| `start`, `finish` | Binder names for the endpoints of a walk. | `source`, `target` as vertex binders |
| walk | A typed finite sequence of composable edges, `G.Walk start finish`. | route; path (see below) |
| path | Only in the fixed phrases *path category*, *path functor*, *path closure*, *path independence*. Never a vertex-simple walk. | |
| closed walk | A walk whose endpoints agree. Its common endpoint is its *base*. | loop, circuit, cycle (in prose) |
| cycle | In prose, only in *simple cycle*, *cycle mean*, and named results such as the Kolmogorov cycle criterion. In identifiers (`HasTrivialCycleLabels`, `HasZeroCycleSums`, …) it means an arbitrary closed walk; see the implementation notes of `Maths/Graph/EdgeGraph.lean`. | |
| simple cycle | A closed walk with no proper closed subwalk, `IsSimpleCycle`. | simple circuit |
| loop | A one-edge closed walk. | a closed walk of any length |
| circuit | Only the matroid sense: a minimal dependent set, as in `IsPositiveCircuit`. | |
| trail | A walk with pairwise distinct edges. | |
| return walk | A walk back from the target of a walk, or of an edge, to its start. | return map |
| base, root | `base`: the base of a closed walk or a basepoint. A root is a base reaching every vertex (`RootReaches`). | |
| strongly connected | Every vertex reaches every other; `LinkedTo` is mutual reachability of two vertices. | recurrent |
| weakly connected | Connected after forgetting edge directions, as for circulation supports. | connected, when the weak sense is meant |

## Transports

| Term | Meaning | Not |
| --- | --- | --- |
| fiber | The type `Fiber v` carried by a vertex. *State space* may gloss it once. | fibre, carrier, value type |
| transport | The structure `Transport G Fiber`: an edge map for every edge, read as *a transport on `G`*, like an action. As a verb, *transports a point along a walk*. | path action, operator-labelled quiver |
| edge map | `T.edgeMap e : Fiber (source e) → Fiber (target e)`. | |
| walk map | `T.walkMap w`, the chronological composite of the edge maps along `w`. | walk transport, return map |
| holonomy | The walk map of a closed walk. With monoid labels it is the *cycle label*, and with additive data the *cycle sum*. Monodromy appears only for graphs of elements. | |
| operator-labelled transition graph | Informal name for a graph together with a transport. | |
| function-labelled, relation-labelled | Transports whose edges carry functions, or relations (`RelationTransport`, with `edgeRelation` and `walkRelation`). | map-labelled, operator-valued, relation-valued |
| family | A choice `x : ∀ v, Fiber v` of one value per vertex, before any condition is imposed; a *candidate* when it is tested against a condition. | section, for an arbitrary family |
| section | A family with `T.edgeMap e (x s) = x t` on every edge (`IsSection`). Unqualified, it always means exact. | |
| rooted section | A section with a prescribed value at a root (`IsRootedSection`, `rootedSection`). | section with base |
| flat | Trivial holonomy (`HasTrivialHolonomy`, `HasTrivialCycleLabels`, `IsFlatAt`). | integrable, consistent |
| balanced | The gain-graph name for flat, used only in the Zaslavsky files (Switching, Frustration, Symmetric). Elsewhere it keeps its own meaning: in-degree equals out-degree for circulations, and balanced certificates. | |
| label | Monoid-valued edge data `E → M`, with walk label `walkLabel`. | |
| weight | Additive edge data `E → A`. | `w`, cost, length |
| charge | Group-valued edge data whose walk sums measure circulation imbalance (Graph layer). | |
| gain | In the Zaslavsky files, a unit-valued label. In *gain flow* and *generalized flow*, the factor by which a branch scales the flow it carries, which is the slope of that branch. | gain for the slope of a label |
| potential | A vertex function that is an additive lax section (`IsPotential`), or an exact one when said (`basePotential`). A *unit potential* is a multiplicative exact one. | |
| gauge | A positive vertex scaling of slopes (`IsContractiveGauge`, `IsNonexpansiveGauge`). *Gauge transformation* in Switching is the standard name for a fiberwise isomorphism and is unrelated. | contraction gauge |

## Ordered and mixed constraints

| Term | Meaning | Not |
| --- | --- | --- |
| lax section | `T.edgeMap e (x s) ≤ x t` on every edge. Equivalently a pre-fixed point `incomingSup x ≤ x`; also a superharmonic family, a subeigenvector in max-plus, or an inductive invariant. | subsolution, supersolution, pre-invariant |
| oplax section | `x t ≤ T.edgeMap e (x s)` on every edge; a post-fixed point `x ≤ incomingInf x`. | supersolution, post-invariant |
| pre-fixed point, post-fixed point | `f a ≤ a` and `a ≤ f a`, as in mathlib. | sub-fixed point |
| mode | The per-edge choice `EdgeMode`: `lax`, `exact`, or `oplax`. A *mixed section* satisfies each edge's mode. | polarity |
| lower adjoint, upper adjoint | The two sides of a `GaloisConnection`, as in mathlib. Relative to a relation, `IsLowerAdjointFor` is the map that reverses an oplax constraint. | residual, left adjoint, right adjoint |
| laxification | The graph and transport that turn a mixed section into an all-lax one. | adjoint reversal, as a name for the construction |
| path closure | The join over all walks of transported lower data (`pathClosure`, `maxIncomingWeight`). | path envelope |
| least lax majorant | The least lax section above given lower data (`leastLaxMajorant`). | |
| Bellman operator | `lower ⊔ incomingSup` (`bellman`). | |
| relation | The parameter of a relation-parametric statement, which need not be an order. | comparison relation |

## Quantitative layers

| Term | Meaning | Not |
| --- | --- | --- |
| slope, shift, floor | The coefficients of a max-affine label `x ↦ max floor (shift + slope * x)`. Queueing names (retention, service) may gloss them in the reflection files. | gain, bias, offset, rate |
| defect | The per-edge failure of an inequality: positive when violated, the negative of LP slack. | edge slack |
| residual | The per-row or per-branch failure, as in `WorstResidualAtMost`. | |
| slack | Only LP complementary slackness. | |
| relaxation level | The uniform level `lam` subtracted from every label (`relaxationLevels`, `IsCyclicRelaxationLevel`). The least one, when it exists, is a *relaxation threshold* (`cyclicRelaxationThreshold`). | slack |
| subeigenvector | `A ⊙ v ≤ lam + v`, following Butkovič. The set of such `lam` is a ray of *subeigenvalue levels*. | admissible eigenvalues |
| eigenvalue | A `lam` admitting an exact eigenvector. | |
| maximum cycle mean | The supremum of mean weights of nonempty closed walks; also the max-plus Perron root and the tropical spectral radius. | |
| critical | Only for the critical graph of a cycle mean (`IsCriticalEdge`, `IsCriticalVertex`). Other uses carry a qualifier: recession-critical rows, gauge-critical edges. | |
| Farkas certificate | A nonnegative combination certifying infeasibility. | incompatibility, obstruction (as a name for the certificate) |
| theorem of the alternative | A statement that exactly one of a system and its certificate exists. | theorem of alternatives, strong duality |
| feasible | Said of an inequality system. Equations are *solvable*. | solvable, for inequalities |
| retention product | The product of retentions over a window (`retentionProd`, `pastRetentionProd`). | transport |

## Spelling

American spelling throughout (*fiber*, *-ize*, *-ization*), except *labelled* and *labelling*,
which the library has always used.

## Identifier exceptions

These identifiers predate the vocabulary above and keep their names until they are renamed.

- `*Cycle*` in declaration names means *closed walk*.
- `MaxAffine/AnchoredEigenvalue.lean` is about eigenvectors from reachable lower bounds.
