# Terminology

The canonical vocabulary of the library. Docstrings, comments, and the README use these terms
and avoid the ones marked *not*. When a domain or a classical source uses another name, a
docstring may mention it once as a gloss ("also called …") without adopting it. The `## Tags`
section of each module lists such names as search keywords, and the index at the end of this
file maps them to the canonical term and the module that develops it.

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
| strongly connected | Every vertex reaches every other (`EdgeGraph.IsStronglyConnected`, matching mathlib's `Quiver.IsStronglyConnected`); `LinkedTo` is mutual reachability of two vertices. | recurrent |
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
| Farkas certificate | A nonnegative combination certifying infeasibility. | incompatibility certificate, obstruction (as a name for the certificate) |
| theorem of the alternative | A statement that exactly one of a system and its certificate exists. | theorem of alternatives, strong duality |
| feasible | Said of an inequality system. Equations are *solvable*. | solvable, for inequalities |
| retention product | The product of retentions over a window (`retentionProd`, `pastRetentionProd`). | transport |

## Spelling

American spelling throughout (*fiber*, *-ize*, *-ization*), except *labelled* and *labelling*,
which the library has always used.

## Identifier conventions

`Cycle` in a declaration name means an arbitrary closed walk, as the implementation notes of
`Maths/Graph/EdgeGraph.lean` state; prose says *closed walk*. Simple cycles are
`IsSimpleCycle`.

## Index of classical and domain names

Names a reader may search for, with the canonical term used here and the module to start from.
Domain readings in the application packages are collected in
[`Applications/CONCEPTS.md`](Applications/CONCEPTS.md) and
[`Applications/THEORY_DICTIONARY.md`](Applications/THEORY_DICTIONARY.md).

| Name | Here | Start at |
| --- | --- | --- |
| abstract interpretation, soundness | lax morphism | [`Multitubes/Morphism`](Maths/Multitubes/Morphism.lean) |
| balance (gain graphs) | flat labelling | [`Graph/WalkLabel`](Maths/Graph/WalkLabel.lean), [`Multitubes/Switching`](Maths/Multitubes/Switching.lean) |
| Bellman equation, Bellman operator | Bellman operator | [`Multitubes/Closure`](Maths/Multitubes/Closure.lean), [`Mixed/Bellman`](Maths/Multitubes/Mixed/Bellman.lean) |
| Bellman-Ford criterion, difference constraints, feasible potential | potential | [`Additive/Potentials`](Maths/Multitubes/Additive/Potentials.lean) |
| chaotic iteration, worklist | fair local relaxation | [`Multitubes/Worklist`](Maths/Multitubes/Worklist.lean) |
| circuit (of a graph), cycle | closed walk, simple cycle | [`Graph/EdgeGraph`](Maths/Graph/EdgeGraph.lean), [`Additive/Cycles`](Maths/Multitubes/Additive/Cycles.lean) |
| circulation, flow decomposition | circulation | [`Graph/Circulation`](Maths/Graph/Circulation.lean), [`Additive/CirculationDecomposition`](Maths/Multitubes/Additive/CirculationDecomposition.lean) |
| closure operator, Moore family, least fixed point | least lax majorant | [`Multitubes/Closure`](Maths/Multitubes/Closure.lean) |
| coboundary, tension, Kirchhoff voltage law | section of translation transport | [`Additive/Exact`](Maths/Multitubes/Additive/Exact.lean) |
| connection, parallel transport, holonomy, monodromy | transport, walk map, holonomy | [`Multitubes/Basic`](Maths/Multitubes/Basic.lean), [`Multitubes/ElementsGraph`](Maths/Multitubes/ElementsGraph.lean) |
| covering graph, derived graph, graph of elements | graph of elements | [`Multitubes/ElementsGraph`](Maths/Multitubes/ElementsGraph.lean) |
| critical graph, Kleene star, max-plus eigenvector | critical graph, eigenvector | [`Additive/CriticalGraph`](Maths/Multitubes/Additive/CriticalGraph.lean), [`Additive/Eigenvector`](Maths/Multitubes/Additive/Eigenvector.lean) |
| Euler circuit, Hierholzer | Eulerian trail | [`Graph/EulerianTrail`](Maths/Graph/EulerianTrail.lean) |
| Farkas lemma, Fourier-Motzkin, infeasibility certificate | Farkas certificate, theorem of the alternative | [`LinearProgramming/FourierMotzkin`](Maths/LinearProgramming/FourierMotzkin.lean), [`FiniteInequality/Basic`](Maths/Multitubes/FiniteInequality/Basic.lean) |
| frustration index | frustration | [`Multitubes/Frustration`](Maths/Multitubes/Frustration.lean) |
| gain graph, voltage graph, switching | monoid labelling, switching | [`Multitubes/Switching`](Maths/Multitubes/Switching.lean), [`Multitubes/Symmetric`](Maths/Multitubes/Symmetric.lean) |
| Galois connection, residuation, residual | lower adjoint, laxification | [`Mixed/AdjointOrder`](Maths/Multitubes/Mixed/AdjointOrder.lean), [`Mixed/Adjoint`](Maths/Multitubes/Mixed/Adjoint.lean) |
| generalized flow, gain flow | Farkas certificate of a max-affine system | [`MaxAffine/Farkas`](Maths/Multitubes/MaxAffine/Farkas.lean) |
| harmonic, superharmonic, subharmonic | section, lax section, oplax section | [`Multitubes/Basic`](Maths/Multitubes/Basic.lean) |
| Helly's theorem, sparse certificate | sparse Farkas certificate | [`MaxAffine/Sparse`](Maths/Multitubes/MaxAffine/Sparse.lean), [`FiniteInequality/Sparse`](Maths/Multitubes/FiniteInequality/Sparse.lean) |
| inductive invariant, pre-invariant, subsolution, supersolution | lax section, oplax section | [`Multitubes/Basic`](Maths/Multitubes/Basic.lean), [`Mixed/Basic`](Maths/Multitubes/Mixed/Basic.lean) |
| Karp's formula, maximum cycle mean, Perron root, tropical spectral radius | maximum cycle mean | [`Additive/CycleMean`](Maths/Multitubes/Additive/CycleMean.lean) |
| Lindley recursion, Loynes construction, Skorokhod reflection | reflection | [`Recursion/TransferSummary`](Maths/Recursion/TransferSummary.lean), [`Recursion/LoynesConstruction`](Maths/Recursion/LoynesConstruction.lean), [`Recursion/TwoSidedReflection`](Maths/Recursion/TwoSidedReflection.lean) |
| linear programming duality, complementary slackness | standard-form duality | [`LinearProgramming/Duality`](Maths/LinearProgramming/Duality.lean) |
| local system, trivialization | trivial holonomy on a component | [`Multitubes/SCC`](Maths/Multitubes/SCC.lean) |
| max-affine eigenvalue, spectrum | eigenvalue, relaxation level | [`MaxAffine/Spectrum`](Maths/Multitubes/MaxAffine/Spectrum.lean), [`MaxAffine/Eigenproblem`](Maths/Multitubes/MaxAffine/Eigenproblem.lean) |
| mean payoff | maximum cycle mean | [`Additive/CycleMean`](Maths/Multitubes/Additive/CycleMean.lean), [`MaxAffine/Sections`](Maths/Multitubes/MaxAffine/Sections.lean) |
| path independence, integrability, flat connection | flat | [`Multitubes/Exact`](Maths/Multitubes/Exact.lean) |
| polarity | mode | [`Mixed/Basic`](Maths/Multitubes/Mixed/Basic.lean) |
| quiver representation, path category | transport, path category | [`Multitubes/Category`](Maths/Multitubes/Category.lean), [`Graph/PathCategory`](Maths/Graph/PathCategory.lean) |
| reduced cost, Johnson reweighting | defect | [`Additive/Potentials`](Maths/Multitubes/Additive/Potentials.lean) |
| shortest path, longest path | path closure | [`Additive/Potentials`](Maths/Multitubes/Additive/Potentials.lean), [`Additive/Budget`](Maths/Multitubes/Additive/Budget.lean) |
| strongly connected component, condensation | strongly connected component | [`Graph/Condensation`](Maths/Graph/Condensation.lean) |
| subeigenvector, subinvariant vector | subeigenvector | [`Additive/Potentials`](Maths/Multitubes/Additive/Potentials.lean) |
| transition system, nondeterministic transition | transport, relation-labelled transport | [`Multitubes/Basic`](Maths/Multitubes/Basic.lean), [`Multitubes/Relational`](Maths/Multitubes/Relational.lean) |
