# Core concepts in domain language

These are concept families, not one alias for every declaration. A domain name is useful only
after choosing the carrier, comparison, and transport direction. The
[application dictionary](CONCEPTS.md) identifies the implemented choices and their formal bridges.
The links below give the precise hypotheses of the generic constructions.

## Transport and constraints

For an edge from `s` to `t`, write its map as `T : X(s) → X(t)` and a candidate family as `x`.
An exact section satisfies `T(x(s)) = x(t)`; a lax section satisfies `T(x(s)) ≤ x(t)`;
an oplax section satisfies `x(t) ≤ T(x(s))`. These are the definitions, regardless of the
physical direction represented by the edge. General relation comparisons need not be orders.

| Concept | Domain meanings and names | What the name needs |
| --- | --- | --- |
| [Fiber and transport](../Maths/Multitubes/Basic.lean) | Local state space, predicate lattice, covariance cone, observable space, or stalk; a local update or restriction. | The fiber may contain certificates about physical states, rather than the physical states themselves. Different vertices may have different types. |
| [Walk and walk map](../Maths/Graph/EdgeGraph.lean) | Execution trace and its transformer; dependency chain and accumulated update; composed relation or restriction. | A typed finite route follows the chosen arrows. For pullback semantics those arrows reverse the physical transitions. |
| [Holonomy](../Maths/Multitubes/Basic.lean) | Closed-route composite, loop transformer, return operator; accumulated delay in additive timing. | Group holonomy or local-system monodromy is a more specialized reading requiring invertible transport. A loop composite alone is neither curvature nor a stability theorem. |
| [Exact section](../Maths/Multitubes/Basic.lean) | Compatible sheaf assignment, coherent local values, edgewise exact covariance update, harmonic observable family. | Equality must hold on every edge. An invariant value for a loop is weaker than identity of the loop map on the whole fiber. |
| [Lax section](../Maths/Multitubes/Basic.lean) | Inductive predicate, upper propagated covariance bound, invariant error radius, reversed-pullback superharmonic or storage certificate. | Comparison and orientation fix the interpretation. The same inequality cannot be called “decrease” independently of them. |
| [Oplax and mixed sections](../Maths/Multitubes/Mixed/Basic.lean) | Lower propagated bounds; post-fixed simulation relations; families of upper, lower, and equality constraints. | There is no single established domain name for every mixed family. Polarity is inequality direction, not game priority or ownership. |
| [Relation-labelled transport](../Maths/Multitubes/Relational.lean) | Nondeterministic transition, component feasibility relation, set-valued portfolio transfer, span compatibility. | Composition is existential relational composition. A nonfunctional relation should not be named a deterministic update. |
| [Transport morphism and upper simulation](../Maths/Multitubes/Morphism.lean) | Intertwining maps, change of representation, sound abstraction, one-sided comparison of systems. | Exact commuting maps and inequality simulations have different strength. An upper simulation need not be a bisimulation, invertible encoding, or complete abstraction. |
| [Adjoint reversal](../Maths/Multitubes/Mixed/AdjointOrder.lean) | Strongest-postcondition/weakest-precondition conversion; dilation/erosion residuation; backward constraint propagation. | The chosen maps must satisfy an order adjunction. An order adjoint is neither an inverse nor a Hilbert-space adjoint. |

## Aggregation, feasibility, and reduction

| Concept | Domain meanings and names | What the name needs |
| --- | --- | --- |
| [Path closure](../Maths/Multitubes/Closure.lean) | All-path reachable states, generated evidence, propagated resource envelope. | Joins collect path images. Their identification with the least invariant family needs the stated join-preservation hypothesis. |
| [Least lax majorant](../Maths/Multitubes/Closure.lean) | Least inductive invariant containing seeds; least sound evidence extension; least feasible envelope above lower data. | Complete lattices and monotone maps give the fixed-point construction. Execution or an effective termination bound needs more. |
| [Fair worklist relaxation](../Maths/Multitubes/Worklist.lean) | Chaotic iteration, local constraint propagation, or repeated dataflow sweeps. | With monotone edge maps and complete-lattice fibers as in the preceding row, a fair schedule reaches the least lax majorant under ACC on the product order. For finite sweep iteration, the edge list must cover every edge. Fairness alone gives no step bound. |
| [Bellman operator and fixed point](../Maths/Multitubes/Closure.lean) | Dataflow equation, aggregate resource demand, dynamic-programming update, invariant envelope equation. | Equality is after joining incoming demands and any prescribed seed. Incoming demands zero and one can have aggregate value one although the first constraint is loose. |
| [Mixed Bellman interval](../Maths/Multitubes/Mixed/Bellman.lean) | Simultaneous lower-demand and upper-demand feasibility; ordered subsolution/supersolution constraints. | Lower incoming values are joined and upper values met. This is an order interval, not necessarily a real interval; it need not have a special field-specific name. |
| [Strongly connected components](../Maths/Multitubes/SCC.lean) and [condensation](../Maths/Multitubes/Additive/Condensation.lean) | Mutual-reachability blocks and an acyclic dependency graph of blocks. | A graph decomposition alone does not make local solutions compatible across blocks. The normal-form and assembly results have additional hypotheses. |
| [Retract normal form](../Maths/Multitubes/CategoricalRetracts.lean) | Split image or reduced compatible interface with explicit inclusion and retraction. | It is not automatically a quotient, isomorphism, sufficient statistic, or minimum representation. Information preservation must be stated for the domain. |
| [Finite inequality system](../Maths/Multitubes/FiniteInequality/Basic.lean) | Linear feasibility: sensor tolerance constraints, comparison-radius budgets, branch inequalities. | The encoded matrix and inequalities must match the intended model; feasibility of the encoding is the actual conclusion. |
| [Normalized dual certificate](../Maths/Multitubes/FiniteInequality/Quantitative.lean) | Farkas obstruction or optimality lower bound: a nonnegative, unit-mass combination cancels the unknowns. | Unit mass fixes scale; it does not supply a probability model. General row balance need not be ordinary conservation of edge flow. |
| [Sparse certificate](../Maths/Multitubes/FiniteInequality/Sparse.lean) | An obstruction using few rows, with a rank-based support bound. | Small support does not mean minimum support, a unique explanation, or a diagnosed defective component. |
| [Active optimal certificate](../Maths/Multitubes/FiniteInequality/OptimalCertificate.lean) | Balanced active residuals explaining a Chebyshev or worst-case affine optimum. | The least residual level must be attained. A matching certificate can use at most the row-span rank plus one rows; this is not ordered polynomial alternation. |
| [Rational witness checker](../Maths/LinearProgramming/CertificateCheck.lean) | Exact validation of a supplied feasible point or infeasibility certificate. | Checking is executable; searching for a witness or optimizing is a separate operation. |
| [Parametric feasibility](../Maths/Multitubes/FiniteInequality/Parametric.lean) | Admissible tolerance levels, budget ranges, or eigenlevels. | Fixed row normals and continuous bounds give closedness; affine bounds in one real parameter give convexity. These are mathematical properties, not a solver. |

The closure distinction matches the path-versus-fixed-point distinction in
[Cousot's account of abstract interpretation](https://www.di.ens.fr/~cousot/AI/).
The dilation/erosion terminology uses an order adjunction: its two composites give an opening
and a closing, not mutually inverse maps; see
[Goutsias and Heijmans' lattice treatment](https://ir.cwi.nl/pub/1185/1185D.pdf).

## Scalar, spectral, and graph specializations

| Concept | Domain meanings and names | What the name needs |
| --- | --- | --- |
| [Additive potential](../Maths/Multitubes/Additive/Potentials.lean) and [coboundary](../Maths/Multitubes/Additive/Exact.lean) | Difference-constraint labels or event phases; exact edge differences are tensions/coboundaries. | A feasible inequality potential is not necessarily an exact potential. Cycle criteria require the graph hypotheses of the selected theorem. |
| [Defect and residual](../Maths/Multitubes/Additive/Potentials.lean) | Constraint violation, reduced edge weight, local error. | Additive defect is `x(s) + weight - x(t)`, hence feasible when nonpositive. This sign is opposite to a convention in which feasible slack is nonnegative. |
| [Switching and balance](../Maths/Multitubes/Switching.lean) | Gain-graph switching, endpoint changes of coordinates, trivial closed-route gain. | Switching uses unit-valued vertex corrections for monoid labels. Balance and switching-triviality agree under the stated reachability hypotheses. |
| [Affine and max-affine summaries](../Maths/Recursion/TransferSummary.lean) | Compressed affine updates; saturated lower bounds; one-breakpoint monotone recurrences. | Composition of the max-affine coefficient formula needs nonnegative outer slope. Finite-floor summaries have no identity; labels with a bottom floor restore one. |
| [Join-semidirect label](../Maths/Algebra/JoinSemidirect.lean) | A threshold joined with a propagated value; an algebra for composing these two parts. | The monoid action preserves joins and bottom. The [max-affine identification](../Maths/Multitubes/MaxAffine/JoinSemidirect.lean) has nonnegative slopes; there is no need to invent a separate domain name for the general algebra. |
| [Reflected recurrence](../Maths/Recursion/TransferSummary.lean) and [two-sided reflection](../Maths/Recursion/TwoSidedReflection.lean) | Lindley-type workload or backlog; finite-buffer saturation between lower and upper barriers. | These are pathwise recurrences. The [Loynes construction](../Maths/Recursion/LoynesConstruction.lean) does not assert a stationary stochastic queue without a probability model and drift assumptions. |
| [Clamped fixed point](../Maths/Recursion/ClampedAffineFixedPoint.lean) | Obstacle solution; lower or upper contact; interior affine continuation. | These terms describe the scalar recurrence. A stopping-game value needs an additional game and payoff semantics. |
| [Inverse coordinate](../Maths/Recursion/InverseCoordinate.lean) | Reciprocal linearization, fractional-linear or projective recurrence, transfer-matrix representation. | Affine-chart formulas have nonzero-denominator hypotheses; the reciprocal coordinate is not an odds transform. |
| [Max-plus eigenpair](../Maths/Multitubes/Additive/Eigenvector.lean) and [critical cycle](../Maths/Multitubes/Additive/CriticalGraph.lean) | Steady event-time phase and cycle time; a bottleneck attaining the maximum cycle mean. | Unit-slope additive homogeneity gives linear growth. Critical means mean-attaining, not an arbitrary cycle. Existence uses the specified connectivity or reachability conditions. |
| [General max-affine eigenpair](../Maths/Multitubes/MaxAffine/Eigenproblem.lean) and [spectrum](../Maths/Multitubes/MaxAffine/Spectrum.lean) | Additive eigen-equation of the aggregate operator; admissible common residual levels. | Varying slopes lose additive homogeneity. Eigenlevels need not describe long-run growth or ordinary cycle means; feasible relaxation levels need not be eigenlevels. |
| [Branch policy](../Maths/Multitubes/MaxAffine/PolicySpectrum.lean) | Selection of an active incoming branch, giving a linear description of one part of the spectrum. | Finite graphs with incoming edges admit the finite-union description. No game strategy semantics or executable policy-iteration algorithm follows just from that selection. |
| [Recession and slope gauges](../Maths/Multitubes/MaxAffine/Slopes.lean) | Directions along which feasible potentials can grow; change of scale for slope comparisons. | This is feasibility geometry. A recession direction alone is not an asymptotic stability result for trajectories. |
| [Contractive gauge](../Maths/Multitubes/MaxAffine/ContractiveGauge.lean) | Positive mode scaling, weighted sup-norm contraction certificate, small-gain-type comparison. | Individual raw gains may exceed one. The finite-cycle criterion assumes nonnegative gains and strict contraction on nonempty cycles. A full input-to-state stability theorem needs a subsystem model and its own hypotheses. |
| [Least radius fixed point](../Maths/Multitubes/MaxAffine/RadiusFixedPoint.lean) | Least invariant comparison radius above prescribed floors; smallest admissible error envelope. | A positive gauge with rate below one yields uniqueness and convergence for the aggregate operator. “Invariant” refers to the encoded comparison dynamics. |
| [Circulation](../Maths/Graph/Circulation.lean) and [Eulerian realization](../Maths/Graph/EulerianTrail.lean) | Balanced nonnegative integer edge multiplicities; realization as a closed execution or route. | A circulation can have disconnected support. One closed-walk realization requires the appropriate support connectivity. |
| [Charged relation](../Maths/Graph/ChargedRelation.lean) and [zero-charge lasso](../Maths/Graph/ZeroChargeLasso.lean) | Accumulated path budget and bounded potential; finite prefix followed by a repeatable zero-net-charge loop. | A lasso can certify bounded discrepancy under the realization conditions. Acceptance, fairness, or scheduling semantics are additional requirements. |

For comparison, [Dashkovskiy, Rüffer, and Wirth's small-gain theorem](https://arxiv.org/abs/0901.1842)
includes subsystem input-to-state stability assumptions. The positive-gauge comparison here
should not inherit that stronger domain conclusion merely by sharing scaling terminology.

## Where the dictionary remains open

The applications give strong local meanings for transport and sections. They do not instantiate
every construction above. In particular, retract compression, mixed Bellman intervals, general
max-affine spectra, and sparse explanations still lack domain-specific endpoints in many clients.
There may be no useful conventional name for an uninstantiated concept-domain pair.

A new translation should identify the domain object, comparison and orientation, the formal
definition or adapter, and the hypotheses supporting the claimed consequence. The four
[prose-only dossiers](CONCEPTS.md#prose-only-dossiers) remain proposed translations throughout.
