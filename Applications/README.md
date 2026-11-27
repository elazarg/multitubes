# Applications

This directory records domain perspectives for Multitubes. Each subdirectory describes the
interpretation a domain can give to its walk maps and constraints; domain-specific
developments may live in a separate project.

The [concept dictionary](CONCEPTS.md) maps abstract constructions to domain terminology,
with formal theorem anchors, transport directions, and qualifications for prospective mappings.

## Specializations and applications

A **specialization** adds reusable mathematical structure, such as additive weights, complete
lattices, adjoints, or max-affine maps. Its statements are independent of any particular field
and belong in the library.

An **application** supplies domain semantics and domain-specific mathematics. It may use the
library's specializations and can live in an independent Lake package under its dossier or in a
separate client project. Max-affine transport is a specialization, not an application: queueing,
stopping, and control are domains that can use it.

## Domains

| Dossier | Central interpretation |
| --- | --- |
| [Switched and hybrid control](SwitchedHybridControl/) | Lyapunov certificates, affine error radii, and gauge contraction |
| [Max-affine operating points](AffineOperatingPoints/) | Exact common offsets for networks of monotone affine responses |
| [Riccati equations and filtering](RiccatiFiltering/) | Covariance transport in the Löwner order |
| [Program semantics](ProgramSemantics/) | Invariants, predicate transformers, and finite reachability |
| [Mathematical morphology](MathematicalMorphology/) | Adjoint morphology on image lattices |
| [Monotone co-design](MonotoneCoDesign/) | Relational functionality and resource feasibility |
| [Cellular sheaves](CellularSheaves/) | Compatible assignments across heterogeneous stalks |
| [Stochastic processes](StochasticProcesses/) | Expectation pullback, finite hitting, and barrier bounds |
| [Resource theories](ResourceTheories/) | Monotones on networks of free conversions |
| [Quantum channels](QuantumChannels/) | Kraus transport, sequential instruments, and sharp detection probabilities |
| [Data migration](DataMigration/) | Route consistency and adjoint migration |
| [Formal concept analysis](FormalConceptAnalysis/) | Transport among concept lattices |
| [Conic finance](ConicFinance/) | Solvency orders and attainable portfolio increments |
| [Coalgebraic refinement](CoalgebraicRefinement/) | Simulations transported by relation liftings |
| [Games and model checking](GamesModelChecking/) | Alternating fixed points and limits of local sections |
| [Obstacle problems](ObstacleProblems/) | Contact and continuation for two-sided recurrences |
| [Persistence modules](PersistenceModules/) | Compatible elements in noninvertible diagrams |
| [Discrete-event systems](DiscreteEventSystems/) | Max-plus timed synchronization and cycle time |
| [Quantitative relations](QuantitativeRelations/) | Additive path budgets and pseudometric error bounds |
| [Web of trust](WebOfTrust/) | Provenance-aware endorsement and evidence closure |

## Executable application algorithms

These notes connect Lean results with derived algorithms, their hypotheses and Python examples.
The algorithms and complexity proofs are documented in the linked application dossiers.

| Application | Computation |
| --- | --- |
| [Rooted linear quivers](PersistenceModules/algorithms/README.md) | Compute section dimensions after every single arrow deletion, including failures that cut off a subtree. |
| [Battery storage](ObstacleProblems/algorithms/README.md) | Compute the full solar-rating curves for grid imports and spill on a finite or contractive periodic trace. |
| [Switched error bounds](SwitchedHybridControl/algorithms/README.md) | Compute jointly attainable offset margins for new transitions entering the same mode. |
| [Single storage interventions](ObstacleProblems/algorithms/pulse-response.md) | Compute the changes in shortage, spill and terminal charge from one signed injection at a chosen time, through any deadline. |
| [Routes under interval uncertainty](ProgramSemantics/algorithms/README.md) | Find one sequence of actions guaranteed to take every possible initial state and outcome into a target band. |
| [Quantum measurement reports](QuantumChannels/algorithms/README.md) | For each report, find the cheapest set of other reports whose suppression makes that report affect detection by the deadline. |
| [Inverse binary dilation](MathematicalMorphology/algorithms/README.md) | After any contiguous outage on a scan line, find the cheapest seed mask that still produces the observed pixels. |
| [Scalar filter deadlines](RiccatiFiltering/algorithms/README.md) | On any window of a fixed observation log, find the peak relative covariance, the first cap violation, and the largest safe starting covariance. |
| [Correlated production delays](DiscreteEventSystems/algorithms/README.md) | Compute worst deadline lateness under a budget of shared delay causes, including the effect of ruling out or requiring each cause. |
| [Max-affine operating points](AffineOperatingPoints/) | Test an offset with certificates, compute all offsets for a strongly connected network, or synthesize a network for a prescribed set of intervals. |
| [Feedback connection repair](AffineOperatingPoints/algorithms/connection-retuning.md) | At a missing operating level, find every intercept of each candidate connection that restores an operating point in an expansive network. |
| [Operating points from partial readings](AffineOperatingPoints/algorithms/counting-operating-points.md) | Represent all readings at a fixed level by a partial order and find the greatest operating point within reported measurement ranges. |
| [Individual calibration replacements](CellularSheaves/algorithms/calibration-replacement.md) | Compute the best uniform fit after any one comparison changes, and find all replacement offsets that meet a given tolerance. |
| [Migration round trips](DataMigration/algorithms/round-trip-audit.md) | Classify every record by round-trip stability and compute the largest domain of unambiguous registry readback. |
| [Zero-drift schedules](DiscreteEventSystems/algorithms/periodic-buffers.md) | Realize a connected circulation in compressed form and find every restart phase safe under shared calibration uncertainty. |

## Compiled capstones

Several dossiers contain standalone Lake packages with checked end-to-end examples:

- [Program semantics](ProgramSemantics/) computes finite-state reachability by bounded
  saturation and proves agreement with typed-walk execution and least path closure. It assumes
  finite control locations, edges, and a common finite state space for exact saturation. A finite
  abstraction can also analyze infinite concrete states: a lax morphism carries the computed
  abstract closure to a concrete all-walk guarantee. The parity analyzer verifies natural-number
  executions with addition by two and reset to zero. Octagon constraints over a field are
  decided by closed walks of a doubled literal graph, with a checked integer counterexample.
- [Stochastic processes](StochasticProcesses/) defines finite-horizon target hitting, identifies
  it with the endpoint event for the kernel stopped on the target, and proves superharmonic
  barrier bounds. Its eventual value is the supremum of finite horizons; no probability measure
  on infinite trajectories is constructed.
- [Discrete-event systems](DiscreteEventSystems/) implements a max-plus timed network, proves
  linear growth from an eigen-schedule, bounds timing offsets, and constructs an optimal phase
  from a maximizing cycle. Finite global reachability and a nonempty cycle give existence; the
  returned bottleneck certifies optimality against every feasible cycle-time bound. This is a
  mathematical construction, and the throughput result uses floorless unit-slope labels.
- [Cellular sheaves](CellularSheaves/) models approximate affine sensor agreement as signed
  inequalities, checks rational assignments and inconsistency certificates, and proves that a
  least nonnegative uniform tolerance is attained. A three-sensor inconsistent triangle has
  exactly optimal tolerance one third, certified by a reading and normalized dual weights.
  At any attained optimum with at least one comparison, a normalized balanced certificate can
  be chosen on worst signed comparisons, with support bounded by the signed-row rank plus one.
- [Switched and hybrid control](SwitchedHybridControl/) propagates affine error radii along
  executions. A gauge with rate below one gives geometric excess decay even with an amplifying
  edge;
  bounded bias changes have an explicit radius margin, and strict contraction of every nonempty
  cycle gives radius existence. On finite graphs, the contractive gauge criterion only needs
  closed walks of length at most the number of modes. The least-radius construction gives an
  exact upper-budget criterion, and rational witness checks certify radii or infeasibility.

- [Web of trust](WebOfTrust/) applies finite covering sweeps to a monotone conjunctive evidence
  rule that does not preserve unions. Two reverse-ordered sweeps reach a fixed sound assignment,
  and the generic sweep stopping theorem proves it lies below every sound assignment containing
  the seeds. Separately, the core worklist theory proves fair-schedule convergence under product
  ACC and convergence of repeated covering sweeps.
