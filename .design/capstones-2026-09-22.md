# Application capstones — 2026-09-22

## Scope

This round follows the implementation order in `completeness-review-2026-09-06.md`:
finite program reachability, stochastic target reachability, and timed-event synchronization.
It also extends the switched-control comparison model with contraction gauges and quantitative
disturbance margins. These are bounded application capstones, not complete theories of their
respective fields.

The working baseline is commit `26622ce`, with Lean and mathlib at `v4.34.0`. Sol subagents
implement the application interfaces and examples. The root develops the strict-cycle gauge
argument, its control consequences, and reviews the mathematical claims across applications.

## Mathematical addition: strict cycle contraction

For a finite graph with nonnegative scalar edge gains, the following are equivalent:

- Every nonempty directed cycle has gain product strictly below one.
- There are positive vertex scales and a common rate strictly between zero and one such that
  each gain times the source scale is at most the rate times the target scale.

The proof handles zero gains by restricting logarithms to positive-gain edges. Strictly
negative log-weight on every nonempty cycle admits a uniformly negative additive residual
bound: if cycles exist, use the attained maximum cycle mean; otherwise any negative bound is
feasible. Exponentiation produces the scales and rate. The reverse implication follows by
telescoping the edge bounds and using positivity of the starting scale.

`Maths.AdditiveTransport.exists_negative_residual_bound` belongs in additive short-cycle
theory. The multiplicative equivalence and walk bound belong in
`Maths/Multitubes/MaxAffine/ContractiveGauge.lean`. No application imports enter the core.

The theorem requires neither strong connectivity nor strictly positive gains. In particular,
zero-gain resets and directed acyclic graphs satisfy the same criterion. Individual gains can
exceed one: gains two and one eighth on a two-mode loop admit scales one and four and rate
one half. No literature novelty claim is made.

The finite criterion is also formalized: only nonempty closed walks of length at most the
number of vertices need be checked. The bounded version of the additive residual theorem
uses the same maximum-cycle-mean witness. This is a finite mathematical characterization,
not an implementation of cycle enumeration or rational gauge synthesis.

## Control consequences

For an affine error comparison and any invariant radius family, an initial excess measured in
source-scale units decays by the common rate to the power of the walk length. This applies to
the actual concrete and approximate executions, not just the scalar comparison recurrence.

A normalized bias increase of at most `delta` is absorbed by adding
`delta / (1 - rate)` times the vertex scale to each invariant radius. The theorem concerns
certified comparison bounds. It does not turn comparison infeasibility into physical unsafety.

On finite graphs, strict cycle contraction gives invariant radii above arbitrary prescribed
lower bounds. The proof takes finite upper bounds on normalized biases and lower data. It does
not assume incoming edges at isolated vertices. Upper budgets remain a separate feasibility
question, handled by the existing finite-inequality encoding.

This closes the gap between cycle conditions, scalable error bounds, and perturbation margins.
It does not yet construct the unique least bounded Bellman fixed point or certify numerical
iteration toward that point.

## Application completion criteria

### Program semantics

Executable synchronous reachability saturation on a finite control graph and a common finite
state type, with a cardinality termination bound, agreement with typed-walk execution, and
agreement with the existing predicate closure. Concrete checks must cover both reachable and
unreachable states and retain a noninjective transition.

This is not a claim of a fair worklist implementation, SCC scheduling, or abstract-domain
widening. Those remain distinct operational extensions.

Implemented in `Applications/ProgramSemantics/ProgramSemantics/FiniteReachability.lean`:
`reachableWithin_stable` proves stabilization after the number of configurations;
`mem_reachableWithin_iff` gives bounded-walk semantics;
`mem_reachableConfigurations_iff` gives unrestricted walk semantics; and
`mem_reachableStates_iff_pathClosure` identifies the result with the existing closure.
The reset example computes exactly the singleton `false`, excluding `true`.

### Stochastic processes

Finite-horizon target hitting, its probability bounds and monotonicity, and a superharmonic
barrier theorem. The recursive definition must have finite-execution probability semantics,
with a checked nontrivial example. The supremum of finite-horizon probabilities can be bounded
without constructing a measure on infinite trajectories.

The eventual value is explicitly this supremum. Identifying it with an infinite-path event
measure and proving general optional stopping are separate future results.

Implemented in `Applications/StochasticProcesses/StochasticProcesses/HittingBarrier.lean`:
`hitBy_eq_expect_stopped` gives the endpoint-event interpretation under the stopped kernel;
finite and eventual values are bounded by one; the barrier theorems apply away from the target;
and the absorbing fair-trial example has exact eventual value one half.

### Discrete-event systems

A compiled application package for max-plus synchronization with explicit event-time update
semantics. Unit slopes and absent floors establish additive homogeneity. An eigen-schedule
then gives exact linear event-time growth; monotonicity and translation yield bounded
deviation for other initial schedules. A delay perturbation must have a verified schedule.

These claims do not apply to arbitrary max-affine additive eigenpairs. General timed Petri
nets, multiple-token edge lags, eventual periodicity, and transient bounds remain outside this
model.

Implemented as the new `Applications/DiscreteEventSystems/` package.
`TimedNetwork.exists_uniform_deviation_bound` proves a firing-count-independent bound for
every initial timing vector on a finite event set. The two-event example has cycle time three
and phase `(0, 2)`; raising one self-delay gives cycle time four and phase `(0, 0)`.
The recurrence is specified over real timestamps; no executable rational simulator is claimed.

### Concrete control example

`Applications/SwitchedHybridControl/SwitchedHybridControl/WeightedError.lean` now connects
the gauge theorem to actual real-state executions and unit-valued approximate states.
The transitions are `x ↦ 1 + 2*x` and `x ↦ 1 + x/8`, and the error is absolute magnitude.
The invariant radii are `3/2` and `4`, with scales `1` and `4` and rate `1/2`.
`weightedExecution_walk_geometric` proves the all-walk bound;
`weightedRadius_le_of_isRadiusFamily` proves those radii are the least comparison radii.

## Remaining priorities

There are now 15 compiled application packages out of 19 dossiers. Data migration,
formal concept analysis, persistence modules, and resource theories remain prose-only.
This round does not complete every capstone in the original census.

The strongest next connections are a general operational closure API (Kleene continuity,
fair worklists and SCC scheduling), least weighted Bellman radii with certified iteration,
and executable rational spectrum/policy enumeration. For application breadth, a finite
image morphology model and finite stopping or reachability-game semantics can reuse the
interfaces exercised here. General graph reindexing, relational comparisons, and gluing
remain structural gaps.

## Validation

`bash scripts/check.sh` completed with exit code zero after cleaning the root and every
application build directory. The log is `/tmp/multitubes-capstones-final-check.log`.

- All 81 core modules and all 15 application packages built with zero errors and zero warnings.
- The kernel audit checked 2,686 core declarations and all 15 application namespaces. Every
  environment had zero `sorryAx` dependencies and zero dependencies outside the permitted
  `propext`, `Classical.choice`, and `Quot.sound` axioms.
- New or extended application namespaces contain 33 program-semantics declarations,
  100 stochastic-process declarations, 88 discrete-event declarations, and 181 control
  declarations, including generated declarations.
- All 1,337 index references and 191 project prose references resolved.
- All four foundation boundaries, the single external Brouwer importer, checker regressions,
  Lean line lengths, and the prohibition on `set_option` passed.
- `git diff --check` passed.

Sol subagents implemented and reviewed the application work and ran integration assurance.
The root reviewed the application semantics and developed the strict-cycle contraction and
general control-bound arguments. Independent Sol review found no mathematical or API issues
in the new core results.
