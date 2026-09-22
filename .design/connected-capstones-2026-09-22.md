# Connecting existing theory to application answers

Baseline: `0faf534`. This implements the three priorities in
`application-utilization-2026-09-22.md`: certified timed schedules, abstract program analysis,
and affine sensor consistency. Sol agents own the three application implementations; the root
reviews the mathematical interfaces and develops optimal sensor tolerance.

## Main results

### Timed synchronization

Use the additive cycle/eigenvector theory to construct a phase from a maximizing cycle that
reaches every event. Reduced delays have no positive closed walk; their rooted maximum is a
potential and has a tight incoming edge at each event. The timed-network adapter turns this
into an eigen-schedule. The cycle supplies a lower bound on every feasible cycle-time bound,
so the resulting cycle time has an explicit optimality certificate.

Implemented in `DiscreteEventSystems/CertifiedSchedule.lean`. `exists_optimalSchedule` selects
a maximizing cycle of length at most the number of events on a finite graph with global directed
reachability and a nonempty cycle. Its conclusion links the exact returned walk to the attained
mean, constructs a schedule, and proves optimality against every edge-feasible cycle-time bound.
The conditional `rootedPhase_isSchedule` needs only outward reachability from a critical vertex.

The two-event example has cycle time three and constructed phase `(-2, 0)`, a translate of the
previous phase `(0, 2)`. Its bottleneck is the second event's delay-three self-loop. These are
mathematical existence and certificate results. An executable timing optimizer or rational
timing checker has not been added.

### Abstract program analysis

Use a finite abstract state space to analyze a possibly infinite concrete state space.
Concretization supplies an upper simulation from abstract predicate transport to concrete
predicate transport. The generic least-closure comparison proves soundness, and finite
abstract saturation supplies an executable analysis result. An abstract invariant contained
in the safe concrete states therefore proves safety of every concrete typed execution.

Implemented in `ProgramSemantics/AbstractAnalysis.lean`. The generic
`reachableStates_eq_leastLaxMajorant` identifies finite saturation with abstract least closure.
`computedReachability_sound` combines that equality with the existing upper-simulation theorem;
`walkMap_le_computedReachability` gives the all-walk concrete guarantee.

The example uses natural-number states, parity abstraction, addition by two, and a noninjective
reset. Computation on finite abstract states certifies that odd states are unreachable. The
initial abstract even cell contains two although the concrete initial set is the singleton zero,
explicitly recording loss of precision. No widening or general interval analyzer is claimed.

### Affine sensor consistency

A finite scalar sensor network has an affine source and target restriction on every edge.
An assignment is consistent within edge tolerances when the two restrictions differ in
absolute value by at most the tolerance. At zero tolerance this is exactly compatibility
in the existing graph-sheaf model.

Two signed linear inequalities encode each measurement constraint. Exact rational point
checking certifies a consistent assignment over the reals; rational Farkas weights explain
why no real assignment can meet a proposed tolerance. No invertibility or positivity of
the restriction scales is assumed.

For a uniform nonnegative tolerance, normalized finite-inequality duality characterizes
feasibility by all balanced row combinations. Fixed row normals make the feasible tolerance
set closed; a large enough tolerance fits the zero assignment, and zero is a lower bound.
Thus a least uniform tolerance is attained without requiring bounded sensor assignments.
A matching assignment and normalized dual value certify that the tolerance is optimal.

Implemented in `CellularSheaves/SensorNetwork.lean` and `OptimalTolerance.lean`. The graph-sheaf
bridge is `isConsistent_zero_iff_isCompatible`; the signed-row specification connects both
exact rational checkers to the real affine constraints. `uniformTolerance_iff_normalizedDual`
uses the existing normalized threshold duality, and `isLeast_minimumUniformTolerance` uses
the existing fixed-normal closedness theorem. The empty-edge case is included: its least
nonnegative tolerance is zero, with no normalized row certificate asserted to exist.

The triangle has offsets zero, zero, and one around its directed cycle. Its least uniform
tolerance is one third. The assignment `(0, -1/3, -2/3)` realizes that value, and weights one third
on the three forward inequalities prove optimality. A second exact check certifies inconsistency
at zero tolerance. The real minimum construction is noncomputable; the rational functions
validate supplied witnesses and do not search for them.

## Implementation notes

All new domain semantics remain in the independent application packages. No new core module is
needed: these capstones consume the existing cycle/eigenvector, morphism/closure, and
finite-inequality theories. Every new application source enters its package umbrella.

The capstones are bounded formal developments. They do not establish industrial scalability,
continuous-time control semantics, arbitrary abstract-domain analysis, sensor reconstruction
without hypotheses, or novelty in the mathematical literature.

## Validation

`bash scripts/check.sh` passed from clean build state. The full log is
`/tmp/multitubes-connected-capstones-check.log`.

- All 84 core modules and all 15 application packages rebuilt with zero errors and warnings.
- The kernel audit checked 2,768 core declarations and every application namespace, including
  112 cellular-sheaf, 112 timed-event, and 70 program-semantics declarations. Every declaration
  is free of `sorryAx` and axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
- All 1,428 indexed names and 191 project prose references resolved.
- Foundation layering, the single external Brouwer importer, checker regressions, Lean line
  lengths, and the prohibition on `set_option` passed.
- The two sensor checker examples additionally evaluated to `true`; finite parity saturation
  and odd-cell exclusion are established by kernel computation.
- `git diff --check` passed.

Independent Sol review checked the three mathematical interfaces, linked certificate witnesses,
empty-network behavior, actual use of the core simulation/duality theorems, and the distinction
between executable checking and noncomputable construction. No blocking defects remained.
