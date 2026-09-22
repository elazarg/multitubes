# How much do the applications exercise the library?

Assessment of commit `8804c68`, following the spectral and least-radius additions.
This is a source-level mathematical review, not a theorem-dependency coverage measurement.

## Assessment

The applications test the architecture broadly but exploit the deeper theorem families unevenly.
Switched control now supplies the strongest chain from domain executions through reusable
constraints to certificates and quantitative conclusions. Program reachability, stochastic
hitting, and timed synchronization have substantive bounded capstones. Several smaller clients
prove useful structural or negative results. Much spectral, optimization, graph-certificate,
and exact-normal-form machinery still lacks a domain-facing capstone.

There are 19 dossiers and 15 compiled application packages; data migration, formal concept
analysis, persistence modules, and resource theories remain prose-only. Counting packages is
not a measure of domain completeness, and declaration counts are not a measure of reuse.
Applications use a small set of narrow core imports, while ObstacleProblems imports the whole
Maths umbrella. Import counts therefore cannot support a percentage of library utilization.
Likewise, an indirectly used theorem can be essential: control's contraction gauge theorem
already depends substantively on the additive cycle theory.

## Evidence by application

| Application | What is genuinely exercised | Main remaining limit |
| --- | --- | --- |
| Switched/hybrid control | Concrete/approximate executions, affine error comparisons, bounded-radius LP encoding, sparse and executable rational certificates, cycle gauges, perturbation margins, least radii and geometric convergence | Witness checking rather than a solver; tiny concrete network; no continuous-time semantics |
| Program semantics | Predicate adjunctions, least path closure, executable finite saturation, exact agreement with typed-walk execution | No client of the new transport simulation/abstraction-soundness interface; no abstract analyzer or fair worklist |
| Stochastic processes | Heterogeneous kernel composition, expectation pullbacks, stopped-kernel finite hitting, superharmonic barriers | No optimal stopping/control Bellman problem or infinite-path probability semantics |
| Discrete-event systems | Max-plus recurrence, linear growth from an eigen-schedule, bounded deviation, concrete delay perturbation | Schedule is supplied; no application derivation from cycle means, Karp, critical graph, or spectral certificates |
| Coalgebraic refinement | Greatest deterministic simulation equals finite-trace relatedness | No executable refinement decision procedure or nondeterministic extension |
| Conic finance | Relational transaction paths, Minkowski sums, convexity preservation, failure of convexity under path alternatives | No market optimization, no-arbitrage, or superhedging duality |
| Quantum channels | Kraus positivity and ordered walks; discard has neither order residual | No full state/observable correctness pipeline, tensor guarantee, or complete trace-preserving-channel development |
| Web of trust | Least evidence closure with explicit endorsement-path provenance | No policy evaluation, revocation, or executable query capstone |
| Obstacle problems | Unique scalar clamped solution, contact trichotomy, convergence | Single scalar operator, without a finite-state stopping interpretation |
| Mathematical morphology | Dilation/erosion adjunction and least invariant envelope; noninverse example | No concrete finite-image operation with executable correctness |
| Cellular sheaves | Incidence and relational encodings of compatibility; information-loss counterexample | No section computation, monodromy classification, or quantitative sensor reconciliation |
| Games/model checking | Nested least/greatest fixed points; priorities cannot be recovered from local section equations | No arena, winning strategy, or model-checking procedure |
| Quantitative relations | Graded walk propagation and a pseudometric instance | No second domain consumer of the graded API or full approximate-simulation application |
| Monotone co-design | Serial feasibility, monotonicity, upper resource sets, relational closure | No feedback solution, parallel synthesis, or finite Pareto computation |
| Riccati filtering | Covariance/scalar observation monotonicity and ordered walk bounds | No invariant covariance construction, periodic Riccati solution, or convergence theorem |

The smaller clients should not all be dismissed as examples of notation. Quantum discard
tests the real boundary of residual reversal; finance separates exact reachability from
convexification; sheaves separate compatibility from reconstruction; games separate local
equations from fixed-point priority. These are useful tests of the library's design even when
the client is not a complete domain development.

## Underused connections

1. **Spectral theory to application output.** `MaxAffine/AnchoredEigenvalue.lean`,
   `LeastEigenvalue.lean`, and `PolicySpectrum.lean` currently have no characteristic
   application consumer. The reducible/reset examples are core examples. The timed client
   in `DiscreteEventSystems/Synchronization.lean` proves consequences of a supplied
   eigen-schedule; it does not yet find or certify its optimum using the spectral core.
2. **Model comparison to program analysis.** `Multitubes/Morphism.lean` supplies
   `UpperSimulation.leastLaxMajorant_le_map`, but applications do not yet instantiate it
   as an abstract interpreter with a meaningful concrete-to-abstract soundness result.
   Finite reachability and transport comparisons are presently separate achievements.
3. **Optimization to decisions.** The control client exercises feasibility and Farkas
   certificates. Standard-form LP optimization and complementary slackness have no
   comparable domain capstone selecting an optimal budget, resource vector, or hedge.
4. **Graph certificates to infinite behavior.** Eulerian realization, connected integer
   circulations, and bounded-discrepancy/zero-charge lassos remain largely internal.
   No application turns their witnesses into a recurring schedule or fair execution.
5. **Exact geometry to reconstruction.** Exact-section, SCC normal-form, switching, and
   rigidity APIs have no substantial data/sensor/diagram reconstruction client. The sheaf
   package establishes the representation bridge but does not yet use that deeper theory.
6. **Recurrences to domain models.** The scalar obstacle client uses clamped recurrence
   results, but the Loynes and two-sided-reflection developments do not yet support a
   queueing or storage application with a domain-level long-run conclusion.

These are gaps in demonstrated domain use, not assertions that every named theorem is absent
from the transitive proof dependencies of applications. A kernel dependency census would be
needed for the latter claim. Forcing every application to import more modules would not help.

## Highest-return next work

Prefer joining existing results into complete domain conclusions over adding more dossiers.

1. **Automatic timing certificates.** Connect the timed network to additive cycle means and
   eigenvector existence. Derive an optimal cycle time and compatible phase, with an explicit
   bottleneck cycle certificate. Add rational witness checking where the existing finite
   inequality API applies. This requires a search or certificate-production layer beyond the
   current existence theorems; it would replace a supplied schedule with a certified answer.
2. **A certified abstract analyzer.** Instantiate transport simulations between a concrete
   transition system and an abstract domain; connect computed or certified invariants to
   concrete safety. Use finite reachability for an exact reference example and affine/rational
   constraints for a less trivial abstract example. A numerical domain and its soundness
   adapter are additional work, not already supplied by the generic morphism theorem.
3. **Sensor/sheaf consistency with explanations.** For an explicit finite affine sensor model,
   encode consistency tolerances as finite inequalities, accept compatible assignments, and
   explain inconsistency with dual certificates. Use transport/graded error bounds for path
   propagation. Add exact holonomy classification only with the needed invertibility or
   injective-return assumptions; arbitrary sheaf restrictions do not permit reconstruction.

A finite-market duality capstone, recurring-resource schedule, or stochastic stopping problem
would also exercise neglected mathematics. Each needs its domain hypotheses and interpretation
proved; generic circulation or LP results cannot simply be renamed as those domain theorems.

## Validation

The assessment used a direct-import and declaration-body audit plus independent Sol review
of the eleven smaller compiled clients. No Lean source changed. `scripts/check.sh` passed from
clean build state: 84 core files and all 15 application packages rebuilt with zero errors and
warnings; 2,768 core declarations and every application declaration were free of `sorryAx` and
forbidden axioms; 1,377 index names and 191 prose references resolved; layering, checker
regressions, line length, and `set_option` checks passed. The full log is
`/tmp/multitubes-utilization-check.log`.

## Subsequent capstones

The three recommended connections are now implemented in the follow-up described by
`connected-capstones-2026-09-22.md`: cycle-certified optimal timing, generic finite abstract
analysis with concrete safety, and affine sensor consistency with optimal tolerance. The table
above records the `8804c68` baseline. General executable timing/sensor optimization remains open;
the delivered timing construction is mathematical, and the sensor functions check witnesses.
