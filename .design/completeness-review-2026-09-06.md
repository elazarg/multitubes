# Completeness review — 2026-09-06

## Assessment

The codebase has a substantial mathematical core, but is not yet a complete application theory.
The largest remaining work connects existing results: between different transports, between
existence theorems and computation, and between transport certificates and domain conclusions.

The review covered 75 core modules and 29 application source files. A clean run of
`scripts/check.sh` passed for the core and all 14 application packages with zero warnings. The
core kernel audit found 2,566 declarations with no `sorryAx` dependencies. Separate temporary
audits of the application namespaces found only `propext`, `Classical.choice`, and `Quot.sound`.
These counts describe the baseline before the follow-up implementation.

A bounded definition of completeness is: for each advertised class of systems, provide its
semantics, solution criteria, usable constructions or certificates, and explicit limits, then
demonstrate those results through complete domain examples. Completeness cannot mean solving
every question about arbitrary functions, relations, or all of the application fields.

The exact, additive, and finite-inequality theories are closest to this target. The
least-eigenvalue theorem in `Maths/Multitubes/MaxAffine/LeastEigenvalue.lean`, gauge-critical
feasibility results, and the failure of cyclewise max-affine feasibility deserve prominence.

## Core priorities

### 1. Maps between transports

`Maths/Multitubes/Category.lean` gives the correspondence with path functors, but there is no
general transport-morphism or simulation interface at the baseline.

For transports `T` and `S` on one graph, introduce fiber maps satisfying
`h_t ∘ T_e = S_e ∘ h_s`, with ordered and relational variants. Derive preservation of walks,
sections, holonomy, and closure under the exact hypotheses each requires. This supports
abstraction soundness, coordinate changes, refinement, and comparison of application models.
Graph reindexing, restriction, compatible gluing, and section-space universal properties are
subsequent extensions. Some specialized constructions already exist.

The existing `abstract-interpretation-via-transport.md` design note supplies a more detailed
semantic direction: paired transport, invariant logical relations, concretization soundness,
and least-closure comparison. Keep analyzer algorithms downstream of the semantic theory.

### 2. Operational closure

`Maths/Multitubes/Closure.lean` supplies path closure and a least Bellman majorant. Add a
reusable account of approximations reaching the solution:

- Kleene iteration under suitable continuity hypotheses;
- finite-height termination and fair worklist correctness;
- SCC-wise computation through condensation;
- the dual greatest-solution interface.

Monotonicity alone does not justify convergence of countable iteration. These results serve
static analysis, co-design, reachability, and evidence propagation.

### 3. Certified finite computation

Fourier–Motzkin elimination, rational/integral certificates, and sparse witnesses are already
formalized. Package executable finite rational input and checking of candidate solutions and
Farkas certificates, with soundness against the original semantics. External solvers may supply
witnesses; a complete industrial solver need not be formalized first.

### 4. Spectral and dynamical classification

`Maths/Multitubes/MaxAffine/Spectrum.lean` explicitly leaves open which levels above the least
relaxation level are eigenvalues. A direct next theorem is:

> For a finite max-affine vertex operator with nonempty incoming branch sets, its additive
> spectrum is a finite union of closed intervals, rays, and points. Rational coefficients give
> rational finite endpoints.

Derivation: choose an active branch at each vertex, impose all branch inequalities and equality
on each selected branch, project the resulting polyhedron in `(x, lambda)` onto `lambda`, and
take the finite union over policies. This suggests exact policy enumeration. It is a proposed
addition, not a baseline formalized theorem or a verified novelty claim. Stronger structural
classifications may exist.

For max-plus, further completion includes reducible matrices with absent entries, eventual
periodicity, cyclicity, and transient bounds. Existing critical-graph/eigenspace results are
substantial groundwork.

### 5. Quantitative model comparison

The generic material in
`Applications/QuantitativeRelations/QuantitativeRelations/GradedTransport.lean` belongs in the
reusable theory. Extend nonexpansive additive-error propagation to Lipschitz gains:
`epsilon_t <= b_e + a_e * epsilon_s`. This connects approximate transport to affine summaries,
slope gauges, sparse certificates, and perturbation estimates.

## Application census and capstones

There are 19 advertised domains, 14 compiled packages and five prose-only dossiers. Each target
below is a bounded capstone, not a demand to formalize its entire application field.

| Application | Baseline | Next capstone |
| --- | --- | --- |
| Program semantics | Predicates, adjunctions, reachability closure | Execution semantics, abstraction soundness, terminating analysis |
| Mathematical morphology | Relational dilation/erosion and envelopes | Verified operation on a finite image model |
| Monotone co-design | Serial feasibility and upper resource sets | Parallel composition, feedback, Pareto representation and computation |
| Cellular sheaves | Incidence/relational equivalence, compatibility | Linear section computation and sensor-consistency example |
| Stochastic processes | PMF kernels and finite-path expectations | Hitting probabilities or a stopping-time certificate theorem |
| Quantum channels | Kraus positivity and discard obstructions | Trace preservation, tensor positivity, state/observable guarantee |
| Riccati filtering | Matrix prediction, scalar observation | Periodic scalar covariance convergence, later matrix observations |
| Switched/hybrid control | Storage inequalities and walkwise decrease | Stability or robust safety for actual executions |
| Conic finance | Transactions, Minkowski sums, convexity limits | Finite-market no-arbitrage or superhedging duality |
| Coalgebraic refinement | Deterministic simulations and traces | Finite decision procedure or a nondeterministic lifting |
| Games/model checking | Alternation and necessity of priorities | Reachability games and strategies, later parity |
| Obstacle problems | Scalar solutions, contacts, convergence | Finite-state stopping model and value equation |
| Quantitative relations | Graded propagation, pseudometric bounds | Concrete approximate simulation or privacy semantics |
| Web of trust | Provenance reachability and sound closure | Authorization policies, revocation, checked queries |
| Discrete-event systems | Prose; extensive reusable foundations | Timed events, throughput, synchronization network |
| Resource theories | Prose | Specific conversions with operational monotones |
| Data migration | Prose | Schema/instance migration and its universal property |
| Formal concept analysis | Prose | Contexts, concept lattices, context transformation |
| Persistence modules | Prose | Linear diagram sections and computation |

Keep the negative application results: sheaf compatibility need not permit reconstruction;
local exact equations do not determine parity priorities; quantum discard has no order residual.

General max-affine additive eigenpairs do not automatically describe throughput or long-run
growth. Without additive homogeneity, `F x = x + lambda` need not imply
`F^[n] x = x + n * lambda`. For `F x = max 10 (2 * x)`, `x = 4`, `lambda = 6` is an eigenpair,
but `F^[2] 4 = 20`, not `16`. Domain semantics must justify spectral interpretations.

## Concrete research direction: robust switched error bounds

Connect the control client, quantitative relations, max-affine feasibility, and sparse duality.
Let concrete and approximate executions have error satisfying
`epsilon_(k+1) <= b_e + a_e * epsilon_k` on edge `e : s -> t`, with nonnegative gains and
disturbances. Given initial requirements `ell_v` and safety budgets `u_v`, seek radii satisfying

```
ell_v <= r_v <= u_v
b_e + a_e * r_s <= r_t.
```

A complete theorem package should establish:

1. Execution soundness along every permitted walk.
2. Exact feasibility for the scalar comparison inequalities.
3. Rational infeasibility certificates on at most `n + 1` rows for `n` radius variables,
   with sharper rank bounds where available.
4. If every nonempty cycle has gain product below one, positive-gauge contraction and a unique
   least invariant radius vector, permitting individual edge gains above one.
5. Perturbation bounds with denominator `1 - q` in the gauge norm.
6. A checked heterogeneous-mode example with a noninvertible reset and a concrete safety budget.

Completeness concerns the comparison model: its infeasibility does not prove physical unsafety.
Small-gain scaling is established mathematics. The promising contribution is the combined
machine-checked result, heterogeneous semantics, exact budgets, and sparse explanations. The
review did not establish mathematical novelty.

## Assurance findings

The baseline passes, but the existing checks do not enforce every documented invariant:

- `scripts/check.sh` ignores build-pipeline exit status, allowing failures without matching
  `error:` output to escape detection.
- `scripts/audit.lean` audits only `Maths`; applications need permanent independent audits.
- The axiom set is printed but not checked against the permitted allowlist.
- `scripts/check-docstrings.py` recognizes only `Maths.…`, omitting application declaration names.
- Layering checks enforce LP isolation, not all four independent foundation groups. The baseline
  source scan found no actual cross-group violation.
- Brouwer is an external dependency. The manifest pins its current revision, but root
  `lakefile.toml` requests `main`; use an explicit revision for deliberate updates.

## Recommended implementation order

1. Harden assurance, introduce transport comparisons, and add executable rational witness checks.
2. Connect comparison semantics to a complete robust-control application.
3. Formalize finite-policy spectral classification.
4. Build capstones for program analysis, stochastic reachability, and timed-event systems.
5. Expand the remaining applications after the reusable interfaces have been exercised.

## Literature checked

- Andrea Censi, *A Mathematical Theory of Co-Design*:
  <https://arxiv.org/abs/1512.08055>.
- Angeli, Philippe, Athanasopoulos, Jungers, *Path-Complete Graphs and Common Lyapunov Functions*:
  <https://arxiv.org/abs/1612.03983>.
- Dashkovskiy, Rüffer, Wirth, *Small gain theorems for large scale systems and construction of ISS
  Lyapunov functions*: <https://arxiv.org/abs/0901.1842>.
- Akian, Gaubert, *Spectral Theorem for Convex Monotone Homogeneous Maps, and Ergodic Control*:
  <https://arxiv.org/abs/math/0110108>.

## Follow-up implementation

The user authorized addressing the most important parts and requested Sol subagents for
nonresearch work. The initial work is split into assurance, transport morphisms/simulations, and
executable rational certificate checking. Mathematical design, integration, and validation are
coordinated by the root agent. The implementation below passed the final clean checks.

### Implemented mathematical additions

- `Maths/Multitubes/Morphism.lean`: commuting fiberwise morphisms, directed simulations,
  walk comparison, section preservation, and least-closure soundness for concretization.
- `Maths/LinearProgramming/CertificateCheck.lean` and its finite-inequality adapter: executable
  rational primal and dual witness checks with exact specifications and real-cast soundness.
- `Maths/Multitubes/FiniteInequality/Parametric.lean`: feasibility with fixed normals and
  continuously varying bounds is closed; affine real bounds give a convex parameter set.
- `Maths/Multitubes/MaxAffine/PolicySpectrum.lean`: exact finite-policy characterization of
  the full spectrum, closedness/convexity of every policy set, closedness of the spectrum, and
  attainment of its infimum whenever it is nonempty and bounded below. Slopes may have either
  sign and strong connectivity is not required; incoming edges at every vertex are required.
- `Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean`: local affine
  comparisons between dependent concrete and approximate state spaces, all-walk error bounds,
  exact finite LP encoding of bounded radii, and normalized real infeasibility certificates
  supported on at most the number of modes plus one rows. A heterogeneous example retains a
  noninjective reset. Its Boolean-mode lower radius of one forces the finite-mode radius to be
  at least two along the expansion edge, so a finite-mode budget of `3/2` is infeasible for
  the comparison constraints. This does not claim physical unsafety.

The spectrum proof does not need a general polyhedral projection library. Farkas duality
expresses feasibility of each policy system as the intersection of its dual inequalities;
continuous lower bounds make each inequality closed. Convexity follows by combining feasible
potentials. Selecting one branch at each vertex proves that the finite union is exact.
This establishes the closed-interval union description, but not executable enumeration,
explicit finite endpoint formulas, or rationality of the endpoints.

The morphism API also supplies extensionality, identity and composition laws, holonomy
intertwining, and conversion of exact morphisms into either directed simulation. Rational
witness examples are compile-failing `#guard` checks, including rejected points, negative
certificate weights, unbalanced weights, and nonpositive dual objectives.

### Implemented assurance changes

`scripts/check-command.sh` propagates command and pipeline failures and rejects errors or
warnings. `scripts/check.sh` audits the core and every application independently, checks the
exact axiom allowlist, clears and writes audit dumps under `.lake/audit`, validates application
and umbrella references, and enforces all four foundation boundaries. The external Brouwer
dependency is pinned to its existing resolved commit instead of following `main`.

`scripts/test-checkers.py`, run by the main check, exercises successful commands, silent failures,
warning/error output with successful process exits, valid and invalid core/application references,
cross-foundation imports, and forbidden axioms. The expanded docstring audit found and fixed a
pre-existing reference to nonexistent `ProgramSemantics.reverseGraph`; the correct declaration
is `Maths.EdgeGraph.reverse`. Other abbreviated max-affine references were qualified or rewritten
as mathematical prose where the full identifier could not fit the line-length limit.

### Final validation

`bash scripts/check.sh` completed successfully after a fresh removal of the core and each
application's build directory:

- All 80 core modules and all 14 application packages built with zero errors and zero warnings.
- The kernel audit checked 2,680 core declarations and every application namespace, with zero
  `sorryAx` dependencies and zero dependencies outside the three-axiom allowlist.
- The documentation audit checked 1,255 index references and 191 project prose references,
  with zero unresolved names.
- All four foundation import boundaries and the single external Brouwer entry point passed.
- Checker regressions, the 100-character Lean line limit, and the absence of `set_option` passed.
- `git diff --check` passed.

Sol subagents implemented and independently reviewed the routine interfaces, application, and
assurance work. The root agent developed the parametric-feasibility and finite-policy spectral
arguments and integrated the result. No mathematical novelty beyond the repository is claimed.

### Remaining after this implementation scope

Graph-changing morphisms, relational comparison, reindexing and gluing; generic Kleene/worklist
and SCC computation; complete rational solver or policy enumerator; rational spectrum endpoints;
weighted contraction synthesis and perturbation bounds for the error comparison model; max-plus
eventual periodicity; and the application capstones in the census remain further work.
