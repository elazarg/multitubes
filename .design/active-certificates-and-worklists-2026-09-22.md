# Active optimal certificates and fair local closure

Baseline: `e407e51`. This implements the next two priorities from
[application result transfers](application-result-transfers-2026-09-22.md).
The mathematical sources are Chebyshev optimality and chaotic iteration; these are known
results. The contribution here is a reusable formal interface and applications that exercise
its hypotheses. No literature novelty is claimed.

## Balanced active certificates

For finite row vectors `δᵢ` and offsets `bᵢ`, define a feasible residual level by

```text
there exists x such that bᵢ - ⟨δᵢ, x⟩ ≤ t for every i.
```

If t is the least such level, there is a normalized balanced certificate u with

```text
uᵢ ≥ 0,   ∑ uᵢ = 1,   ∑ uᵢ δᵢ = 0,   ∑ uᵢ bᵢ = t.
```

At any feasible point x at level t, every row with positive certificate weight is tight.
Moreover, a certificate can be chosen with at most `rank(span {δᵢ}) + 1` nonzero weights.
The rank is that of the actual row vectors, rather than the ambient state dimension.

This result is stronger than the existing sparse infeasibility result in its endpoint:
it explains an attained optimum instead of merely rejecting a proposed level. The proof
reuses normalized duality, compactness of the normalized certificate polytope, and the
standard-form LP extreme-point theorem. Complementary slackness follows by summing the
nonnegative weighted residual slacks. Support independence of augmented columns then gives
the rank bound.

The core hypothesis is an attained least level. A separate nonempty-row hypothesis is
unnecessary: an empty row family admits every real level and hence has no least level.
Conversely, nonempty rows alone do not guarantee a finite optimum: the single residual `-x`
is unbounded below. This distinction matters when exporting the theorem beyond sensors.

The relevant API is
[FiniteInequality/OptimalCertificate](../Maths/Multitubes/FiniteInequality/OptimalCertificate.lean),
with common compactness and support bounds in
[FiniteInequality/Sparse](../Maths/Multitubes/FiniteInequality/Sparse.lean).

### Sensor interpretation

An affine sensor comparison has physical error

```text
error(e) = targetScale(e) * x(target(e))
           - (sourceScale(e) * x(source(e)) + offset(e)).
```

The forward signed row residual is `-error(e)`; the reverse row residual is `error(e)`.
This sign is part of the adapter, not an informal convention. At an optimal uniform
tolerance, the certificate identifies a balanced group of worst signed comparisons that
prevents any reading from improving the tolerance. Both arbitrary endpoint scales and
disconnected networks are allowed.

The adapter in
[CellularSheaves/ActiveCertificate](../Applications/CellularSheaves/CellularSheaves/ActiveCertificate.lean)
requires a nonempty comparison set. Its absolute-value constraints then force every feasible
residual level to be nonnegative, so the existing least nonnegative sensor tolerance is also
the unrestricted least residual level. With no comparisons the sensor convention still gives
tolerance zero, but no normalized signed-row certificate exists.

The support bound counts signed comparisons, not distinct sensors. It need not be a
minimum-cardinality explanation. Neither ordered alternation nor uniqueness follows from
balance and activity. Those need additional hypotheses in classical approximation theory.
This result also does not identify a malfunctioning sensor: inconsistency belongs to the
modelled collection of comparisons.

The new existence statements supply real weights. They do not implement an optimizer or
extract an optimal certificate from the input data. The existing rational witness checkers
remain useful for supplied witnesses; rational optimal weights with this same support bound
are not a separate endpoint of the new sensor adapter.

### Return to other applications

The same theorem applies directly to finite max-affine branch residuals and worst-case
calibration models expressed as finite affine inequalities. The branch-specific tightness
theorem in `MaxAffine/LeastEigenvalue` is an earlier specialization of this phenomenon.
The generic result makes future applications independent of that specialization.

For unit-scale sensors, the signed row normals are incidence vectors. Balance then has its
usual circulation meaning, relating active row certificates to the signed cycle certificates
already formalized in `CellularSheaves/CycleConsistency`. The new adapter does not prove an
equivalence between sparse optimal row certificates and critical simple cycles. Establishing
that bridge, and deriving graph-specific rank bounds, remain useful follow-ups.

## Fair local closure

For monotone transport maps, processing an edge changes one coordinate:

```text
x(target(e)) := x(target(e)) ⊔ T(e)(x(source(e))).
```

All other coordinates remain unchanged. Every update increases x and preserves the upper
bound by every lax majorant of the seeds. These statements require only ordered joins and
the relevant monotonicity; no join-preservation assumption is used.

A schedule is a function from natural numbers to optional edges. `none` is an idle step,
which also makes schedules meaningful for empty graphs. Fairness says that every edge is
processed at some time after each supplied time. On complete-lattice fibers, if the product
order satisfies the ascending chain condition, every fair run eventually becomes exactly
the least lax majorant. ACC first yields a constant tail; fairness forces each local
constraint to hold on that tail; comparison with all feasible majorants gives leastness.

The executable finite variant folds updates over a list of edges. A list covering every
edge provides a full sweep. A fixed sweep is a lax section even without monotonicity:
inflationarity forces every intermediate state to equal the input. With monotone maps,
an observed fixed sweep iterate is the least majorant of the seeds, without an ACC
assumption. ACC guarantees that repeated covering sweeps eventually reach such a point.
The definitions and correctness statements are in
[Worklist](../Maths/Multitubes/Worklist.lean).

ACC is an explicit hypothesis on the whole family order. It holds in the finite application
below. Finiteness of the graph alone would not justify convergence over unbounded numeric
domains. Fairness alone gives no numerical runtime bound: arbitrary idle intervals are
permitted. The finite sweep definitions do not constitute a queue implementation with an
automatic stopping rule, an extraction backend, or a complexity analysis.

### Threshold evidence propagation

The WebOfTrust client previously used arbitrary-union-preserving maps. Such maps have
pathwise provenance semantics: every output can be traced through one path from seeds.
Threshold rules require several incoming facts to be combined before proceeding.

The finite example has four vertices, three edges, and three evidence tokens:

```text
vertex 0: {0}  ──identity──┐
                          vertex 2 ──both 0 and 1 present ⇒ {2}──> vertex 3
vertex 1: {1}  ──identity──┘
```

The threshold transfer is monotone but does not preserve joins: applying it to either
singleton returns nothing; applying it to their union returns token 2. Thus the example
uses a part of the generic monotone theory unavailable to the previous evidence interface.

Processing the threshold edge before both input edges leaves vertex 3 empty after the
first sweep. A second sweep produces the family `{0}, {1}, {0,1}, {2}`. The application
connects this finite computation to the generic least-majorant correctness theorem in
[WebOfTrust/ThresholdPolicy](../Applications/WebOfTrust/WebOfTrust/ThresholdPolicy.lean).

The executable fibers are `Finset (Fin 3)`, with their existing finite-join instance.
`thresholdSweep_two_isLeast` uses the semilattice-level
`sweepRelaxation_isLeast_of_relaxSweep_eq`: it proves seed containment, satisfaction of
every edge constraint, and comparison below every other such assignment. It does not
require a new complete-lattice instance for finite sets. The computed passes and fixedness
are checked by kernel reduction with `decide`.

Failure of binary-join preservation is separately formalized. The discussion of why
individual paths cannot produce the combined threshold conclusion is mathematical
explanation; a separate theorem comparing `pathClosure` with this example's least closure
has not been added.

This is a rule for two distinct evidence tokens. Their interpretation as independent
introducers, their authenticity, and any numerical confidence semantics remain outside
the model. The same finite rule is also a conjunctive dataflow transfer or a small Horn
inference rule; the closure theorem does not depend on the trust vocabulary.

## What this completes and what remains

The finite-inequality API now has a path from attained optimum to a bounded active
explanation. The monotone closure API now has a path from local updates to eventual exact
computation under ACC. Sensor fitting and conjunctive evidence inference provide concrete
uses of those endpoints.

These additions do not complete all proposed application transfers. Bekić/block closure,
Hoffman repair bounds, finite Doob normalization, exact abstraction commutation, and boundary
elimination remain separate projects. A covering sweep also leaves practical queue design,
dependency tracking, and quantitative termination bounds open.

## References

- [Sukhorukova, Ugon, and Yost, Chebyshev approximation for multivariate functions](https://arxiv.org/abs/1510.06076):
  signed active-gradient balance in minimax approximation.
- [Cousot and Cousot, Abstract Interpretation and Application to Logic Programs](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-JLP-v2-n4-p511--547-1992.pdf),
  section 4.2.4: chaotic iteration under chain conditions.

## Validation

`bash scripts/check.sh` completed successfully with exit status zero. Full log:
`/tmp/multitubes-active-worklist-check.log`.

- All 86 core modules and all 15 application packages rebuilt from clean state, with zero
  errors and zero warnings.
- The kernel audit checked 2,808 core declarations, 125 CellularSheaves declarations,
  28 WebOfTrust declarations, and every other application namespace. No declaration depended
  on `sorryAx` or a forbidden axiom.
- All 1,463 indexed declaration names and 191 prose references resolved.
- Foundation layering, the sole `FixedPointTheorems` importer, checker regressions, Lean line
  lengths, and the prohibition on `set_option` passed.
- Independent reviews checked theorem strength, sensor residual signs, empty-comparison
  handling, fixed-sweep leastness, executable finite computation, and application claims.
- The Markdown audit checked 177 local relative links with no missing targets.
- `git diff --check` passed.

Sol agents implemented the core and application modules, integrated the public documentation,
reviewed the statements independently, and ran the full clean checks. The research review
separates the proved results from the follow-up questions above.
