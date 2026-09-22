# Application results that can become transport theorems

Baseline: `5afaae4`. Sources checked on 2026-09-22.
This follows the [terminology audit](domain-terminology-2026-09-22.md): recognizing a name
is useful, but transferring a theorem requires preserving its hypotheses and conclusion.

There are strong candidates. Some are already generic mathematics waiting for a domain adapter;
others require a new core theorem or genuinely new structure. The statements below are research
specifications and proof outlines, not claims that all have been formalized. Their classical
ingredients are known; no literature novelty is claimed for the proposed transfers.

## Main results

| Known result and source field | Portable statement | Applications after transfer | Current gap |
| --- | --- | --- | --- |
| Max-plus cycle means; log-Chebyshev pairwise ranking | The least uniform additive residual is the largest signed cycle mean. | Timing bottlenecks, unit-scale sensor inconsistency, relative ranking. | Core threshold theorem exists; sensor threshold/certificate adapter added. |
| Chebyshev optimality and complementary slackness | An optimal worst-residual fit has a small balanced set of active rows. | Sensor explanations, worst-case calibration, max-affine residual optimization. | Implemented generically and connected to affine sensors. |
| Chaotic iteration in program analysis | Fair local inflationary updates stabilize at the least section above seeds under ACC. | Finite reachability, morphology, evidence propagation, finite resource domains. | Generic fair schedules and finite covering sweeps implemented; finite threshold evidence client added. |
| Bekić decomposition in synchronous/dataflow semantics | Simultaneous monotone least fixed points can be solved by nested block fixed points. | Modular analysis, recursive co-design, SCC-based closure computation. | Heterogeneous product theorem and block restriction/assembly API. |
| Hoffman error bounds in optimization | Small linear constraint violations imply proximity to a feasible section. | Sensor repair, radius correction, quantitative verification. | A normed polyhedral error-bound layer. |
| Doob harmonic transform in probability | Positive exact sections normalize positive kernel transport; lax ones give sub-Markov transport. | Stochastic verification, positive-operator normalization, changed-measure finite paths. | Finite kernel normalization and its transport adapter. |
| Complete abstract interpretation | Exact local abstraction commutation gives exact abstract closure, under an adjunction. | Reliable finite representations of reachability, morphology, evidence/resource propagation. | Equality theorem beyond the existing one-sided simulation theorem. |
| Kron reduction and variable elimination | Hiding interior states preserves boundary behavior and composes by shared interfaces. | Open sensor networks, co-design interfaces, modular constraint solving. | Boundary semantics and gluing; Schur complements require a further linear specialization. |

### 1. Cycle means become sensor inconsistency certificates

Known source: [Krivulin, *Methods of tropical optimization in rating alternatives based on
pairwise comparisons*](https://arxiv.org/abs/1608.02666), especially the spectral-radius
formula and log-Chebyshev optimization result. In logarithmic coordinates its multiplicative
cycle means become additive cycle means. This is established mathematics in decision analysis,
as well as the max-plus theory used for timed networks.

For sensors with both restriction scales equal to one, the fitting constraints are
`|x(t) - x(s) - b(e)| ≤ τ`. Replace each comparison by a forward edge of weight `b(e)`
and a reverse edge of weight `-b(e)`. Then a reading exists exactly when every closed walk C
in that signed graph satisfies

```text
signedOffsetSum(C) ≤ length(C) * τ.
```

For a finite sensor graph with a nonempty edge set, reversal supplies both signs and a
zero-weight backtrack.
Consequently the least nonnegative tolerance is the maximum signed cycle mean, equivalently
the largest absolute cycle inconsistency divided by its length. Simple cycles suffice.
With no comparisons the least nonnegative tolerance is zero instead. Disconnected networks
are allowed; their components need no common additive eigenvalue or globally reaching root.

This is already the substance of
`MixedAdditiveTransport.mixedResidualAtMost_iff_laxified_closedWalk_le` and its simple-cycle
version in [Additive/MixedQuantitative](../Maths/Multitubes/Additive/MixedQuantitative.lean),
using exact mode on every edge. The sensor adapter fixes the sign convention and the
nonnegative-tolerance convention. A feasible reading at τ together with a nonempty cycle
attaining `length * τ` certifies optimality. The existing triangle's value one third is the
unit inconsistency spread over three comparisons.

Back in decision analysis, choose a convention in which a positive observation `a(e)` estimates
`score(t) / score(s)`. Taking `b(e) = log(a(e))` and `x(v) = log(score(v))` gives the same problem.
The general additive core accepts real logarithms; the current rational sensor input need not
contain them. Arbitrary sensor scales instead require weighted row balance, so their optimum
must not be described by this unweighted cycle formula.

### 2. Chebyshev optimality becomes a small balanced active set

Known source: [Sukhorukova, Ugon, and Yost, *Chebyshev approximation for multivariate
functions*](https://arxiv.org/abs/1510.06076), section 2. The convex optimality condition
uses signed gradients of worst residuals; ordinary ordered alternation is a further special case.

For a nonempty finite row family, write
`ρ(x) = maxᵢ (bᵢ - ⟨δᵢ, x⟩)`. A global minimizer x with value t admits weights u such that

```text
uᵢ ≥ 0;  ∑ uᵢ = 1;  ∑ uᵢ δᵢ = 0;
uᵢ > 0 implies bᵢ - ⟨δᵢ, x⟩ = t.
```

Conversely these conditions and the residual upper bound prove optimality by weighted summation.
The weights can be chosen on at most `rank(span {δᵢ}) + 1` active rows by a convex-hull or
extreme-point argument. This is a certificate for the optimum, not merely for a rejected threshold.

The generic result is now packaged in
[OptimalCertificate](../Maths/Multitubes/FiniteInequality/OptimalCertificate.lean). It combines
normalized threshold duality with compact dual attainment, complementary slackness, and the
extreme-point sparsity mechanism from
[Sparse](../Maths/Multitubes/FiniteInequality/Sparse.lean). A related branch-specific tightness
theorem already appears as `MaxAffineTransport.branchResidual_eq_of_pos` in
[LeastEigenvalue](../Maths/Multitubes/MaxAffine/LeastEigenvalue.lean).

For sensors, [ActiveCertificate](../Applications/CellularSheaves/CellularSheaves/ActiveCertificate.lean)
identifies worst signed comparisons that jointly prevent improvement.
For general max-affine systems it identifies active affine/floor branches at an optimal relaxation.
There need not be an ordering with alternating signs, uniqueness, a minimum-cardinality
explanation, or at least `dimension + 1` active rows. Degenerate normals invalidate those claims.
An explicit nonempty-row assumption is unnecessary: existence of an attained least real level
already rules out the empty family. The sensor adapter assumes a comparison exists so that its
least nonnegative tolerance is also the unrestricted least residual level.

### 3. Fair worklists become a generic closure algorithm

Known source: [Cousot and Cousot, *Abstract Interpretation and Application to Logic Programs*](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-JLP-v2-n4-p511--547-1992.pdf),
section 4.2.4, particularly the chaotic-iteration termination statement.

The formal transport version starts from the seed family. Processing edge `e : s → t` changes
only the target to `x(t) ⊔ T(e)(x(s))`. Assume monotone edge maps and the ascending chain
condition on the product of the fibers. A schedule processing every edge infinitely often
eventually stabilizes at the least lax section above the seeds. Finite graphs and finite-height
fibers give a direct implementation setting; arbitrary-join preservation is not required.

Proof outline: updates increase the current family and preserve its upper bound by every
feasible majorant. ACC gives eventual constancy. Fairness then forces every local constraint,
and the preserved comparison gives leastness. Complete-lattice fibers identify this result
with `leastLaxMajorant` in [Closure](../Maths/Multitubes/Closure.lean).

The generic theorem is implemented in [Worklist](../Maths/Multitubes/Worklist.lean). Fair
schedules converge eventually under ACC on the family product, and repeated finite sweeps do so
when their edge list covers every edge. The finite threshold-evidence client uses the generic
fixed-sweep stopping theorem to prove its computed result least among sound seed extensions.
Termination of a concrete queue requires a queue invariant; a numerical step bound requires
bounded fairness as well as a height bound. A finite graph alone does not prevent infinite
ascending value chains. Widening can restore termination but generally sacrifices equality with
the least solution.

### 4. Bekić decomposition becomes modular section solving

Known application source: [Edwards and Lee, *The semantics and execution of a synchronous
block-diagram language*](https://www.cs.columbia.edu/~sedwards/papers/edwards2003semantics.pdf),
Theorem 3 and its no-feedback corollary. Their evaluation scheme uses Bekić decomposition;
[Censi's co-design theory](https://arxiv.org/abs/1512.08055) is another application of monotone
fixed-point methods to feedback.

For monotone `f : A × B → A` and `g : A × B → B` on complete lattices, define

```text
β(a) = leastFixedPoint (b ↦ g(a,b));
a* = leastFixedPoint (a ↦ f(a,β(a)));
b* = β(a*).
```

Then `(a*, b*)` is the simultaneous least fixed point. Monotonicity and complete lattices
suffice for this mathematical statement; continuity is needed only for a particular
countable-iteration construction. Applied to Bellman operators, finite SCC blocks can be
solved in condensation order, keeping predecessor results as external lower inputs.

Mathlib already supplies `OrderHom.map_lfp_comp` and `OrderHom.lfp_lfp`.
The project has [SCC structure](../Maths/Multitubes/SCC.lean), but its
[additive condensation theorem](../Maths/Multitubes/Additive/Condensation.lean) is an existence
decomposition, not a generic block solver. Product fixed-point packaging and restriction/assembly
remain missing. This could reduce repeated work in recursive analysis and finite co-design
without claiming Pareto-front representability. Interchanging mixed least/greatest nesting is
invalid, as the current games example already demonstrates.

### 5. Hoffman bounds turn local violations into global repair guarantees

Known source: [Hoffman, *On Approximate Solutions of Systems of Linear Inequalities*](https://nvlpubs.nist.gov/nistpubs/jres/049/4/v49.n04.a05.pdf), 1952.

For a fixed finite matrix A, chosen norms, and a nonempty feasible set `P = {x | A x ≥ b}`,
there is a constant H depending on the normals and norms such that

```text
distance(x, P) ≤ H * norm(positivePart(b - A*x)).
```

This would strengthen the finite-inequality application layer: an approximate sensor reading
or radius assignment with small violations is close to some valid assignment. It applies to
max-affine lax sections once their branch constraints are written as finite linear inequalities.
It does not automatically estimate distance to a Bellman fixed point or select a unique repair.

[Parametric feasibility](../Maths/Multitubes/FiniteInequality/Parametric.lean) proves closedness,
and the control client has a contraction-based bias margin. Neither gives this arbitrary-point
distance bound. Required additions include the metric formulation and a polyhedral error-bound
proof. Full rank is unnecessary for existence of H. Feasibility and finite dimension are
essential to this version; a useful explicit H also needs control of conditioning. Scaling
the inequality to `ε*x ≥ 1` shows why H cannot be independent of the matrix.

### 6. Doob normalization is transport by a positive change of coordinates

Known source: the harmonic-kernel and Doob-transform construction in
[*Markov chains on the nonnegative integers: analysis of stationary measure via harmonic
functions approach*](https://link.springer.com/article/10.1007/s11134-019-09602-5), especially
section 4. The following finite heterogeneous version is a proposed transport adapter.

Let a physical edge `e : s → t` carry a nonnegative finite matrix K, and let each h(v) be a
strictly positive finite-valued function. Define

```text
Q(e)(x,y) = K(e)(x,y) * h(t)(y) / h(s)(x).
```

If `K(e) h(t) = h(s)`, the rows of Q sum to one. If `K(e) h(t) ≤ h(s)`, they sum to at most
one. Thus a harmonic exact section normalizes the kernels, while a superharmonic lax section
normalizes them to sub-Markov kernels. For every finite path, intermediate factors cancel:
`Q(path)(x,y) = K(path)(x,y) * h(finish)(y) / h(start)(x)`.

Expectation transport runs against the physical edges. Multiplication by h gives the
intertwining relation `K(e) D(t) = D(s) Q(e)`, bringing
[transport morphism naturality](../Maths/Multitubes/Morphism.lean) into play. The current
[kernel client](../Applications/StochasticProcesses/StochasticProcesses/KernelTransport.lean)
already identifies sections with harmonicity and defines finite path kernels.

The missing finite normalization module should use positive real or nonnegative-real h;
positivity alone is insufficient for division in the existing extended-nonnegative observables,
which may equal infinity. This would support certified finite-path reweighting and normalize
positive linear comparison operators. Conditioning on a probabilistic event requires a separate
choice of h and probability semantics. The existing monoid-valued switching theorem is related,
but is not already a heterogeneous kernel-conjugation theorem.

A further return to applications is suggested by quantum Doob transforms, as in
[Cilluffo et al., *Microscopic biasing of discrete-time quantum trajectories*](https://arxiv.org/abs/2007.15659). The elementary proposed matrix counterpart is narrower:
given a Kraus map `Φ : s → t` and positive-definite matrices with `Φ(H(s)) = H(t)`, conjugate
by `D(v)(X) = H(v)^(1/2) X H(v)^(1/2)`. Then `D(t)⁻¹ ∘ Φ ∘ D(s)` is again Kraus-form and
maps the identity to the identity. A lax inequality instead gives a subunital map. This could
share the same generic change-of-coordinates theorem as finite Doob normalization, without
requiring an order adjoint of Φ. It asserts unitality; trace preservation would concern the
appropriate linear adjoint and is not the same equation. The square-root, invertibility, and
normalization adapters are not yet formalized in the quantum client.

### 7. Complete abstraction gives exact results in a chosen representation

Known source: [Giacobazzi, Ranzato, and Scozzari, *Making Abstract Interpretations Complete*](https://www.sci.unich.it/~scozzari/paper/JACM00.pdf), 2000.

Proposed sufficient condition: let `α(v) ⊣ γ(v)` connect complete-lattice fibers, with monotone
edge maps T and S and exact local commutation `α(t) ∘ T(e) = S(e) ∘ α(s)`.
For corresponding seeds `a = α(c)`, their least closures satisfy

```text
α(closureT(c)) = closureS(a).
```

One inequality follows because α sends concrete lax majorants to abstract ones. For the other,
the adjunction and commutation give `T(e) γ(s) ≤ γ(t) S(e)`, so γ is the existing upper
simulation and transports a sound abstract closure back to a concrete majorant.

[Morphism](../Maths/Multitubes/Morphism.lean) already contains that soundness inequality.
Packaging equality would identify when finite morphological features, abstract program states,
or evidence summaries add no error beyond the chosen abstraction. It would also make failed
commutation a precise target for refining a representation. Recovering the concrete closure
itself still requires `γ α` to fix that result; equality in the abstract domain does not imply
lossless reconstruction. A bare Galois connection is insufficient.

### 8. Boundary elimination generalizes circuit reduction

Known source: [Dörfler and Bullo, *Kron Reduction of Graphs with Applications to Electrical
Networks*](https://arxiv.org/abs/1102.2950). Circuit reduction uses a Schur complement to retain
boundary behavior while eliminating interior variables.

A more general target is a boundary relation: a boundary assignment is admissible exactly when
some interior assignment extends it to a section. Gluing two systems with a shared interface
then corresponds to existentially quantifying that interface in the conjunction of their
boundary relations. Internal variables must be disjoint and every shared constraint retained.

For the [sensor inequality encoding](../Applications/CellularSheaves/CellularSheaves/SensorNetwork.lean), this is projection of a
finite rational polyhedron, so [Fourier–Motzkin elimination](../Maths/LinearProgramming/FourierMotzkin.lean) provides a route to an explicit representation.
The same semantic operation underlies serial co-design feasibility and modular verification.

This is more than composing one walk relation: shared interior variables couple branches.
Projection can produce higher-arity constraints, requiring product fibers or a boundary relation
over a tuple. The Schur-complement formula further needs a linear equality model and an
invertible interior block; preserving a Laplacian needs its own structural hypotheses.
Neither exact SCC retracts nor generic relation composition already proves these facts.

## Priorities and implementation status

1. **Sensor cycle characterization: implemented.** Its abstract theorem was already checked;
   the new adapter makes a timing/optimization theorem answer a sensor question without
   reproducing its proof.
2. **Balanced active optimal certificates: implemented.** The generic endpoint and affine-sensor
   adapter give matching active certificates with rank-plus-one support.
3. **Fair worklists and threshold evidence: implemented.** Fair schedules under product ACC,
   finite covering sweeps, and a finite conjunctive evidence client are formalized. Bekić/block
   closure remains a separate proposal.
4. **Develop finite Doob normalization.** This is the clearest conceptual transfer between
   probability and the transport/gauge viewpoint, with a concrete finite-path theorem.
5. **Treat Hoffman repair and boundary reduction as separate larger developments.** They offer
   substantial application value but need metric/polyhedral or interface structure absent today.

## Implemented transfers and current status

Added [CellularSheaves/CycleConsistency.lean](../Applications/CellularSheaves/CellularSheaves/CycleConsistency.lean), imported by the
application umbrella. Under explicit unit source and target scales:

- `exists_isConsistent_uniform_iff_closedWalk_le` proves the exact cycle-threshold equivalence.
- `mem_uniformToleranceLevels_iff_closedWalk_le` includes nonnegativity, including empty networks.
- `minimumUniformTolerance_eq_of_cycle` proves optimality from the supplied consistent reading
  and the exact supplied positive-length signed cycle attaining the bound.

`signedComparisonGraph` and `signedComparisonWeight` expose the comparison graph and signed
real offsets. The proof uses the existing mixed-additive theorem; no core theorem is duplicated.
This cycle addition provides a characterization and supplied-cycle certificate, not an executable
optimizer or cycle search. Selection of a maximizing cycle is not packaged in the sensor API.

[FiniteInequality/OptimalCertificate](../Maths/Multitubes/FiniteInequality/OptimalCertificate.lean)
now proves dual attainment at an attained least residual level, complementary slackness on the
positive support, the converse optimality certificate, and a choice with support at most the
row-span rank plus one. The affine-sensor adapter packages these results for worst signed
comparisons at the minimum uniform tolerance.

[Worklist](../Maths/Multitubes/Worklist.lean) now proves eventual equality with the least lax
majorant for fair schedules under product ACC and for repeated finite sweeps whose list covers
every edge. [ThresholdPolicy](../Applications/WebOfTrust/WebOfTrust/ThresholdPolicy.lean) uses
the generic fixed-sweep theorem to prove that its two-pass conjunctive evidence result is the
least sound assignment above its seeds.
Bekić decomposition, Hoffman bounds, Doob normalization, complete abstraction, and boundary
elimination remain proposals with the prerequisites described above. The clean rebuild of all
86 core modules and 15 application packages passed with zero warnings; kernel, documentation,
and repository audits also passed. The [implementation review](active-certificates-and-worklists-2026-09-22.md)
records the exact statements, application limits, and validation counts.
