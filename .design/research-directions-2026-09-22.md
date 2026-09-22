# Spectral reachability and certified control radii

Investigation baseline: `29aa4a6`, Lean/mathlib `v4.34.0`.
This records the follow-up to the application capstones and the request to investigate
interesting consequences. Mathematical novelty remains unestablished; the statements below
distinguish checked additions from research questions and known proof methods.

## Main results

### Reachability replaces strong connectivity in spectral existence

Write `F` for the vertex maximum of incoming max-affine labels with nonnegative slopes.
Assume finitely many edges and at least one incoming edge at every vertex. A relaxation
level `λ` is feasible when some real vector `p` satisfies `F(p) ≤ λ + p`.
An additive eigenvector satisfies `F(x) = λ + x`.

`Maths/Multitubes/MaxAffine/AnchoredEigenvalue.lean` adds two sufficient conditions.

1. If every vertex is reachable from the target of a constant branch or from a vertex
   admitting a closed walk with slope product strictly below one, **every feasible
   relaxation level is an eigenvalue**. Thus the spectrum equals the relaxation set.
2. Given a feasible potential and a normalized dual certificate of the same value,
   every vertex need only be reachable from the union of those lower-bound vertices
   and the certificate's critical vertices. The certificate value is then the least
   eigenvalue. This second theorem assumes finite vertices for the certificate calculus.

A constant branch includes both a finite floor and a zero-slope affine branch. Individual
edges may expand. No global contraction, strictly positive slopes, or strong connectivity
is required. Reachability follows the original edge direction. These are sufficient
conditions, not necessary ones: the one-vertex map `F(x) = 2*x` has every real number as
an additive eigenvalue despite having neither type of lower-bound vertex.

The proof starts the descending iteration `x₀ = p`, `xₙ₊₁ = F(xₙ) - λ`.
For a contracting closed walk of length `k`, its relaxed affine part is `B + A*x`,
where `0 ≤ A < 1`. Walk propagation and descent give
`B + A*xₙ(v) ≤ xₙ₊ₖ(v) ≤ xₙ(v)`, hence `B / (1 - A) ≤ xₙ(v)`.
A constant branch supplies a lower bound directly. At an optimal certificate's critical
coordinates the old complementary-slackness argument freezes the orbit. Monotone walk
transport propagates each such lower bound to reachable vertices. Coordinatewise infima
then give an eigenvector below the original feasible potential.

The formal entry points are
`eigenvalues_eq_relaxationLevels_of_reachable_lowerBounds` and
`isLeast_eigenvalues_of_reachable_certificate` in `Maths.MaxAffineTransport`.
The spectrum is consequently upward closed under the first criterion; if the relaxation
minimum is attained, the spectrum is precisely the closed ray starting at that minimum.
The construction uses completeness of the reals. It is not an executable spectral solver
or a convergence-rate theorem for arbitrary max-affine maps.

`ReducibleExamples.lean` tests the connectivity boundary. Disconnected unit-slope loops
`F₀(x) = x₀ + 1` and `F₁(x) = x₁` have relaxation set `[1, ∞)` but empty spectrum.
In contrast, a shift-one loop at vertex zero feeding a doubling edge into vertex one
has eigenvalue one with vector `(0, -1)`, despite not being strongly connected.
Its normalized certificate has all its mass on the shift-one loop, and the example applies
the new reachable-certificate theorem. The existing reset/doubling map `F(x) = max(10, 2*x)`
also instantiates the new spectrum/relaxation equality using its constant reset branch.

### Least radii and exact rational evidence

For nonnegative edge gains and a supplied positive contraction gauge with rate below one,
the radius Bellman operator is
`H(r)(v) = max(lower(v), max incoming (bias(e) + gain(e)*r(source(e))))`.
Synthetic constant edges implement the lower bounds, including at isolated vertices.
Gauge normalization makes this a contraction. The fixed point is the least family
satisfying all lower and edge bounds; Bellman iteration converges from every initial
vector, and an upper budget is feasible exactly when this least family respects it.
The reusable construction belongs in `MaxAffine/RadiusFixedPoint.lean`.
The normalized iteration also has the a priori error estimate
`dist(Hⁿ(z), fixed) ≤ dist(z, H(z)) * qⁿ / (1 - q)` for the normalized operator and
`0 ≤ q < 1`. Unlike the general spectral theorem, this contraction result gives uniqueness.
`SwitchedHybridControl/LeastRadius.lean` exposes the construction through `ErrorComparison`
and identifies the existing weighted example with the general least radius above zero.

`SwitchedHybridControl/RationalRadius.lean` specializes exact rational point and Farkas
checking to bounded comparison radii. Accepted points imply real all-walk error bounds
for a matching comparison model; accepted dual weights rule out all real comparison
radii within the given bounds. The two-mode example uses gains two and one eighth,
unit biases, and radii `(3/2, 4)`. An explicit sparse dual rejects a tighter budget.
These are witness checkers, not witness generators. Comparison infeasibility does not
establish physical unsafety.
For the rejected second-mode budget `7/2`, the certificate weights are four and eight
on the two edge rows and three on that upper-budget row. The variable coefficients
cancel and the weighted right-hand side is `3/2 > 0`. Both lower bounds remain zero.

## References

The following primary sources were checked on 2026-09-22. This is a focused comparison,
not an exhaustive priority search.

- Akian and Gaubert, [Spectral Theorem for Convex Monotone Homogeneous Maps, and
  Ergodic Control](https://arxiv.org/abs/math/0110108), 2001 preprint / 2003 journal.
  Despite the title, its scope includes nonhomogeneous convex monotone maps that are
  nonexpansive in the sup norm. Critical-coordinate fixed-point representations and
  descending iteration are established ideas. Nonhomogeneity alone therefore does
  **not** distinguish our result. This corrects the overly narrow comparison suggested
  in the initial discussion.
- Akian, Gaubert, and Lemmens, [Stability and convergence in discrete convex monotone
  dynamical systems](https://arxiv.org/abs/1003.5346), 2011.
  This closer predecessor allows maps that are not nonexpansive, and studies tangentially
  stable fixed points. Section 7 constructs fixed points by descending iteration from
  supersolutions when orbits are bounded below. Our elementary iteration method is not
  a novelty claim; the specific graph/certificate hypotheses that ensure the bounds are
  the remaining point for comparison. Their general framework also cautions against
  treating expansive branches alone as evidence of novelty.
- Dadush, Koh, Natura, and Végh, [An Accelerated Newton–Dinkelbach Method and Its
  Application to Two Variables per Inequality Systems](https://arxiv.org/abs/2004.08634),
  ESA 2021; [published paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol204-esa2021/LIPIcs.ESA.2021.36/LIPIcs.ESA.2021.36.pdf).
  Monotone two-variable-per-inequality systems have at most one positive and one negative
  coefficient per row. Their Theorem 3.3, attributed to Shostak, characterizes infeasibility
  through negative unit-gain cycles or negative bicycles: connected contracting and
  expanding cycles with incompatible bounds. Thus the earlier example where every cycle
  has some pre-fixed point but no common feasible potential belongs near an established
  obstruction theory, rather than establishing a new phenomenon. The paper also supplies
  a strongly polynomial algorithm; no such algorithm is implemented here.
- Dashkovskiy, Rüffer, and Wirth, [Small gain theorems for large scale systems and
  construction of ISS Lyapunov functions](https://arxiv.org/abs/0901.1842).
  Cycle small-gain conditions and positive scalings are established control tools.
  The contraction-gauge and least-radius additions are formal infrastructure and concrete
  applications, not claimed new control theorems.

## TODO

1. Compare the exact reachable-lower-bound and optimal-certificate criteria with the
   convex monotone stability literature, including reducible critical-graph results.
   Determine whether the criteria are known specializations, useful sharpenings, or new
   statements. A checked proof alone cannot decide literature novelty.
2. Formalize generalized-flow/negative-bicycle infeasibility witnesses, then connect them
   to the existing Farkas certificates. The present radius rows are monotone two-variable
   inequalities, including unary bounds and self-loop cancellations. Zero gains need
   explicit handling when matching literature conventions that require positive gains.
3. Implement a certificate-producing radius solver and prove its termination and output
   correctness. Keep the existing exact checker as the small verification boundary.
   **The augmented least-level LP is generally not two-variable:** adding the unknown
   `λ` to an edge row introduces a third variable. Fixed-level radius/relaxation checking
   and optimizing the level must not be conflated.
4. Add executable, certified approximations to least radii with stopping tolerances,
   and quantitative sensitivity to simultaneous gain and bias perturbations. Real-valued
   convergence and exact checking are separate from such an implementation.
5. General max-affine eigenpairs do not imply linear growth under iteration. Such a claim
   requires additional structure, such as the additive homogeneity already used in the
   timed synchronization application.

## Validation

`bash scripts/check.sh` passed after cleaning and rebuilding the root and every application
package. The log is `/tmp/multitubes-research-final-check.log`.

- All 84 core modules and all 15 application packages built with zero errors and warnings.
- The kernel audit checked 2,768 core declarations and every application namespace,
  including 234 switched-control declarations. All had zero `sorryAx` dependencies and
  zero dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.
- All 1,377 indexed names and 191 project prose references resolved.
- Foundation layering, the single external Brouwer importer, checker regressions,
  100-character Lean lines, and the prohibition on `set_option` passed.
- Both new rational checker examples were additionally evaluated and returned `true`.

Sol subagents implemented the least-radius theory/application bridge, exact rational
checking, and spectral examples. Independent Sol review found no mathematical defect
in the new spectral and least-radius arguments. Review corrected an unnecessary lower-bound
strengthening in the rejection example and made critical reachability explicit in its
example theorem. The root developed the spectral reachability proof and literature review.
