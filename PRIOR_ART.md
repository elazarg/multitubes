# Prior art: generalized gain graphs

A survey of work that generalizes Zaslavsky's group-valued gain graphs along the directions
Multitubes takes, and of the applications those generalizations serve. Status markers:

- **[verified]**: checked against the primary source by at least two of three independent
  adversarial readers.
- **[lead]**: fetched or named but not yet verified; treat as a pointer, not a claim.
- **[open]**: searched for and not found; absence is not evidence of nonexistence.

Last updated: 2026-11-15.

## Summary

Each feature of the library has close precedent, but no verified source combines them:

- monoid- or function-valued labels on a functor from the free path category of a quiver, with
  vertex-dependent fibers;
- exact, lax, oplax, and relational edges in one constraint system;
- holonomy-based existence criteria for sections that specialize uniformly to the additive,
  multiplicative, max-plus, and Loynes cases.

This combination is an *inference from absence* in the sources checked so far, not an
established novelty result. See [Gaps](#gaps-and-open-questions).

The contribution to claim is therefore *unification*, not new specializations:

> The individual specializations are classical: balance of gain graphs, difference constraints
> and TVPI systems, generalized networks, max-plus spectra, and constraint networks; the
> fixed-point view of lax sections goes back to abstract interpretation. Multitubes places them
> in one framework: transports on a quiver with vertex-dependent fibers; exact, lax, oplax, and
> mixed constraints; and holonomy criteria for each regime, together with the counterexamples
> marking where cyclewise criteria fail. To our knowledge it is the first such unified
> treatment, and the first machine-checked one.

Expected objections: category theory (sections as limits, lax sections as lax cones of a
functor from the free category, folklore as definitions); abstract interpretation (per-point
lattices, monotone transfer maps, invariants as post-fixed points); path algebras (Carré,
Gondran–Minoux) as an earlier one-algebra-for-all-path-problems attempt, for summaries rather
than solvability. One concrete payoff of unification: the "every cycle passes, no solution
exists" obstruction appears independently as Montanari's K₄, Shostak's Fig. 1, Cohen–Megiddo's
path-plus-cycle certificates, and `MaxAffine/Farkas` here, and no prior source relates them.

## By feature

### Non-involutive directed labels

- **[verified]** M. Evans, *Group graphs* (arXiv:2505.22802, 2025, preprint). Generalizes signed
  networks to labels in an arbitrary group with Zaslavsky-style balance, and drops the gain-graph
  convention that reversing an edge inverts its label: edges need not be reciprocated, and labels
  of reciprocated edges need not be inverses. Monoids, status, and weak balance appear only as
  discussed extensions. Closest recent move toward non-involutive quiver labelling; still
  group-valued.

### Vertex-dependent fibers (sheaves)

- **[verified]** J. Hansen, R. Ghrist, *Toward a spectral theory of cellular sheaves*
  (J. Appl. Comput. Topol. 2019; arXiv:1808.01513). Global sections equal H⁰ = ker δ⁰ = ker L₀.
  The Singer–Wu graph connection Laplacian "is simply the sheaf Laplacian of an O(n)-vector
  bundle over a graph".
- **[verified]** R. Ghrist, H. Riess, *Cellular sheaves of lattices and the Tarski Laplacian*
  (Homology Homotopy Appl. 24(1), 2022; arXiv:2007.04099). Lattice-valued stalks, Galois-connection
  restriction maps; the Tarski Laplacian is order-preserving and its fixed points recover global
  sections in degree 0. Applications: consensus, distributed optimization.
- **[verified]** M. Robinson, *Assignments to sheaves of pseudometric spaces* (Compositionality
  2020; arXiv:1805.08927). Consistency radius: a continuous metric measure of how far an
  assignment is from a section, zero on sections, bounding distance to the nearest section under
  Lipschitz restrictions. Metric, not order-theoretic, relaxation.

*Structural difference.* A cellular sheaf puts two maps on each edge, from each endpoint stalk
into an edge stalk; the library puts one map Tₑ : F s → F t between vertex fibers. The library's
exact sections correspond to the sheaf case where one restriction is the identity. A broader
claim that sheaves are simply the linear special case of the library's setting was refuted
(1–2) on exactly this point. Sheaf solvability is characterized by kernels or Tarski fixed points,
not by closed-walk holonomy.

### Holonomy, connections, synchronization

- **[verified]** A. Singer, H.-T. Wu, *Vector diffusion maps and the connection Laplacian*
  (CPAM 2012). Edges carry O_ij ∈ O(d) with O_ji = O_ijᵀ; path transformations are ordered
  products (eq. 3.11), compared to parallel transport; consistency O_ij = O_iᵀ O_j. Other groups
  "are not treated here". Applications: cryo-EM, manifold learning.
- **[verified]** A. Bandeira, A. Singer, D. Spielman, *A Cheeger inequality for the graph
  connection Laplacian* (SIMAX 2013; arXiv:1204.3873). Spectral bound on O(d) synchronization
  frustration.
- **[verified]** C. Lange, S. Liu, N. Peyerimhoff, O. Post, *Frustration index and Cheeger
  inequalities for discrete and continuous magnetic Laplacians* (Calc. Var. PDE 2015;
  arXiv:1502.06299). Cheeger constant mixing frustration index and expansion; cyclic signatures,
  discrete U(1) magnetic Laplacians; links Harary balance to gauge invariance.
- **[lead]** T. Gao, J. Brodzki, S. Mukherjee, *The geometry of synchronization problems and
  learning group actions* (Discrete Comput. Geom. 2021). Synchronization as flat-bundle holonomy.

All of the above assume invertible gains and one group at every vertex: prior art for the
library's switching, balance, and frustration results in the group case only.

### Multiplicative gains, switching, duality

- **[verified]** Generalized networks (networks with gains): positive-real multiplicative gain
  graphs. Path/cycle gains are products; a cycle of gain > 1 is flow-generating. Glover–Klingman
  relabeling γ_μ(v,w) = γ(v,w) μ(v)/μ(w) is gain-graph switching, and the labels are LP dual
  variables; with no residual flow-generating cycle, canonical labels come from one
  shortest-path run on costs −log γ. Verified via K. Wayne, L. Fleischer, *Faster approximation
  algorithms for generalized flow* (gain-scaling paper). Cite the originals:
  W. S. Jewell (Oper. Res. 1962), K. Onaga (1966/67), K. Truemper (Networks 1977),
  F. Glover, D. Klingman.

### Additive weights, difference constraints, potentials

- **[verified]** R. Dechter, I. Meiri, J. Pearl, *Temporal constraint networks* (AIJ 1991),
  Theorem 3.1: an STP is consistent iff its distance graph has no negative cycle; shortest-path
  distances give the latest and earliest schedules. Also R. Shostak (JACM 1981), Y. Liao,
  C. K. Wong (1983), C. Leiserson, J. Saxe (retiming, 1991); ultimately Bellman–Ford.
  Applications: temporal reasoning, scheduling, timing analysis.

### Max-plus spectra and recurrences

- **[verified, cite the monographs]** For irreducible A, the unique eigenvalue is the maximum
  cycle mean; in general every finite eigenvalue is a cycle mean and the largest is the maximum
  cycle mean. If no circuit is positive, x = A*b solves x = Ax ⊕ b, uniquely if all circuits are
  negative (sufficient, not necessary). F. Baccelli, G. Cohen, G. J. Olsder, J.-P. Quadrat,
  *Synchronization and Linearity* (1992), Thms 3.17, 3.23; R. A. Cuninghame-Green,
  *Minimax Algebra* (1979); P. Butkovič, *Max-linear Systems* (2010); R. M. Karp (1978).
- **[lead]** A Springer *Queueing Systems* paper (doi:10.1007/s11134-006-7730-5) on max-plus
  recurrences, fetched but not verified.

### Two-variable-per-inequality (TVPI) systems: affine edge maps

- **[verified]** V. R. Pratt (1977), as reported in R. Shostak, *Deciding linear inequalities by
  computing loop residues* (JACM 28(4), 1981): feasibility of x ≤ y + c over ℝ and ℤ is decided
  by examining loops. This is the translation-holonomy (no negative cycle) case.
- **[verified, full text]** R. Shostak, JACM 28(4):769–779, 1981. Undirected multigraph, one
  vertex per variable plus a zero variable v₀, one edge per inequality ax + by ≤ c. A path is
  *admissible* if consecutive coefficients on each shared variable have opposite signs (§2), so
  the composable walks carry a direction the graph does not. Residues compose by an associative
  operation on triples, (a,b,c) * (a′,b′,c′) = (kaa′, −kbb′, k(ca′ − c′b)) with k = a′/|a′|:
  a monoid of affine bounds. A loop is *infeasible* if a_P + b_P = 0 and c_P < 0 (§3).
  - Raw-graph loops are not enough: Fig. 1 is an unsatisfiable system whose graph "has no
    infeasible loops, simple or otherwise" (§3).
  - Main theorem: form a *closure* G′ by adding, for each simple admissible loop, an edge
    labelled with its residue; then S is unsatisfiable iff G′ has an infeasible simple loop.
  - For difference constraints (Pratt's "separation theory") the graph is its own closure, so
    the theorem reduces to "no simple loop with negative constant sum" (§4).
  - Holonomy-style invariances: infeasibility is preserved by cyclic permutation of a
    permutable loop (Lemma 6) and by reversal (Cor. 5).
  - The *discriminant* c_P/(a_P + b_P) is the fixed point of the loop's composed affine bound
    (§7); the proof constructs a solution. §5: strict inequalities; §6: arbitrary systems by
    iterating closure (an elimination procedure).
- **[verified, full text]** B. Aspvall, Y. Shiloach, *A polynomial time algorithm for solving
  systems of linear inequalities with two variables per inequality* (SICOMP 9(4), 1980). Same
  graph and residue operation; "the residue imposes a direction on P even though the graph is
  undirected". Makes the fixed-point reading explicit (§2.1): pushing a guess g around a loop
  gives μg + (1 − μ)h with μ = −a_P/b_P and h = c_P/(a_P + b_P), the loop's "hidden
  inequality". Loops are classified by μ (Table 1): flipping (μ < 0, antitone), converging
  (0 < μ < 1), diverging (μ > 1); μ = 1 is the slope-one case where the test reduces to the sign
  of c_P. Loops of length ≤ n suffice (Lemma 8), and the closure can be replaced by the tightest
  single-variable bounds found by binary search (Thms 3–5). This is the closest found precedent
  for "solvability via the fixed points of closed-walk holonomies", for affine maps on ℝ, with
  the caveat that it holds only after closure.
- **[verified, full text]** E. Cohen, N. Megiddo, *New algorithms for generalized network flows*
  (Math. Programming 64, 1994). Not the TVPI paper. Positive multipliers aₑ on arcs; bidirected
  case via negative multipliers (§4). The LP dual of uncapacitated generalized transshipment is
  πᵢ − aₑπⱼ ≤ cₑ, a monotone TVPI system (a lax-section condition), solved by one call to their
  TVPI algorithm (SICOMP 1994, unread). A dual bound corresponds to a "generalized augmenting
  path": a flow-generating cycle plus a path (Adler–Cosares). No cycle feasibility theorem.
- **[verified, full text]** E. Cohen, N. Megiddo, *Improved algorithms for linear
  inequalities with two variables per inequality* (SICOMP 23(6), 1994; preliminary version
  STOC 1991, pp. 145–155). The closest TVPI precedent for the library's directed,
  transport-style view. Numbers below follow the STOC abstract; journal-only results are
  listed after them.
  - Def. 2.1: each variable gets an upper-bound and a lower-bound vertex; each inequality gives
    an edge e labelled with an affine fₑ and a reverse edge labelled with fₑ⁻¹. This doubled
    graph is a genuine directed graph with affine edge maps, the signed-literal structure that
    Shostak's admissibility encodes implicitly.
  - Def. 2.6: path maps f_p are compositions of edge maps; increasing iff both ends are on the
    same side. Def. 2.7: a cycle at v closes at v or at its mirror v⁻¹ and yields the bound
    x ≤ f_c(x), i.e. a constraint at the fixed point of the cycle's holonomy.
  - Prop. 2.3: x is a solution iff it lies in the single-variable intervals and is *invariant
    under pushes*: a lax section as a fixed point of edge-wise propagation.
  - Prop. 2.9 (Shostak): on a feasible system, [x_min, x_max] is the projection of the solution
    set. 2n push phases suffice (Alg. 2.15); certificates for monotone systems are a path plus a
    cycle (§4.2).
  - Prop. 4.1: solutions of monotone systems form a lattice under ∨, ∧ (a semilattice under a
    pre-Leontief sign condition, after Cottle–Veinott).
  - §5.1: the dual of uncapacitated generalized transshipment, πᵢ − aᵢⱼπⱼ ≤ cᵢⱼ, is monotone;
    its maximal or minimal feasible point is optimal (Adler–Cosares).
  - Journal version, Def. 2.3: *closed* cycles (v to v, increasing f_c) and *open* cycles
    (v to v⁻¹, decreasing f_c, a one-sided bound). Prop. 2.17 treats a closed cycle by the sign
    of f_c(y) − y, which changes sign at most once: if it is a constant of the wrong sign
    (the slope-one case) the system is infeasible; otherwise the cycle's bound is the half-line
    cut at its unique fixed point y*. The cleanest statement found of "a cycle constrains by
    the fixed point of its holonomy" for affine maps.
  - Journal Prop. 2.10 (Shostak): feasible iff every interval [x_min, x_max] built from simple
    cycles and simple paths is nonempty. Certificates of infeasibility are a simple path to w
    plus a disjoint simple cycle at w (§2.5), "closed" or "open".
  - Journal Cor. 2.11 and Prop. 2.12: TVPI polyhedra are exactly those with a Helly number 2
    for bounds (a box misses P iff two of its bounds already do); a conflict between two added
    bounds is certified by a single simple path. Polyhedral lattices are exactly solution sets
    of monotone systems (§7, after Veinott); pre-Leontief systems give ∨-semilattices
    (Cottle–Veinott).
- **[verified, secondary]** On a feasible TVPI system, chains and cycles of length ≤ d give each
  variable's exact range, but not the joint feasible set (Fukuda–Szedlák, arXiv:1610.02820).
- **[verified]** D. Hochbaum, J. Naor, *Simple and fast algorithms for linear and integer programs
  with two variables per inequality* (SICOMP 23(6), 1994). Integer feasibility of monotone
  systems a xᵢ − b xⱼ ≤ c (a, b > 0) by descending iteration with non-invertible floor maps
  xᵢ ← ⌊(c + b xⱼ)/a⌋, from the top of the fractional lattice; the feasible set is a distributive
  lattice (Thm 3.1). In library terms, a greatest lax section reached by Kleene iteration, with no
  cycle test. Closest precedent for non-invertible monotone edge maps with lax constraints.

### Relation-labelled edges: constraint networks

- **[verified]** U. Montanari, *Networks of constraints* (Inform. Sci. 7, 1974). Directed graph,
  finite domain Xᵢ per vertex, arbitrary binary relation Rᵢⱼ per arc, composition along walks
  (Boolean matrix product) and intersection for conjunction; no invertibility (converse is
  transpose). A pair is legal iff every walk allows it; path consistency reduces all walks to
  length 2. All-walk consistency is *necessary but not sufficient* for solvability: the
  3-coloring of K₄ is path-consistent and unsolvable. The precise counterpart, and limit, of a
  holonomy criterion for relational sections.
  - **[verified, full text] Section 5, lattice-valued domains.** Each Xᵢ is a complete
    lattice. A total relation is *monotone* iff it has the form s ≤ fᵢⱼ(r) with fᵢⱼ preserving
    binary inf (Thm 5.4); dually r ≥ gᵢⱼ(s) with gᵢⱼ preserving sup. Monotone relations are
    closed under intersection and composition (Thm 5.5): a lax-constraint calculus on
    per-vertex lattices. Shortest paths, x_j ≤ x_i + tᵢⱼ, are the stated special case, and
    the closure algorithm is likened to Warshall–Floyd.
  - Thm 5.7: if the off-diagonal relations are monotone and the loop relations after one
    closure iteration are the identity ("all pairs (x_i,r, x_i,r) must be allowed by all
    circuits"), then the network is star-distributive, decomposable, and its symmetrization
    is minimal. A *circuit-contains-the-diagonal* hypothesis, i.e. every circuit's composed
    relation is reflexive at its base, used as a *sufficient* condition. It is not stated as
    an iff and not as a solvability criterion; in the shortest-path case it amounts to "no
    negative cycle", though the paper does not say so. The earliest found use of a
    closed-walk hypothesis for lax constraints on lattices.
- **[verified, full text]** P. Ladkin, R. Maddux, *On binary constraint problems*
  (JACM 41(3), 1994). One universe shared by all variables (no per-vertex domains); a complete
  digraph with one edge per ordered pair, i.e. an n×n matrix over a relation algebra with
  diagonal ≤ 1′. Path consistency is M ≤ M², equivalently composition along every *open* path
  bounds the direct edge; no cycle or closed-walk criterion appears. Results: path consistency
  terminates within d·n² iterations over a finite algebra with d atoms (Thm 6.2); an order-4
  matrix with infinite relations on which no iterative local algorithm terminates (Thm 6.4);
  Θ(n²) lower bound via the "Hard Algebra" (Thm 7.1); proto-solutions of closed interval-algebra
  matrices are NP-complete (Cor. 5.12). Solvability is relative to a representation: a basic
  containment-algebra matrix solvable in one representation and not another (Thm 5.9). Closure
  is necessary but not sufficient (citing Allen 1983).
- **[verified]** P. van Beek (AAAI 1992), P. van Beek, R. Dechter (JACM 42, 1995): row-convex
  relations closed under composition, intersection, transpose make path consistency compute the
  minimal, globally consistent network; proof by a Helly-type lemma, not a cycle argument.
- **[verified]** R. Dechter, *From local to global consistency* (AIJ 55, 1992): strong
  (|D|(r−1)+1)-consistency implies global consistency; refined by tightness in van Beek–Dechter.

None characterizes global solvability by closed-walk holonomy; the tractable cases come from
local consistency plus structural (convexity, topology, domain-size) hypotheses.

### Monoid labels on control-flow graphs: algebraic program analysis

- **[verified]** R. E. Tarjan, *Fast algorithms for solving path problems* (JACM 28(3), 1981):
  single-source path expressions, a regular expression for all s→v paths.
- **[verified]** A. Farzan, Z. Kincaid, *Compositional recurrence analysis* line
  (arXiv:1310.3481): path expressions interpreted in a *pre-Kleene algebra* (join-semilattice
  for choice, monoid for sequencing, an iteration operator weaker than Kleene star). Edge labels
  are non-invertible monoid elements; loops are *summarized* by the iteration operator, not
  tested. No solvability condition: the path problem always has an answer.
- **[lead]** P. Cousot, R. Cousot (abstract interpretation; inductive invariants as post-fixed
  points, which are lax sections of the transfer-function transport); G. Kildall (dataflow);
  B. Carré, *Graphs and Networks* (1979); M. Gondran, M. Minoux, *Graphs, Dioids and Semirings*
  (2008); M. Mohri, *Semiring frameworks and algorithms for shortest-distance problems*
  (J. Autom. Lang. Comb. 2002); Z. Kincaid et al., POPL 2019. All fetched, not verified.

### Partial (non-invertible) maps: synchronization of partial matchings

- **[lead]** F. Bernard, J. Thunberg, J. Goncalves, C. Theobalt, *Synchronisation of partial
  multi-matchings via non-negative factorisations* (Pattern Recognition 2019;
  arXiv:1803.06320). With partial permutations, compositions around a cycle may vanish, so cycle
  consistency must be redefined; it is shown equivalent to a factorization W = UUᵀ through a
  "universe". Closest found precedent for cycle consistency with non-invertible edge maps.
  Background: D. Pachauri, R. Kondor, V. Singh (NeurIPS 2013, permutation synchronization);
  Q. Huang, L. Guibas (SGP 2013, consistent shape maps).

### Signed-graph balance in dynamics

- **[verified, full text]** D. Angeli, E. Sontag, *Monotone control systems* (IEEE TAC 48(10),
  2003). Monotonicity with respect to an orthant is a sign condition on the Jacobian
  (Cor. III.3), proved by the change of variables z = Px with P = diag(±1), credited to Smith:
  exactly a ±1 switching, not named as such. The graph criterion ("there should not be any
  negative (nonoriented) loops") is one unproved sentence deferred to their *Multi-stability*
  paper; Harary and Zaslavsky are not cited. Per-subsystem state spaces with their own cones.
  Small-gain theorem (Thm 3): equilibria of a negative-feedback loop correspond one-to-one with
  fixed points of the composed I/O characteristic k_w ∘ k_y, and the loop is globally attractive
  if that composite map's iteration is: a holonomy-fixed-point statement for monotone maps on a
  two-vertex cycle.
- **[verified, full text]** D. Angeli, E. Sontag, *Multi-stability in monotone input/output
  systems* (Systems Control Lett. 51, 2004). Signed digraph on states, inputs, outputs from
  partial-derivative signs (self-loops ignored; defined only when each sign is constant).
  Prop. 4.1: orthant-monotone iff no negative cycle, cycles "not necessarily directed". Not
  proved here: cited to Kunze & Siegel, and no switching is constructed. Theorem 3: under
  unitary positive feedback, equilibria correspond one-to-one with fixed points of the I/O
  characteristic k_Y; fixed points with k_Y′ < 1 are stable, those with k_Y′ > 1 unstable, and
  almost all trajectories converge to stable ones (via Hirsch's generic convergence).
- **[lead]** H. Kunze, D. Siegel, *A graph theoretical approach to monotonicity with respect to
  initial conditions* (Part I, early 1990s; venue unconfirmed) and *... II* (Nonlinear Anal. 35,
  1999, 1–20); also *A graph theoretic approach to strong monotonicity with respect to
  polyhedral cones* (Positivity 6, 2002, 95–113), and Kunze's Waterloo thesis (1997). Primary
  source for the signed-graph monotonicity criterion that Angeli–Sontag cite. R. Iacob, C. Altafini (2009, Linköping): distance to
  monotonicity equals the minimal number of negative fundamental cycles (a frustration index).
  B. DasGupta, G. Enciso, E. Sontag, Y. Zhang (BioSystems 2007): approximation for maximal
  sign-consistent subgraphs. Applications: systems biology, multistability.

### Group gains: other recent Zaslavsky-school work

- **[lead]** M. Gottstein, T. Zaslavsky, *The Rhodes semilattice of a biased graph*
  (arXiv:2309.02700): Rhodes semilattices of a group reinterpreted via gain graphs and extended to
  biased graphs; v2 adds groupoids. Group gains.
- **[verified, full text]** P. Potočnik, M. Toledo, *Generalised voltage graphs* (European
  J. Combin. 94, 2021, 103313). Undirected dart graphs with semi-edges; voltages ζ in a *group*
  G plus a subgroup weight ω on vertices and darts, so the fibre over v is the coset space
  G/ω(v): vertex-dependent, but always homogeneous G-sets. Walk voltages are *subsets* of G
  (eq. 6.1, Lemma 30). Closed-walk voltages characterize connectivity of the cover (Thm 33),
  not existence of sections; reconstruction of any graph from a group of automorphisms
  (Thms 4, 14) generalizes Gross–Tucker, coset and bicoset graphs. Tangential to the library.

### Set-valued quiver representations, queues

- **[lead]** arXiv:2608.16636 (2026): set-valued quiver representations (functors into finite
  sets) and "eventual constancy" along long paths, compared with nilpotent linear
  representations. Closest found treatment of the library's function-labelled transport as a
  quiver representation in **Set**.
- **[lead]** R. M. Loynes, *The stability of a queue with non-independent inter-arrival and
  service times* (Proc. Cambridge Philos. Soc. 58, 1962) and *Stationary waiting-time
  distributions for single-server queues* (Ann. Math. Statist. 33(4), 1962): the Lindley–Loynes
  equation under stationarity and ergodicity only. Cite for the library's Loynes reflection.
  Network calculus: J.-Y. Le Boudec, P. Thiran, *Network Calculus* (2001); C.-S. Chang,
  *Performance Guarantees in Communication Networks* (2000); R. Cruz (IEEE Trans. Inf. Theory
  1991). Not verified.

## Gaps and open questions

**[open]** Still no verified prior art for:

- gain or voltage graphs over monoids, semigroups, or categories (searches return only group
  gains, groupoid-*domain* voltage assignments, and graphs of monoids in C*-algebra theory);
- a theorem "a section exists iff every closed-walk holonomy fixes a point" for non-invertible
  labels;
- mixed exact/lax edges in a single framework beyond STPs with equalities;
- abstract interpretation framed as sections of a transport (only leads above).

*Note on the holonomy criterion for non-invertible maps.* For invertible labels, fixing a base
point under every closed-walk holonomy suffices for a section. For non-invertible maps it does
not in general: two paths p, q from b to v can send x to different points that a non-injective
return map r sends back to x. Montanari's K₄ example is the relational analogue. Any prior
theorem should be checked for which side of this line it sits on.

Open questions:

1. Has anyone proved a holonomy criterion for monoid, semigroup, or groupoid gains, and with what
   extra hypothesis (injectivity, ordering, a closure step as in Shostak)?
2. Does the Ghrist–Riess Tarski-Laplacian fixed-point characterization coincide with the
   library's lax-section results on quivers, or derive from them? Same question for
   Hochbaum–Naor's descending iteration.
3. Is there prior work mixing exact and inequality edge constraints in one framework, beyond STPs
   with equalities or generalized flows?
4. How far does Zaslavsky's dynamic bibliography (EJC DS8) cover non-group gains? All three claims
   sourced to it were refuted or rejected.
5. Full text still unread: Kunze–Siegel, the primary source of the signed-graph monotonicity
   criterion.
6. *Checked:* Shostak's Fig. 1 does not contradict any library theorem. Translated into lax
   form (negate every variable), it needs an edge of slope −2 and an upper bound on one
   vertex, so it falls outside every cyclewise iff in the library: those assume unit slopes
   (`exists_isLaxSection_iff_forall_cycle_exists_prefixed`), nonnegative slopes with a gauge
   (`MaxAffine/GaugeHolonomy`), or all slopes below one with floors only. The library already
   proves the same phenomenon independently: `MaxAffine/Farkas` exhibits two loops at one
   vertex (x ↦ 10 and x ↦ 2x) where every closed walk has a pre-fixed point but no lax section
   exists, and replaces the cyclewise test with a Farkas certificate; `Closure` notes that one
   common pre-fixed witness at a root suffices where per-walk witnesses do not. This is the
   Shostak / Cohen–Megiddo path-plus-cycle certificate phenomenon. The library cites none of
   Pratt, Shostak, Aspvall–Shiloach, or Cohen–Megiddo; `MaxAffine/Sections`, `MaxAffine/Farkas`
   and `Closure` are the natural places. Shostak's closure is an alternative *cyclewise* complete
   test (after adding residue edges) to the library's linear one.

## Formalization roadmap

What the prior art suggests adding, sorted by effort. Items marked *done* are in the library.

### Done

- **Rotation invariance of holonomy** (Shostak, Lemma 6): `Maths.Transport.holonomy_append_rotate`,
  with fixed and, for monotone maps, pre-fixed versions. Holds for arbitrary edge maps, not only
  affine ones.
- **Lattice of lax sections** (Cohen–Megiddo, Prop. 4.1; Veinott): `IsLaxSection.inf` for
  monotone maps, `IsLaxSection.sup` for join-subadditive maps, `sup_of_linearOrder` on chains.
- **Composition of lax constraints** (Montanari, Thm 5.5, first half):
  `RelationTransport.mem_walkRelation_concat_ofSectionFor_le_iff`.
- **Path consistency without a section** (Montanari's tetrahedron):
  `Maths/Multitubes/RelationalCycles.lean`, the relational twin of `MaxAffine/Farkas`.
- **Citations** across the library for the classical specializations (Pratt, Shostak,
  Aspvall–Shiloach, Cohen–Megiddo, Hochbaum–Naor, Dechter–Meiri–Pearl, Montanari, Ladkin–Maddux,
  Jewell, Truemper, Tarski, Cousot–Cousot, Kildall, Ghrist–Riess, Karp, Bellman, Tarjan,
  Ford–Fulkerson, Euler, Hierholzer, Mac Lane, Gross, Harary, Farkas, Motzkin, Gale–Kuhn–Tucker,
  Helly, Schrijver).

### Moderate

- **Shostak's closure theorem.** A system is unsatisfiable iff its closure, with a residue edge per
  simple closed walk, has an infeasible simple closed walk. This is a *complete cyclewise* test, an
  alternative to the linear test of `MaxAffine/Farkas`. Needs edges of both slope signs (antitone
  maps) and simple-cycle enumeration; Section 7 of the paper is the proof to follow.
- **Projection theorem and Helly number two** (Cohen–Megiddo, Props 2.10 and 2.12). On a feasible
  two-variable system the per-variable intervals from simple paths and closed walks are the exact
  projections, and a box misses the polyhedron iff two of its bounds do. Sharpens
  `MaxAffine/Sparse` (Helly, `|V| + 1`) for bound queries.
- **Montanari's Theorem 5.7.** Monotone relations on complete lattices whose closed-walk relations
  contain the diagonal give a decomposable, minimal network. Should connect to the rooted closure
  of `Closure` and to `Mixed/Closure`.
- **Greatest lax sections by descending iteration** (Hochbaum–Naor). The dual of `Worklist`, with
  integer floors as non-invertible monotone maps.
- **Sections on a directed cycle graph** (Angeli–Sontag, Thm 3 in the two-vertex case). For
  arbitrary edge maps, sections correspond to fixed points of the holonomy at one vertex. Needs a
  cycle-graph construction.
- **Tarski Laplacian** (Ghrist–Riess). Lattice-valued sheaves with Galois-connection restrictions,
  whose Tarski Laplacian has the global sections as fixed points. The `CellularSheaves`
  application already embeds sheaves on graphs into transport; the Laplacian should be the
  Bellman operator of the laxification.
- **Least and greatest schedules** (Dechter–Meiri–Pearl, Thm 3.1). Check that both extremal
  potentials are stated, the greatest one through the reversed graph.

### Hard or out of scope

- **Spectral frustration**: Cheeger inequalities for connection and magnetic Laplacians
  (Bandeira–Singer–Spielman; Lange–Liu–Peyerimhoff–Post). Needs spectral theory of matrices
  over `O(d)` or `U(1)`.
- **Cycle consistency for partial maps** (Bernard et al.): consistency as a factorization through a
  universe. Relates to exact transport beyond groups, `Multitubes/Exact`.
- **Signed-graph monotonicity of ODEs** (Kunze–Siegel; Angeli–Sontag): the graph criterion is
  balance over `ℤˣ`, which the library has, but the dynamical side is outside its scope.
- **Consistency radius** (Robinson): a metric relaxation of sections; the library's quantitative
  residuals are the order-theoretic counterpart.
