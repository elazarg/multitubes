# Proof-mining `directed-transport`

Investigation note, 2026-08-24. Mathematical proof-mining of the library at HEAD
(`5d76ff7`): hypothesis strengthening, cross-specialization generalization, missing
connections, and absent theorems. Style and structure were out of scope (see
`Mathlibify.md`).

**Evidence classes used below, in decreasing strength:**

- **VERIFIED** — the claim was tested against the actual build: either the library was
  temporarily edited and rebuilt to zero errors and zero warnings, or a standalone Lean
  file elaborating against the built library was checked. Every verified artifact is
  reproduced in the appendix, so nothing depends on ephemeral scratch state.
  *Update: finding 1.1 has since been **applied to the library** (see 1.1 and Appendix
  A); the other findings remain proposals and the tree is otherwise at HEAD.*
- **INSPECTED** — the proof was read and the claim follows from what it does and does not
  use, but no build was run with the change.
- **SKETCH** — a paper argument exists; formalization was not attempted.
- **CONJECTURAL** — plausible, clearly labelled, with the evidence stated.

---

## 1. Strengthening

### 1.1 The tropical Farkas duality does not need any hypothesis on the vertex type — VERIFIED and APPLIED

`MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos`
(`Additive/Potentials.lean`) is stated with `[Fintype V] [Finite E]`. The `Fintype V`
can be **dropped entirely** — not merely weakened to `Finite V`. The point is
mathematical, not bureaucratic: the pruning lemma
`exists_nodup_visited_walkWeight_le` produces a walk whose *visited vertices* are
pairwise distinct, and such a walk also traverses pairwise distinct *edges* (two uses
of one edge would repeat its source vertex). So the length bound `≤ Fintype.card V`
used by `exists_bound_walkWeight` can be replaced by `≤ Fintype.card E`, and the rest
of the section never touches V-finiteness. Conceptually: with finitely many edges,
only finitely many vertices are non-isolated, and potentials are unconstrained
elsewhere — but the theorem needs no such preprocessing; the proof simply never needed
the vertex count.

Verified by editing and rebuilding the **whole library to zero errors and zero
warnings**. The full diff is in Appendix A. Declarations that shed a hypothesis:

| Declaration | Before | After |
| --- | --- | --- |
| `MaxPlusPotential.exists_bound_walkWeight` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxPlusPotential.bddAbove_incomingWeights` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxPlusPotential.maxIncomingWeight_isPotential` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxPlusPotential.exists_subeigenvector_iff_forall_closedWalk_le` | `[Fintype ι]` | `[Finite ι]` |
| `AdditiveTransport.worstDirectedResidualAtMost_iff_closedWalk_le` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `AdditiveTransport.worstDirectedResidualAtMost_iff_simpleCycles_le` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_shift_nonpos` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_exists_prefixed` | `[Fintype V] [Finite E]` | `[Finite E]` |
| `MaxAffineTransport.criticalAffineGaugeResidualAtMost_iff_closedWalk_mean_le` | section `[Fintype V]` | omitted |
| `MaxAffineTransport.criticalAffineGaugeResidualAtMost_iff_simpleCycle_mean_le` | section `[Fintype V]` | omitted |
| `MaxAffineTransport.criticalAffineResidualAtMost_iff_closedWalk_ratio_mul_le` | section `[Fintype V]` | omitted |
| `MaxAffineTransport.criticalAffineResidualAtMost_iff_cycleRatio_le` | section `[Fintype V]` | omitted |
| `MaxAffineTransport.exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos` | section `[Fintype V]` | omitted |

The five `GaugeFeasibility` entries were discovered *by the linter*: once the additive
duality lost `Fintype V`, the zero-warning discipline flagged them as carrying an
unused section variable — i.e. their only use of vertex-finiteness was feeding the
additive theorem. The unit-slope max-affine strong duality (mean-payoff feasibility)
therefore also holds on an arbitrary vertex type with finitely many edges.

Two new walk-calculus lemmas carry the argument, useful independently (they belong in
`EdgeGraph.lean` or next to `visited`):

- `mem_visited_of_mem_edges` — an edge used by a walk has its target among the
  visited vertices;
- `edges_nodup_of_visited_nodup` — a walk with pairwise-distinct visited vertices
  traverses pairwise-distinct edges.

**Sharpness — `[Finite E]` is provably necessary (VERIFIED).** Appendix B is a
counterexample checked against the library: `V = Bool`, `E = ℕ`, every edge `n` from
`false` to `true` with weight `n`. Closed walks are empty, so the cycle condition holds
vacuously, yet `φ false + n ≤ φ true` for all `n` is unsatisfiable. So after this
change both remaining hypotheses are exactly right.

**APPLIED (2026-08-24).** Landed in the five files of Appendix A, with proper
docstrings on the two new lemmas and the drifted docstrings reworded:

> Drop vertex-finiteness from the tropical Farkas duality; only `[Finite E]` remains.
> A walk pruned to distinct visited vertices also traverses distinct edges
> (`mem_visited_of_mem_edges`, `edges_nodup_of_visited_nodup`), so the pruned-walk
> bound is `card E`, not `card V`. Fourteen declarations shed a hypothesis:
> the duality and its Finite-section lemmas, the max-plus subeigenvector criterion
> (`Fintype ι` → `Finite ι`), the one-sided and simple-cycle residual thresholds,
> both unit-slope max-affine strong dualities, and five gauge-critical theorems
> (via `omit [Fintype V]`). Docstrings updated in `Potentials.lean` (title, intro,
> Main results, duality), `Cycles.lean` (Main results), and `Sections.lean`
> (strong-duality docstring). Verified: from-clean `lake build` at zero errors and
> zero warnings; changed declarations depend only on `propext`, `Classical.choice`,
> `Quot.sound`; docstring-name resolution re-checked for the five files.

**Follow-up move, also landed (2026-08-24):** the entire visited-vertex walk
calculus moved from `Additive/Potentials.lean` into
`DirectedTransport/EdgeGraph.lean`, namespace `DirectedTransport.EdgeGraph.Walk`, with
the rest of the finite-walk calculus: `visited`, `visited_nil`, `visited_concat`,
`length_visited`, `exists_split_of_mem_visited`, `exists_closedSubwalk_of_not_nodup`,
and the two new lemmas — all of it facts about walks, none about potentials, and none
of it dragging weights or any other potential-specific content into the foundation
file (no new imports were needed; `Mathlib.Data.List.Nodup` was already there).
`walk.visited` now works by dot notation. Call sites adjusted (no new `open`s) in
`Additive/Potentials.lean`, `Additive/CirculationDecomposition.lean`, and
`Additive/ShortCycles.lean`; `EdgeGraph.lean`'s module docstring advertises `visited`,
`edges_nodup_of_visited_nodup`, `exists_split_of_mem_visited`, and
`exists_closedSubwalk_of_not_nodup`, and `Potentials.lean`'s duality section points
back at them.

Not investigated: whether `Additive/ShortCycles.lean` can be repointed at
`Nat.card`/`Finite` — its statements mention `Fintype.card V` intrinsically, so any
change there alters statements, not just hypotheses.

### 1.2 The monoid unit-potential reconstruction needs only edge-endpoint linkage — VERIFIED

`DirectedTransport.exists_unitPotential_of_trivialCycleLabels` (`Exact.lean`) assumes
`IsStronglyConnectedAt G base`. The additive-group analogue
(`CycleCoboundary.exists_coboundary_of_baseCycleSums_eq_zero`) already gets by with the
strictly weaker `EdgeEndpointsLinkedTo G base` (only the endpoints of edges need to be
linked to the base; untouched vertices get the trivial potential). The same weakening
goes through for the monoid version: vertices not linked to `base` take potential `1`,
and the edge equation only ever consults linked vertices.

Verified by adding the weakened theorem to `Exact.lean` and building it cleanly (proof
in Appendix C; it compiled on first attempt, mirroring the existing proof with a `dite`
potential). **To act:** either weaken the existing theorem in place (call sites in
`PotentialRigidity.lean`/`NormalForms.lean` then pass
`hconnected.edgeEndpointsLinkedTo`) or add the general form and derive the strongly
connected one. Note the asymmetry that remains and is genuine: the additive-group
version needs zero sums only for cycles *at the base*, while the monoid version needs
global flatness — base-only flatness does not propagate in a general monoid (that is
exactly what `hasTrivialCycleLabels_of_base_of_dedekindFinite` adds Dedekind
finiteness for). A combined corollary — base-flat + Dedekind-finite +
`EdgeEndpointsLinkedTo` implies the unit potential — looks provable by the same
propagation argument restricted to edge endpoints (every vertex on a nonempty cycle is
an edge endpoint), but was **not** formalized: SKETCH.

### 1.3 Standard-form Farkas is algebraic; only the topology needs ℝ — VERIFIED and APPLIED

`LinearAlgebra/StandardForm.lean` states everything over `ℝ`. Reading the proofs splits
the file cleanly:

- `exists_isStandardCertificate_of_not_nonempty` /
  `not_nonempty_standardFeasibleSet_iff` / `nonempty_standardFeasibleSet_iff`
  (**Farkas' lemma**) reduce to `theorem_of_alternative` in `FourierMotzkin.lean` —
  which is already stated over an arbitrary linearly ordered field
  (`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`) — plus sum reshuffling and a
  division by the positive mass `t`. Nothing topological. These should generalize to
  the same `𝕜`.
- `isClosed_standardFeasibleSet`, `exists_extreme_standardOptimal_of_standardOptimal`
  (Krein–Milman route) genuinely use the topology and compactness of `ℝ` and should
  stay real.
- The extreme-point ⇔ basic-feasible-solution equivalence sits in between: the
  argument looks purely order-algebraic, but it leans on mathlib's convexity API whose
  generality over `𝕜` was not checked.

Not build-tested: doing it properly means splitting the file into an algebraic and a
topological section with different scalars, which is a restructuring, not a one-line
weakening.

### 1.4 The duality over an arbitrary linearly ordered field — APPLIED

With 1.1 in place, the only use of completeness of `ℝ` in
`exists_isPotential_iff_forall_closedWalk_nonpos` is `sSup (incomingWeights …)`. Since
`[Finite E]` bounds pruned walks by `card E`, the candidate potential can instead be
defined as a `Finset.max'` over the (finitely many) weights of nodup-edge walks into
each vertex, which makes the theorem meaningful over any `LinearOrderedField` — matching
the generality of `FourierMotzkin.lean`. Moderate effort (~80 lines: finiteness of
realizable nodup edge lists, attained max, rerun of the potential estimate). Internal
payoff is limited because `MaxAffine/Arithmetic.lean` already gets ℚ-feasibility
through the linear route; the value would be mathlib-facing.

---

## 2. Generalization

### 2.1 `Closure.lean` is an island: its two conditionally-complete shadows are proved by hand — analysis VERIFIED (by reference search), unification SKETCH

`Closure.lean` advertises itself as "the complete-lattice machinery for the lax side."
No file consumes it: `pathClosure`, `PathClosureSupSpec`, `bellman`,
`leastLaxMajorant`, and their theorems have zero references in the rest of the library
(they are exported terminal results, so this is not deadness — but the advertised role
is aspirational). Meanwhile the library contains **two hand-proved instances of exactly
its content in conditionally complete ℝ**, where `CompleteLattice` fails:

- `MaxPlusPotential.maxIncomingWeight` (`Additive/Potentials.lean`) is
  `pathClosure` for the translation transport with lower data `0`: the sup over all
  incoming walks of transported values. `maxIncomingWeight_isPotential` is
  `isLaxSection_pathClosure` re-proved with `csSup_le`/`le_csSup` under a `BddAbove`
  hypothesis supplied by `exists_bound_walkWeight`.
- `ChargedPathBudget.ChargedRelation.value` (`ChargedRelation.lean`) is the same
  construction on the reversed orientation; `isLeast_value` ("least nonnegative
  supersolution") is `pathClosure_isLeast`, again via `csSup` and an explicit budget
  bound.

The missing generic result: a **conditionally complete path-closure theorem** — for
monotone edge maps that commute with `csSup` on nonempty bounded-above sets
(translations do), and a hypothesis that the transported set at each vertex is bounded
above, the walk-closure is the least lax section above the lower data. Both instances
would follow, and `Closure.lean` would earn its role. Alternative cheaper route:
instantiate `Closure.lean` at `EReal`- or `WithBot (WithTop ℝ)`-valued fibers and
derive the ℝ statements by a boundedness transfer. Either is real work (the
`fiberCast` plumbing is the tedious part); nothing was formalized.

The same island pattern, weaker form: `JoinSemidirect.lean`'s `SupBotMulAction` is
consumed only by its own max-affine adapter (`MaxAffine/JoinSemidirect.lean`), whose
monoid isomorphism `labelMulEquiv` is never used to transport a theorem. Both adapters
say they are adapters; still, no result currently crosses either bridge (see 3.3 for
the categorical twin of this observation, where the bridge *does* carry a theorem and
was tested).

### 2.2 `walkWeight` / `walkSum` / `walkLabel` triplication — minor, already bridged

`MaxPlusPotential.walkWeight` (ℝ), `CycleCoboundary.walkSum` (`AddCommMonoid`), and
`DirectedTransport.walkLabel` (`Monoid`) are three copies of one fold;
`walkWeight_eq_walkSum` is `rfl` and `walkLabel_ofAdd` bridges the third. Folding
`walkWeight` into `walkSum` is a deduplication, not new mathematics; the `@[simp]`
lemma sets are already parallel. Low value; noted for completeness.

---

## 3. Missing connections

### 3.1 The max-plus spectral radius theorem is derivable but absent — VERIFIED and APPLIED

`Additive/Potentials.lean` ends with the subeigenvector criterion
(`exists_subeigenvector_iff_forall_closedWalk_le`) and its Scope note says the
Collatz–Wielandt/attainment side is "not developed here."
`Additive/ShortCycles.lean` proves max-cycle-mean **attainment**
(`exists_short_closedWalk_maximizing_mean`). Nobody composes them — the matrix reading
is referenced nowhere outside its own file. The composite is the max-plus
Perron-root theorem, and it is a ~45-line assembly (Appendix D, checked against the
built library):

> For `[Fintype ι] [Nonempty ι]` and `A : ι → ι → ℝ`, there is a cycle of
> `matrixGraph ι` of length ≤ `card ι` such that for every `lam`, a subeigenvector for
> `lam` exists **iff** that cycle's mean is ≤ `lam`.

So the admissible set is a closed ray and its left endpoint — the max cycle mean, the
tropical spectral radius — is attained on a short cycle. This is the natural headline
for the `Matrix` section of `Potentials.lean` and costs nothing beyond what is already
in the library. (Reference: Baccelli–Cohen–Olsder–Quadrat, *Synchronization and
Linearity*, Ch. 3; the eigen*vector* existence and the critical graph remain genuinely
absent, see 4.2.)

### 3.2 Gordan's transposition theorem is a corollary of `theorem_of_alternative` — APPLIED; the other classical variants are within reach

No Gordan/Stiemke/Ville/Motzkin transposition variant is stated anywhere. Gordan is a
~60-line corollary of `theorem_of_alternative` at `b = 1`, over the same ordered-field
generality (Appendix E, checked): `∃ x, A x > 0` iff there is no nonzero nonnegative
`u` with `uᵀA = 0`. The homogenization trick (`Ax ≥ 1` solvable ⇔ `Ax > 0` solvable;
the Farkas certificate for `b = 1` is precisely a nonzero balanced `u`) is exactly what
the proof does.

Not attempted, but same shape (SKETCH): **Stiemke** (`∃ x, Ax ≥ 0, Ax ≠ 0` vs strictly
positive balanced `u`) and **Motzkin's transposition** (mixed strict/weak rows) via
block right-hand sides `(1, 0)`. **Ville** is Gordan transposed. If `FourierMotzkin.lean`
is a mathlib candidate, these four names are what reviewers will look for first.

### 3.3 The categorical dictionary is sound but never used: the two retract developments are defeq-equal — APPLIED

The library proves the retract normal form twice: concretely
(`Transport.compressed_walkMap_eq` and friends, `Exact.lean`) and categorically
(`categorical_compressed_map_eq` and friends, `CategoricalRetracts.lean`), with
`Category.lean` holding the dictionary (`Transport.toPathFunctor`) that is used by
neither. Appendix F verifies, against the built library:

- the missing bridge lemma `isFlatAt_toPathFunctor_iff` — one-base flatness of a
  transport is `IsFlatAt` of its path functor — is 10 lines; and
- `compressed_walkMap_eq` **is literally an instance** of
  `categorical_compressed_map_eq` at `T.toPathFunctor`: after
  `ConcreteCategory.congr_hom`, `exact` closes both directions *by definitional
  equality* — no rewriting needed.

Two readings, both defensible: (a) deduplicate — derive the `Exact.lean` retract
section from the categorical one (but then `Exact.lean` imports category theory, which
its current layering deliberately avoids); or (b) keep both and **state the bridge** —
add `isFlatAt_toPathFunctor_iff` and a `compressed_walkMap_eq_via_category`-style
lemma to `Category.lean`/`CategoricalRetractAdapter.lean`, which documents that the
dictionary is exact and costs ~25 lines. (b) preserves the layering and is what the
verification actually built. Until one of these lands, the honest description of
`Category.lean`'s `toPathFunctor` half is: decorative.

### 3.4 Connections that were checked and found already present

For the next miner: these leads from the module docstrings are *not* gaps.

- The mean-payoff/Bellman–Ford reading **is** wired into max-affine:
  `exists_isPotential_iff_forall_closedWalk_nonpos` is consumed at nine sites across
  `MaxAffine/{Sections,Slopes,GaugeFeasibility}.lean`; the unit-slope strong duality
  lifts it by the add-a-constant argument, and the gauge theorems reduce to it on the
  critical subgraph.
- `Circulation.lean`'s balance lemma (`edgeMultiplicity_balanced`) is consumed by
  `Additive/Circuits.lean` (`circuitCoefficient_isNormalizedCertificate`).
- The symmetric additive dual is bridged to `FiniteInequality` by
  `symmetricResidualAtMost_iff_finiteInequality`, and `Additive/Exact.lean`'s
  `ChargedBridge` section links the coboundary world to `ChargedRelation`'s decrement
  convention. The additive ⇄ max-affine translation bridge is
  `MaxAffine/Additive.lean`.

---

## 4. New theorems

### 4.1 Switching and balance for gain graphs — APPLIED

`Basic.lean` and `Exact.lean` cite Zaslavsky's gain graphs and prove
balance-as-unit-potential, but the *switching* half of that theory — the group
`M^V` acting on gain functions, switching classes, and balance as
switching-triviality (Zaslavsky, *Biased graphs. I*, JCTB 47 (1989), §5) — is absent.
It formalizes in under 100 lines on the existing API; Appendix G is a checked
prototype containing:

- `switch G η label : E → M` (`η (target e) * label e * (η (source e))⁻¹`);
- `walkLabel_switch` — walk labels transform by endpoint correction;
- `switch_switch`, `switch_one` — a genuine `M^V`-action;
- `hasTrivialCycleLabels_switch_iff` — **balance is a switching invariant**;
- `hasTrivialCycleLabels_iff_exists_switch_one` — on a strongly connected graph,
  balance ⇔ the gain is a switching of the trivial gain, where the switching function
  is exactly the unit potential of `exists_unitPotential_of_trivialCycleLabels`.

With 1.2, the last item's hypothesis weakens to `EdgeEndpointsLinkedTo` (not tested
together). Natural home: a short `Switching.lean` next to `NormalForms.lean`. The
genuinely new-to-the-literature edge of the library's setting — labels in a monoid, so
switching only by *unit-valued* `η` — is a remark worth making in the docstring:
`PotentialRigidity.lean`'s torsor theorem says precisely that the switching functions
trivializing a flat monoid gain form an `Mˣ`-torsor.

### 4.2 Karp's formula and the max-plus eigenproblem — APPLIED (both halves)

Named in `Potentials.lean`'s own Scope note; recorded here with what each would take.

- **Karp's minimum(-here-maximum) mean cycle formula** (Karp, *A characterization of
  the minimum cycle mean in a digraph*, Discrete Math. 23 (1978)): the max cycle mean
  equals `max_v min_{0≤k<n} (D_n(v) − D_k(v))/(n−k)` where `D_k` are `k`-step
  Bellman values. Needs the `k`-step value table (the library only has the
  all-walks supremum `maxIncomingWeight`), so it is a new induction, not an assembly:
  moderate effort. With 3.1 in place its statement can be phrased against the same
  attained threshold.
- **Max-plus eigenvector existence** (irreducible case: `A ⊗ v = lam ⊗ v` with
  `lam` the max cycle mean) and the critical graph. This is the real missing half of
  the spectral theory; the natural route in this library is the unit-slope
  (`topical`) specialization of `MaxAffine`, per the Scope notes' own pointer to
  Gaubert–Gunawardena. Large effort.

### 4.3 LP strong duality and complementary slackness — APPLIED

`LinearAlgebra/StandardForm.lean` stops at Farkas + basic feasible solutions +
attainment at an extreme point. The two theorems any reader will expect next:

- **Strong duality** for `max ⟨c,z⟩ s.t. z ∈ standardFeasibleSet A rhs` against
  `min ⟨rhs,y⟩ s.t. Aᵀy ≥ c`: derivable from `theorem_of_alternative` by the standard
  two-certificate argument; the threshold machinery in
  `FiniteInequality/Quantitative.lean` (`worstResidualAtMost_iff_normalizedDual_le`)
  is a sibling and suggests the level-by-level phrasing that avoids naming an
  extended-real optimum. Moderate effort.
- **Complementary slackness**: cheap once duality is stated; pairs naturally with
  `mem_extremePoints_standardFeasibleSet_iff`.

Note the library-wide pattern: every duality here is stated as an exact *threshold*
equivalence rather than an optimum equality. LP strong duality in that house style
would be: `∀ t, (∃ feasible z, ⟨c,z⟩ ≥ t) ↔ (∀ dual-feasible y, ⟨rhs,y⟩ ≥ t)` — which
sidesteps attainment and matches `MaxAffine/Duality.lean`'s
`worstResidualAtMost_iff_normalizedDual_le` exactly.

### 4.4 Condensation-based decomposition of lax feasibility — APPLIED

`SCC.lean` proves the condensation acyclic and `NormalForms.lean` gives the
componentwise normal form for the *exact* case
(`hasTrivialCycleLabels_iff_hasSCCUnitPotentials`). The lax additive analogue is
absent: a potential for `(G, w)` exists iff a potential exists on each strongly
connected component's induced subgraph — the cycle test is intrinsically per-SCC, and
the DAG stitching argument (topologically order the finitely many components, shift
each component's potential by a large constant) is standard. With 1.1, `Finite E`
suffices (only finitely many components are non-isolated). Moderate effort; the
payoff is an algorithmically meaningful preprocessing statement to sit beside
`worstDirectedResidualAtMost_iff_simpleCycles_le`.

### 4.5 CONJECTURE: bicycle-sparse certificates for mixed-slope infeasibility

`MaxAffine/Farkas.lean` proves the mixed-slope duality (lax section iff no nonnegative
balanced certificate) and its Scope note observes the certificate is a generalized-flow
object; `MaxAffine/Sparse.lean` bounds certificate support by `card V + 1` via Helly.
The generalized-flow literature suggests a *graph-shaped* sharpening: extreme
certificates should be supported on a **bicycle** (two cycles joined by a path, one
with slope product < 1 and one with slope product > 1) or a single unit-product
cycle — the analogue of `worstDirectedResidualAtMost_iff_simpleCycles_le` one level
up. Evidence: (i) extreme points of generalized-flow polyhedra are supported on
augmented forests with one cycle per component (Goldberg–Plotkin–Tardos, *Combinatorial
algorithms for the generalized circulation problem*, Math. OR 16 (1991)); (ii) the
library's own `Farkas.lean` counterexample (reset loop + doubling loop at one vertex)
is exactly a two-cycle support; (iii) the balance condition at each vertex is a flow
conservation with gain, so the support of a minimal certificate is a minimal
gain-graph dependency, and minimal dependencies of gain-graphic matroids are known to
be bicycles (Zaslavsky, *Biased graphs. II*). **No Lean evidence and no
counterexample search was done**; the statement also needs care about which of the
`E ⊕ E` branch rows (floor vs affine) may appear on the support. Treat strictly as a
conjecture; if true it upgrades `card V + 1` sparsity to a structural description.

---

## 5. Checked and ruled out

So the next miner does not redo these:

- **`hmono` in `pathClosure_isLeast` is not redundant** given `PathClosureSupSpec`.
  The spec only asserts sup-preservation for `V`-indexed and walk-indexed families;
  on `V = {a, b}` with a single edge `a → b`, both index families at the relevant
  vertices are subsingletons, so the spec degenerates to `map_bot` plus trivialities
  and a non-monotone bot-preserving edge map satisfies it. (Paper argument; not
  formalized.)
- **`[DecidableEq V]` on `Closure.rootedLower`** could be discharged with
  `Classical.dec`, but the def is data and mathlib convention keeps instance-based
  decidability in data definitions; not a mathematical weakening. Left alone.
- **The `[Fintype V] [DecidableEq V] [Fintype E]` blocks on
  `MaxAffine/{Duality,Farkas,Slopes,Sparse}.lean` and
  `FiniteInequality/*.lean`** are load-bearing in the *statements* (`dotProduct`,
  `Finset.univ` sums, indicator rows need them), not just the proofs. No test
  performed beyond reading the statements; the prior Phase-3 audit's four removal
  tests (all load-bearing) stand.
- **`Nonempty E` in `Additive/CirculationDecomposition.lean`** is documented in the
  module docstring (the canonical lift parks unused `l1` mass on an edge) and was not
  challenged.
- **The Bellman–Ford / gauge connections listed in 3.4** — checked present, not gaps.
- **`Additive/Exact.lean` vs `Exact.lean` reconstruction**: neither subsumes the
  other (additive-group version has weaker hypotheses, monoid version has more general
  algebra); the honest unification is 1.2 plus the sketched Dedekind-finite corollary,
  not a merge.

---

## Appendix A — diff for finding 1.1 (LANDED; kept here as the record of the change)

*Post-landing note: the first hunk below shows the two walk lemmas being added to
`Additive/Potentials.lean`, where they were first verified. A follow-up commit moved
them — together with `visited`, `visited_nil`, `visited_concat`, `length_visited` —
into `DirectedTransport/EdgeGraph.lean` under `DirectedTransport.EdgeGraph.Walk`,
stated in dot-notation form, and adjusted the call sites in `Potentials.lean`,
`CirculationDecomposition.lean`, and `ShortCycles.lean`. The mathematical content is
unchanged.*

```diff
--- a/DirectedTransport/Additive/Potentials.lean
+++ b/DirectedTransport/Additive/Potentials.lean
@@ (general section, after exists_closedSubwalk_of_not_nodup)
+/-- An edge used by a walk has its target among the walk's visited vertices. -/
+theorem mem_visited_of_mem_edges {start finish : V} (walk : G.Walk start finish)
+    {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ visited walk := by
+  induction walk with
+  | nil => simp [EdgeGraph.Walk.edges_nil] at hmem
+  | concat walkSoFar e legal ih =>
+      rw [EdgeGraph.Walk.edges_concat, List.mem_append, List.mem_singleton] at hmem
+      rw [visited_concat]
+      rcases hmem with hmem | rfl
+      · exact List.mem_append_left _ (ih hmem)
+      · exact List.mem_append_right _ (List.mem_singleton_self _)
+
+/-- A walk whose visited vertices are pairwise distinct traverses pairwise
+distinct edges: a repeated edge would revisit its target vertex.  This is what
+lets walk bounds below count edges rather than vertices, so the duality needs
+no hypothesis on the vertex type. -/
+theorem edges_nodup_of_visited_nodup {start finish : V} (walk : G.Walk start finish)
+    (hnd : (visited walk).Nodup) : walk.edges.Nodup := by
+  induction walk with
+  | nil => simp
+  | concat walkSoFar e legal ih =>
+      rw [visited_concat, List.nodup_append] at hnd
+      obtain ⟨hvisited, -, hdisjoint⟩ := hnd
+      rw [EdgeGraph.Walk.edges_concat, List.nodup_append]
+      refine ⟨ih hvisited, List.nodup_singleton _, ?_⟩
+      intro a ha b hb
+      rw [List.mem_singleton] at hb
+      subst hb
+      rintro rfl
+      exact hdisjoint (G.target a) (mem_visited_of_mem_edges walkSoFar ha)
+        (G.target a) (List.mem_singleton_self _) rfl
@@
 section Finite

-variable [Fintype V] [Finite E]
+variable [Finite E]
@@ theorem exists_bound_walkWeight
+  cases nonempty_fintype E
   obtain ⟨cap, hcap⟩ := Finite.exists_le weight
-  refine ⟨Fintype.card V * max cap 0, ?_⟩
+  refine ⟨Fintype.card E * max cap 0, ?_⟩
   intro start finish walk
   obtain ⟨pruned, hnd, hle⟩ :=
     exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
   refine hle.trans ?_
-  have hlen : pruned.length ≤ Fintype.card V := by
-    have hcard := hnd.length_le_card
-    rw [length_visited] at hcard
-    omega
+  have hlen : pruned.length ≤ Fintype.card E := by
+    have hcard := (edges_nodup_of_visited_nodup pruned hnd).length_le_card
+    rwa [EdgeGraph.Walk.edges_length] at hcard
@@
-theorem exists_subeigenvector_iff_forall_closedWalk_le [Fintype ι]
+theorem exists_subeigenvector_iff_forall_closedWalk_le [Finite ι]
--- a/DirectedTransport/Additive/Quantitative.lean
+++ b/DirectedTransport/Additive/Quantitative.lean
@@
 theorem worstDirectedResidualAtMost_iff_closedWalk_le
-    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
+    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
--- a/DirectedTransport/Additive/Cycles.lean
+++ b/DirectedTransport/Additive/Cycles.lean
@@
 theorem worstDirectedResidualAtMost_iff_simpleCycles_le
-    [Fintype V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
+    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
--- a/DirectedTransport/MaxAffine/Sections.lean
+++ b/DirectedTransport/MaxAffine/Sections.lean
@@
-theorem exists_isLaxSection_iff_forall_cycle_shift_nonpos [Fintype V] [Finite E]
+theorem exists_isLaxSection_iff_forall_cycle_shift_nonpos [Finite E]
@@
-theorem exists_isLaxSection_iff_forall_cycle_exists_prefixed [Fintype V] [Finite E]
+theorem exists_isLaxSection_iff_forall_cycle_exists_prefixed [Finite E]
--- a/DirectedTransport/MaxAffine/GaugeFeasibility.lean
+++ b/DirectedTransport/MaxAffine/GaugeFeasibility.lean
@@ (five sites, before criticalAffineGaugeResidualAtMost_iff_closedWalk_mean_le,
   criticalAffineGaugeResidualAtMost_iff_simpleCycle_mean_le,
   criticalAffineResidualAtMost_iff_closedWalk_ratio_mul_le,
   criticalAffineResidualAtMost_iff_cycleRatio_le,
   exists_criticalAffinePotential_iff_gaugeCriticalCycles_nonpos)
-omit [DecidableEq V] in
+omit [Fintype V] [DecidableEq V] in
```

## Appendix B — `[Finite E]` necessity counterexample (elaborates clean against the library)

```lean
import DirectedTransport.Additive.Potentials
import Mathlib.Tactic.Linarith

namespace MiningScratch

open DirectedTransport DirectedTransport.MaxPlusPotential

/-- Two vertices, edge `n` from `false` to `true` with weight `n`. -/
def badGraph : EdgeGraph Bool ℕ where
  source := fun _ => false
  target := fun _ => true

/-- Every nonempty walk of `badGraph` goes from `false` to `true`. -/
theorem badGraph_walk_endpoints :
    ∀ {s f : Bool} (walk : badGraph.Walk s f),
      0 < walk.length → s = false ∧ f = true
  | _, _, .nil => by simp
  | _, _, .concat .nil edge legal => fun _ => ⟨legal.symm, rfl⟩
  | _, _, .concat (.concat inner e' legal') edge legal => fun _ => by
      obtain ⟨hs, -⟩ :=
        badGraph_walk_endpoints (inner.concat e' legal') (by simp)
      exact ⟨hs, rfl⟩
termination_by s f walk => walk.length
decreasing_by
  show inner.length + 1 < inner.length + 1 + 1
  omega

/-- Closed walks of `badGraph` are empty. -/
theorem badGraph_closed_length {v : Bool} (cycle : badGraph.Walk v v) :
    cycle.length = 0 := by
  by_contra hne
  obtain ⟨hs, hf⟩ :=
    badGraph_walk_endpoints cycle (Nat.pos_of_ne_zero hne)
  rw [hs] at hf
  exact Bool.noConfusion hf

/-- The vacuous cycle condition holds. -/
theorem badGraph_cycles_nonpos :
    ∀ (v : Bool) (cycle : badGraph.Walk v v),
      walkWeight (fun n : ℕ => (n : ℝ)) cycle ≤ 0 := by
  intro v cycle
  have hlen := badGraph_closed_length cycle
  have hlen' := cycle.edges_length
  rw [hlen] at hlen'
  rw [walkWeight, List.length_eq_zero_iff.mp hlen']
  simp

/-- No potential exists. -/
theorem badGraph_no_potential :
    ¬ ∃ φ : Bool → ℝ, IsPotential badGraph (fun n : ℕ => (n : ℝ)) φ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (φ true - φ false)
  have hedge := hφ n
  have hsource : badGraph.source n = false := rfl
  have htarget : badGraph.target n = true := rfl
  rw [hsource, htarget] at hedge
  linarith

/-- **`[Finite E]` is necessary**: the duality fails for this graph. -/
theorem finiteE_necessary :
    ¬ ((∃ φ : Bool → ℝ, IsPotential badGraph (fun n : ℕ => (n : ℝ)) φ) ↔
      ∀ (v : Bool) (cycle : badGraph.Walk v v),
        walkWeight (fun n : ℕ => (n : ℝ)) cycle ≤ 0) := by
  intro h
  exact badGraph_no_potential (h.mpr badGraph_cycles_nonpos)

end MiningScratch
```

## Appendix C — finding 1.2 (built clean when temporarily added to `Exact.lean`)

```lean
theorem exists_unitPotential_of_trivialCycleLabels' {base : V}
    (hlinked : EdgeEndpointsLinkedTo G base)
    (hflat : HasTrivialCycleLabels G label) :
    ∃ potential : V → Mˣ, ∀ edge : E,
      label edge =
        (potential (G.target edge) * (potential (G.source edge))⁻¹ : Mˣ) := by
  classical
  let potential : V → Mˣ := fun vertex ↦
    if h : LinkedTo G base vertex then
      { val := walkLabel label h.1.some
        inv := walkLabel label h.2.some
        val_inv := by simpa using hflat vertex (h.2.some.append h.1.some)
        inv_val := by simpa using hflat base (h.1.some.append h.2.some) }
    else 1
  refine ⟨potential, fun edge ↦ ?_⟩
  obtain ⟨hsourceLinked, htargetLinked⟩ := hlinked edge
  have hsource : potential (G.source edge) =
      { val := walkLabel label hsourceLinked.1.some
        inv := walkLabel label hsourceLinked.2.some
        val_inv := by
          simpa using hflat (G.source edge)
            (hsourceLinked.2.some.append hsourceLinked.1.some)
        inv_val := by
          simpa using hflat base
            (hsourceLinked.1.some.append hsourceLinked.2.some) } := by
    simp only [potential, dif_pos hsourceLinked]
  have htarget : potential (G.target edge) =
      { val := walkLabel label htargetLinked.1.some
        inv := walkLabel label htargetLinked.2.some
        val_inv := by
          simpa using hflat (G.target edge)
            (htargetLinked.2.some.append htargetLinked.1.some)
        inv_val := by
          simpa using hflat base
            (htargetLinked.1.some.append htargetLinked.2.some) } := by
    simp only [potential, dif_pos htargetLinked]
  rw [hsource, htarget]
  have hparallel := walkLabel_eq_of_trivialCycleLabels_of_return hflat
    (hsourceLinked.1.some.concat edge rfl) htargetLinked.1.some
    htargetLinked.2.some
  simp only [walkLabel_concat] at hparallel
  have hpathReturn : walkLabel label hsourceLinked.1.some *
      walkLabel label hsourceLinked.2.some = 1 := by
    simpa using hflat (G.source edge)
      (hsourceLinked.2.some.append hsourceLinked.1.some)
  change label edge = walkLabel label htargetLinked.1.some *
    walkLabel label hsourceLinked.2.some
  calc
    label edge = label edge *
        (walkLabel label hsourceLinked.1.some *
          walkLabel label hsourceLinked.2.some) := by rw [hpathReturn, mul_one]
    _ = (label edge * walkLabel label hsourceLinked.1.some) *
        walkLabel label hsourceLinked.2.some := by rw [mul_assoc]
    _ = walkLabel label htargetLinked.1.some *
        walkLabel label hsourceLinked.2.some := by rw [hparallel]
```

## Appendix D — finding 3.1 (elaborates clean against the library)

```lean
import DirectedTransport.Additive.Potentials
import DirectedTransport.Additive.ShortCycles
import Mathlib.Tactic.Linarith

namespace MiningScratch

open DirectedTransport DirectedTransport.MaxPlusPotential

/-- **Max-plus Perron root, assembled.**  For a real matrix over a nonempty finite
index type, some cycle of the matrix graph of length at most `card ι` is an exact
threshold: a subeigenvector for `lam` exists precisely when that cycle's mean weight
is at most `lam`. -/
theorem exists_critical_cycle_subeigenvector_iff
    {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → ι → ℝ) :
    ∃ (i : ι) (best : (matrixGraph ι).Walk i i),
      0 < best.length ∧ best.length ≤ Fintype.card ι ∧
        ∀ lam : ℝ,
          ((∃ v : ι → ℝ, IsSubeigenvector A lam v) ↔
            walkWeight (matrixWeight A) best ≤ best.length * lam) := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hexists : ∃ (vertex : ι) (cycle : (matrixGraph ι).Walk vertex vertex),
      0 < cycle.length := by
    refine ⟨i, ((EdgeGraph.Walk.nil : (matrixGraph ι).Walk i i).concat (i, i)
      (matrixGraph_source _)).castFinish (matrixGraph_target _), ?_⟩
    rw [EdgeGraph.Walk.length_castFinish, EdgeGraph.Walk.length_concat]
    exact Nat.succ_pos _
  obtain ⟨vertex, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean
      (matrixGraph ι) (matrixWeight A) hexists
  have hbestLenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  refine ⟨vertex, best, hpos, hcard, fun lam => ?_⟩
  constructor
  · intro hv
    exact (exists_subeigenvector_iff_forall_closedWalk_le A lam).mp hv vertex best
  · intro hbest
    refine (exists_subeigenvector_iff_forall_closedWalk_le A lam).mpr ?_
    intro j cycle
    rcases Nat.eq_zero_or_pos cycle.length with hzero | hposCycle
    · have hlen := cycle.edges_length
      rw [hzero] at hlen
      have hedges : cycle.edges = [] := List.length_eq_zero_iff.mp hlen
      simp [MaxPlusPotential.walkWeight, hedges, hzero]
    · have hlenPos : (0 : ℝ) < cycle.length := by exact_mod_cast hposCycle
      have hmean := hmax j cycle hposCycle
      have hbestMean :
          walkWeight (matrixWeight A) best / best.length ≤ lam := by
        rw [div_le_iff₀ hbestLenPos]
        linarith [hbest]
      have hcycleMean := hmean.trans hbestMean
      rw [div_le_iff₀ hlenPos] at hcycleMean
      linarith [hcycleMean]

end MiningScratch
```

## Appendix E — finding 3.2, Gordan (elaborates clean against the library)

```lean
import DirectedTransport.LinearAlgebra.FourierMotzkin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace MiningScratch

open DirectedTransport.LinearAlgebra Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Gordan's theorem.**  Exactly one of the following holds: some `x` makes
every row strictly positive, or some nonzero nonnegative `u` balances the
columns of `A`. -/
theorem gordan {I : Type*} [Fintype I] {n : ℕ} (A : I → Fin n → 𝕜) :
    (∃ x : Fin n → 𝕜, ∀ i, 0 < rowEval A i x) ↔
      ¬ ∃ u : I → 𝕜, (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * A i j = 0) ∧ u ≠ 0 := by
  classical
  have halt := theorem_of_alternative A (fun _ : I => (1 : 𝕜))
  constructor
  · rintro ⟨x, hx⟩ ⟨u, hnonneg, hbalance, hne⟩
    have hzero : ∑ i, u i * rowEval A i x = 0 := by
      have hswap : ∑ i, u i * rowEval A i x
          = ∑ j, (∑ i, u i * A i j) * x j := by
        simp only [rowEval, mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hswap]
      simp [hbalance]
    have hpos : ∃ i, 0 < u i := by
      by_contra hall
      push Not at hall
      apply hne
      funext i
      exact le_antisymm (hall i) (hnonneg i)
    obtain ⟨i₀, hi₀⟩ := hpos
    have hlt : 0 < ∑ i, u i * rowEval A i x := by
      refine Finset.sum_pos' (fun i _ => mul_nonneg (hnonneg i) (hx i).le) ?_
      exact ⟨i₀, Finset.mem_univ i₀, mul_pos hi₀ (hx i₀)⟩
    rw [hzero] at hlt
    exact lt_irrefl 0 hlt
  · intro hnocert
    have hnofarkas : ¬ HasCertificate A (fun _ : I => (1 : 𝕜)) := by
      rintro ⟨u, hnonneg, hbalance, hposmass⟩
      refine hnocert ⟨u, hnonneg, hbalance, ?_⟩
      intro hzero
      rw [hzero] at hposmass
      simp at hposmass
    have hfeas : IsFeasible A (fun _ : I => (1 : 𝕜)) := by
      by_contra hinf
      exact hnofarkas (halt.mp hinf)
    obtain ⟨x, hx⟩ := hfeas
    exact ⟨x, fun i => lt_of_lt_of_le one_pos (hx i)⟩

end MiningScratch
```

## Appendix F — finding 3.3, the retract bridge (elaborates clean against the library)

```lean
import DirectedTransport.Exact
import DirectedTransport.CategoricalRetracts

namespace MiningScratch

open DirectedTransport CategoryTheory

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {Fiber : V → Type uF}
variable (T : Transport G Fiber) {base : V}

/-- One-base flatness of a transport is flatness of its path functor. -/
theorem isFlatAt_toPathFunctor_iff :
    IsFlatAt T.toPathFunctor base ↔
      ∀ cycle : G.Walk base base, T.holonomy cycle = id := by
  constructor
  · intro hflat cycle
    funext point
    have h := ConcreteCategory.congr_hom (hflat cycle) point
    exact h
  · intro hbaseFlat cycle
    ext point
    have h := congrFun (hbaseFlat cycle) point
    exact h

/-- `Transport.compressed_walkMap_eq`, rederived from the categorical retract
theorem through the path-functor dictionary.  Both `exact`s close by
definitional equality: the concrete theorem is literally an instance. -/
theorem compressed_walkMap_eq_via_category
    (ingress : ∀ vertex, G.Walk base vertex)
    (returns : ∀ vertex, G.Walk vertex base)
    (hbaseFlat : ∀ cycle : G.Walk base base, T.holonomy cycle = id)
    {start finish : V} (walk : G.Walk start finish) :
    T.retractProjector ingress returns finish ∘ T.walkMap walk ∘
        T.retractProjector ingress returns start =
      T.ingressMap ingress finish ∘ T.returnMap returns start := by
  have hflat : IsFlatAt T.toPathFunctor base :=
    (isFlatAt_toPathFunctor_iff T).mpr hbaseFlat
  have h := categorical_compressed_map_eq T.toPathFunctor hflat
    ingress returns walk
  funext point
  have hpoint := ConcreteCategory.congr_hom h point
  exact hpoint

end MiningScratch
```

## Appendix G — finding 4.1, switching prototype (elaborates clean against the library)

```lean
import DirectedTransport.Exact
import Mathlib.Tactic.Group

namespace MiningScratch

open DirectedTransport DirectedTransport.CycleCoboundary

universe uV uE uM

variable {V : Type uV} {E : Type uE} {M : Type uM} [Group M] {G : EdgeGraph V E}

/-- Switching a group-valued gain by a vertex function `η`. -/
def switch (G : EdgeGraph V E) (η : V → M) (label : E → M) : E → M :=
  fun e => η (G.target e) * label e * (η (G.source e))⁻¹

/-- Switching acts on walk labels by endpoint correction. -/
theorem walkLabel_switch (η : V → M) (label : E → M) {start finish : V}
    (walk : G.Walk start finish) :
    walkLabel (switch G η label) walk =
      η finish * walkLabel label walk * (η start)⁻¹ := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkLabel_concat, ih, walkLabel_concat, switch, legal]
      group

/-- Switching composes: switching by `θ` after `η` is switching by `θ * η`. -/
theorem switch_switch (θ η : V → M) (label : E → M) :
    switch G θ (switch G η label) = switch G (fun v => θ v * η v) label := by
  funext e
  simp only [switch]
  group

/-- Switching by the constant one is the identity. -/
theorem switch_one (label : E → M) : switch G (fun _ => 1) label = label := by
  funext e
  simp [switch]

/-- **Balance is a switching invariant.** -/
theorem hasTrivialCycleLabels_switch_iff (η : V → M) (label : E → M) :
    HasTrivialCycleLabels G (switch G η label) ↔
      HasTrivialCycleLabels G label := by
  constructor <;> intro h vertex cycle
  · have hswitched := h vertex cycle
    rw [walkLabel_switch] at hswitched
    calc walkLabel label cycle
        = (η vertex)⁻¹ *
            (η vertex * walkLabel label cycle * (η vertex)⁻¹) * η vertex := by
          group
      _ = (η vertex)⁻¹ * 1 * η vertex := by rw [hswitched]
      _ = 1 := by group
  · rw [walkLabel_switch, h vertex cycle]
    group

/-- The trivial gain gives every walk the trivial label. -/
theorem walkLabel_one {start finish : V} (walk : G.Walk start finish) :
    walkLabel (fun _ : E => (1 : M)) walk = 1 := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih => rw [walkLabel_concat, ih, mul_one]

/-- The trivial gain is balanced. -/
theorem hasTrivialCycleLabels_one :
    HasTrivialCycleLabels G (fun _ : E => (1 : M)) :=
  fun _ cycle => walkLabel_one cycle

/-- **Balance is switching-triviality.**  On a strongly connected graph a
group-valued gain is balanced exactly when it is a switching of the trivial
gain. -/
theorem hasTrivialCycleLabels_iff_exists_switch_one {base : V}
    (hconnected : IsStronglyConnectedAt G base) (label : E → M) :
    HasTrivialCycleLabels G label ↔
      ∃ η : V → M, label = switch G η (fun _ => 1) := by
  constructor
  · intro hflat
    obtain ⟨potential, hpotential⟩ :=
      exists_unitPotential_of_trivialCycleLabels hconnected hflat
    refine ⟨fun v => (potential v : M), ?_⟩
    funext e
    rw [switch]
    calc label e = (potential (G.target e) * (potential (G.source e))⁻¹ : Mˣ) :=
          hpotential e
      _ = (potential (G.target e) : M) * 1 *
            ((potential (G.source e) : M))⁻¹ := by
          simp
  · rintro ⟨η, rfl⟩
    rw [hasTrivialCycleLabels_switch_iff]
    exact hasTrivialCycleLabels_one

end MiningScratch
```
