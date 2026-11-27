# Which detector reports matter after other reports are suppressed?

A detector runs at each of $n$ times. Suppressing a report keeps the physical hit branch and its state update active, while allowing the run to continue without logging a hit. Give each report a nonnegative suppression cost. For every report $i$, the algorithm finds a cheapest set of **other** reports to suppress so that subsequently suppressing $i$ strictly reduces the probability of a logged hit by the deadline. It returns a set attaining each finite cost. With maximum Hilbert-space dimension $d$, at most $r$ Kraus matrices per stage and a reduced initial Gram factor, the algorithm takes $O(nrd^3)$ field operations using ordinary dense arithmetic. Costs can be arbitrary nonnegative rationals.

`QuantumTransport.FiniteInstrument` supplies the normalized branches. Its `sequential_branch_apply` pulls an observable back through the later branch first. `QuantumTransport.hitBy_add_survival` identifies detection as the complement of survival for a repeated normalized detector. The same complement holds with time-varying instruments. The algorithm below uses finite-dimensional `krausMap` for the corresponding state evolution, with the observable evolution as its adjoint. [Finite instruments](../QuantumTransport/Instruments.lean#L72) · [Detection and survival](../QuantumTransport/Detection.lean#L84) · [Matrix Kraus maps](../QuantumTransport/Kraus.lean#L73)

## Reporting model

At stage $t$, the hit family $H_t$ and continue family $C_t$ consist of Kraus matrices from the incoming to the outgoing Hilbert space. Together they satisfy $\sum_{K\in H_t\sqcup C_t}K^\dagger K=I$. Define their state maps by summing $X\mapsto KXK^\dagger$ over each family. All instruments are fixed in advance. With a suppressed set $F$, the no-logged-hit evolution uses $C_t+H_t$ at $t\in F$ and $C_t$ elsewhere, where the sum denotes the sum of state maps. Let $S(F)$ be the trace of the resulting subnormalized state. Then the drop in deadline detection when additionally suppressing $i$ is $S(F\cup\{i\})-S(F)$.

The model describes suppression of the report. Physically bypassing a measurement, or allowing its output to change future instruments, would require a different state evolution. The deadline probability can also be understood using a completed run that continues through all physical branch updates even after a logged hit. Trace preservation of the subsequent stages gives the same probability of at least one logged hit as first-hit stopping.

Write the input density as $\rho=\sum_a u_a u_a^\dagger$. More generally, a completed run may be tested by a final effect $0\le E=\sum_b v_b v_b^\dagger\le I$. The probability of no logged hit and a successful final test is the trace paired with $E$, denoted $S_E(F)$. The loss of joint detection and final success is again $S_E(F\cup\{i\})-S_E(F)$, since the unconditional final success probability is independent of suppression. The same strict comparison applies to detection conditional on a final success of positive probability. For ordinary first-hit detection take $E=I$ and $v_b$ the coordinate basis.

## Why positive sensitivity is a minimum-cost trajectory

A trajectory chooses one Kraus matrix $K_t$ at every stage. Let $B$ be the hit positions of that trajectory. Expanding the finite product of state maps gives a term
$$
 \sum_{a,b} |v_b^\dagger K_n\cdots K_1u_a|^2
$$
in $S_E(F)$ exactly when $B\subseteq F$. In the difference $S_E(F\cup\{i\})-S_E(F)$, the surviving terms have $i\in B$ and $B\setminus\{i\}\subseteq F$. Consequently report $i$ is pivotal under $F$ exactly when one of these trajectories has a nonzero amplitude. Its other hits alone already form a valid suppression set. Nonnegative costs imply that the smallest additional cost is the minimum sum of hit costs over the rest of a trajectory with a hit at $i$ and nonzero amplitude.

For example, the first round may send coordinate 0 to coordinate 1 and report a hit, or send coordinate 1 to coordinate 0 and continue. The second round reports a hit on coordinate 1 and continues on coordinate 0. With input $(3/5,4/5)$, the physical histories are two hits with probability $9/25$, or no hits with probability $16/25$. Suppressing either report by itself leaves detection at $9/25$. Suppressing both reduces it to zero. At costs $3,5$, the additional costs for the two reports are $5,3$.

With full deadline readout, suppose each other round has an invertible continue Kraus matrix and report $i$ has an invertible hit Kraus matrix. Their product sends every nonzero input factor to a nonzero vector, so the single-hit trajectory is already feasible and the additional cost is zero. The singular projections in the paired-hit example erase precisely the candidate single-hit trajectories.

## Two passes give the optimal context for every report

A vector tagged with a trajectory cost can be removed if it is in the span of vectors whose costs are at most its own. Sort by cost and accept vectors greedily when they increase the span. For every cutoff $b$, the retained vectors of cost at most $b$ span all candidates of cost at most $b$. The retained vectors are actual trajectory vectors. Keep the elimination pivots separately, so the trajectory linked to each vector remains valid.

Start with the input factors $u_a$ at cost zero. Save the resulting basis just before each stage. Apply each Kraus matrix to the current basis and add the stage cost for a hit matrix. Compress the candidates by the same rule. The cutoff property holds by induction. If an omitted vector is a linear combination of vectors no more expensive than itself, its image under each Kraus matrix has the same representation after shifting the cost. In the reverse pass, start with $v_b$ at cost zero and use adjoint Kraus matrices. Just after stage $i$, the reverse basis represents all suffix effects as row vectors after taking the adjoint, again at every cutoff.

For report $i$, test $q^\dagger Kp$ for the retained prefix vectors $p$, retained suffix vectors $q$, and $K\in H_i$. For each nonzero test the candidate additional cost is the sum of the two retained costs. A genuine trajectory of no greater cost appears among these tests whenever any trajectory is feasible. Its prefix and suffix vectors expand separately into retained vectors at their respective cutoffs, and a nonzero pairing requires at least one nonzero pairing of retained vectors. Conversely every tested nonzero pairing combines a genuine prefix, hit, and suffix, and its other hits give the claimed context. If all tests vanish, the report cannot be pivotal at any budget.

The bases have size at most $d$. Stage $t$ with $r_t$ Kraus matrices produces at most $r_td$ vectors, each using $O(d^2)$ operations for application and incremental elimination. Each branch emits candidates in sorted cost order and the two streams merge without searching the range of possible costs. The join tests at most $r_td^2$ pairings. For each $K,p$ compute $Kp$ once, so the join also costs $O(r_td^3)$. Initial and terminal Gram factors contribute $O((a+b)d^2)$ work for $a,b$ supplied factors. One can use at most $d$ factors per side, and the unfiltered $E=I$ side initializes directly. Stored prefix bases take $O(nd^2)$ field elements in addition to the instrument. Each retained entry uses one persistent link for its most recent hit in the direction of its pass. Listing a context of size $s$ takes $O(s+1)$ additional work, so printing all contexts can take quadratic time even when computing all costs takes linear time in the deadline for fixed $r,d$.

These are arithmetic bounds, using exact zero and cost comparisons. The prototype accepts real rational square matrices of a common dimension. It uses primitive integer directions and keeps the original rational costs. Clearing denominators and rescaling each Kraus matrix or vector changes no amplitude zero test or span used here. Rational coefficient size affects timings. The proof also permits complex coefficients, rectangular stages, singular operations and mixed input factors. The final effect changes only the initial vectors of the backward pass. The Python function also accepts rational terminal Gram factors, supplied by the caller, and the command line uses $E=I$.

## A positive probability threshold makes the problem NP-complete

Consider the decision question whether there exists a set of at most $k$ unit-cost suppressed reports whose deadline detection loss $S(F)-S(\varnothing)$ is at least the supplied rational $\tau>0$. Even the commuting-projector case is NP-complete. For a simple graph with $m>0$ edges, let $L=\lceil\sqrt m\rceil$. Take one coordinate per edge and pad to dimension $d=L^2$ with inert coordinates. The unit input vector has amplitude $1/L$ at every coordinate. Put one report at each vertex. Its hit projector selects the edge coordinates incident to that vertex. Its continue projector selects all remaining coordinates. Every edge trajectory hits exactly at its two endpoints. Thus
$$
 S(F)-S(\varnothing)=\frac{|\{\{u,v\}\text{ an edge}:u,v\in F\}|}{d}.
$$
For $k\ge2$, a set of size at most $k$ reaches $\tau=\binom{k}{2}/d$ exactly if it contains a $k$-clique. Instances with $m<\binom{k}{2}$ can be rejected in the reduction with a fixed no instance, so $\tau$ can be restricted to $(0,1]$. These are explicit rational input matrices of polynomial size. For membership in NP the witness is the suppressed set. Two density propagations and rational trace calculations verify it. Clearing common denominators at each stage makes the numerator and denominator bit lengths grow by at most an additive polynomial per step. The same hardness holds for a fixed report $i$ and a threshold on its marginal loss, by appending a report that hits exactly on the edge coordinates. If it remains logged, detection on every edge is assured regardless of the other suppressions. Suppressing this last report loses exactly the mass of the edges induced by the context. [Karp’s original CLIQUE reduction](https://www2.seas.gwu.edu/~simhaweb/champalg/tsp/papers/KarpOriginal.pdf)

## Relation to existing algorithms

Tzeng's weighted-automaton equivalence test uses span pruning to find a nonzero word. Fomin, Lokshtanov, Panolan and Saurabh use weighted representative families for more general linear-matroid extension tests. Dai and Ying's QReach computes ordinary quantum reachable subspaces directly in Hilbert space. The linear pruning, greedy basis selection and Hilbert-space representation each have these precedents. Here the output is one minimum-cost context per report, with forward and backward reuse of weighted bases through both outcomes. For a generic signed linear model of hidden density evolution, expanding suppression produces sums that may cancel, so a nonzero individual word is insufficient unless the physical positivity premise supplies the sign. Applying the same filtered-basis calculation directly to the positive density branch maps is valid but can require $d^2$ vectors of dimension $d^2$ at each cut instead of $d$ vectors of dimension $d$. It can also benefit from small reachable or observable rank. Ordinary forward and backward state/effect propagation tests every report for a **fixed** context in one pair of passes. The present computation optimizes a different context for each report. For classical finite-state chains the positive trajectories can instead be evaluated by ordinary shortest paths on a layered graph, with forward and backward reuse. The minimum-contingency question also resembles degree of responsibility for Boolean structural models. [Kiefer et al., §2](https://archive.model.in.tum.de/um/bibdb/kiefer/KMOWW-CAV11.pdf) · [Fomin et al., Theorem 3.7](https://sites.cs.ucsb.edu/~daniello/papers/efficientRepSetJ.pdf) · [Dai and Ying, §4](https://link.springer.com/chapter/10.1007/978-3-031-65633-0_23) · [Chockler and Halpern, §3](https://arxiv.org/abs/cs/0312038)

## Reproduce

```sh
python3 report_sensitivity.py paired-hits.json --witnesses
python3 report_sensitivity_check.py
python3 report_sensitivity_check.py --bench
```

The input file specifies the Gram factors of the starting density and each round's hit matrices, continue matrices and suppression cost. Strings such as `"3/5"` are exact rationals. Reports are numbered from zero. The command validates the state normalization and both branches' combined trace preservation. It outputs `null` for an impossible report.

The independent checker evaluates every suppressed set by exact density-matrix multiplication on 100 seeded valid instruments. It verifies 296 report answers and witnesses against 1,641 subset probabilities, including 148 positive-cost contexts, 70 zero-cost contexts and 78 impossible reports. Separate checks cover the paired-hit example with and without a terminal projector, and every subset in two commuting-projector instances on the opposite sides of the clique threshold, including the designated-report variant.

For the synthetic timing test, a four-dimensional system has a hit or continue
flag that persists over a block of stages. Both flag choices have positive
probability at every block boundary. The rational Kraus matrices are supplied
in varying orthogonal bases. All reports in a block must be suppressed to change
detection by suppressing any one of them, so every optimum uses the other
reports in that block. The tests compare with an exact weighted-basis solver
that shares prefix computations and reruns the suffix for each forced hit.
Input validation is outside the timing. Times are seconds, medians of three
for the side-by-side rows.

| Rounds | Block length | Shared passes | Forced-hit suffix reruns |
|---:|---:|---:|---:|
| 64 | 16 | 0.010 | 0.074 |
| 128 | 32 | 0.020 | 0.245 |
| 256 | 64 | 0.046 | 1.038 |

A separate 1,024-round test has 128 eight-round blocks and hence $2^{128}$
positive-probability outcome histories. All expected costs and seven-report
witness lengths agreed. The shared passes took 0.17 seconds in this run.
