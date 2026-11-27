# What would one extra burst do to a finite buffer?

Given a recorded trace through a bounded queue or store, add one signed burst before the clamp at any chosen time. How much would it change total overflow, unmet demand and final contents by a chosen deadline? One exact index handles all burst times, amplitudes and deadlines in $O(n)$ preprocessing and space and $O(\log(2n))$ per query. For a fixed amplitude with retention at most one, a chronological sweep computes all $n$ timing alternatives in $O(n)$ total work. Both bounds allow time-dependent limits and prices, complete resets, and zero-width bands. They count ordered-field operations and comparisons. The Python prototype uses exact rationals, whose bit lengths can grow with the trace.

The two cumulative losses are distinct pieces of information. On the [96-hour household PV and load excerpt](opsd_residential3_may2017.csv), take a lossless 2 kWh store, initially at 1 kWh. An extra 0.5 kWh supplied at any of 59 times would reduce grid import by the full 0.5 kWh, including the hour starting May 1, 2017 at 00:00 UTC. At 31 others it would be spilled in full, including May 2 at 04:00 UTC. In both cases the final state of charge is unchanged. The timings are separate counterfactuals on the same trace. [Meter provenance](metered-pv-hinges.md#metered-household-example)

## From a baseline trace to fixed thresholds

For stage $j$, write $z_j=a_jx_{j-1}+b_j$ for the raw input and $x_j=\min(h_j,\max(l_j,z_j))$ for the retained state. Assume $a_j\ge0$ and $l_j\le h_j$. The two losses are $(l_j-z_j)_+$ and $(z_j-h_j)_+$. A query adds $\delta$ to the raw input at one stage $i$ and asks for the changes in each weighted sum of these losses through stage $d\ge i$, together with the change in $x_d$. The lower and upper weights $w_j^-,w_j^+$ are fixed before the queries.

A stage with $a_j=0$ begins a new block. A burst at that stage still affects its raw input. Any earlier burst ceases to affect the trajectory at the reset, so clip the queried deadline to the end of the burst's block when summing the losses, and return zero for the state change if the requested deadline is later. In a block beginning at $b$, set $P_b=1$ and $P_j=a_jP_{j-1}$ for $j>b$. All $P_j$ are positive. For a positive burst define the baseline lower deficit $D_j=(l_j-z_j)_+$ and upper headroom $R_j=h_j-x_j$. For any increase $v\ge0$ of the raw input at $j$, direct evaluation of the two clamps gives

$$
\begin{aligned}
\text{avoided lower loss}&=\min(v,D_j),\\
\text{extra upper loss}&=(v-D_j-R_j)_+,\\
\text{extra retained state}&=\min(R_j,(v-D_j)_+).
\end{aligned}
$$

Dividing by $P_j$ puts both the entering and retained amounts in common units. Indeed, at a later step $j>i$ the raw input increases by $a_j$ times the previous extra retained state, and $a_j/P_j=1/P_{j-1}$. Define the nondecreasing sequence $C$ and the upper thresholds $H$ by

$$
C_{j+1}=C_j+D_j/P_j,\qquad H_j=C_{j+1}+R_j/P_j.
$$

The origin of $C$ is arbitrary. The implementation starts from zero and keeps a running sum even across block boundaries. Represent a burst by the interval of levels $[C_i,y]$ with $y=C_i+\delta/P_i$. At stage $j$, amounts entering the stage are represented by a possibly empty interval with left endpoint $C_j$. The part below $C_{j+1}$ pays down the lower deficit, the part above $H_j$ becomes upper overflow, and the intersection with $[C_{j+1},H_j]$ propagates. The three widths give the previous three formulas in normalized units. Thus a level $v$ never changes its coordinate as it traverses the trace. A unit of width absorbed at stage $j$ represents $P_j$ physical units. Endpoints of the intervals have zero width.

## Which stage absorbs each level?

For the effective deadline $d$, let $r$ be the first minimizer of $H$ on $[i,d]$ and $m=H_r$. The key inequality is $H_j\ge C_{j+1}$. If $H_j<v$, then $C_{k+1}\le C_{j+1}<v$ for every earlier stage $k<j$. A level that exceeds any upper threshold therefore hits its first such upper threshold before any lower deficit can absorb it. The upper loss comes from the levels above $m$. Among the levels at most $m$, those below $C_{d+1}$ pay down lower deficits, and those above $C_{d+1}$ remain. This partitions $[C_i,y]$ into consecutive lower, retained and upper intervals, allowing any of them to be empty.

**Lower.** Set $B=\min(y,m,C_{d+1})$. The overlap of $[C_i,B]$ with $[C_j,C_{j+1}]$ represents avoided lower loss at stage $j$. Precompute prefix sums of $w_j^-D_j$ and binary-search $C$ for the last $k\in[i,d+1]$ with $C_k\le B$. The sum on the full intervals is one prefix difference. If $k\le d$, add $w_k^-P_k(B-C_k)$. The change in baseline lower loss is the negative of that sum.

**Upper.** The stage absorbing level $v>m$ is the first $j\in[i,d]$ with $H_j<v$. As $v$ decreases, these stages are the strict record minima of $H$ scanned from $i$. Build the forest whose parent $p(j)$ is the nearest later stage in the same block with strictly smaller $H$. A right-to-left monotone stack builds all parents in linear time. An edge $j\to p(j)$ contributes $w_{p(j)}^+P_{p(j)}(H_j-H_{p(j)})$ to the upper integral. Precompute $S_j$ as the sum of these edge contributions from $j$ to its block's forest root, or zero at a root.

If $y\le m$, upper loss is unchanged. Otherwise take $f$ to be the first stage in $[i,d]$ with $H_f<y$. The relevant record minima follow parent edges from $f$ until $r$, since every strictly smaller record before the first minimum is still inside the deadline. Stage $f$ handles width $y-H_f$. The later complete intervals are a difference of forest sums, so the upper change is

$$
w_f^+P_f(y-H_f)+S_f-S_r.
$$

**Retained.** The remaining change within the block is $P_d\bigl(\min(y,m)-C_{d+1}\bigr)_+$.

A range-minimum tree on $H$ finds $r$ and the first strict crossing $f$ in $O(\log(2n))$ time. The first-crossing search uses the chronological canonical subintervals of $[i,d]$, skips the ones whose minimum is too high, and descends only in the first qualifying subinterval. The tree stores scalar minima and indexes. The integrals come from the prefix sums and forest sums. No factor depends on the number of intermediate contacts. For a negative burst, apply the same construction to $-x$, shifts $-b_j$, band $[-h_j,-l_j]$ and exchanged weights. Exchange the resulting lower and upper changes and negate the state change. Two orientations have the same linear preprocessing and space bound.

## All timing alternatives for one amplitude

For a common positive $\delta$, the levels $y_i=C_i+\delta/P_i$ are nondecreasing within each block if $0<a_j\le1$ at its noninitial stages. This also holds for the reflected orientation. Let every query run through the trace end. Sweep stage $j$ forward and append $j$ to the pending starts. The pending starts are sorted by level, so the ones that first cross $H_j$ form a suffix. Pop that suffix and record $j$ as the first upper crossing for each pop. Clear the pending starts between blocks. Every start is pushed once and popped at most once.

The minimizer $r$ for each start is its forest root, stored during construction. As $i$ advances within a block, the suffix minimum $m$ cannot decrease. Therefore $\min(y_i,m,C_{d+1})$ cannot decrease, and one forward pointer finds all lower prefix endpoints. The totals and final differences then take constant work per start. The sweep still applies with gains above one if the computed levels within each block are nondecreasing. Otherwise the prototype uses the logarithmic index separately at each start.

The representation can save quadratic space compared with storing one piecewise-affine response curve per start. Use a fixed band $[0,1]$, $a_j=1/2$, zero initial state and choose $b_j$ to realize $x_j=1-6^{-j}/3$ at zero-based stage $j$. The baseline never clips, so $C_j=0$, $P_j=2^{-j}$, and $H_j=3^{-(j+1)}$. The thresholds are strictly descending. For a burst at $i$ and the full deadline, each $j\ge i$ contributes a distinct amplitude knot $P_iH_j$. With unit upper weights the slope on the interval assigned to $j$ is $P_j/P_i$, so every knot survives even in total physical overflow. The knot amplitudes $2^{-i}3^{-(j+1)}$ distinguish all pairs $0\le i\le j<n$ by unique prime factorization. The $n$ response curves thus have $n(n+1)/2$ different knot amplitudes between them.

## Prototype and checks

[Implementation](reflection_impulses.py) · [Exact replay checker and benchmark](reflection_impulses_check.py)

```python
from fractions import Fraction
from reflection_impulses import ImpulseIndex, Stage

index = ImpulseIndex([
    Stage(1, -1, 0, 2),
    Stage('1/2', '-3/4', 0, 2),
    Stage(1, 2, 0, 2),
], initial=0)

lower, upper, state = index.query(stage=0, amplitude=4, deadline=2)
assert (lower, upper, state) == (Fraction(-7, 4), Fraction(5, 4), 0)
all_timings = index.all_stages('1/2')
```

```bash
python3 -B reflection_impulses_check.py --meter opsd_residential3_may2017.csv
python3 -B reflection_impulses_check.py --benchmark 4000
```

Independent direct trajectory replay agreed on 217,728 exhaustive comparisons, 267,645 seeded randomized comparisons and 19,008 metered comparisons. The cases covered both signs, arbitrary deadlines, different stage prices, loss, amplification, tied contacts, singleton bands and hard resets. A separate fixed-band construction checked 1,275 distinct upper-loss knots across 50 burst-response curves.

Timings below are seconds for 4,000 stages and 4,000 exact timing alternatives of amplitude 7. The replay baseline uses integer arithmetic on these integer workloads and exits at the first state coalescence. Frequent contacts favor replay. Late contacts preserve the burst for much of the suffix and favor the index. Query time excludes construction.

| Synthetic trace | Build index | Linear timing sweep | 4,000 logarithmic queries | Replay |
|---|---:|---:|---:|---:|
| Late contact | 0.141 | 0.053 | 0.177 | 3.416 |
| Frequent contacts | 0.136 | 0.065 | 0.199 | 0.011 |

## Related work

Multitubes' `ClampedAffineSummary.apply_comp` composes stage maps to summarize the endpoint, and `bandIter_eq_inf'_sup'` represents the reflected state by an infimum over upper restarts. Kruk et al. identify the explicit two-sided Skorokhod map for fixed boundaries and compare the two individual regulators in Theorems 1.4 and 1.7. Burdzy, Kang and Ramanan derive the time-dependent map in Theorem 2.6, treating piecewise-constant trajectories in Proposition 2.9. The index here accounts for time-weighted changes of both regulators and shares the computation across retrospective impulses. [Multitubes two-sided reflection](../../../Maths/Recursion/TwoSidedReflection.lean) · [Kruk, Lehoczky, Ramanan and Shreve](https://arxiv.org/pdf/0710.2977) · [Burdzy, Kang and Ramanan](https://arxiv.org/pdf/0712.2863)

Cassandras et al. use finite differences in §IV.A and sample derivatives in §IV.B to estimate gradients of loss and workload with respect to thresholds. Ho, Cao and Cassandras address finite perturbation analysis for queueing networks, including changes to queue size. The queries here are finite signed impulses to one stage input of a discrete reflected trace, with exact separate regulator changes for arbitrary deadlines. The nearest-smaller relation is the standard array primitive studied by Berkman, Schieber and Vishkin. Its role here is to index integrals weighted by the first upper absorption stage. [Cassandras et al.](https://people.bu.edu/cgc/Published/TACprint0802.pdf) · [Ho, Cao and Cassandras](https://doi.org/10.1016/0005-1098(83)90060-2) · [Berkman, Schieber and Vishkin](https://doi.org/10.1006/jagm.1993.1018)
