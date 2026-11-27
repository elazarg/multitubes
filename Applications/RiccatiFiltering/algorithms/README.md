# Covariance deadline queries on a scalar packet log

After an outage or a filter restart, an engineer can ask how a scalar variance estimate would have evolved from a proposed restart variance. The packet log and model parameters are already known. Across many overlapping windows, the start time, restart variance and safety multiplier can each change. A query reports the terminal variance, the peak relative to a deadline profile, the earliest time of that peak and the first deadline breach. It can also solve the inverse question and return the exact set of restart variances that meet every deadline.

For an $n$-step log, the index builds in $O(n\log n)$ exact arithmetic operations, stores $O(n\log n)$ records and answers each query in $O(\log^2 n)$ arithmetic operations. This counts rational arithmetic and constant-degree algebraic comparisons at unit cost. With $B$-bit input rationals, some stored integers require $O(n(B+1))$ bits and exact Python arithmetic costs depend on those lengths. The included measurement shows the index paying off across many long windows, while direct replay is faster for short windows.

## Log and queries

Step $t$ takes the covariance $p_{t-1}$ to $p_t$. Prediction yields $s=g_t p_{t-1}+q_t$, with squared gain $g_t\ge 0$ and process noise $q_t\ge 0$. A lost packet sets $p_t=s$. An observation with noise $r_t>0$ sets $p_t=r_t s/(s+r_t)$. A perfect observation, $r_t=0$, sets $p_t=0$, including at $s=0$. Zero gain is also allowed. This uses the prediction and scalar observation maps in the Lean client. Its `monotone_scalarRiccati` theorem proves monotonicity of the observation step and `scalar_walkMap_le_of_lax_or_exact` propagates covariance bounds along walks. The single-crossing argument below adds information about relative values at different times. [Scalar Riccati transport](../RiccatiFiltering/ScalarRiccati.lean), [covariance prediction](../RiccatiFiltering/CovariancePrediction.lean).

Fix a positive profile $w_0,\ldots,w_n$ with the log. On a query window $(l,r]$ and cap multiplier $h\ge 0$, a deadline is met at time $t$ if $p_t\le h w_t$. Take $w_t=1$ for a constant ceiling. The initial variance $p_l$ is supplied by the caller and the checks begin at $l+1$. An empty window has no peak or breach, returns $p_l$ as its terminal variance and accepts every restart variance. For a calibration interval of possible initial variances, the upper endpoint yields the exact worst peak ratio and detects the earliest possible breach. Every update is nondecreasing, and the upper endpoint is itself an allowed calibration.

## Ordered crossings of prefix maps

Use normalized covariance $x_t=p_t/w_t$. Put $a_t=g_t w_{t-1}$. Every step $x\mapsto (a x+b)/(c x+d)$ has nonnegative coefficients, $d>0$ and determinant $ad-bc\ge 0$. Matrices for the three cases are

$$
\begin{pmatrix}a_t&q_t\\ 0&w_t\end{pmatrix},\qquad
\begin{pmatrix}r_t a_t&r_t q_t\\ w_t a_t&w_t(q_t+r_t)\end{pmatrix},\qquad
\begin{pmatrix}0&0\\ 0&1\end{pmatrix}.
$$

Composition is matrix multiplication, with the later step on the left. The coefficient conditions survive multiplication, and positive denominators hold throughout $[0,\infty)$. A map of positive determinant is strictly increasing. A zero determinant gives a constant map, regardless of the previous covariance.

Within a block, write $P_i(x)$ for the normalized covariance at its $i$-th step with entering covariance $x$. For $i<j$, let $G(y)=(a y+b)/(c y+d)$ be the intervening composition, so $P_j=G\circ P_i$. If $P_i$ is constant, the pair's comparison is constant. Otherwise $y=P_i(x)>0$ for every $x>0$, and

$$
G(y)>y \quad\Longleftrightarrow\quad (a-d)+\frac{b}{y}-cy>0.
$$

The expression on the right is nonincreasing in $y$ and $y$ increases with $x$. Thus $P_j(x)>P_i(x)$ holds on an initial interval of $x>0$. That interval can be empty, all of $(0,\infty)$, or $(0,\tau)$ for one positive crossing $\tau$. At the crossing the earlier time wins by convention. It follows that, when scanning $x$ from large to small, the earliest maximizing time can only move later. At $x=0$, an equality can precede strict dominance, so the index records the peak value and earliest time at zero separately. For example $P_1(x)=x$ and $P_2(x)=2x/(1+x)$ tie at zero, then $P_2$ wins on $(0,1)$.

The prefix relation is essential. The two maps $(3x+1)/(x+1)$ and $(40x+1)/(20x+2)$ satisfy the coefficient and determinant conditions individually, but the sign of the second minus the first is the sign of $-20x^2+15x-1$, which has two positive roots.

### Build a block summary in linear work

Process the prefix maps in time order. Store a stack of earliest maximizers from large to small positive inputs, with decreasing cutoffs at which each map takes over from the previous one. When a new map arrives, compare it to the last map in the stack. If the strict dominance interval is empty, discard the new map because the last map is at least as large everywhere. If the cutoff reaches or exceeds the last map's own cutoff, pop the last map because its whole winning interval has been taken over. Then compare with the new last map. Otherwise append the new map at its cutoff. If the stack empties, the new map wins at every positive input.

When a map is appended at a cutoff strictly below the last map's own cutoff, the old last map is still maximal in a neighborhood of the cutoff. The new map exceeds it below the cutoff and loses to it, or ties it, above. For any pieces popped during this insertion, the new map covers their former winning intervals. At shared boundaries the earlier time keeps the tie. Each map enters and leaves the stack at most once. Independently, a single sweep tracks the earliest maximum at zero and produces the terminal map. A block of $k$ steps therefore takes $O(k)$ arithmetic operations and at most $k$ envelope pieces.

A cutoff comes from cross multiplying two positive denominators. Let $A x^2+B'x+C$ be the resulting polynomial for the sign of the later map minus the earlier one. The first and last nonzero coefficients in ascending degree give the signs near zero and positive infinity. Ordered crossing determines whether a positive cutoff exists. For a finite cutoff, the polynomial is either linear or has $A<0$. In the quadratic case the positive root is

$$
-\frac{B'}{2A}+\sqrt{\frac{(B')^2-4AC}{4A^2}}.
$$

The code stores these two rationals, with zero radicand for a rational cutoff. It compares cutoffs by comparing $u_1-u_2+\sqrt{v_1}$ and $\sqrt{v_2}$ after swapping the sides if needed to make $u_1-u_2\ge 0$. Squaring both nonnegative sides reduces the sign to a rational plus a nonnegative multiple of $\sqrt{v_1}$. One further sign-aware squaring suffices. The implementation uses rational comparisons throughout, including ties at irrational cutoffs. Rational priors, reported peak values, terminal variances and finite inverse limits use exact fractions.

## Range queries

Build the block summaries on a balanced segment tree. The canonical cover of $(l,r]$ uses $O(\log n)$ disjoint blocks. From left to right, evaluate each block's envelope at the entering covariance by binary searching its cutoffs, then evaluate its terminal map to get the input to the next block. Compare the local peaks and keep the earliest tie. For the first breach, identify the first block with peak greater than $h$. Descend that block, testing its left child's peak. If the left child is safe, apply its terminal map and continue in the right child. This adds at most one path of $O(\log n)$ block lookups. Each lookup costs $O(\log n)$ exact operations, giving $O(\log^2 n)$ in total.

### Invert the range constraint

For a single map, $P(x)\le h$ is exactly $(a-hc)x\le hd-b$. If $hd-b<0$, the feasible set is empty by monotonicity. Otherwise a nonpositive coefficient of $x$ makes it unbounded, and a positive coefficient gives the inclusive bound $(hd-b)/(a-hc)$.

For a whole block let $H(x)=\max_i P_i(x)$. This maximum is continuous and nondecreasing. First check $H(0)\le h$. If the large-input piece's limit is at most $h$, all finite inputs pass. Otherwise the feasible set is $[0,x^*]$ for some finite $x^*$. At each stored cutoff $\tau$, test $H(\tau)>h$ by comparing $\tau$ to a rational using $(a-hc)\tau>hd-b$ for either incident piece. This predicate is equivalent to $\tau>x^*$. Binary search therefore finds the piece active immediately to the right of $x^*$, whose inverse yields $x^*$ exactly. When $x^*$ is a cutoff, both pieces have the same value there, and the piece on the right admits a finite inverse.

Process the canonical blocks from right to left. Pull back the downstream bound through the current block's terminal map and intersect it with the bound from the block's own envelope. Both sets are intervals anchored at zero or empty, so intersection keeps the smaller endpoint and any empty preimage ends the query. Scale the resulting bound by $w_l$ to return it in physical variance units. This uses $O(\log^2 n)$ exact operations and distinguishes an inclusive endpoint of zero from an empty feasible set. A bounded Riccati map can also give an unbounded preimage at its limiting value.

## Where the speedup applies

At each tree depth the block lengths sum to $n$. The stack build therefore uses $O(n\log n)$ arithmetic operations. Building an upper envelope independently at each node by generic divide-and-conquer gives an $O(n\log^2 n)$ bound even with linear merging and linear-size intermediate envelopes. The stack removes that additional logarithm by exploiting the direction of crossings in time order. A block can genuinely need all $k$ pieces. For example, take affine prefix slopes $m_i=k-i+1$, intercept $b_1=0$ and intercept increments $b_{i+1}-b_i=k-i$. These are realized by nonnegative affine steps with gain $m_{i+1}/m_i$ and noise $b_{i+1}-(m_{i+1}/m_i)b_i$. Consecutive crossing inputs are $k-1,\ldots,1$, so each prefix uniquely wins on a nonempty open interval.

Direct forward replay and a direct backward cap pullback each cost $O(r-l)$ operations per query and need no index. Over $Q$ full-length queries this gives $O(Qn)$ arithmetic work, while the index costs $O(n\log n+Q\log^2 n)$. A tree of products alone is sufficient for terminal covariance. A precomputed trajectory and range maximum structure are sufficient when the query starts at a state on that same trajectory. The envelope index handles restarted trajectories with independent initial covariances and includes peak and deadline information. The indexed log and the shape of the cap profile are fixed across the query batch. The result concerns scalar covariance, a realized packet history and uncertainty in the entering covariance.

Clearing denominators of a step's $2\times2$ matrix gives integer coefficients with $O(B)$ bits. A product of $k$ such matrices has $O(k(B+1))$-bit entries, and the cutoff representation uses the same order of bit lengths. Summing the squared block lengths across the tree gives an $O(n^2(B+1))$ upper bound on the stored numerical bits. With $L$-bit query inputs, intermediate query numbers have $O(n(B+1)+L)$ bits. Constant transfers are stored as reduced constant fractions, so a reset drops all dependence on the preceding covariance and discards common factors from that part of the product. Exact arithmetic and the extra index storage matter for long logs with few resets. The complexity bounds above count arithmetic operations and records.

## Run the example and checks

```sh
python3 riccati_deadlines.py
python3 riccati_deadlines_check.py
python3 riccati_deadlines_check.py --benchmark
```

The example log has five steps and profile $(1,1,1,2,1,1)$. Step 2 receives a noisy observation and step 4 a perfect observation. The other steps are outages. The executable reports the following exact values.

| Window | Restart variance | Cap | Terminal variance | Peak ratio at time | First breach | Safe restart upper bound |
| --- | ---: | ---: | ---: | --- | ---: | --- |
| $(0,5]$ | $3/4$ | $4/5$ | $1$ | $1$ at $5$ | $2$ | Impossible |
| $(1,3]$ | $1/2$ | $4/5$ | $5/3$ | $5/6$ at $3$ | $3$ | $3/7$ |
| $(3,5]$ | $7$ | $1$ | $1$ | $1$ at $5$ | None | Unbounded |

Use `python3 riccati_deadlines.py request.json` for a file or pass `-` to read JSON from standard input. Steps are `[squared_gain, process_noise, observation_noise]`, with `null` for an outage. An input can be an integer or a rational string, such as `"4/5"`. The optional `profile` has $n+1$ positive entries and defaults to ones. Each record in `queries` takes `left`, `right`, `initial` and an optional `cap`. The script emits one JSON result per query, using strings for rational numbers and the strings `"impossible"` and `"unbounded"` for the two inverse cases. [Implementation](riccati_deadlines.py), [exact checker](riccati_deadlines_check.py).

The checker compares the index against direct physical-covariance recurrence and a separate backward pass that inverts individual observation and prediction equations. It checks 266,500 exact report and bound pairs, including every log of length up to four from a six-step palette, plus targeted cases for zero-input ties, perfect observations, irrational cutoffs, bounded outputs and a full-size envelope. In one run with 2,048 steps, a build took 0.315 s. With the index built, 400 windows of lengths 1–4 took 0.029 s through the index and 0.010 s by direct computation. For 400 windows of lengths 512–1,536, the index took 0.224 s plus the same build, against 4.937 s direct. These are timings for the checker’s synthetic rational workload with proportional caps and periodic resets.

## Related work

- Sinopoli et al. formulate the Kalman recurrence conditional on packet arrivals and analyze expected covariance under random arrivals. Huang and Dey use the peaks of prediction covariance across stochastic loss runs to study stability and tails. Here the logged arrival sequence is fixed, and the envelope variable is the proposed entering covariance for a finite window. [Sinopoli et al., §II–III](https://people.eecs.berkeley.edu/~sastry/pubs/PDFs%20of%20Pubs2000-2005/Publications%20of%20Grad%20Students%2020042005/Sinopoli/SinopoliKalmanFiltering2004.pdf), [Huang and Dey, §II–IV](https://people.math.carleton.ca/~mhuang/cdc06kf.pdf).
- Dance and Silander represent scalar posterior variance updates as Möbius maps and multiply their $2\times2$ matrices along observation words in a threshold-policy analysis. Vitus et al. use the corresponding numerator and denominator matrix recursion for predictor covariance perturbations in sensor scheduling. The finite-log index uses the relative order of *different prefixes* of one sequence to answer exact peak and preimage queries. [Dance and Silander, §1.1 and Definition 68](https://www.jmlr.org/papers/volume20/17-185/17-185.pdf), [Vitus et al., Theorem 3](https://engineering.purdue.edu/~jianghai/Publication/CDC2010_SensorSch_Bound.pdf).
- The stack update is the ordered upper-envelope technique used for affine functions. The factorization $P_j=G\circ P_i$ supplies the required crossing order for these nonlinear covariance maps. Generic envelope construction by recursive merging is also established. The contribution substantiated here is this Riccati crossing property and its use for the range and inverse queries above. Literature priority for the combined workload is open. [Bringmann et al., Algorithm 2](https://people.mpi-inf.mpg.de/~kbringma/paper/2014GECCO.pdf), [CGAL envelope construction](https://doc.cgal.org/6.1.3/Envelope_2/index.html).
