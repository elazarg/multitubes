# Exact feedback margins for affine radius constraints

A mode-dependent error certificate assigns a radius $r_v$ to every mode. A transition $u\to v$ demands $r_v\ge b+a r_u$, with $a\ge0$. In the fixed comparison model the radii also have lower floors and upper budgets. The [switched-control application](../README.md) constructs the least invariant radius under a contractive gauge and checks supplied rational witnesses.

Suppose many candidate transitions return to one mode $h$, while the existing model and upper budgets are fixed. Two passes through the original graph produce the exact region of simultaneous admissible offsets for a precisely characterized range of candidate gains. An indexed heap gives $O((m+n)\log(2+n))$ preprocessing for one head, $O(1)$ rational operations per candidate, and $O(n+m)$ storage. It takes a single shared backward pass and one forward pass per distinct queried head. A candidate outside the characterized gain range may have its best feasible offset at an interior point.

The [Lean least-radius construction](../SwitchedHybridControl/LeastRadius.lean) supplies the underlying comparison theorem. The graph algorithm and its complexity proof below extend this result. The Python example and rational tests can be run from this directory.

## Normalize the original feasible model

Let $B$ be the pointwise least radius satisfying the original constraints and floors, and $C\ge B$ be the finite upper budgets. Let $g_v>0$ be a supplied gauge such that original gains $a_e$ obey $a_e g_u/g_v\le1$. For a candidate added to the existing model, every feasible radius still satisfies $r\ge B$. Put $x_v=(r_v-B_v)/g_v$ and $K_v=(C_v-B_v)/g_v$. The resulting bounded feasible region is

$$
0\le x_v\le K_v,\qquad x_v\ge \alpha_e x_u- s_e,
\qquad \alpha_e=\frac{a_e g_u}{g_v}\in[0,1],\quad
s_e=\frac{B_v-b_e-a_e B_u}{g_v}\ge0.
$$

The algorithm also applies to any feasible $B$ when the application requires all revised radii to be at least $B$. For a same-gain increase of an existing offset, retaining the original arc is harmless because the revised arc implies it. An arbitrary replacement can use this result when the new inequality implies the removed one over the permitted radius interval. Otherwise, preprocess the graph with that arc removed and use its least baseline, or impose a no-decrease requirement explicitly. Claiming feasibility over the original lower floors using an arbitrary feasible baseline could miss solutions.

The normalized candidate inequality is $x_h\ge\beta+\gamma x_u$, with $\gamma=a g_u/g_h\ge0$ and $\beta=(b+a B_u-B_h)/g_h$. Its gain need not satisfy the original gauge bound. The theorem is about bounded invariant radii. The derivative test also applies to some candidate gains that would put the enlarged model outside the strictly contractive setting.

## Passes and the exact gain range

**Backward pass.** For every original positive-gain arc $u\to v$, the upper bound $x_v\le z$ implies the bound $x_u\le(z+s_e)/\alpha_e$. The reverse map is increasing and at least $z$ on nonnegative inputs. Run multi-source min-Dijkstra backwards, initially setting every label to its local budget $K_v$. The final labels $U$ are the pointwise greatest feasible vector. Each label is sound by its path to an original budget. The absence of relaxations proves that $U$ itself satisfies the positive-gain inequalities. Zero-gain inequalities already follow from $x\ge0$ and need no reverse arc. Retaining each improving edge gives a path to a budget attaining $U_v$.

**Forward pass at the selected head.** For $0\le t\le T=U_h$, let $Y(t)$ be the least vector satisfying the original edge inequalities, nonnegativity and $x_h\ge t$. The vector $U$ is an admissible upper bound on this closure, so $Y(t)$ lies inside the budgets. Every original edge map is increasing and weakly reduces nonnegative labels. Forward max-Dijkstra seeded at $h$ with $t$ therefore computes $Y(t)$. A nonpositive intermediate label can be discarded because it cannot lead to a positive label. The values are also the maximum of zero and the composed affine maps over original simple paths from $h$. Removing a cycle from a path whose final value is positive can only improve that value. The empty path gives $Y_h(t)=t$.

When $T>0$, compute both $Y(T)$ and $p_u=Y'_{u,-}(T)$ in the same pass. A path reaching $u$ has value $A_P T-D_P$ and slope $A_P=\prod_{e\in P}\alpha_e$. Among paths tied for the largest value, choose the *smallest* slope, including the constant zero branch. This is the branch that is maximal immediately to the left of $T$. Equivalently, propagate a lexicographic key $(z,-p)$, ordered from large to small. An arc maps it to $(\alpha_e z-s_e,-\alpha_e p)$. This map is order-preserving and never improves a live input key. If $z>0$ and the first component stays equal, then $\alpha_e=1$ and $s_e=0$, so the entire key stays equal. Zero labels already have slope zero. Strict improvements consequently give the ordinary Dijkstra finalization argument and a predecessor forest even with unit gains, zero slack, ties, loops or parallel arcs. Set $p_u=0$ for all $u$ when $T=0$, since the head has just one feasible value.

**Margin theorem.** For candidate tail $u$ and gain $\gamma$, the head-maximal assignment $Y(T)$ attains the exact support value
$$
\max_{x\text{ original feasible}}(x_h-\gamma x_u)
  = T-\gamma Y_u(T)
$$
if and only if $T=0$ or $\gamma p_u\le1$. Indeed, for each $t\in[0,T]$ the maximizer conditional on $x_h=t$ can take $x=Y(t)$, since it minimizes $x_u$. The objective reduces to $t-\gamma Y_u(t)$. The path of slope $p_u$ selected at $T$ is a global lower bound
$Y_u(t)\ge Y_u(T)-p_u(T-t)$. Thus
$$
t-\gamma Y_u(t)\le T-\gamma Y_u(T)-(1-\gamma p_u)(T-t).
$$
Conversely, for $T>0$ the finite piecewise-affine envelope equals the selected line immediately left of $T$. If $\gamma p_u>1$, the objective is strictly better there. The proof also handles the constant zero branch.

For any number of candidates $u_i\to h$ with gains in this range, the full joint feasible offset region is the product of half-lines
$\beta_i\le T-\gamma_i Y_{u_i}(T)$. Necessity holds for each candidate, and the *same* radius assignment $Y(T)$ simultaneously witnesses all the inequalities at their maximum offsets. After the preprocessing, a $k$-candidate batch costs $O(k)$ arithmetic operations to check. If feasible, it shares the stored witness. For a common tuning knob that adds $d_i\lambda$ to normalized offsets, with $d_i>0$, the maximum knob value is the minimum of the individual offset margins divided by $d_i$.

The endpoint test includes every candidate for which $\gamma_i$ times the largest original $h\to u_i$ path gain is at most one. This sufficient condition can use the old return path rather than the maximum single edge gain. The endpoint test can be strictly more permissive. For example, take original paths with transfers $t/2-1$ and $3t/10$ from $h$ to $u$, and $T=5$. Both arrive with value $3/2$, so the left slope is $3/10$. Candidate gain $3$ passes the exact test even though it exceeds the largest-return-gain criterion. In contrast, with just $t/2-1$ and $T=10$, candidate gain $3$ has optimum offset $2$ at $t=2$, while the endpoint value is $-2$.

Different queried heads can interact. Even with no original edges and two unit budgets, the two opposite candidate arcs with gain $1/2$ and offset $3/4$ are individually feasible and jointly infeasible. Independent profiles answer independent what-if queries or batches whose additions share a head.

## Certificates

For a supported candidate exceeding its margin, the forward forest supplies a path $P$ from $h$ to $u$ with bound $x_u\ge p x_h-d$, where $p=p_u$. If the selected value is zero, take the bound $x_u\ge0$ instead. The backward forest supplies a path $Q$ from $h$ to a budget vertex $w$, with gain $c>0$ and slack $d_Q$, satisfying $T=(K_w+d_Q)/c$. A path of length zero uses gain one and slack zero. The new arc and $P$ yield

$$
(1-\gamma p)x_h\ge\beta-\gamma d
  >(1-\gamma p)T,
$$

contradicting $x_h\le T$. A certificate is two references into the shared forests and the failed candidate. Materializing and checking the paths take $O(n)$ arithmetic operations in the worst case, or time proportional to their actual lengths. Forward predecessor edges point to earlier settlements, and reverse successor edges point to earlier reverse settlements, so these paths are simple.

This contradiction is a Farkas certificate. Write every row with a less-than-or-equal sign. Compose each path by adding edge rows with suffix-gain multipliers, giving the composed affine inequality. Add $\gamma$ times the $P$ bound to the candidate row. Add $(1-\gamma p)/c$ times the sum of the $Q$ bound and the budget row. The variable coefficients cancel and the right-hand side is strictly negative. When a zero branch uses $x_u\ge0$, this bound is itself an input under an explicit no-decrease contract. With a pointwise least baseline and strict original contraction, it can be derived from the original rows. Follow any tight predecessor policy from $u$. A tight floor ends the path. A tight cycle of gain $q<1$ gives $x_j\ge qx_j$ in shifted coordinates, hence $x_j\ge0$ at its root. A zero-gain tight edge also gives a direct zero bound. Transport this bound down the tight path to $u$. This derives the auxiliary row with a nonnegative linear combination. The small prototype emits the two-path format in normalized coordinates.

## Common-tail batches

A separate exact check applies when the candidates all leave one tail $u$, with fixed gains and offsets. Let $M_{vu}$ be the greatest product of original edge gains along a path from $v$ to $u$, with zero for no path and one for the empty path. Assume $\gamma_i M_{v_i u}\le1$ for each added arc $u\to v_i$. This holds automatically if every new normalized gain is at most one. Larger gains can be checked by a reverse max-product pass.

Any feasible tail value is at most
$$
T=\min\left(U_u,\min_{i:\gamma_i>0}\frac{U_{v_i}-\beta_i}{\gamma_i}\right).
$$
Reject any candidate with $\beta_i>U_{v_i}$ since $x_u\ge0$. Given $s\in[0,T]$, seed every candidate head with $\beta_i+\gamma_i s$ and let $Z(s)$ be the least original closure above those seeds and zero. The seeds are within $U$ and hence $Z(s)\le U$. The function $Z_u(s)$ is a maximum of zero and finitely many affine functions of slope $\gamma_i A_P\le1$, using the same path argument as above. Thus $Z_u(s)-s$ is nonincreasing. If some feasible vector has $x_u=s$, it supplies $Z_u(s)\le s$, and hence $Z_u(T)\le T$. Conversely, when $Z_u(T)\le T$, the vector $Z(T)$ satisfies all old and new inequalities, because the new demands into it were evaluated at $T\ge Z_u(T)$. This gives a shared feasible witness for a batch with several heads.

Each common-tail batch needs only one multi-seed forward pass after its ceiling calculation, apart from the optional gain check. If the test fails within its gain range, a candidate head and budget path certify a failed ceiling test, or the active seed at $u$ gives a feedback lower bound contradicting the path-supported upper ceiling. The prototype returns the witness or a rejection in this case.

## Cost, prior algorithms and validation

Indexed heaps have at most one live key per vertex. Each pass scans each edge at most once and runs in $O((m+n)\log(2+n))$ arithmetic operations, or $O(m+n\log(2+n))$ with a Fibonacci heap. The Python implementation uses ordinary heaps with stale entries, taking $O((m+n)\log(2+n+m))$ arithmetic operations. A single head profile takes $O(n)$ additional storage. With input rationals of at most $L$ bits after normalization, each selected path has $O(n)$ edges. The composed affine values and gain products have $O(n(L+\log(2+n)))$-bit representations. The preprocessing is strongly polynomial in arithmetic operations and polynomial in bit complexity. Exact comparisons and products are not constant-time at the bit level. The code assumes the original least radius and gauge are already supplied, as is appropriate for independent what-if queries around a verified design.

Forward and reverse label setting use FIFO shortest-path machinery, and affine path composition predates this construction. Orda and Rom treat time-dependent shortest paths, while Foschini, Hershberger and Suri study the full arrival profile and minimum-delay interval queries. A fixed-time forward pass is a standard primitive. The margin computation uses it only at the maximum feasible head, with a coherent left-slope tie break. The resulting simultaneous support region concerns *maximization* of a concave affine-feedback objective, and the full time profile is unnecessary. [Orda and Rom, JACM 1990](https://sites.cs.ucsb.edu/~suri/cs231/Rlist/ordaRom.pdf) · [Foschini, Hershberger and Suri, SODA 2011, §§4–5](https://sites.cs.ucsb.edu/~suri/psdir/soda11.pdf)

This is also a monotone two-variables-per-inequality system. Generic solvers cover the one-shot feasibility test and wider gains. Cohen and Megiddo derive forward and inverse pushes, characterize extreme bounds, and use path and cycle certificates. Karczmarz addresses general static monotone 2VPI and deterministic discounted MDPs. Dadush and coauthors give a strongly polynomial label-correcting algorithm that uses Dijkstra-type steps for deterministic MDPs. Those solve for values or feasibility without a supplied least feasible baseline or a shared-head query workload. Howe, King and Simon maintain complete two-variable projection representations under general insertions, with an $O((n^2+m^2)\log m)$ insertion bound on an already closed system. They materialize more information than the single endpoint and its supporting paths used here. The TVPI abstract-domain application uses pair projections for sound entailment, alongside integer approximation and program-transfer operations. Ramalingam and coauthors give bounded incremental algorithms for unit-gain difference constraints. The contribution here is the exact gain test for a single common optimizing assignment, with constant arithmetic per new candidate once the two forests have been computed. The sources surveyed did not give this workload-specific profile. [Cohen and Megiddo, SICOMP 1994](https://epubs.siam.org/doi/10.1137/S0097539791256325) · [Karczmarz, SODA 2022](https://arxiv.org/abs/2110.15070) · [Dadush et al., ESA 2021](https://doi.org/10.4230/LIPIcs.ESA.2021.36) · [Howe, King and Simon, TCS 2019](https://openaccess.city.ac.uk/id/eprint/21241/) · [Simon, King and Howe, TVPI abstract domain](https://kar.kent.ac.uk/30678/1/tvpi-rev.pdf) · [Ramalingam et al., Algorithmica 1999](https://cris.huji.ac.il/en/publications/solving-systems-of-difference-constraints-incrementally/)

[feedback_margins.py](feedback_margins.py) uses only the Python standard library. Run `python3 feedback_margins.py` for the application’s two-mode graph. The original transfers are $A\to B:r\mapsto1+2r$ and $B\to A:r\mapsto1+r/8$, with the original least radii $(3/2,4)$ and gauge $(1,4)$. With budgets $(5/2,16)$, the greatest feasible head $B$ is $12$ because its return transition reaches the budget at $A$. The largest physical offset on the gain-two arc into $B$ is $7$, attained at $(5/2,12)$. Run `python3 feedback_margins.py --gain 2 --offset 8` to display a rejection. Gains outside the exact profile range produce an unsupported-query message and exit status 2.

[feedback_margins_check.py](feedback_margins_check.py) independently enumerates the vertices of small rational polyhedra and compares exact support values, including the failure of the endpoint criterion outside its range. It checks 3,712 exact margins and two-path rejection certificates, simultaneous common-head assignments for 300 graphs, and 300 common-tail decisions.
