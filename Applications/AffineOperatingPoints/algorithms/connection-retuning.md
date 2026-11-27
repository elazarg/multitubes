# One-connection repair of a missing operating level

A max-affine network can miss a prescribed operating level even though all relaxed inequalities are feasible. For a network with gains strictly above one, one calibration query asks whether an added connection $u\to v$ of given gain $a>1$ can restore that level, and which intercepts $b$ work. Preprocessing uses one rational LP and graph searches. Each candidate gains an exact answer in constant many rational operations. A repairing set can consist of two disjoint closed rays, so testing one cutoff or assuming that a stronger connection always helps gives the wrong answer.

Assume every vertex has an incoming branch and an outgoing branch, and that the original network has no operating point at the given level $\lambda$. Each branch $e:i\to j$ has gain $a_e>1$ and intercept $b_e$, contributing $a_e x_i+b_e$ to the maximum at $j$. The new connection contributes $a x_u+b$ to the maximum at $v$. Parallel branches and loops are allowed.

## Diagnose the source components

Write $\phi_e(z)=a_ez+b_e-\lambda$. The relaxed inequalities are $x_j\ge\phi_e(x_i)$. Let $U$ be their greatest simultaneous solution, and let $J$ be the vertices on cycles of edges tight at $U$. Call an original source strongly connected component *uncovered* if it contains no vertex of $J$. A source component has no incoming edge from another component.

If there is more than one uncovered source, every candidate fails. If there is exactly one, say $S$, **the added connection must enter $S$**. For each tail $u$, the full answer is then given by the table below. The quantities in it use only the original network at level $\lambda$.

For each vertex $j$, let
$$
T_j(u)=\max_{P:j\leadsto u}\phi_P(U_j).
$$
Here $\phi_P$ is the forward composition along an old walk. Include the empty walk and take $T_j(u)=-\infty$ when there is no such walk. Otherwise the maximum is attained on a simple path. For each covered source $Q$, its threshold is $\min_{j\in Q\cap J} T_j(u)$. Define
$$
H_u=\max_{Q\text{ covered source}}\ \min_{j\in Q\cap J} T_j(u),
\qquad
A_u=\min_{j\in J:\ S\leadsto j\leadsto u} T_j(u).
$$
The empty maximum is $-\infty$ and the empty minimum is $+\infty$. Let $U^t$ be the greatest old solution subject to $x_u\le t$. For the candidate head $v\in S$, put $D=T_v(u)$ and $B_0=U_v+\lambda$.

| Condition on the tail and head | All repairing intercepts $b$ |
| --- | --- |
| $H_u$ finite | $(-\infty,\ U^{H_u}_v+\lambda-aH_u]$ |
| $H_u=-\infty$ and $A_u=+\infty$ | $[B_0-aD,\ \infty)$ |
| $H_u=-\infty$ and $A_u\le D$ | $\mathbb R$ |
| $H_u=-\infty$ and $D<A_u<+\infty$ | $(-\infty,\ B_0-aA_u]\ \cup\ [B_0-aD,\ \infty)$ |

When $H_u=-\infty$, the tail is reachable only from $S$ among the original sources, so $D$ is finite. If candidate edges have fixed installation costs and a price per unit departure from a nominal intercept, clamp that nominal intercept to each returned interval and take the least total cost. Scanning $k$ candidates takes $O(k)$ rational operations after preprocessing.

## Why the diagnostic works

The original relaxed inequalities have a feasible constant vector with sufficiently negative entries because all gains exceed one. Every vertex can reach an expansive cycle by following outgoing edges. Composing its inequalities gives an upper bound at the cycle, and applying inverse branch maps along a path bounds every vertex reaching it. The relaxed polyhedron is closed under coordinatewise maxima. Maximizing the sum of its coordinates therefore gives the simultaneous greatest solution $U$. These arguments also apply after adding the branch. They apply under a fixed cap $x_u\le t$ because shifting any old feasible vector down by a nonnegative constant preserves feasibility. In particular, every cap has a greatest solution $U^t$.

At a greatest relaxed solution, a finite operating point exists exactly when each source component contains a tight cycle. For necessity, trace selected tight predecessors of an operating point inside a source until they repeat. Each cycle has gain product above one, so equality on it attains its cycle upper bounds, which also have to be attained at the greatest solution. For sufficiency, select a tight cycle in each source. Start at the greatest solution and iterate the map $F(x)-\lambda\mathbf 1$. Monotonicity makes the iteration decreasing. The selected cycle coordinates stay fixed. Paths from their vertices supply finite lower bounds for the other coordinates, and continuity then makes the limit an operating point. This specializes the criterion using tight cycles and reachable bounds. [Fixed-level criterion and proof](affine-spectrum.md) · [Reachable lower bounds in Lean](../../../Maths/Multitubes/MaxAffine/ReachableLowerBounds.lean)

### Replace the new branch by a cap

For a fixed candidate $u\to v$ and gain $a$, associate to a cap $t$ the intercept
$$
b(t)=U^t_v+\lambda-at.
$$
Increasing the cap by $\Delta\ge0$ can only increase $U^t_v$, and it increases it by at most $\Delta$. The latter bound follows by shifting the less constrained potential down by $\Delta$ to meet the tighter cap. Thus $b(t)$ is continuous, strictly decreasing and onto $\mathbb R$, with absolute change of at least $(a-1)|\Delta|$.

The greatest relaxed solution after adding a branch of intercept $b(t)$ is exactly $U^t$. This vector satisfies the new branch because $U^t_u\le t$. If another solution $x$ to the augmented inequalities had $x_u=s>t$, then $x\le U^s$ and the new inequality would imply $b(t)\le U^s_v+\lambda-as=b(s)$, a contradiction. Hence every augmented solution meets the cap and is dominated by $U^t$. For $t\le U_u$, shifting $U$ down by $U_u-t$ proves $U^t_u=t$ and the added branch is tight. For $t>U_u$, the new branch is slack.

### Find which cycles survive

A vertex keeps its old reading at the cap exactly when $t\ge T_j(u)$. In fact the old walk inequalities give
$$
U^t_j=\min\left(U_j,\ \inf_{P:j\leadsto u}\phi_P^{-1}(t)\right).
$$
The infimum over no walks is $+\infty$. All capped vectors obey these upper bounds. Conversely, the vector on the right obeys the cap by the empty path. It obeys every old inequality by prepending the branch to walks and by using the corresponding inequality at $U$ when the bound at the head is its old reading. Its coordinates are finite because the uniformly shifted $U$ satisfies all bounds. To see why a finite $T_j(u)$ is attained, transport $U_j$ along a walk. Every reading stays below the corresponding entry of $U$. An expansive cycle applied at any such reading returns a value at most as large as the reading: its fixed point is an upper bound for $U$ at its base. Removing cycles can only improve the final reading.

An old tight cycle survives at $U^t$ exactly when any one of its vertices retains its reading at $U$. Indeed the cycle fixes universal upper bounds at its vertices, and equality in the composed bound forces every branch in the cycle tight. The same argument shows that a cycle made entirely of old edges cannot become tight for the first time after addition, since the new greatest solution is at most $U$. Consequently each old covered source that remains a source requires $t$ at least the minimum of $T_j(u)$ over its cycle vertices.

An old source whose component does not contain $v$ still has no incoming edge. It cannot merge with another component and gains no new internal cycle. This proves the impossibility test for multiple uncovered sources or an added head outside $S$. All old covered sources remain sources when $v\in S$, and their joint requirement is $t\ge H_u$.

If any covered source can reach $u$, then it can reach $v$ by the added branch. Even when the added branch closes a directed cycle, the component containing $S$ now has a separate upstream source. It needs no tight cycle of its own. This is precisely the case $H_u$ finite, and the cap inequality gives the first row of the table.

Otherwise only $S$ can reach $u$ among the old sources. The new branch merges exactly the components on old paths from $S$ to $u$, and the merged component is still a source. No additional source component can appear, because every vertex was already reachable from some old source. The merged source has a surviving old tight cycle exactly when $t\ge A_u$, interpreted as impossible if $A_u=+\infty$.

A tight cycle using the new branch exists exactly when $t\le D$. If $t<D$, then $U^t_v<U_v$. In this case the inverse walk bound for $v$ is attained on a path. For an inverse cap bound at or below $U_v$, cycle deletion preserves or improves the bound, since from its starting reading deleting a cycle can only increase the walk's ending reading. One can therefore take a simple path. Along a minimizing path the transport of $U^t_v$ ends at $t=U^t_u$, forcing its edges tight, along with the new branch. If $t=D$, take a path realizing $T_v(u)$, which transports $U^t_v=U_v$ to $t$ and again forces equality along the path. If $t>D$ and the new branch is tight, a tight return path would transport $U^t_v=U_v$ to $t$, which exceeds $T_v(u)$. Thus the merged source requires $t\le D$ or $t\ge A_u$. At $D$ and every larger finite cap the coordinate $U^t_v$ is $U_v$, giving the closed intercept endpoints in the table.

## Preprocessing and query cost

Let $s_e=U_j-\phi_e(U_i)\ge0$ for branch $e:i\to j$. Expressing a reading by its deficit from $U$ makes forward transport the map $z\mapsto s_e+a_e z$. On nonnegative deficits it is monotone and never decreases the deficit. The smallest deficit at each destination from a vertex with initial deficit zero is therefore computed by Dijkstra's label-setting rule. Subtract the resulting deficits from $U$ to get $T_j$.

To compute $U^t$, instead start at $u$ with deficit $\max(0,U_u-t)$ and propagate backwards with the map $z\mapsto\max(0,(z-s_e)/a_e)$. It is monotone and never increases the deficit, so the analogous maximum-priority label-setting rule gives the largest deficit required at every vertex. By the walk formula these values give $U^t$ on subtracting them from $U$.

Each run settles each vertex at most once. Group parallel branches by neighbor and optimize over that group before pushing a candidate, so the lazy queue gets at most one insertion per ordered vertex pair in a run. Its size is $O(n^2)$ even on a multigraph, and one pass takes $O((n+m)\log(n+1))$ rational operations. Compute forward rows for the cycle vertices used in $H_u$ or $A_u$ and for the possible heads in $S$. Compute one reverse row for each tail with finite $H_u$, storing only the head entries. The preprocessing costs one $n$-variable, $m$-inequality rational LP and $O(n(n+m)\log(n+1))$ arithmetic and comparison operations, with $O(n^2+m)$ storage. Each walk formula can use a simple path, so transported rationals grow by at most a polynomial bit length from the input and the initial rational LP solution. Each candidate uses a constant number of lookups and rational operations.

## Examples and run instructions

Take three channels $x,y,z$ with outputs
$$
F(x,y,z)=(\max(2x,3x),\ \max(2y,2x),\ \max(3z,2x+2)).
$$
The original operating levels are $(-\infty,-4]\cup[4,\infty)$. The root equation fixes $x=\min(\lambda,\lambda/2)$, and the sink self-loops give $y\le\lambda$, $z\le\lambda/2$. The relaxed interchannel constraints at those sink caps reduce to $x\le 3\lambda/4-1$ and $x\le\lambda$. The sink caps make their loops tight.

At $\lambda=0$ the greatest relaxed reading is $(-1,0,0)$. Add the connection $2y+b$ to the first channel. The original root is the sole uncovered source. The return path from $x$ transports its reading $-1$ to $-2$ at $y$. The loop at $y$ is a possible old pin and keeps its reading if the cap is at least $0$. Thus $D=-2$, $A_y=0$, and the answer is **$(-\infty,-1]\cup[3,\infty)$**. At low intercepts the old loop at $y$ supplies a pin to the merged source. At high intercepts the new two-edge cycle supplies the pin.

Add a fourth channel $p$ with output $2p$ and an additional input $2p-3$ at $y$. The added connection $2y+b$ can now repair the level for **$b\le9/2$**. The source at $p$ reaches $y$ and hence reaches the merged component after insertion. It keeps its pin exactly when $t\ge-3$. At that cap the greatest reading of $x$ is $-3/2$, giving $b(-3)=9/2$.

Run the following with Python and `z3-solver` installed. The branch arrays give tail, head, gain and intercept. The candidate arrays give tail, head and gain. Rational numbers may be integers or strings such as `"3/2"`. Each output interval is a pair of inclusive endpoints, with `null` for an infinite endpoint. An empty array denotes impossibility for that candidate.

```json
{
  "vertices": 3,
  "level": 0,
  "branches": [[0,0,2,0], [0,0,3,0], [1,1,2,0], [2,2,3,0], [0,1,2,0], [0,2,2,2]],
  "candidates": [[1,0,2], [1,2,2]]
}
```

`python3 connection_retuning.py --input graph.json` returns `{"bad_sources":[[0]],"intercepts":[[[null,"-1"],["3",null]],[]]}`. The independent checker uses rational linear quantifier elimination of all original reading variables with the intercept left free. It compares sets over every real intercept and verifies the original example's operating levels over all real $\lambda$. [Query index](connection_retuning.py) · [Independent checker](connection_retuning_check.py)
