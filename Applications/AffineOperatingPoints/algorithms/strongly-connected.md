# The spectrum of a strongly connected max-affine graph

For a finite strongly connected graph with at least one incoming branch at every vertex, the spectrum is **one level, a closed upper ray, or all of $\mathbb R$**. One rational LP and a graph traversal identify which case holds. In particular, a strongly connected network with gains $2$ and $3$ has every real level as an eigenvalue. The disconnected spectra from the [inverse compiler](inverse-spectrum.md) require loss of strong connectivity.

A branch $e:u\to v$ contributes $a_e x_u+b_e$ to $F_v(x)$, with $a_e\ge0$. The spectrum consists of levels $\lambda$ admitting a finite real solution to $F(x)=x+\lambda\mathbf 1$. Check strong connectivity in the full branch graph, including zero-gain branches. A finite floor supplies a zero-gain branch with the same endpoints as its edge.

## The classification

Let $P_\lambda$ be the relaxed system $x_v\ge a_e x_u+b_e-\lambda$ on every branch. Seek a positive scale $h$ with $h_0=1$ and $a_e h_u=h_v$ on all branches. The answer is determined by the scale and the relaxation cutoff.

| Positive scale | Relaxation levels | Spectrum |
| --- | --- | --- |
| Exists | $[\lambda_*,\infty)$ | $\{\lambda_*\}$ |
| Absent | $[\lambda_*,\infty)$ | $[\lambda_*,\infty)$ |
| Absent | $\mathbb R$ | $\mathbb R$ |

**When the scale exists.** All branches are positive and every cycle has gain product one. Conversely, if every branch is positive and every cycle has product one, the gain on a path from vertex $0$ to $v$ is independent of the path. Append a common return path to compare the resulting closed walks. These path gains give $h$. Compute them along a spanning traversal and check every branch.

In coordinates $x_v=h_v z_v$, the relaxed rows are difference constraints with branch weights $(b_e-\lambda)/h_v$. They are feasible exactly when every cycle has nonpositive weight. Sufficiency follows by assigning each vertex the largest weight of a walk ending there, allowing a zero-length start at any vertex. Removing nonpositive cycles reduces this computation to paths. Thus
$$
\lambda_*=\max_{C}
 \frac{\sum_{e:u\to v\in C} b_e/h_v}
      {\sum_{e:u\to v\in C} 1/h_v},
$$
where simple directed cycles suffice. At $\lambda_*$, a maximizing cycle has all its edges tight at any feasible potential. That cycle can support a finite eigenvector by the descent argument below. At an eigenvector, choosing a tight incoming branch at every vertex gives a tight cycle. Its weight is zero, so the level equals the largest weighted cycle mean. For ordinary unit gains the scale is all ones and the ratio is the usual maximum cycle mean.

**When there is no scale.** Every feasible relaxation yields an eigenvector. A zero-gain branch gives an absolute lower bound at its head. From that head, reach any vertex along a path in the full graph. If the path includes another zero-gain branch, start at the head of its last such branch and use the positive suffix. With no zero-gain branches, failure of the scale test means some cycle has product different from one. A contracting cycle gives an absolute lower bound by composing its inequalities. These bounds propagate to the entire graph. [Reachable lower bounds in Lean](../../../Maths/Multitubes/MaxAffine/ReachableLowerBounds.lean)

For an expansive cycle, the composed inequality instead caps its vertices above. Every vertex can reach that cycle by positive branches, so the cap propagates backwards to every vertex. The relaxed feasible set is closed under coordinatewise maximum. Maximizing the sum therefore gives its greatest element $U$. Every vertex has an outgoing branch tight at $U$. Otherwise one could increase that coordinate slightly and preserve all constraints, since the outgoing rows would have positive slack and the other incoming rows can only improve. Following tight outgoing branches gives a directed tight cycle. [Upper potentials and tight cycles](affine-spectrum.md)

In each case start the iteration $x\mapsto F(x)-\lambda\mathbf1$ at a feasible upper potential. It descends by monotonicity. If there is a tight cycle at the starting potential, its coordinates stay fixed during descent. Each lower bound or fixed coordinate supplies a finite lower bound along paths. The finite maximum defining each coordinate is continuous, so the descending limit is an eigenvector.

## One LP for the cutoff

Use the normalized gain-flow polytope
$$
p_e\ge0,\qquad \sum_e p_e=1,\qquad
\sum_{e:\,u\to v}p_e=\sum_{e:\,v\to w}a_e p_e\quad\text{for every }v.
$$

If it is empty, every level is relaxed-feasible. Otherwise maximize $\sum_e b_e p_e$ on this compact polytope. Its maximum is the exact cutoff $\lambda_*$, and the relaxed set includes the cutoff. These are the normalized branch-certificate threshold and compactness results in Lean. In the scaled case, putting $q_e=h_v p_e$ on $e:u\to v$ makes $q$ an ordinary circulation. Decompose $q$ into cycles. The objective becomes a weighted average of the cycle ratios above, so the same LP computes the weighted maximum without enumerating cycles. [Normalized threshold duality](../../../Maths/Multitubes/MaxAffine/Duality.lean) · [Compact certificates and the least relaxation level](../../../Maths/Multitubes/MaxAffine/LeastEigenvalue.lean)

The graph checks, scale search and LP construction take $O(n+m)$ graph and rational operations. A scale entry is the product along a simple path and uses $O(nL)$ bits if individual gains have at most $L$ bits. The LP has $m$ variables, $m$ nonnegativity constraints and $n+1$ equality rows, with $O(n+m)$ sparse entries. This is one call to rational linear optimization. The normalization couples the branch variables, so the fixed-level solver's two-variable-per-inequality bound does not apply to this LP. The prototype uses Z3 rational arithmetic. The full three-shape statement and solver have the written proofs here and executable checks.

When every gain exceeds one, the balance equations and mass-one condition are incompatible: summing over vertices would give $1=\sum_e a_e p_e>1$. No scale exists either. This proves the gains-$2,3$ consequence for strong connectivity.

## Examples and use

- **All real levels.** For $F(x_0,x_1)=(2x_1,3x_0)$, the vector $(3\lambda/5,4\lambda/5)$ works at every $\lambda$.
- **Upper ray.** For $F(x_0,x_1)=(\max(2x_0,0),x_0/2)$, take the constant branch from vertex $1$ into vertex $0$. The graph is strongly connected with that branch, and the spectrum is $[0,\infty)$. The vector $(\lambda,-\lambda/2)$ works throughout that ray.
- **Singleton with unequal gains.** For $F(x_0,x_1)=(2x_1+3,x_0/2+1)$, the scale is $(1,1/2)$ and the only level is $5/3$. An eigenvector is $(0,-2/3)$.

The two-gain inverse example has a gap $(-1,1)$ for
$F(x,y)=(\max(2x,3x),\max(3y,2x+1/2))$. Add the return branch $2y$ to the first maximum.
The new graph is strongly connected and its spectrum is all of $\mathbb R$.
At level zero one eigenvector is $(-1/3,-1/6)$.

Run `python3 strongly_connected_spectrum.py --input graph.json` with `z3-solver` installed. The input uses the same branch arrays as the [fixed-level solver](affine-spectrum.md). Each array contains the tail, head, gain and offset. If present, the `level` field is ignored by the classifier and can be used by the fixed-level solver on the same file.

```json
{"vertices": 2, "level": "5/3", "branches": [[1, 0, 2, 3], [0, 1, "1/2", 1]]}
```

This returns `{"kind":"singleton","cutoff":"5/3","scale":["1","1/2"]}`. An upper ray has kind `upper_ray` and an empty scale. An all-real spectrum has kind `all_real`, a null cutoff and an empty scale. The independent checker eliminates all potential coordinates from the eigen-equation and the relaxation inequalities and verifies the claimed sets over all real levels on 41 graphs, including parallel branches, single-vertex graphs, and connectivity through a zero-gain branch. [Classifier](strongly_connected_spectrum.py) · [All-level checker](strongly_connected_spectrum_check.py)
