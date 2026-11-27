# Restart phases for zero-drift buffer schedules

A machine can switch among a finite set of controller states. Each permitted transition adds or removes material from one or more buffers. The equipment must repeat a legal sequence indefinitely, starting with specified stock, and the same restart phase must work for every allowed calibration. The algorithm returns the exact stock extrema at a requested phase and all restart phases that satisfy the capacities, even when the period is far too long to list.

## Model and guarantee

Use a finite directed multigraph with $n$ vertices and $m$ distinguishable edges. Each edge $e$ adds a vector $w_e(\theta)$ to stock. Its $d$ coordinates are affine functions of a **single fixed but unknown** calibration $\theta$ in a rational box $[\ell,u]\subseteq\mathbb R^b$. Store the integer constant and $b$ integer coefficients per coordinate. Rational coefficients can be put in common integer units, scaling the stocks and capacities too. Capacities apply at every transition boundary.

Write $B$ for the incidence matrix and $W$ for the matrix of flattened charge coefficients. Given reachable multiplicities $x\in\mathbb Z_{\ge0}^m$ with $x\ne0$, $Bx=Wx=0$ and weakly connected positive support, the construction produces a closed period at any requested vertex in that support. It uses each edge exactly $x_e$ times. The period may have $P=\sum_e x_e$ events, but its representation uses at most $Q=2mn$ stored edge references and at most $m$ words with a binary repeat count greater than one.

For the period so constructed, fix starting stock $s$, lower and upper capacities $L,U$, and an optional set of legal restart vertices. The algorithm returns every admissible phase in $[0,P-1]$ as at most $Q$ disjoint finite arithmetic progressions. A phase is admissible when starting there with stock $s$ respects $[L,U]$ forever for every $\theta$. After building the index, the query takes $O(Qd)$ arithmetic operations for known charges or $O(Q^2d(b+1)\log(b+2))$ for box uncertainty. The arithmetic operation count is independent of the expanded period length $P$. The bit cost still depends on the sizes of inputs and intermediate rationals, including the binary repeat counts. No step enumerates calibration corners.

## From the Lean theorem to a period

`exists_boundedDiscrepancy_iff_reachableConnectedIntegerCirculation` equates existence of an offline bounded-discrepancy walk with existence of a reachable connected integer circulation with zero charge. `ConnectedIntegerCirculation.exists_closedWalk_exactMultiplicity_at` realizes the exact counts at any incident base. Apply the results with the **coefficients** as the integer-lattice coordinates. Repeating a word of zero coefficient-wise charge brings every buffer back to its initial stock at every calibration. For a full-dimensional calibration box, bounded stock for one infinite schedule at each calibration also bounds its prefix coefficient vectors: evaluate them at $b+1$ affinely independent calibrations and invert that fixed evaluation matrix. The repeated-configuration direction of the lasso theorem then applies. Substitute fixed calibration coordinates beforehand if the box has zero-width sides. [ZeroChargeLasso.lean](../../../Maths/Graph/ZeroChargeLasso.lean) · [EulerianTrail.lean](../../../Maths/Graph/EulerianTrail.lean)

**Find counts if needed.** In each reachable strongly connected component, consider the rational cone $Bx=Wx=0$, $x\ge0$. Its maximum support contains precisely the edges $e$ for which $x_e\ge1$ is feasible, since the cone is homogeneous. Add one witness per such edge to get a vector positive exactly on that support. A nonnegative balanced vector decomposes into directed cycles, so no positive edge crosses between the strongly connected components of its support. If the support has more than one component, repeat the test inside each component. Every connected witness survives the restriction in one branch. An empty support closes that branch and a nonempty strongly connected support gives a witness by clearing denominators. This takes polynomially many rational LP calls. The reference implementation uses exact phase-I simplex for small graphs, with the usual exponential worst case. It also accepts externally supplied counts. Kosaraju and Sullivan already gave a polynomial algorithm for zero-circuit detection. [Kosaraju and Sullivan, STOC 1988](https://doi.org/10.1145/62212.62251) · [Velner et al., Lemma 3 and §4](https://lsv.ens-paris-saclay.fr/~doyen/papers/The_Complexity_of_Multi-Mean-Payoff_and_Multi-Energy_Games.pdf)

Connectivity matters even when the input graph itself is strongly connected. Put charge $(1,0)$ on a loop at one vertex and $(-1,0)$ on a loop at another, with an edge of charge $(0,1)$ in each direction between the two. Equal counts of the two loops solve the equations, but any walk that visits both vertices acquires strictly positive second charge. Each isolated loop has nonzero charge too.

**Realize counts without expanding tokens.** Follow live edges until a vertex repeats. Subtract the minimum live count along that simple directed cycle and record the cycle with that repeat count. Each subtraction removes at least one edge, so there are at most $m$ recorded cycles of length at most $n$. The union of the cycles is the positive support. Connect the recorded cycles into a tree by shared vertices, rooted at a cycle containing the base. Traverse a cycle's plain copies together and insert its children into a single remaining copy, each child entered at the shared vertex. All insertions return to their entry. Each cycle contributes at most two written copies of its edges, one as the body of a power and one as part of the written-out splices. The output is a flat list of factors $v^q$, with $q=1$ permitted for an ordinary path. This gives a count-input construction of a linear path scheme of the kind used to preserve Parikh vectors in graph walks. [Blondin et al., JACM 2021, Lemma 4.10](https://www.cs.ox.ac.uk/people/christoph.haase/home/publication/befghlmt-21/befghlmt-21.pdf)

## Query a compressed period

For each written edge of a factor $v^q$, index the phase just before that edge. Across the copies these phases have positions $p+j|v|$ for $0\le j<q$, the same controller vertex, and prefix charge $A(\theta)+jD(\theta)$. Here $A$ is the prefix through the first copy up to that edge and $D$ is the charge of $v$. The index partitions the phases into at most $Q$ such progressions.

Let $C_t(\theta)$ be the prefix charge at phase $t$ of the unrotated word. Starting at $h$ with stock $s$, the stock at a visit to $t$ is $s+C_t(\theta)-C_h(\theta)$, including across the seam, by zero drift. At fixed $\theta$, for each destination progression the stock is affine in its copy index. Only the first and last copy of each progression can contribute extrema. This gives at most $2Q$ endpoint coefficient vectors to check. For any two endpoints or phases, a linear coefficient $a_i$ times $\theta_i$ contributes $\min(a_i\ell_i,a_i u_i)$ to the lower envelope and $\max(a_i\ell_i,a_i u_i)$ to the upper envelope. This computes the exact coordinatewise stock ranges for a fixed $h$. [Ben-Tal and Nemirovski, *Robust Solutions of Uncertain Linear Programs*](https://www2.isye.gatech.edu/~nemirovs/stablpn.pdf)

For a **candidate restart progression**, let its copy index $j$ vary. For each destination endpoint, buffer and capacity side, its worst signed violation has the form

$$
g(j)=\alpha+\beta j+\sum_{k=1}^b\max\{\ell_k(a_k+d_kj),u_k(a_k+d_kj)\}.
$$

Each summand is convex and switches between its two affine functions only at the zero of $a_k+d_kj$. Sort the at most $b$ interior breakpoints. Evaluate the function and its right slope at the left boundary, then sweep the affine pieces, increasing the slope by $|d_k|(u_k-\ell_k)$ at breakpoint $k$. On each piece, solve the single affine inequality $g(j)\le0$. Convexity ensures their union is an interval. Intersect with the copy-index bounds and round the endpoints inward to integers. Intersect the resulting intervals over endpoint vectors, buffers and both capacity sides to obtain at most one finite progression. Each constraint takes $O((b+1)\log(b+2))$ arithmetic operations.

The checker also uses an alternative search. The maximum of all the functions $g$ is convex, so its integer forward differences are nondecreasing. Binary searches locate a minimum and the two ends of its nonpositive sublevel interval. This alternative uses $O(Q^2d(b+1)(1+\log P))$ arithmetic operations.

When charges are known, precompute the global prefix extrema $M_i=\max_t C_{t,i}$ and $m_i=\min_t C_{t,i}$. All constraints reduce directly to $s_i+M_i-U_i\le C_{h,i}\le s_i+m_i-L_i$. Intersect these affine integer intervals within each progression.

## Example

Let $N=2^{80}$. Use transitions $a:0\to1$ of charge $0$, $b:1\to0$ of charge $1+\theta$, and $c:0\to0$ of charge $-N(1+\theta)$, with $\theta\in[-2,1]$. Take counts $(N,N,1)$. The implementation emits $(ab)^{N-1}cab$, with $2N+1$ events and five written edge references.

Start with stock $N$, capacity interval $[0,5N/2]$, and require controller state 1 at restart. In the long factor these phases are $2j+1$ with nominal prefix $j$, where $0\le j<N-1$. The two extremal nominal prefix values of the period are $-1$ and $N-1$. Applying the box interval to their difference from $j$ gives exactly $N/4-1\le j\le N/2-1$. The other phase at state 1, in the final copy of $ab$, has nominal prefix $-1$ and exceeds capacity at $\theta=1$. The output is the single progression with first term $N/2-1$, step $2$ and count $N/4+1$.

```python
from periodic_buffers import Edge, Progression, admissible_phases, index_period, realize

N = 2**80
edges = (Edge(0, 1, (0, 0)), Edge(1, 0, (1, 1)), Edge(0, 0, (-N, -N)))
index = index_period(edges, realize(edges, (N, N, 1), base=0))
phases = admissible_phases(
    index, inventory=(N,), limits=((0, 5*N//2),), box=((-2, 1),), allowed={1}
)
assert phases == (Progression(first=N//2 - 1, step=2, count=N//4 + 1),)
```

## Scope and verification

The capacity result concerns the order of the constructed word. On one vertex with $N$ copies of each of charges $+1$ and $-1$, grouped signs require capacity width $N$, whereas alternating the same counts requires width $1$. A negative phase query rules out all rotations of the chosen order. Qualitative graph reachability also allows an unconstrained transient. If capacities apply on the approach to a restart, that approach needs a separate certificate.

Run `python3 check_periodic_buffers.py` alongside the implementation. The checker compares all envelopes to expanded rotations at every calibration corner across 180 small schedules, checks 720 phase queries against the binary search and expansion, and uses independent basic-support enumeration on 140 small feasibility instances. It also checks the huge witness, disconnected cancellation, and the two orderings of the same counts. [Implementation](periodic_buffers.py) · [Differential checker](check_periodic_buffers.py)
