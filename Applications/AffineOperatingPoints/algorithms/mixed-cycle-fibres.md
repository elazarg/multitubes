# Finite or continuous operating points with mixed cycle gains

Fix a level $\lambda$ in a strongly connected floorless max-affine
network with positive gains, at least one contracting cycle, and at
least one expansive cycle. A cycle is contracting or expansive when
its gain product is below or above one, respectively. If the relaxed
inequalities are feasible, the operating points at $\lambda$ either
form a finite ordered set of upsets or contain a continuum. Two
rational LPs and graph searches decide which case holds. Unit-product
cycles are allowed.

Let $\phi_e(t)=a_e t+b_e-\lambda$ for a branch $e:u\to v$. The
relaxation consists of vectors satisfying $x_v\ge\phi_e(x_u)$.
Write $T(x)_v=\max_{e:u\to v}\phi_e(x_u)$, so operating points are
the fixed points of $T$. Composing the inequalities around a
contracting cycle bounds its readings below, and applying forward
paths gives a lower bound at every vertex. An expansive cycle gives
upper bounds, which propagate backward along paths. The feasible
polyhedron is therefore compact if nonempty.

Feasibility is preserved by coordinatewise minimum and maximum. For a
minimum use the vector supplying the smaller head reading, and for a
maximum use the vector supplying the larger tail reading. Thus
minimizing and maximizing the sum of the coordinates gives the least
vector $L$ and the greatest vector $U$ simultaneously across
coordinates. For any feasible $x$, the inequality $T(x)\le x$ and
monotonicity imply $T(T(x))\le T(x)$, so $T(x)$ is feasible.
In particular $T(L)=L$ by minimality. Feasibility and extremal
potentials can use the existing exact LP backend. [Fixed-level solver](affine-spectrum.md)

## Detecting a continuum

Keep the vertices with $U_v>L_v$ and the branches between them that
are tight at both $L$ and $U$. The fibre contains a continuum exactly
when this graph contains a directed cycle. Indeed, on each such
branch, the equality of the two residuals gives
$$
U_v-L_v=a_e(U_u-L_u).
$$
Multiplying around a cycle with positive differences shows its gain
product is one.

Conversely, a unit-product cycle that is tight at any feasible vector
is tight at every feasible vector. Its composed map is $t\mapsto t+D$
and tightness forces $D=0$. The difference between a starting reading
and its value after a tour is a positively weighted sum of the edge
slacks. It is zero at every feasible vector, which forces each
summand to vanish. Thus every unit-product cycle that can be tight
with $U_i>L_i$ on one of its vertices belongs to the jointly tight
graph. The differences propagate around the cycle, so it suffices to
have $U_i>L_i$ at a single vertex.

If the graph contains a directed cycle, fix any vertex $i$ on it and
any $t\in[L_i,U_i]$. Interpolate between $L$ and $U$ to obtain a
feasible vector with $i$-coordinate $t$. Iterate $T$ downward from
that vector. Each cycle coordinate stays fixed because its incoming
cycle edge is tight, and each iterate is feasible and bounded below
by $L$. The limit is an operating point by continuity. In particular
the entire interval $[L_i,U_i]$ is the projection of the fibre onto
coordinate $i$.

## The finite fibre

Suppose the jointly tight graph on $U_v>L_v$ has no cycle. In the
graph of all branches tight at $U$, retain the strongly connected
components that contain a cycle and have $U_i>L_i$ at their vertices.
Order these components by reachability in the full tight graph. The
operating points are in order-preserving bijection with **all**
upsets of this poset, including the empty upset for $L$. An upset
contains every component reachable from each one it contains.

The condition $L_i=U_i$ propagates forward along branches tight at
$U$, because $L$ is feasible and both bounds agree at the tail.
Consequently it is constant as a predicate on each tight component.
A contracting cycle tight at $U$ attains its universal lower cycle
bound there, so every coordinate on that cycle has $L_i=U_i$. A
unit-product cycle tight at $U$ must also have $L_i=U_i$ on it in
the finite case. Therefore all cycles in the retained components
are expansive.

For a proposed upset, start at $U$ on its vertices and at $L$
elsewhere. This vector $z$ satisfies $z\le T(z)$. A selected vertex
has a tight incoming edge within its component, and elsewhere use
$T(L)=L$. Iterating upward is bounded by $U$. The resulting operating
point is the maximum of $L$ and all forward path values from selected
vertices with their $U$ readings.

In fact, paths of length at most $n-1$ suffice for $n$ vertices.
For a path traversing $e:u\to v$, clip the result below at $L_v$.
Clipped transport along a whole walk equals the maximum of its
unclipped transport and the final $L$ reading. This follows because
$a_e>0$ and $\phi_e(L_u)\le L_v$. For a closed walk at $i$, its
unclipped affine map satisfies $\phi(L_i)\le L_i$ and
$\phi(U_i)\le U_i$ by feasibility. It thus sends every reading
in $[L_i,U_i]$ to at most itself. Clipping preserves this inequality.
Deleting a closed subwalk can only increase the eventual result,
by monotonicity of the remaining transports. The maximum over
simple paths is attained and gives the limit after at most $n-1$
synchronous rounds.

The same path computation produces a continuum witness at any
prescribed reading $t\in[L_i,U_i]$ of a reported varying coordinate
$i$. Seed $t$ at $i$ and $L$ elsewhere. The feasible interpolation
with coordinate $t$ bounds the propagation from above, so the
coordinate stays at $t$. The neutral cycle returns the seed to
itself after one tour. This supplies a tight incoming branch at
$i$ after propagation. Every other coordinate is supported by
either $L$ or the last branch of a maximizing path.

At vertices with $U_i>L_i$, the reconstructed reading attains $U_i$
exactly when a path from a selected vertex is tight throughout at
$U$. Indeed a strict loss relative to $U$ on one edge persists
through all subsequent edges by positivity of gains. Clipping
could erase a strict loss only at a vertex with $U=L$, and after
such a vertex a tight suffix also has $U=L$ throughout. Thus the
retained components attaining $U$ are exactly the selected upset.

For the converse, take an arbitrary operating point and choose
an incoming branch at equality for each vertex. Trace predecessors
from any vertex until they repeat. A contracting cycle at equality
attains its universal lower cycle bound, so its readings are at
$L$. A unit-product cycle at equality also has readings at $L$ by
the diagnostic assumption. Propagating these readings along the
traced path gives at most $L$ at its target, so the target is at
$L$. An expansive cycle at equality attains its universal upper
cycle bound, so its readings are at $U$. Either they also equal $L$,
or the cycle lies in a retained component saturated at the given
operating point. In the latter case the traced path is among the
paths used in the reconstruction. This proves that the reconstructed
point is at least the arbitrary one coordinatewise. The reverse
inequality follows from feasibility and the shared seed readings.

Component saturation is therefore the inverse of reconstruction.
The two maps respect order. More selected components can only raise
a reconstructed point, and increasing an operating point preserves
every saturation at $U$. This also gives an extension of the
upset representation from strictly expansive cycle gains.
[Counting operating points](counting-operating-points.md)

## Examples and use

At $\lambda=0$, the operator
$F(x)=\max(x/2,2x-1)$ has relaxed interval $[0,1]$ and two operating
points, $0$ and $1$. Adding the branch $x-1$ keeps both conclusions.
Adding the branch $x$ instead keeps the same relaxation and makes
every point in $[0,1]$ an operating point. The latter branch is tight
at both extrema and the coordinate varies. A unit-gain loop at a
coordinate fixed by the relaxation does not cause a continuum.

Run the diagnostic with Python and `z3-solver` installed. The JSON
format is the fixed-level solver's. The following returns status
`"finite"` with least reading $0$, greatest reading $1$, and one
retained component.

```json
{"vertices":1,"level":0,"branches":[[0,0,"1/2",0],[0,0,2,-1]]}
```

```sh
python3 mixed_cycle_fibres.py --input graph.json
python3 mixed_cycle_fibres.py --input graph.json --upset 0
python3 mixed_cycle_fibres_check.py
```

With status `"continuum"`, the output gives one varying coordinate
and its exact projected interval. For a finite fibre, component IDs
are array indices. The optional `--upset` argument computes an exact
reading for those IDs, and an empty list of IDs gives $L$. Use
`--reading 1/2` on a continuum fibre to realize that coordinate value
when it belongs to the reported interval.

For $m$ branches the prototype uses two rational LPs with $n$
variables and $m$ inequalities. A cycle search in the jointly tight
graph suffices to distinguish finite from continuous once $L,U$ are
known. Gain-cycle validation and building the finite reachability
order take $O(nm)$ rational or graph operations. Each reconstruction
also takes $O(nm)$ rational operations. The independent checker uses
the equations directly over exact reals and verifies the finite
sets and continuum projections, including frozen and slack neutral
cycles. [Diagnostic](mixed_cycle_fibres.py) · [Independent checker](mixed_cycle_fibres_check.py)
