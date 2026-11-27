# All operating points at a fixed level

Fix a level $\lambda$ and a strongly connected max-affine graph.
An arc $e:u\to v$ contributes $a_e x_u+b_e$ to the maximum $F_v(x)$.
An operating point satisfies $F_v(x)=x_v+\lambda$ at every channel.
Assume every channel has an incoming branch, the gains are positive,
and the gain product on every directed cycle is strictly greater than one.
Individual gains may be below one.

One rational linear program and a reachability computation represent **all**
operating points by the nonempty upsets of a finite poset. This representation
supports enumeration and queries with partial observations. Exact counting is
$\#\mathrm P$-complete even when every gain is 2 and every offset is 0 or 1.

## The poset of operating points

Let $U$ be the greatest relaxed reading, satisfying $F(U)\le U+\lambda$.
It exists at every level under the stated assumptions. A positive scale $h$
with $a_e h_u>h_v$ exists by the strict cycle gauge theorem applied to reciprocal
gains and then inverting the gauge. For sufficiently large $T$, the reading
$-Th$ satisfies every relaxed inequality. Each vertex belongs to an expansive
cycle, which gives it a finite upper bound by composing its relaxed inequalities.
The relaxed set is closed under coordinatewise maxima and limits, so it contains
its componentwise supremum. Maximizing the sum of coordinates in one LP obtains
$U$. [Strict cycle gauge](../../../Maths/Multitubes/MaxAffine/ContractiveGauge.lean)

Write $d_v=U_v-x_v$ and $s_e=U_v+\lambda-a_e U_u-b_e\ge0$. The operating
point equation becomes

$$
d_v=\min_{e:u\to v}(s_e+a_e d_u).
$$

Call an arc tight when $s_e=0$. Keep the strongly connected components of the
tight graph that contain a directed cycle, including a singleton when it has
a tight loop. Make them a poset $P$ by tight reachability in the full tight
graph, allowing paths through components without cycles. An upset is a set
closed under following that order. At least one such cyclic component exists.
Every vertex must have a tight outgoing arc, since otherwise raising its
reading a little at $U$ preserves every relaxed inequality.

**Theorem.** Operating points ordered coordinatewise are isomorphic to the
nonempty upsets of $P$ ordered by inclusion. Map $x$ to the cyclic components
where $d=0$. To invert the map, seed deficit zero at all vertices in the
selected components. At each vertex take the minimum cost of a path from a
seed, applying $z\mapsto a_ez+s_e$ on each arc.

For the forward direction, zero deficits propagate along tight arcs. Following
an attaining predecessor backwards from any channel eventually traces a cycle.
On that cycle $d=h_C+A_C d$, with $h_C\ge0$ and gain product $A_C>1$.
Nonnegative deficits force $d=h_C=0$ and then every slack on the cycle is zero.
Thus the chosen components form a nonempty upset. The equation bounds the
actual deficit above by the cost of every seeded path, and the predecessor
trace supplies a path that attains it.

For the reverse direction, strong connectivity gives a path to every channel.
On nonnegative inputs an expansive cycle with nonnegative composed offset
can only increase the deficit, so deleting it cannot increase path cost.
The minimum is attained on a simple path, including an empty path at a seed.
Decomposing paths at their last arc gives the minimum equation away from
seeds. At a seed, an internal tight incoming arc gives the same equation
with value zero. A path has zero cost exactly when all its arcs are tight,
so the cyclic components with zero deficit are precisely the selected upset.
Adding seeds can only decrease deficits, and the recovered zero components
reflect the order.

The union of upsets gives the coordinatewise maximum of readings.
An intersection gives the meet when it is nonempty. This meet can differ from
the coordinatewise minimum of the readings. A formal bottom for the empty
upset completes the order to a distributive lattice.

## Indexing, enumeration, and partial observations

The [index](operating_point_poset.py) checks strict cycle expansion using
minimum gain-products of walks of length at most $n-1$, with empty paths
allowed at all vertices. These products give positive scales with
$a_e h_u/h_v\ge1$. A violated inequality detects a below-one cycle. A directed
cycle of equalities detects a unit-product cycle, and a unit-product cycle must
consist of equalities whenever the inequalities hold. This check takes
$O(nm)$ rational operations for $n$ channels and $m$ branches, and the
edgewise $a_e>1$ case can skip the product computation.

The reconstruction works in normalized deficits $d_v/h_v$. Each normalized
affine arc map is monotone and never decreases a nonnegative input. This is the
label-setting condition for multi-source Dijkstra. The supplied lazy binary
heap groups parallel arcs by endpoints and uses $O((m+n)\log(n+1))$ operations.
In addition to the LP and scale computation, reachability from each of the
$k$ cyclic components uses $O(k(n+m))$ graph work and an at-most-$k^2$-bit
reachability index. Enumerating components from the sinks of the poset upwards
gives polynomial delay. Include a component only when all its strict
successors are included, and either exclude it or include it when allowed.
Every valid partial choice extends by excluding all remaining components.
Decoding checks the operating-point equations and reads the zero components.

For repeated measurement queries, precompute the $k$ generator readings
obtained by seeding a single cyclic component each. Each generator represents
that component's principal upset. Every operating point is a coordinatewise
maximum of generators. Given upper bounds on some channels, discard each
generator that violates a bound. Every admissible reading is a maximum of
survivors, and the maximum of all survivors is admissible. If there are no
survivors, or their maximum misses any lower bound, the measurement box is
empty. Otherwise the maximum is its greatest operating point.
Precomputing generators takes $k$ path solves and $O(kn)$ stored numbers.
Once cached, a box on $q$ measured channels takes $O(k(q+1))$ comparisons to
decide, plus $O(kn)$ to return the entire reading. There is no LP solve per box.
The theorem classifies exact real readings, and the implementation uses
rational arithmetic for rational input and bounds.

For repeated boxes on a large sparse network, a second implementation uses two graph
searches per box with linear storage. Each query returns the greatest compatible real
reading and takes $O((n+m)\log(n+1))$ rational operations after preprocessing.
[Sparse measurement-box solver](measurement-boxes.md)

## Counting and realization

A parsimonious reduction starts with an implication graph $j\to i$ for a
finite poset and introduces a hub $p$. At level zero set

$$
p=\max(2p,\max_i 2x_i),\qquad
x_i=\max(2x_i,\,2p-1,\,\max_{j\to i}2x_j).
$$

An empty maximum contributes no branch. The hub makes the full graph strongly
connected with directed diameter at most two. All gains are 2. The greatest
relaxed reading is zero, since every channel has its zero-offset self-loop.
The tight cyclic components are the implication components and the hub, which
is reachable by tight arcs from all the others. Every nonempty upset includes
the hub. The remaining choices are exactly the upsets of the implication
graph. In the realized reading the hub equals zero, selected coordinates equal
zero, and unselected coordinates equal $-1$ by the direct hub branches.
Replacing readings by $x-1$ adds 1 to each offset, giving the alphabet
$\{0,1\}$ without changing the level or count. Upward reachability also handles
implication graphs with directed cycles. Applying the construction to the
dual of the poset of join-irreducibles realizes any finite distributive lattice.
[Birkhoff's representation theorem](https://doi.org/10.1215/S0012-7094-37-00334-X)

A separate bounded-in-degree construction uses at most two branches per
channel and $O(n+m)$ total size for $n$ implication vertices and $m$ arcs.
Make balanced binary trees of $\max(2u,2v)$ rows to aggregate the hub inputs
and each predecessor list. Introduce a gate $g_i$ taking the maximum of
$2p-1$ and twice its predecessor aggregate, with the aggregate omitted for
an empty list. Set $x_i=\max(2x_i,2g_i)$. The greatest relaxed reading is
zero everywhere. The original loops cap the original channels and hub,
and the zero-offset arcs from each added channel to a capped channel
cap the added channels too. The tight cyclic components and
their reachability through the added channels give the same choices as before.
Each gate or tree reading is determined by the original coordinates and hub.
The original coordinates are $-2$ or zero, because an unselected channel's
path from the hub costs 2 in deficit, and every path from a seed into an
unselected channel crosses a hub-to-gate branch and the following doubling.
The full graph is strongly connected; this variant uses tree-depth routes.

For hardness, orient the edges of a bipartite graph from one side to the other.
Its independent sets are the antichains of the resulting height-at-most-two
poset, and taking upward closure bijects antichains with upsets. Thus exact
$\#\mathrm{BIS}$ reduces parsimoniously to the operating-point count.
Provan and Ball's hardness for exact bipartite vertex-cover counting, equivalent
by complementation to independent-set counting, uses polynomial-time
interpolation. The resulting $\#\mathrm P$-completeness statement is under
polynomial-time Turing reductions. [Provan and Ball, 1983](https://doi.org/10.1137/0212053)

For membership, guess one incoming branch per vertex in a fixed order.
For each selected cycle, the composed affine equation has a unique solution
since its gain product is greater than one. Solve along the trees of selected
branches feeding out of those cycles. All rationals have polynomial bit length
because products and affine compositions traverse paths of length at most $n$.
Check the complete operating-point equations and accept only when each guessed
branch is the first attaining branch in its row. This counts each reading once
even when several branches tie. The argument applies to rational inputs with
every cycle expansive, including reducible graphs. The Lean policy theorem
supplies the correspondence between an operating point and some active policy.
[Active branch policy](../../../Maths/Multitubes/MaxAffine/PolicySpectrum.lean)

Boolean disjunctive systems already use SCC reachability to describe
fixed points, and exact fixed-point counting is known to be hard for Boolean
max-functions. Max-plus spectral theory similarly uses critical cycle path
generators. Here the tight graph is computed from a real-valued relaxation
at the supplied level, and the affine path costs recover the actual readings.
[Jarrah, Laubenbacher, and Veliz-Cuba](https://arxiv.org/abs/0805.0275) ·
[Homan and Kosub](https://repository.rit.edu/other/95/) ·
[Akian, Bapat, and Gaubert](https://www.cmap.polytechnique.fr/~gaubert/PAPERS/hla-preprint.pdf)

## Run the example

Save `{"vertices": 3, "arcs": [[0, 1], [1, 2]]}` as `chain.json`.
The [compiler](operating_point_lattice.py) emits the adjacent fixed-level
solver's JSON format. Use `--nonnegative-offsets` for offsets 0 and 1,
or `--bounded-indegree` for the binary-tree construction.
The solver and index use `z3-solver` for the initial exact LP.

```sh
python3 operating_point_lattice.py chain.json > problem.json
python3 affine_spectrum.py --input problem.json
python3 operating_point_lattice_check.py
```

```python
import json
from operating_point_poset import OperatingPointPoset

with open("problem.json") as source:
    index = OperatingPointPoset(**json.load(source))
assert len(list(index.upsets())) == 4
reading = index.match_box({0: (None, -1), 2: (0, None)})
assert reading == (-1, 0, 0, 0)  # Three original channels, then the hub.
assert index.vector(index.decode(reading)) == reading
```

The [checker](operating_point_lattice_check.py) independently enumerates
solutions by blocking complete models of the real linear-arithmetic formula.
It compares the counts and readings, checks the greatest relaxed potential,
and tests partial-observation queries against explicit filtering.
