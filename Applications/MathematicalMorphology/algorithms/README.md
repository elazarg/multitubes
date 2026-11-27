# Minimum-cost inverse dilation after a source outage

A line of individually addressable seed sites feeds several binary observation layers.
Each observation specifies that a detector must fire, must stay dark, or may do either.
Seed sites have activation costs. Given a contiguous block of disabled source sites, find
the cheapest seed mask that still matches every observation. The mask can be redesigned
after learning the outage. Branches can have different resolutions and share earlier
dilation layers.

The index uses linear preprocessing in the compact route encoding, answers each optimal
cost or infeasibility query in constant time, and reconstructs $k$ selected seed sites in
$O(1+k)$ time. It also reports a required detector that no remaining eligible seed can
reach when a match is impossible. The bounds count word operations on indices, costs, and
cost sums.

## Two camera observations

Camera A first applies a radius-one dilation, clipped at the ends of a 15-site line, and
then samples sites $1,4,7,10,15$. Camera B uses five detector footprints directly on the
source. The intervals are $[3,7], [4,4], [5,9], [7,11], [12,14]$, in detector order.
Both full observations admit these two disjoint minimum-cost source masks.

```text
Source positions     123456789012345
Seed sites 3,6,11    ..#..#....#....
Seed sites 5,7,9     ....#.#.#......
Camera A (both)      .###.
Camera B (both)      #.##.
```

The source costs are $(2,2,1,4,1,1,1,5,1,4,1,2,2,2,2)$. The three lit detectors
in A constrain three disjoint source intervals. Each needs a seed of cost at least 1, so
both masks attain the minimum 3. Camera B forbids source site 4 even though it lies
inside required footprints. The two alternatives at sites 6 and 7 hide a joint outage
that no individual-site test reveals.

| Disabled source sites | Minimum cost | One matching mask or infeasibility witness |
| --- | ---: | --- |
| None | 3 | $\{5,7,11\}$ |
| $[6,6]$ | 3 | $\{3,7,9\}$ |
| $[7,7]$ | 3 | $\{5,6,11\}$ |
| $[6,7]$ | 7 | $\{3,8,9\}$ |
| $[6,8]$ | Infeasible | A's middle detector has no surviving predecessor. |

Run the [example](seed_block_index.py) and the [independent checker](seed_block_index_check.py)
with Python 3.10 or later.

```sh
python3 seed_block_index.py
python3 seed_block_index_check.py
```

## Compressing the routes and inverting the observations

The root is the list of $N$ source sites in physical order. Each subsequent layer names
one earlier parent layer. A row gives one inclusive interval in the parent's order,
or gives the empty set. The row fires if any parent site in that interval fires. Each
layer can have multiple children, and an observation can be attached at any nonroot
layer. This represents the relation image in
[RelationalTransport.lean](../MathematicalMorphology/RelationalTransport.lean).
Under composition each detector has an effective reverse support $S$, the set of
source sites that can reach it. The detector fires exactly when the seed mask intersects
$S$.

The compact algorithm certifies every effective support as an interval or the empty
set. In any layer used as a parent, the left and right endpoints of the nonempty
effective supports must both be nondecreasing in layer order. Index each parent once.
Store the list of its nonempty intervals, a prefix count of its nonempty rows, and a
prefix count of gaps between adjacent nonempty intervals. The prefix count of rows
locates the first and last participating nonempty supports for any child row in constant
time. The union is an interval exactly when no gap separates those participating
intervals. Its endpoints are the first left and last right endpoints. The seed layer
starts with singleton supports, so induction certifies the computation through every
branch. A hole is detected before using an interval hull. A layer with no children can
have its interval endpoints in any order.

Let $E$ denote the size of the compact input in words, including the $N$ costs, the
layer, row and observation records, and the root description. Certifying and composing
the supports takes $O(E)$ time and temporary space. A row with $N$ parent sites still
occupies one record. If the input instead lists each relation pair, reading those
incidences is an additional cost. The implementation accepts the endpoint encoding
above. For a single dilation with $N$ detectors whose reverse supports all span
$\Theta(N)$ sites, the expanded relation has $\Theta(N^2)$ incidences with only
$O(N)$ endpoint records.

Every forbidden detector removes its entire effective support from consideration.
Equivalently, the allowable source mask is the erosion of the allowable output
family. This follows from the dilation–erosion adjunction: keeping the dilated image
within the allowable family is equivalent to keeping the seeds in the corresponding
erosion. The code unites the forbidden intervals with a difference array in physical
source coordinates. [Heijmans and Ronse, *The Algebraic Basis of Mathematical
Morphology I*](https://ir.cwi.nl/pub/5977/5977D.pdf)

Write $r(t)$ for the number of eligible sources in physical positions $1$ through $t$,
with $r(0)=0$. A required detector whose effective support is $[\ell,u]$ now needs
one selected eligible rank in $[r(\ell-1)+1,r(u)]$. The ranks discard holes caused
by forbidden detectors while preserving order. Any required detector with no
eligible source certifies infeasibility even before an outage. Otherwise, selecting
all eligible sites hits every required interval. With unrestricted reverse supports
the same reduction gives general weighted set cover, even for a single dilation
layer. In the compact algorithm the resulting weighted interval stabbing problem
is solved without materializing its incidence matrix.

## Paths through a line of eligible sites

Number the $m$ eligible sites $1,\ldots,m$ and add sentinels $0$ and $s=m+1$.
Use activation costs $w_p$ at ranks $p$ and $w_0=w_s=0$. For each $p<s$ set

$$
R(p)=\min\bigl(\{u:[\ell,u]\text{ is a required rank interval and }\ell>p\}
                   \cup\{s\}\bigr).
$$

A path uses a strictly increasing sequence of selected ranks between the sentinels.
Two consecutive choices $p<q$ leave all intervening ranks unselected. The sequence
hits every interval exactly when $q\le R(p)$ for every consecutive pair. Indeed,
an unhit interval must lie in one such open gap, and a gap contains an interval
exactly when some $[\ell,u]$ satisfies $p<\ell\le u<q$.

Compute $R$ by recording the least upper endpoint at each lower endpoint and then
taking suffix minima. $R$ is nondecreasing and $R(p)\ge p+1$. Consequently all prefix
and suffix path costs are finite for a feasible no-outage instance. Let $f(p)$ be
the minimum cost from $0$ through $p$ and $g(q)$ the minimum cost from $q$ through $s$,
both inclusive at their inner endpoint. The recurrences are

$$
f(q)=w_q+\min_{p<q,\ R(p)\ge q} f(p),\qquad
g(p)=w_p+\min_{p<q\le R(p)} g(q).
$$

In the forward sweep, candidate predecessor ranks arrive in increasing order and
expire in that order because $R$ is nondecreasing. In the backward sweep, successor
ranks arrive in decreasing order and expire when they exceed the receding bound
$R(p)$. Each sweep maintains a monotone deque of cost minima. A newer candidate
that is at least as cheap as an older one will outlast it, so it can remove the
older candidate. Thus both passes take $O(m)$ time and store minimizing links for
reconstruction. They compare costs directly and allow zero-cost sites.

The no-outage optimum is $f(s)$. For an eligible site $j$ the optimum that must use
$j$ is $f(j)+g(j)-w_j$. Comparing this and the optimum excluding the singleton
outage at $j$ with $f(s)$ determines whether the site occurs in every, some, or no
minimum-cost matching mask. A forbidden site cannot occur in a matching mask.

## Reducing an outage query to one array range

For physical outage $[a,b]$, set $p_0=r(a-1)$ and $q_0=r(b)+1$. Any matching path
avoiding the block has one transition from a last left rank $p\le p_0$ to a first
right rank $q\ge q_0$. This also holds when the block contains no eligible site.
For a legal transition, an optimal prefix through $p$ and suffix from $q$ remain
outside the block, by the increasing order. The optimum is therefore

$$
\min_{0\le p\le p_0,\ q_0\le q\le s,\ q\le R(p)} f(p)+g(q).
$$

The query is infeasible exactly when $q_0>R(p_0)$, since otherwise the pair
$(p_0,q_0)$ itself is legal. When the inequality holds, a required interval attaining
$R(p_0)$ is wholly inside the failed eligible ranks. Storing the minimizing detector
with each suffix minimum returns that detector as an infeasibility certificate.

Build a single event list with one suffix event $Q_q$ at key $q$ and one prefix event
$P_p$ at key $R(p)$. Merge by increasing key. Put $Q_q$ before all prefix events
at an equal key and put the tied prefix events in increasing $p$ order. The resulting
list takes $O(m)$ time to construct. Store each event's list index. For the query,
take the event range from $Q_{q_0}$ through $P_{p_0}$, inclusive. Legal transitions in
the formula correspond exactly to a suffix event followed by a prefix event in
this range. Suffix events occur in $q$ order, prefix events in $p$ order, and $Q_q$
precedes $P_p$ precisely when $q\le R(p)$.

Let $W=\sum_{j=1}^m w_j$ and $C=3(1+W)$. Assign values on events by

$$
z(Q_q)=g(q)-C,\qquad z(P_p)=C-f(p).
$$

For a legal suffix-before-prefix pair, the rise between the two event values is
$2C-f(p)-g(q)\ge 2C-2W>W$. Two events of the same kind differ by at most $W$.
A prefix-before-suffix pair has negative rise. Thus the largest forward rise in a
feasible event range identifies a minimizing transition and its cost. On successive
differences $d_i=z_{i+1}-z_i$, a maximum forward rise over event indices $L$ through
$U$ is exactly a maximum-sum nonempty segment of $d_L,\ldots,d_{U-1}$. The segment
endpoints identify the two events, and their stored path links reconstruct a seed
mask.

Chen and Chao give a linear-preprocessing, linear-space, constant-query algorithm
for these maximum-sum segment queries. The implementation uses their two candidate
arrays and range-minimum formulation, with rightmost ordinary range extrema as in
Gawrychowski and Nicholson's Section 4.1. On a final score tie the code keeps the
earlier clipped candidate. Either candidate gives an optimal mask. A decreasing stack finds each candidate's
minimum starting value since the nearest preceding value at least as large. Querying
uses the maximum candidate ending inside the range, at most one later candidate,
and a clipped prefix minimum. For constant-time ordinary range minima, the
implementation builds Cartesian trees and uses Euler-tour depth arrays. Euler
block patterns share tables of within-block minima, and a sparse table over block
minima costs linear space and time because each block has $\Theta(\log m)$
entries. [Chen and Chao, *On the Range Maximum-Sum Segment Query
Problem*](https://www.csie.ntu.edu.tw/~kmchao/papers/2007_DAM_RMSQ.pdf),
[Gawrychowski and Nicholson, *Encodings of Range Maximum-Sum Segment Queries
and Applications*](https://arxiv.org/pdf/1410.2847),
[Bender and Farach-Colton, *The LCA Problem
Revisited*](https://ics.uci.edu/~eppstein/261/BenFar-LCA-00.pdf)

## Costs and comparisons

| Operation | Time | Retained index space |
| --- | ---: | ---: |
| Read, certify and compress routes | $O(E)$ | $O(N)$ after compression |
| Build the path and event indexes after compression | $O(m)$ | $O(m)$ |
| Query one physical outage cost or blocking observation | $O(1)$ | |
| Return one optimal witness mask of size $k$ | $O(1+k)$ | |
| Query all outages of one specified width | $O(N)$ total | |
| Find a shortest outage that exceeds a budget | $O(N)$ total | |

Temporary space for construction is $O(E)$. The retained index includes a
length-$N+1$ physical rank table. The scan of the required rank intervals that initializes $R$ is included in compression. The index never stores the composed relation or the
path DAG. The word bounds apply when input sizes and the cost sums fit in a constant
number of words. Python uses exact integers, so arithmetic on unusually large costs
has the corresponding bit cost.

The budget scan regards infeasibility as exceeding any finite budget. For a fixed
left endpoint the cost is nondecreasing as the right endpoint grows. The first
budget-breaking right endpoint cannot move left when the left endpoint increases,
since removing fewer sites can only improve the optimum. Two forward pointers
therefore find a minimum-length nonempty outage with at most linear work. In the
fixture the shortest block exceeding budget 3 is $[6,7]$.

The shortest-path formulation is an instance of paths avoiding a failed interval.
Bernstein and Karger's detour lemma for general graphs decomposes such a path around
a failed interval of an original shortest path. Here the order includes all
eligible vertices and every path increases in that order. Hence the detour is a
single transition in the implicit path DAG, whose feasibility depends only on
$R(p)$ and $q$. Repeating the sliding-minimum DP with disabled ranks skipped takes
$O(m)$ per outage, including dense path graphs. The event index reduces $Q$ scalar
outage queries to $O(E+Q)$ total work.
[Bernstein and Karger, *A Nearly Optimal Oracle for Avoiding Failed Vertices and
Edges*, Section 3.1](https://aaronbernstein.cs.rutgers.edu/wp-content/uploads/sites/43/2018/12/STOC_2009_fault_tolerance.pdf)

A stronger generic baseline is to use the implicit matrix with entry
$-f(p)-g(q)$ where $q\le R(p)$. Its defined entries form a staircase, and every
fully defined Monge inequality is equality. The outage is a submatrix maximum
query. Theorem 8 of Gawrychowski, Mozes and Weimann gives $O(m\log m)$
preprocessing, $O(m)$ words and $O(\log\log m)$ query time for general staircase
Monge matrices. The improvement here uses the additive entry scores and the
one-sided query bounds to reduce the query to a single interval on the merged
event list. The morphology contribution is the certified compact route inversion
and this specialized reduction. The maximum-sum segment and range-minimum
indexes follow the cited algorithms.
[Gawrychowski, Mozes and Weimann, *Submatrix Maximum Queries in Monge and Partial
Monge Matrices Are Equivalent to Predecessor Search*](https://arxiv.org/pdf/1502.07663)

The checker enumerates seed subsets and runs forward dilation on individually scanned
rows. It tests every physical outage, the returned masks and blocking observations,
site inclusion costs, and the shortest budget-breaking block. Its independent
materialized support sets check acceptance and rejection of the local interval
certificate. Separate array scans check the query index on all ternary arrays
through length 7 and several larger arrays.
