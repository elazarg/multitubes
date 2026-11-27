# Prescribing the spectrum with exactly two strong components

Every finite union of closed rational intervals and rays is the exact
spectrum of a weakly connected floorless max-affine network with exactly
two strongly connected components. The network uses gains $2$ and $3$
and nonnegative rational offsets. All real levels satisfy its relaxed
inequalities. This includes the empty set, singletons, and the whole line.
For $k$ component intervals after merging overlaps and touching endpoints,
the construction uses at most $2k+4$ vertices and $6k+5$ branches.

Two strongly connected components are minimal for every proper spectrum
in the strictly expansive class. With one component, every real level is
an eigenvalue. [Strongly connected classification](strongly-connected.md)

## The source cycles and sink tests

A branch $u\to v$ with gain $g$ and offset $b$ contributes $g x_u+b$ to
$F_v(x)$. At a level $\lambda$, the equations $F(x)=x+\lambda\mathbf 1$
say that $x_v$ is the maximum of incoming branch values after subtracting
$\lambda$. We work in these equations and choose the offsets below
before shifting them to be nonnegative.

The source component has a root $x_i$ for each interval $I_i$, plus a
center $x_0$. There is one sink $y$ with a gain-$3$ loop of offset zero.
The sink inequalities imply $y\le\lambda/2$. A gain-$g$ branch from
$x_i$ into $y$ with offset $b$ then requires
$x_i\le (3\lambda/2-b)/g$. These ceilings are sufficient at the sink
because $y=\lambda/2$ makes its own loop tight.

Give each root an internal directed cycle whose value at a tight
cycle is $p_i(\lambda)=\beta_i\lambda$. The table gives the gains along
the cycle starting at $x_i$, with offset zero on each edge. A separate
relay receives the first edge of each cycle of length two. Its one
incoming branch forces its coordinate to be the corresponding affine
value minus $\lambda$. Substituting this value gives the root's
inequality $x_i\le p_i(\lambda)$, with equality exactly when its cycle
is tight. For example, the gain word $(3,2)$ gives
$x_i\ge 6x_i-3\lambda$, so $p_i(\lambda)=3\lambda/5$.

| Interval at the root | Gains along the cycle | $\beta_i$ |
| --- | --- | --- |
| A bounded interval $[a,b]$ | $3,2$ | $3/5$ |
| A right ray $[a,\infty)$ | $3$ | $1/2$ |
| A left ray $(-\infty,b]$ | $2,3$ | $4/5$ |
| The center | $3,2$ | $3/5$ |

For a finite lower endpoint $a$, use a gain-$2$ branch to the sink
with offset $2(3/4-\beta_i)a$. For a finite upper endpoint $b$, use a
gain-$3$ branch with offset $3(1/2-\beta_i)b$. The two resulting
ceilings are
$$
x_i\le \frac34\lambda+\left(\beta_i-\frac34\right)a,
\qquad
x_i\le \frac12\lambda+\left(\beta_i-\frac12\right)b.
$$
At $x_i=p_i(\lambda)$, a lower test requires precisely $\lambda\ge a$
and an upper test precisely $\lambda\le b$. Give the center both tests
with $a=1$ and $b=0$. Its cycle can never be tight in a full eigenvector.

## Connecting the roots

Let $H$ be the maximum of $1$ and the absolute values of all finite
input endpoints. Put $M=10H$. For each pair consisting of the
center and a leaf, add one directed path of each orientation, with gains
$3,2$ and offsets $0,-M$. All paths starting at the same root share
their first edge and its relay, whose level equation is
$r_i=3x_i-\lambda$. It also serves the root's internal cycle when
that cycle starts with gain $3$ and has length two. The internal
cycle with gains $2,3$ uses its own relay.

After substituting the relay values, every directed spoke contributes
the same map
$$
C_\lambda(z)=6z-3\lambda-M
$$
from its tail root to its head root. A directed cycle of tight spokes
forces its coordinates to equal the fixed point
$q(\lambda)=3\lambda/5+M/5$ of $C_\lambda$. Indeed, any positive iterate
has the same fixed point since its gain is a positive power of $6$.
Every spoke cycle includes the center, where $q(\lambda)$ exceeds the
internal ceiling $3\lambda/5$. Thus a tight cycle must be internal to
a root. In any eigenvector, choose a tight incoming branch at each
root after the relay substitutions and follow predecessors until a
root repeats. A tight internal cycle at some leaf is necessary, and its
sink tests imply that $\lambda$ lies in that leaf's interval.

For the converse, suppose $\lambda\in I_i$ and set
$$
x_j=C_\lambda^{d(i,j)}(p_i(\lambda)),
$$
where $d(i,j)$ is the distance in the star of roots. At any finite
endpoint of $I_i$, we have $|\lambda|\le H$ and
$|p_i(\lambda)|\le 4H/5$, so
$C_\lambda(p_i(\lambda))\le -11H/5<p_i(\lambda)$.
The inequality $C_\lambda(p_i(\lambda))<p_i(\lambda)$ extends along
either ray. It is equivalent to $p_i(\lambda)<q(\lambda)$, and the
slope of $p_i$ is $1/2$ on a right ray and $4/5$ on a left ray,
on the appropriate side of the slope $3/5$ of $q$. For a bounded
interval it extends by affinity.

The iterates in the formula for $x_j$ now strictly decrease with distance.
For a spoke from $u$ to $v$, the inequality $d(i,v)\le d(i,u)+1$
gives $x_v\ge C_\lambda(x_u)$. There is a tight incoming spoke at
each nonselected root by taking the last edge on a shortest path.
The selected root's internal cycle is tight.

It remains to check the internal and sink ceilings. At every finite
endpoint of $I_i$, each other root has $x_j\le -11H/5$,
whereas its ceilings are at least $-H$. Affinity extends the strict
inequalities between endpoints. For a ray, at distance $d\ge 1$
the slope of the assigned coordinate is
$$
\frac35+6^d\left(\beta_i-\frac35\right).
$$
It is at most zero for a right ray and at least $9/5$ for a left ray.
All ceiling slopes lie in $[1/2,4/5]$, so the inequalities persist
toward the unbounded end. At the selected root its own tests hold
throughout $I_i$. To restore a relay reached by a gain-$g$ branch,
give it coordinate $g x_j-\lambda$, where $j$ is its tail. All relay
equations hold, and the root equations are exactly the substituted
ones. The choice $y=\lambda/2$ finishes the eigenvector.

## Eigenpair curves and network size

Each component interval other than the whole-line special case has a
unique source vector at every admitted level. The merged intervals are
disjoint, so their sink tests permit
only one root to have a tight internal cycle. Tracing tight spokes
backward from any other root must end at that selected root. It cannot
repeat a vertex because a tight spoke cycle is impossible. The traced
path is therefore the unique path between the roots in the star, so
the equality above forces every source coordinate.

With the source fixed, let $b$ be the largest incoming value at the
sink among branches from the source, before subtracting $\lambda$.
The sink equation has the two candidates $\lambda/2$ and
$b-\lambda$. Both work, and they coincide exactly when $b=3\lambda/2$.
The tests at nonselected roots are strict at finite endpoints, between
them, and along the rays by the bounds above. At the selected root
the feed for a finite endpoint attains $3\lambda/2$ exactly at that
endpoint. The maximum $b$ thus reaches $3\lambda/2$ precisely at finite
endpoints of the spectrum. Each finite endpoint has one eigenvector
and each interior level has two.

The source coordinates are affine in $\lambda$ on each component.
The two choices for the sink are continuous piecewise-affine functions
of $\lambda$. Over a bounded nondegenerate interval their graphs in
$(\lambda,x,y)$ are two polygonal arcs meeting at both endpoints and
disjoint in their interiors. The full eigenpair set over that interval
is a simple closed polygonal curve. A singleton gives a point. Over
a ray, two polygonal rays meet at the finite endpoint, forming a
piecewise-linear copy of the real line whose level coordinate
reverses direction at that endpoint.

The root and relay vertices form one strongly connected component.
Each relay lies on a cycle through its starting root, and the two
directions of each spoke connect every root to the center. The sink
receives a branch from the center and has no path back to the source.
There are $k+1$ roots and $k+1$ shared relays, at most one extra
relay for a left ray, and one sink. Counting the shared relay edges,
internal cycle closures, spokes, and sink edges gives at most
$6k+5$ branches. With no intervals, the source consists of the center
and its internal relay. The center's incompatible tests give the
empty spectrum. For the whole line use
$$
F(x,y)=(\max(2x,3x),\max(3y,3x)).
$$
It also has two strongly connected components and both gains.
The vector $(\min(\lambda,\lambda/2),\lambda/2)$ is an eigenvector
at every level. The two sink choices coincide for $\lambda\ge 0$
and are distinct for $\lambda<0$.

To make offsets nonnegative, choose
$T=\max(0,\max_e -b_e/(g_e-1))$ and replace each offset by
$b_e+(g_e-1)T$. Subtracting $T$ from every coordinate maps
witnesses for the original network to witnesses for the shifted
network, with the same level. For the relaxed inequalities, a constant
vector with value at most $\min_e(\lambda-b_e)/(g_e-1)$ works for
any level, using the offsets of whichever network is being tested.

The earlier inverse compiler uses separate required source equations
to impose the intersection of their tests. Here the source is one
component. It supplies a tight cycle for any one of the indicated
intervals and meets the other tests by lowering the other roots.
[Inverse compiler using separate sources](inverse-spectrum.md)

## Exponentially many eigenvectors at one level

There is also a family with spectrum $[0,1]$ and exactly two strongly
connected components whose eigenpair sets contain exponentially many
arcs. For $d\ge 2$, use a two-vertex source with
$F_x=2w$ and $F_w=3x$, and $d$ sink coordinates in a directed ring.
Before the common offset shift, use
$$
F_{y_i}=\max(3y_i,\,2x,\,3x-3/10,\,3y_{i-1}-1)
$$
with subscripts cyclic modulo $d$. The gains are $2$ and $3$. There are
$d+2$ vertices and $4d+2$ branches, and shifting by $T=1/2$ makes
every offset nonnegative.

The source forces $x=3\lambda/5$ and $w=4\lambda/5$. Write
$b(\lambda)=\max(6\lambda/5,9\lambda/5-3/10)$ for the direct feed to
each sink coordinate. Its self-loop caps $y_i$ at $\lambda/2$, so any
eigenvector needs $b(\lambda)\le 3\lambda/2$, which is precisely
$0\le\lambda\le1$. On that interval,
$$
3\lambda/2-b(\lambda)
=\min(3\lambda/10,3(1-\lambda)/10)\le 3/20.
$$
Every ring branch then contributes at most $3\lambda/2-1$, strictly
below the direct feed at every possible eigenvector. The ring gives
the sink component its strong connectivity. Its branches are slack
in the eigen-equations even at the endpoints.

Each sink coordinate independently chooses $\lambda/2$ or
$b(\lambda)-\lambda$. There are $2^d$ eigenvectors at every interior
level and one at each endpoint. The complete eigenpair set consists
of $2^d$ polygonal arcs with the same pair of endpoints and otherwise
disjoint. Its first Betti number is $2^d-1$.

## Example and verification

For $(-\infty,-1]\cup[1,\infty)$, take $M=10$. The left root has a
gain-$3$ feed of offset $9/10$, and the right root has a gain-$2$
feed of offset $1/2$. The center's gain-$2$ and gain-$3$ feeds have
offsets $3/10$ and $0$. At $\lambda=-2$ the center, left, and right
root coordinates before the nonnegative-offset shift are
$(-68/5,-8/5,-428/5)$. At $\lambda=2$ they are $(-10,-76,1)$.
At level zero neither ray's root can be tight. The center cannot be
tight at any level, and a tight spoke cycle would force its value to
$2$ at level zero, above its ceiling of $0$.

Use the same JSON interval format and witness flags as the earlier
compiler. Use `null` for infinity and strings for rational endpoints.
Sorting and merging $s$ input intervals costs $O(s\log s)$ comparisons.
After merging, construction and witness computation use $O(k)$ rational
operations. The compiler emits the adjacent fixed-level solver's
`vertices`, `branches`, and optional `level` fields.

```sh
printf '%s\n' '[[null,-1],[1,null]]' > gap.json
python3 two_component_spectrum.py gap.json --level 0 > network.json
python3 two_component_spectrum.py gap.json --witness 1
python3 two_component_spectrum_check.py
```

The independent checker enumerates active branch policies on the expanded
graphs. With every gain above one, each policy has a unique affine
potential as a function of level. Substitution into every branch
inequality yields its exact level interval. The checker compares the
union with the raw input over all real levels on 47 targets. It checks
the exact eigenvector counts by adding the intersection levels of
distinct affine policy potentials to the interval boundaries. It also
checks the ring counts for sizes two through six and checks connectivity,
exact witnesses, and size on a 62-interval target.
[Compiler](two_component_spectrum.py) · [Exact checker](two_component_spectrum_check.py)
