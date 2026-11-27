# What does replacing one calibration buy?

A unit-scale comparison from sensor $u$ to sensor $v$ reports an offset $a_e$.
A reading $p$ fits it at tolerance $t$ when $\lvert p_v-p_u-a_e\rvert\le t$.
Given a fixed calibration log, an engineer can ask which single comparison to
revisit, what improvement is possible, or which replacement values meet a
prescribed tolerance. The index returns the entire optimal-tolerance curve
$T_e(x)$ for every comparison $e$, with only that offset replaced by $x$.
Parallel comparisons retain distinct identities, and the network may have
disconnected components or self-comparisons.

For $n$ sensors and $m$ comparisons, preprocessing takes $O(n+n^2m)$ rational
operations and $O(n^2+nm)$ space. A proposed replacement or a tolerance cap
takes $O(\log(n+1))$ operations to query. Each curve uses the original log as
its starting point.

## From signed walks to replacement curves

In the signed graph, comparison $e$ gives arcs $u\to v$ of weight $a_e$ and
$v\to u$ of weight $-a_e$. The formal sensor theorem makes feasibility
equivalent to the bound $w(C)\le |C|t$ on every closed signed walk. The
simple-cycle reduction makes length at most $n$ sufficient. Thus the optimum
is the maximum of zero and the signed cycle means. These equivalences supply
both the lower bound and the existence of readings at the tolerance computed
by the index.
[Sensor cycle theorem](../CellularSheaves/CycleConsistency.lean) ·
[Simple signed cycles](../../../Maths/Multitubes/Additive/SignedCycles.lean)

Delete both signs of $e$, and let $B_e$ be the resulting optimum.
In the edited signed graph, a simple cycle can omit $e$, use one sign
of $e$, or use both signs as a zero-weight two-cycle. A self-comparison
contributes the signed loops $x,-x$. For either orientation $s\to r$ of a
non-loop $e$, let $\sigma\in\{-1,1\}$ be its sign. For $1\le k<n$, let
$W_{r,s,k}^{(-e)}$ be the largest weight of a $k$-arc walk from $r$ to $s$
that avoids $e$ and never revisits $r$. With absent walks skipped, the formula
is

$$
T_e(x)
=
\max\!\left(
 B_e,\;
 \max_{(s\to r,\sigma),k}
 \frac{\sigma x+W_{r,s,k}^{(-e)}}{k+1}
\right).
$$

Every simple cycle using one sign supplies a walk in this formula.
Conversely, closing even a nonsimple candidate walk with the edited arc
gives a valid closed walk, so its mean is bounded by $T_e(x)$. This allows
ordinary layered dynamic programming. For a self-comparison the formula is
$T_e(x)=\max(B_e,|x|)$.

The best achievable tolerance is exactly $B_e$. A reading feasible after
deletion at $B_e$ can be extended by restoring $e$ with offset $p_v-p_u$,
making its residual zero. A comparison whose $B_e$ equals the original
optimum cannot improve the fit by itself. For a bridge the curve is constant
because no complementary walk exists. A cap below $B_e$ gives an empty set
of replacements.

## Shared preprocessing and queries

1. Compute the original maximum cycle mean and find one simple cycle
   attaining it when that mean is positive. Deleting a comparison outside
   this cycle preserves its witness and cannot increase the maximum.
   Recompute only for the at most $n$ comparison IDs on the witness. Karp's
   algorithm costs $O(nm+n)$ per solve on the signed graph. To recover a
   witness, subtract the mean from arc weights and find longest shifted-walk
   potentials with a start allowed at every vertex. Removing cycles of
   nonpositive weight bounds this computation by $n-1$ arcs. Every
   maximum-mean cycle is tight along each arc, and any directed cycle in the
   tight graph attains the mean.
   [Karp's cycle-mean algorithm](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/29121.html) ·
   [Chaturvedi and McConnell's cycle recovery](https://www.cs.colostate.edu/~rmm/minCycleMean.pdf)
2. For each root $r$ with a non-loop comparison, run one exact-length
   dynamic program with no arrivals back at $r$. At each vertex and layer
   keep the two largest weights whose **first comparison IDs differ**.
   A walk avoids an incident $e$ exactly when its first comparison differs
   from $e$. Any later traversal of $e$ would revisit $r$. Thus at most
   one of the two labels is disqualified. Keeping the pair is inductively
   sufficient because a common next arc adds the same weight to both
   labels and preserves their IDs. At each layer read the best eligible
   label at the other endpoint of each incident comparison. This yields
   all $W_{r,s,k}^{(-e)}$ in $O(n^2m+n)$ total time.
3. Build each upper envelope by scanning lines in slope order.
   Negative slopes appear in this order during the length scan, and
   positive slopes appear in reverse order. A stack discards pieces with
   no open interval of dominance. Evaluate a replacement by binary search
   on the breakpoints. For a cap $t\ge B_e$, each negative-slope line $ax+b$
   requires $x\ge(t-b)/a$, and each positive-slope line requires
   $x\le(t-b)/a$. Store upper envelopes for the lower endpoint and the
   negative of the upper endpoint as functions of $t$, again using a linear
   slope scan. Missing bounds give infinite endpoints. Querying the cap
   at $B_e$ returns all best replacements.

The envelope work uses $O(nm)$ operations, with at most $2n+1$ pieces
per comparison. The complexity counts exact arithmetic and comparisons on
rational numbers. Running Karp after each proposed replacement costs
$O(nm+n)$ per query. Computing separate complementary-walk tables and
deleted-graph baselines for all comparisons takes $O(nm^2)$ on connected
graphs. The shared pass improves that preprocessing bound on dense graphs
or networks with many parallel comparisons. Dechter, Meiri, and Pearl's
minimal temporal network solves the tight difference bounds at a fixed
tolerance by shortest paths. Nishida studies the broader setting in which
every arc can depend affinely on the parameter. Here the opposite signed
arcs of one edited comparison let us share work across all comparison
choices. [Temporal constraint networks](https://cse.unl.edu/~choueiry/Documents/DechterMeiri-AIJ.pdf) ·
[Linear parametric minimum cycle mean](https://arxiv.org/abs/2609.29234)

## Worked example on World Cup margins

Fit one additive rating per team to the six full-time results from Qatar
2022 Group E. A score margin for the first team estimates its rating minus
the second team's rating. The hypothetical replacement changes the
Spain–Costa Rica margin while holding the other five fixed.
[Published openfootball data](https://raw.githubusercontent.com/openfootball/worldcup.json/master/2022/worldcup.json)

| First team | Second team | Full-time score |
| --- | --- | --- |
| Germany | Japan | 1–2 |
| Spain | Costa Rica | 7–0 |
| Japan | Costa Rica | 0–1 |
| Spain | Germany | 1–1 |
| Japan | Spain | 2–1 |
| Costa Rica | Germany | 2–4 |

The index gives $T(x)=\max(4/3,(2+x)/3,(2-x)/3)$ in goals. The observed
$+7$ requires a worst residual of $3$ goals. The best uniform fit is
$4/3$ goals, attained precisely for hypothetical margins in $[-2,2]$.
The interval is continuous because the query treats the margin as a
real-valued offset.

For an independent exact check, sum the signed error inequalities around
the triangles Germany–Japan–Costa Rica–Germany, Costa Rica–Spain–Japan–Costa
Rica, and Spain–Costa Rica–Germany–Spain. The ratings telescope and give
$3t\ge4$, $3t\ge x+2$, and $3t\ge2-x$, respectively. The observed margin
and both optimum interval endpoints have the following feasible ratings,
which can be checked by subtraction against the match scores.

| Margin $x$ | Cap $t$ | Spain | Costa Rica | Germany | Japan |
| ---: | ---: | ---: | ---: | ---: | ---: |
| $7$ | $3$ | $4$ | $0$ | $1$ | $2$ |
| $-2$ | $4/3$ | $-2/3$ | $0$ | $2/3$ | $1/3$ |
| $2$ | $4/3$ | $2/3$ | $0$ | $2/3$ | $1/3$ |

Interpolating the endpoint ratings certifies every margin inside the
interval. The triangle inequalities exclude all other margins at the
optimal cap.

## Run the index

The Python implementation uses the standard library. The tuple for
each comparison gives its source, target, and offset. In team order
Spain, Costa Rica, Germany, Japan, the source is the second team
because the observed margin is first minus second.

```python
from calibration_replacement import replacement_curves

games = [(3, 2, -1), (1, 0, 7), (1, 3, -1),
         (2, 0, 0), (0, 3, 1), (2, 1, -2)]
curve = replacement_curves(4, games)[1]
print(curve.tolerance(7))       # 3
print(curve.minimum)            # 4/3
print(curve.best_offsets())     # (Fraction(-2, 1), Fraction(2, 1))
print(curve.pieces())           # (start, slope, intercept) triples
```

Run `python3 calibration_replacement_check.py` from this directory
for independent simple-cycle enumeration on small networks, including
the group results, rational offsets, loops, parallel comparisons, and
disconnected cases.
[Python index](calibration_replacement.py) · [Checker](calibration_replacement_check.py)
