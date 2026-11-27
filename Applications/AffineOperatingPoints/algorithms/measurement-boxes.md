# Matching operating points to measured ranges

Fix a level $\lambda$ in a finite strongly connected network. Each branch $e:u\to v$
contributes $a_e x_u+b_e$ to the maximum $F_v(x)$, and an operating point satisfies
$F_v(x)=x_v+\lambda$ at all vertices. Assume positive rational gains, rational offsets
and level, a nonempty incoming maximum at every vertex, and gain product greater than
one on every directed cycle. The index uses the tight cycles of a greatest relaxed
potential to recover compatible readings. [Operating-point representation](counting-operating-points.md)

Given lower and upper bounds on any channels, return the greatest operating point in that box, or report that there is none. One approach precomputes the $k$ principal readings, where $k$ is the number of critical components. Keep the principal readings that meet the upper bounds. If any survive, their coordinatewise maximum is the greatest operating point below the upper bounds. It meets the box exactly when it also meets every lower bound.

The same query takes two graph searches and does not need to construct either the reachability poset or the principal readings. Use the greatest relaxed potential $U$ and a positive scale $h$ with $r_e=a_eh_u/h_v\ge1$ on each branch $e:u\to v$. Define
$$
z_v=\frac{U_v-x_v}{h_v},
\qquad
s_e=\frac{U_v-a_eU_u-b_e+\lambda}{h_v}.
$$
Both are nonnegative for an old relaxed solution, and its branch inequalities become $z_v\le s_e+r_ez_u$.

1. Initialize each required deficit to $\max(0,(U_v-\bar x_v)/h_v)$ for upper bound $\bar x_v$, using zero where the bound is absent. Propagate requirements backwards across $e$ with $z\mapsto\max(0,(z-s_e)/r_e)$ and take the greatest value received at each vertex. These maps are monotone and never increase a nonnegative deficit, so a maximum-priority label-setting search suffices. The resulting deficits are the least ones satisfying all reverse inequalities and caps. Indeed any such vector dominates the caps transported along every reverse path, and the coordinatewise path maxima satisfy every inequality by extending paths. Subtract the scaled deficits from $U$ to get the greatest capped relaxation $W$.
2. A principal reading seeded at critical representative $c$ meets the upper bounds exactly when $W_c=U_c$. In one direction $W$ dominates every such reading, including its seed value. In the other, a feasible $W$ with $W_c=U_c$ dominates every reading transported forward from the seed, hence dominates the principal reading. If no representative passes the test, the box has no operating point. Otherwise seed the forward search simultaneously at all representatives that pass, with deficit zero. The minimum path deficits for the maps $z\mapsto s_e+r_ez$ give the coordinatewise maximum of the eligible principal readings. Return that vector if it meets the lower bounds.

Besides the one rational LP for $U$ and the $O(nm)$ rational operations to find the scale, preprocessing takes $O(n+m)$ graph operations and linear storage. A box takes $O((n+m)\log(n+1))$ rational operations and $O(n+m)$ storage. Group parallel branches by neighbor and take the best candidate in that group before inserting a label, so each queue has at most $O(n^2)$ entries even on a multigraph. Both searches use simple paths, so intermediate rational values have polynomial bit length. The index can be reused for any number of boxes at the same operating level.

Run `python3 operating_point_boxes.py --input boxes.json` with `z3-solver` installed. Each box maps channel IDs to inclusive `[lower, upper]` pairs. Missing channels and `null` endpoints are unbounded. Integer numbers and rational strings are accepted. The output is an array with a vector of rational strings or `null` for each box.

```json
{
  "vertices": 2,
  "level": 0,
  "branches": [[0, 0, 2, 0], [1, 1, 2, 0], [0, 1, 2, -1], [1, 0, 2, -1]],
  "boxes": [{}, {"0": [null, "-1/2"]}, {"0": [null, "-1/2"], "1": [null, "-1/2"]}]
}
```

The example returns `[["0","0"],["-1","0"],null]`. The checker compares the graph search against the principal-reading scan and independently encodes the original equations and bounds in rational linear arithmetic. A returned vector must satisfy the box, and the solver must rule out a witness with any coordinate above it. [Box solver](operating_point_boxes.py) · [Box checks](operating_point_boxes_check.py)
