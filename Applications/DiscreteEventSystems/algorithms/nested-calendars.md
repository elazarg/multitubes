# A polynomial deadline profile for noncrossing calendars

The [arc-order deadline algorithm](README.md) keeps one bit for each open group. A different exact value algorithm applies when groups are nested even if hundreds are simultaneously open.

Read the sequence of group names on the chosen topological arc order and omit ungrouped arcs. Assume there is no subsequence $A,B,A,B$ for distinct groups $A,B$. Thus first-to-last intervals of groups are disjoint or nested, and a containing group has no occurrence strictly inside an inner group's interval. The second property matters. For example, the spans in $A,B,A,B,A$ are nested, but the middle $A$ occurrence lies inside the $B$ span. A stack checks the full condition by opening a group at its first occurrence, requiring every later occurrence to belong to the current top group, and closing the group at its last occurrence.

This property resembles the topological order restrictions for nested forbidden-pair paths. Those pairs forbid particular vertex co-occurrences. Here a selected group increases every one of its occurrence weights and costs one unit of a shared budget. [Kolman and Pangrác, *On the Complexity of Paths Avoiding Forbidden Pairs*](https://kam.mff.cuni.cz/~kolman/papers/fpath3.pdf)

For each consecutive arc segment, keep a transfer $T(a,b,j)$, the maximum weight contributed by the segment when a path starts at its left event frontier at $a$, ends at its right event frontier at $b$, and consumes exactly $j$ group activations internal to the segment. Absent transfers have weight $-\infty$. A one-arc segment admits zero-weight waits on unchanged frontier vertices and a transition from the arc's tail to its head at the appropriate nominal or perturbed weight. A wait lets the path use a later arc in the same firing. Event frontiers contain at most $W$ vertices. The product for consecutive segments $P,Q$ is
$$
(T_P\star T_Q)(a,b,j)=
\max_{c,\,i+i'=j}\left(T_P(a,c,i)+T_Q(c,b,i')\right).
$$

Inside a group $g$'s scope, compute one product with $g$ off and another with $g$ on. Each direct arc uses the appropriate weight. Use the same transfer of each child scope in the two products. There are no occurrences of $g$ in a child scope, and every group in the child scope is distinct from those outside it. Close the current scope by taking the pointwise maximum of the off transfer and the on transfer shifted upward by one unit of budget. The root consumes no additional budget.

An induction on scopes proves the invariant. Terminal and initial vertices of adjacent segment transfers agree at the shared frontier. Child scenarios use disjoint group sets and their counts add. The scope takes exactly one of its two group decisions and records its cost. Each path and scenario can be split into these subproblems, and any choice of maximizing transfers glues into a valid path and scenario. At the root, prefix maxima of the source-to-sink entries give the at-most-budget values.

There are $O(M+G)$ products and closures, including both alternatives at each scope. A product takes $O(W^3(K+1)^2)$ arithmetic and index operations. The stack holds at most two matrices per open scope, with $O(W^2(K+1))$ entries per matrix. The resulting polynomial bound includes arbitrary nesting depth. The implementation reuses each child transfer and returns the budget profile. The main calendar sweep also computes forced-group sensitivities and witnesses in its own width bound.

For a depth-$120$ example, let one event fire 240 times with nominal duration one. The calendar names occur in order $1,2,\ldots,120,120,\ldots,2,1$. Group $g$ adds $g$ to each of its two firings. All 120 names are open at the middle, and selecting a group raises the final firing by $2g$. Against a due date of 240, the budgets zero through four yield excesses $(0,240,478,714,948)$. The checker also compares 160 seeded small three-event schedules with exact scenario enumeration, including competing chains, rational timings, and earlier checkpoints.

Use `nested_excess(problem, budget)` from [nested_delay_calendars.py](nested_delay_calendars.py), with the `TimingProblem` input described in the main note. The solver uses the supplied order within each firing and rejects crossings. Run [nested_delay_calendars_check.py](nested_delay_calendars_check.py) with `python3 nested_delay_calendars_check.py`.
