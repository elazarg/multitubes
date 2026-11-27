# Fixed routes for a whole interval of starting states

An incoming lot has an uncertain grade. A standardization step can report different grades, and some downstream steps are legal only for certain grades. Given a starting interval, can one route be chosen in advance that keeps every possible execution legal and delivers every outcome to the required grade band?

For explicit monotone transition tables satisfying a checkable order condition, the index takes linear time in the total number of states and table rows. It answers every starting-interval query at every vertex in constant time for one fixed receiving band. It returns an executable sequence of edge IDs in time proportional to its length. This includes cyclic workflows that need to revisit the same station. For acyclic workflows with compact formulas, a separate index can avoid listing the states entirely.

```sh
python3 interval_routes.py
python3 interval_routes_check.py --benchmark
```

## Transport and robust acceptance

State $i$ at vertex $v$ ranges over $X_v=\{0,\ldots,n_v-1\}$. An edge $e:v\to w$ has an interval of legal source states $D_e=[a_e,b_e]$. For each state $i\in D_e$ there is a nonempty set $R_e(i)\subseteq X_w$ of possible outcomes. Outside $D_e$ the edge is disabled. The row minimum $L_e(i)$ and maximum $U_e(i)$ are both nondecreasing on $D_e$. Individual rows may have holes. Deterministic maps have $L_e=U_e$.

Fix a destination $t$ and an accepted interval $B=[a,b]$ at $t$. For a fixed walk $p$ ending at $t$, let $S_p$ be the set of starting states for which every execution of $p$ remains legal and lands in $B$. The empty walk at $t$ has $S_p=B$. Prepending $e$ gives the rule

$$
S_{ep}=P_e(S_p), \qquad
P_e(S)=\{i\in D_e:R_e(i)\subseteq S\}.
$$

This is a backward predicate transformer that includes the legality check. Multitubes supplies typed walk composition for relations and identifies forward powerset transport with relational execution. Its program-semantics client gives the backward predicate transformer for deterministic maps. The robust requirement here uses universal preimages of the outcome relation and treats any blocked branch as failure. [RelationTransport.walkMap_eq_image_walkRelation and walkRelation_append](../../../Maths/Multitubes/Relational.lean) · [backward_obligation_iff_forward_postcondition](../ProgramSemantics/PredicateTransport.lean)

If $S=[s,r]$, then

$$
P_e([s,r])
=\{i\in D_e:L_e(i)\ge s,\ U_e(i)\le r\}.
$$

The first inequality cuts off a prefix of $D_e$ and the second cuts off a suffix. This gives an interval or the empty set. Induction shows every fixed walk has an interval of safe starting states. In particular, the complete set of possible outcomes after one valid step from $[i,j]$ lies in a safe suffix interval exactly when both $L_e(i)$ and $U_e(j)$ lie in it. The minimum and maximum here belong to actual outcomes. Since each suffix has an interval of safe starting states, replacing a nonempty outcome set by its interval hull preserves acceptance for that suffix. A nonempty set of initial states therefore has a common route exactly when its interval hull does.

Different routes can give incomparable safe intervals. For example, two parallel maps on source states $0,1$ send them to $(1,2)$ and $(0,1)$ respectively. Target state $1$ is attainable from either singleton, and a route that works for the first singleton fails for the second. The index tracks which intervals one route can cover.

## Linear index on cyclic graphs

For each lower endpoint $i\in X_v$, let $F(v,i)$ be the largest $j$ for which some fixed walk from $v$ works on $[i,j]$, or $-1$ when there is no such walk. A row of the index means the pair $(v,i)$. Once the largest feasible upper endpoint is stored, testing $[i,j]$ is one comparison.

For each edge $e:v\to w$ and $i\in D_e$, create a reverse incidence from row $(w,L_e(i))$ to row $(v,i)$. Define $Q_e(r)=\max\{x\in D_e:U_e(x)\le r\}$, taking the maximum of an empty set to be $-1$. A suffix witness for ceiling $r$ at $(w,L_e(i))$ extends over $e$ to ceiling $Q_e(r)$ at $(v,i)$ if $Q_e(r)\ge i$. Every valid interval for a walk beginning with $e$ is covered by this rule. Prepending the same edge can only benefit from a larger valid ceiling at the same successor row.

### Check and construct the order

The condition is that each fiber admits strictly increasing integer ranks $g_v$ with

$$
g_v(i)\le g_w(U_e(i))\qquad(e:v\to w,\ i\in D_e).
$$

For example, ranks can follow a common physical grade so the maximum possible output grade never decreases. The construction also works when raw numeric labels are incomparable across stations. Build a graph of individual fiber states with strict arcs $(v,i)\to(v,i+1)$ and weak arcs $(v,i)\to(w,U_e(i))$. Compute strongly connected components. A strict arc internal to a component makes the condition impossible, since the return path forces the opposite weak inequality. Otherwise, topologically numbering the components gives the required ranks, with at most $N=\sum_v n_v$ distinct ranks. An acyclic base graph always passes this check. Reversing every fiber order exchanges the upper and lower envelopes. The resulting condition in the original coordinates is $g_v(i)\ge g_w(L_e(i))$ for strictly increasing ranks.

If $q=Q_e(r)\ge i$, the reverse incidence obeys

$$
g_v(q)\ \le\ g_w(U_e(q))\ \le\ g_w(r).
$$

This inequality supports descending priority settlement even with directed cycles.

### Settle ceilings and store witnesses

Seed $(t,i)$ with ceiling $b$ for every $i\in[a,b]$. Pop the pending row with greatest ceiling rank, settle it and relax all its reverse incidences with the rule above. On a strict improvement record the edge and the already settled successor row. The priorities created by a settlement are at most its own priority. An array of buckets indexed by the ranks supports constant-time insertions and pops, with a single descending scan across the buckets.

Every propagated ceiling is sound. It comes from prepending one edge to the fixed route recorded at the settled successor row. For completeness, consider any feasible interval and walk, and trace backward from the terminal row to its starting row using the lower endpoints along the walk. The terminal seed covers the final interval. Applying the inverse rule backwards gives a candidate at each row that covers the corresponding interval. Candidate ranks are nonincreasing in this backward traversal. Consider the first settlement whose ceiling would be below its optimum. Choose a walk attaining that optimum and take the first still-unsettled row on its backward trace. The terminal seed or the preceding, correctly settled row has already supplied a candidate there of rank at least the optimal starting rank. Strict increase of ranks within the starting fiber places this candidate above the proposed settlement. This contradicts the choice of the next settlement. The same trace rules out a feasible row left unlabelled when the queue empties.

Recorded pointers go from a settled row to a strictly earlier settlement. They therefore give a finite route of at most $N-1$ edges, with a terminal seed as the last row. That route works for every query interval covered by its starting ceiling. A base vertex may appear many times while the lower endpoint changes. The objective is the largest supported upper endpoint. The returned witness can be longer than another valid route.

### Linear work

For each edge keep a cursor initially at the last legal source state. When a successor row is settled at ceiling $r$, move the cursor left past entries with $U_e(x)>r$. Successive processed ceilings in any particular target fiber are nonincreasing because its gauge is strictly increasing. The same cursor therefore computes every call to $Q_e$ exactly and passes each edge table row at most once. Each reverse incidence is considered at most once. There are at most $N$ queue buckets and at most one insertion for each successful relaxation or seed. Stale queue entries can be skipped when their row has already settled.

With $M=\sum_e|D_e|$, time and space are $O(N+M+|E|)$, including order checking and witness storage. This bound assumes the table gives the two extreme outcomes per legal row and counts operations on state indices. If a full relation is provided instead, obtaining its extremal table takes an initial pass over its row data. A failed order check marks an instance outside the fast algorithm's scope. For example, the two-state transport $0\mapsto0,1\mapsto0$ has a robust reset to $0$ while failing the stated upward rank condition.

## Compact acyclic workflows

With formulas for the two monotone envelopes, store the inclusion-maximal safe intervals instead of one row per lower endpoint. Process base vertices in reverse topological order. Each outgoing edge pulls back each retained interval from its target, and the receiving station also starts with its own acceptance band. Pullback is monotone under inclusion, so discarding included intervals loses no feasible source interval. Pulling back uses two binary searches over the guard or a direct inverse supplied by the formula. Each retained interval stores a link to one chosen edge and suffix interval. The prototype assumes the formula callbacks obey the monotonicity and range hypotheses.

Sort the candidate intervals by increasing left endpoint and decreasing right endpoint, and keep the right-endpoint records. Both endpoints of surviving intervals are then strictly increasing. For a query $[i,j]$, binary search for the last interval with left endpoint at most $i$ and compare its right endpoint to $j$. Its witness pointer chain gives the route.

Writing $k_v$ for the number of retained intervals at $v$ and $C_v=\mathbf 1_{v=t}+\sum_{e:v\to w} k_w$ for the number of candidates tested, the work is linear in the base graph plus $O(\sum_{e:v\to w} k_w\log(2+|D_e|) + \sum_v C_v\log(2+C_v))$, assuming constant-time endpoint evaluation. The query costs $O(\log(2+k_v))$ plus the number of returned edges. The bound depends on the intermediate frontier sizes. Those can reach $n_v$ even though they are often much smaller with coarse grading maps.

## Examples and checks

- **Cyclic reconciling route.** At the grading station, standardization sends grades $0,1$ to $\{1,3\}$ and grades $2,3$ to $\{3\}$. Promotion sends $0$ to $\{0,3\}$ and all other grades to $\{3\}$. Archiving is enabled only at grade $3$ and sends it to archive state $1$. From $[0,3]$, the three-edge witness is standardize, promote, archive. The first step gives the set $\{1,3\}$, and the second coalesces those branches to $\{3\}$. All three actions are required. The common route uses both self-loops at the grading station.
- **Large formula input.** The demonstration uses a trillion-state source fiber and two alternative grading routes into accepted grade $2$. The complete source frontier consists of $[2{,}000{,}000{,}000,2{,}999{,}999{,}999]$ and $[10{,}002{,}000{,}000,10{,}002{,}999{,}999]$. The index stores these two intervals without enumerating the source states.
- **Independent cross-check.** The checker enumerates every initial interval on 1,000 seeded random small graphs and fixed fixtures. It searches over concrete reachable subsets by explicitly unioning actual relation rows with holes and rejecting a route as soon as any branch blocks. It checks every yes/no answer and replays every returned witness through those same concrete rows. A single saturating promotion loop with 12,000 grades also returns a witness of exactly 11,999 transitions from $[0,11999]$ to grade $11999$. Every transition in that witness traverses the one self-loop.
- **Explicit-lift comparison.** For the saturating loop $x\mapsto\min(x+1,n-1)$, the complete endpoint-pair lift builds and settles all $n(n+1)/2$ rows. At $n=1024$ the table index stores 1,024 ceilings and the lift settles 524,800 rows. The benchmark prints median Python construction times from three runs. The lift is a baseline for batch feasibility, and the benchmark only builds that feasibility index. Special-case solvers for a single loop can exploit its form independently.

A related example needs both interval endpoints. On grades $0,\ldots,n-1$ allow the promotion $x\mapsto\min(x+1,n-1)$ and an archive action enabled only on $[T,T+K]$, where $T+K<n-1$. For $i\le T$, the largest feasible upper endpoint is $i+K$. The earliest possible archive time is after $T-i$ promotions, and delaying it can only increase the largest grade. For $T<i\le T+K$ the largest feasible endpoint is $T+K$ by immediate archiving. Larger starting grades can never be archived. With $T$ and $K$ proportional to $n$, quadratically many intervals are feasible, and intervals with the same lower endpoint can have different answers.

[Prototype and examples](interval_routes.py) · [Independent checker and comparison](interval_routes_check.py)

## Prior algorithms

Cimatti and Roveri formulate conformant planning as finding one action sequence guaranteed to reach a goal despite nondeterministic actions, and give backward symbolic search for shortest plans. Ryzhikov and Shemyakov prove that the two extreme states suffice for deterministic monotonic subset synchronization and use the pair graph to search for shortest resetting words. The proof here uses the same extreme-state principle and applies it to the legal universal preimage of guarded relations. [Cimatti and Roveri](https://arxiv.org/abs/1106.0252) · [Ryzhikov and Shemyakov, Theorem 2 and Corollaries 1–2](https://arxiv.org/abs/1703.06356)

Antichain search and monotone label settlement are established techniques. The compact DAG variant uses ordinary antichain pruning, with interval inverses that avoid expanding the fiber. The cyclic bound comes from the one-row-per-lower-endpoint reduction, the graph test that generates a bounded priority order, and the shared inverse cursor for each edge. The cited work does not give this particular linear bound for batch interval queries on guarded relational transports. [De Wulf et al., antichain search](https://lsv.ens-paris-saclay.fr/~doyen/papers/antichains-universality-cav06.pdf) · [Sobrinho, generalized path settlement](https://doi.org/10.1109/TNET.2002.801397) · [Dial, bucket queues](https://doi.org/10.1145/363269.363610)
