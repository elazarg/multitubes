# Exact deadline stress tests for shared delay calendars

One slow supplier can delay several firings of a production line. To test a deadline, select up to $K$ supplier, crew or other common-cause delays, then propagate each selected delay through every affected dependency. The algorithm computes the largest deadline excess for each budget up to $K$. It also computes, in the same two passes, the largest excess at the requested budget with each group suppressed and with each group required. Suppressing a group models making that named resource reliable. Requiring a group tests the remaining margin when that delay is already known and counts it against the budget.

The running time is $O(H+n+(M+WG)(K+1)2^w)$ arithmetic and index operations. Here $H$ is the number of firings, $n$ is the number of event types, $M$ counts dependency, release and deadline arcs, $G$ counts delay groups, $W$ is the peak event frontier, and $w$ is the peak number of group calendars open in a chosen chronological arc order. In particular, hundreds of distinct groups can be tractable when only a few of their first-to-last occurrence intervals overlap. A group can occur several times along the same dependency chain.

[Run the exact Python implementation](delay_calendars.py) with `python3 delay_calendars.py`. [Run the independent checker](delay_calendars_check.py) with `python3 delay_calendars_check.py`. Both use the Python standard library.

A second algorithm handles calendars nested to any depth, provided occurrences of two distinct causes never alternate as $A,B,A,B$. It computes the worst lateness at each budget by reusing a transfer for each enclosed calendar. [Nested calendars and a depth-120 example](nested-calendars.md)

## Timing model

Let $x_0(v)$ be the initial time of event $v$. In firing $t$, every dependency occurrence $e=(u,v)$ has nominal delay $a_e$, nonnegative extra delay $d_e$, and optionally a group $g(e)$. A scenario $S$ is a subset of named groups. The recurrence is
$$
x_t(v;S)=\max_{e=(u,v)\text{ at }t}
 \bigl(x_{t-1}(u;S)+a_e+d_e\mathbf 1[g(e)\in S]\bigr).
$$
Ungrouped occurrences have zero extra delay. The scenario is fixed across the entire horizon, including firings that a particular dependency chain skips by ending early. The same group may affect different arcs with different increments. Each occurrence belongs to at most one group. The horizon contains an explicit list of firing layers, and the same physical dependency can appear in each layer. Unreachable event times are $-\infty$.

Each checkpoint $(t,v,D)$ has deadline $D$. The scenario's excess is the maximum of $x_t(v;S)-D$ over the checkpoints. For each budget, maximize this quantity over $|S|\le K$. A positive result certifies a missed deadline, and a result at most zero certifies that every finite monitored firing is on time across the specified scenarios. If no monitored firing is reachable, the algorithm returns no finite value. The group-conditioned results impose $g\in S$ or $g\notin S$ and retain the same budget.

This is the horizon expansion of the application’s floorless unit-slope firing rule. For a fixed scenario with a finite initial vector and an incoming dependency at every vertex in each layer, the firing updates are exactly the operators implemented by `TimedNetwork.step`, with the corresponding delays installed at each step. The duration change here has finite calendar support, so a nominal long-run cycle time can remain unchanged while a monitored firing changes from on time to late. The expanded graph and the algorithm below work directly with the dates. [Firing operator and eigen-schedules](../DiscreteEventSystems/Synchronization.lean) · [Certified cycle times](../DiscreteEventSystems/CertifiedSchedule.lean)

## Dependency paths and calendar width

Use one vertex $(t,v)$ for each event occurrence. The arcs for firing $t$ go from layer $t-1$ to layer $t$. A super-source has an arc of weight $x_0(v)$ to each finite initial event. A checkpoint arc of weight $-D$ goes from $(t,v)$ to a common sink. By induction on firing layers, the scenario's excess is exactly the longest source-to-sink path weight in this acyclic graph. Parallel dependencies remain distinct. A path and scenario witness a lower bound on the worst excess, even when the deadline being maximized changes with the scenario.

Scan release arcs first, then each firing's arcs followed by the checkpoints it reaches. Process the layer-zero checkpoints after the releases. Any ordering within a firing is legal because each arc goes from the previous layer to the next one. In this serialization all incoming arcs of each ordinary vertex precede all its outgoing arcs. The sink can hold a path that has already reached a monitored checkpoint.

A group's scope starts before its first dependency arc and ends after its last one, inclusive. At each arc let the open set consist of all groups whose scope covers the arc. The maximum set size is $w$. A calendar can stay open during a gap between its occurrences because future occurrences must receive the same decision. A singleton group can open and close around one arc. The prototype clusters occurrences of the same group within each firing, in order of first appearance in that firing, and also accepts the raw order. Both have the same answer. The bound uses the width of the chosen order.

The event frontier holds a source-to-current-vertex path while that vertex still has an outgoing arc to be processed. Ordinary vertices without any future use can be discarded. The sink remains available until the end. At most two firing layers coexist, so $W\le 2n+2$. The cost bound also applies to any supplied topological arc order for an acyclic precedence graph, with $W$ and $w$ measured for that order.

## A forward pass and all one-group results

A forward label $F(v,A,j)$ is the heaviest path so far at frontier vertex $v$, with open selected group set $A$ and exactly $j$ total groups selected since the beginning. The count includes selected groups whose calendars have already closed. Missing labels have weight $-\infty$. Initialize the source label with empty set, count zero, and weight zero.

- **Open a calendar.** Duplicate each state into the off and on branches. The on branch adds the group to $A$ and increments $j$, subject to $j\le K$.
- **Scan an arc.** Carry the path until a later arc or relax the head from the tail using the arc's weight under $A$. This changes neither $A$ nor $j$. The arc update scans only the labels at its tail.
- **Close a calendar.** Project out that bit, taking the larger label when two states coincide. Keep $j$ unchanged.

Every path is scanned in its traversal order. Every globally chosen scenario assigns one bit at each opening. Two prefixes with the same frontier vertex, open mask and total count have the same possible continuations with the same future weights. In particular, any closed group can affect the future only through the remaining budget. This proves the forward invariant by induction. At the sink all bits have closed. Prefix maxima over exact counts give the best excess for every at-most budget.

Run a backward pass through the same transitions, starting at the sink with zero suffix value for every allowed total count. The suffix value $B(v,A,j)$ uses the already-consumed count $j$ from its cut. For a group $g$, retain the forward labels immediately before its opening and inspect its backward labels immediately after. For each status $b\in\{0,1\}$, maximize
$$
F(v,A,j) + B(v,A\cup(\{g\}\text{ if }b=1\text{, else }\varnothing), j+b)
$$
over compatible states with $j+b\le K$. The joined prefixes and suffixes agree at their frontier vertex and on every other group still in scope. Before the opening no path has used an occurrence of $g$. After the opening $g$ is consistently charged and applied across all its occurrences. Each complete scenario and path crosses this decision once, so both conditioned maxima are exact. In particular, the larger of the two conditioned results is the unconditioned result at that cap.

This split computes the entire one-group mitigation table at once. A prefix and a suffix each keep a link to the edge relaxation or group choice that attained the label. They can share unchanged parts of their witness histories. At a conditional optimum, concatenate the two histories and record the forced choice. The resulting scenario and dependency chain can be checked by summing the original arc weights or replaying the original recurrence for that scenario.

Each arc update takes $O((K+1)2^w)$ operations, and each opening or closing, including both conditional maxima, takes $O(W(K+1)2^w)$. The labels, snapshots and witness links require $O(H+n+(M+WG)(K+1)2^w)$ storage in the prototype. A traversal needs only the current frontier tables when snapshots and persistent histories are omitted. These bounds count rational operations and mask and index operations. A mask uses at most $w$ bits, because the code recycles slots at calendar closings. The budget can be capped at $G$, and its counter has $O(\log(2+G))$ bits. With input durations, increments and release or deadline dates of at most $L$ bits, each path score is a sum of $O(H+1)$ such numbers, so its exact representation has $O((H+1)L+\log(H+2))$ bits. The Python version uses sparse dictionaries. Materializing a witness takes time proportional to its path plus its selected groups. Writing every witness in the CLI can cost more than writing just the table of values.

## Why occurrence counts and nominal critical paths are insufficient

The demo has two production paths that start together and reconverge at a single deadline. The nominally slow path takes $4+4+3+3=14$. The other path takes $2+2+2+2=8$ nominally. A supplier delay adds two at its first and third stages, and a crew delay adds two at its second and fourth stages. The due date is $14$. One group leaves the slow path critical and the largest excess at zero. With both groups the other path takes $16$ and excess is two. Suppressing either group restores a worst excess of zero at budget two. On the independently perturbed-occurrence model, two extra delays yield at most $8+2+2=12$ on the exposed path. This certifies a different deadline result.

More generally, a model that pays once per altered occurrence gives a lower bound at the same budget, because activating the labels of the altered occurrences adds at least the same delays. If $\ell$ bounds the number of occurrences of a single group on any path, an occurrence budget of $K\ell$ gives an upper bound, since any allowed path under a group scenario receives at most that many increments. That upper bound also admits paths using more than $K$ groups. Activating every group gives a further upper bound. Exact scenario enumeration can compute all the requested values in one pass over subsets by recording each scenario's value under both statuses of each group. Its number of scenario replays is $\sum_{j=0}^K \binom Gj$.

## Hardness with two occurrences per group

Even with at most two event vertices per firing, zero nominal durations, unit positive increments, and at most two occurrences of each group, testing whether the worst excess reaches a given threshold is NP-complete. The path and group assignment serve as a certificate. The following reduction uses the same mechanism as minimum-label paths: when every arc on an equal-length path must receive its increment, the budget charges the distinct labels along the path. [Hassin, Monnot and Segev, *Approximation Algorithms and Hardness Results for Labeled Connectivity Problems*](https://doi.org/10.1007/s10878-007-9044-x)

The reduction adapts the variable and clause choices in the minimum-color path proof of Broersma, Li, Woeginger and Zhang. Assigning a separate group to every literal occurrence and padding the two variable tracks gives the bounds of two occurrences per group and two event positions per layer here. [*Paths and Cycles in Colored Graphs*, Theorem 11](https://ris.utwente.nl/ws/files/253281267/Broersma2005paths.pdf)

Given a 3-SAT instance, give each literal occurrence its own group. For variable $i$, create two parallel directed tracks, one with each positive occurrence's group and the other with each negative occurrence's group. Their endpoints coincide at the boundaries of the variable gadget. Pad the shorter track to length $b_i$ equal to the longer track's length. Each padding edge receives a private group. Omit variables that do not occur. Chain the variable gadgets in series, followed by one layer per clause with three parallel arcs. The labels on those arcs are the three occurrence groups for the clause. All arcs carry zero nominal time and one positive extra unit. Use initial time zero at the source, budget $B=\sum_i b_i$, and a single final due date $B+m$ for $m$ clauses.

A path reaching that date must receive the increment on every one of its $B+m$ arcs. Its variable tracks have $B$ distinct labels, so the whole budget is committed to those labels. Every clause arc on the path must reuse one of them. The variable tracks then encode an assignment satisfying each clause. Conversely, the tracks of any satisfying assignment use $B$ labels, and each clause has a matching arc carrying one of those labels. This constructs an excess-zero path. Since the arrival weights are integers, moving the due date half a unit earlier gives a strict deadline miss exactly when the formula is satisfiable. Each literal label appears twice, and each padding label appears once. The two tracks have no cross-dependencies before reconvergence, so two event slots per layer suffice. Long calendar scopes are possible even with these restrictions.

## Prior algorithms and scope

For project makespan with nonnegative durations, this is the arc-duration form of Wu, Demeulemeester and Matuschke’s $\mathrm{PSIP\text{-}DG}_{B,\infty}$ with disjoint groups, unit group activation cost, and no limit within an activated group. Splitting a weighted arc into an activity gives their node-duration representation. Since all selected increments are nonnegative, the entire group can be set to its maximum in that variant. Their $B,1$ variant gives each activated group one delayed activity, a different feasible set. Their more general polyhedral group sets can constrain the increments jointly. Section 3.1 solves groups that are singletons or antichains, and a case with no precedence between different groups. Width $w$ allows precedence within a group and between groups. Arbitrarily many antichain groups can overlap in the chosen scan, so their tractable cases can also apply at high width. Section 3.3 proves hardness for $B,\infty$ by maximum coverage, and the at-most-two-activities hardness there is for $B,1$. Their experiments use exact mixed-integer optimization and their §4 heuristics for general instances. This note supplies a width-dependent exact bound with a bulk one-group sensitivity workload. [Wu, Demeulemeester and Matuschke, §§2–5](https://arxiv.org/html/2608.27386v1)

The forward and backward passes are max-sum messages on a path of separators, an instance of variable elimination and junction-tree max-marginals. The specialization exposes a separator with only the current event, the live group bits and the single running cardinality, while allowing sparse arc updates and using exact integer counts. A direct firing-level factor over all groups used in that firing can be much wider, even for a layer of singleton causes. Earlier max-plus predictive-control work propagates finite-horizon matrix perturbations and optimizes controls over uncertainty sets. Here release times and deadlines are fixed, and the optimization returns exact excess and trace evidence for the linked binary calendar scenarios. [Dechter, *Bucket Elimination*](https://doi.org/10.1016/S0004-3702(99)00059-4) · [Aji and McEliece, *The Generalized Distributive Law*](https://authors.library.caltech.edu/records/sw1pm-bwj40) · [Van den Boom and De Schutter, *Model predictive control for perturbed max-plus-linear systems*](https://doi.org/10.1016/S0167-6911(01)00162-1)

## Running a timing problem

Use the default example or pass a JSON input with `python3 delay_calendars.py --input example.json --budget 2`. The input has an `initial` vector, a `layers` list of dependency lists, and a `deadlines` list. Event indices start at zero. Firing layers in deadlines start at one, with layer zero available for initial checkpoints. Rational numbers can be strings such as `"5/2"`. An absent initial value uses `null`. An ungrouped dependency omits `group` and `extra`.

```json
{
  "initial": [0],
  "layers": [
    [{"tail": 0, "head": 0, "nominal": 2, "group": "supplier", "extra": "1/2"}],
    [{"tail": 0, "head": 0, "nominal": 2, "group": "supplier", "extra": "3/2"}]
  ],
  "deadlines": [{"layer": 2, "vertex": 0, "due": 5}]
}
```

The two supported budgets return excesses $-1$ and $1$. With expected supplier reliability the deadline holds, and the selected supplier calendar misses it by one. The result's `best_by_budget` entries run through the smaller of the requested cap and the number of groups. Higher budgets share the last result. The `avoided` and `required` tables use the requested budget, with `null` for unreachable observations or impossible conditions. A witness lists each dependency by its one-based firing layer and zero-based position in the original layer.

The independent checker enumerates allowed scenarios and replays the synchronous firing recurrence using rational arithmetic. It compares all budget values, both conditions for every group, and the reconstructed witnesses in two arc orders. It includes early checkpoints, parallel dependencies, unreachable states, repeated groups crossing between layers, and the hard instances generated by the reduction. Run `python3 delay_calendars_check.py --benchmark` for exact subset-enumeration timings on three-event recurrent schedules whose calendars each recur three times and have width three. The larger schedule has 240 groups and 484 firings, with $137{,}114{,}541$ allowed subsets at budget four.
