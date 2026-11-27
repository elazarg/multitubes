# Exact round-trip audits for typed migrations

A registry, cache, and legacy store may use different record IDs for the same
entity. Each directed conversion supplies a total map from IDs in its source
store to IDs in its target. Two questions arise. Which records survive every
round trip to their own store? For a selected registry, which records resolve
to the same registry key along every return route? The second answer supports
a constant-time normalized conversion between stores, even when raw
conversions produce different aliases.

Use a finite directed multigraph with fibers $X_v$ and maps
$f_e:X_u\to X_v$ for $e:u\to v$. Parallel conversions and loops have distinct
IDs. Write $F(p)$ for the composite along a walk $p$. A closed walk at $v$
stays in the strongly connected component of $v$ in the store graph. We
therefore work within one such component at a time. With $n$ stores, $m$
conversions, $N=\sum_v |X_v|$ records, and
$M=\sum_{e:u\to v\text{ internal}}|X_u|$ internal table entries, the explicit
audits take $O(n+m+N+M)$ time and memory. The model assigns a total map to each
allowed transition. Schema equations, partial migrations, and the Kan
extensions associated with schema mappings require additional structure.
[Spivak, *Functorial Data Migration*, §§3–4](https://arxiv.org/abs/1009.1166)

## One minimum-size store decides all whole-store answers

Call a store flat when every closed walk acts as the identity on its whole
fiber. If $r$ is flat, choose walks $i_v:r\to v$ and $b_v:v\to r$. Then
$F(b_v)F(i_v)=1_{X_r}$, so $|X_v|\ge |X_r|$. If equality holds, $F(i_v)$
and $F(b_v)$ are inverses. For any loop $p$ at $v$,
$F(b_v)F(p)F(i_v)=1_{X_r}$, hence $F(p)=1_{X_v}$. Consequently either
there are no flat stores or precisely the minimum-size stores are flat.
This uses the split retract in
[`Maths.categoricalRetract`](../../../Maths/Graph/FlatPathFunctor.lean#L128-L144)
and finite cardinality.
[`Maths.Transport.isFlatAt_toPathFunctor_iff`](../../../Maths/Multitubes/Category.lean#L260-L265)

With lazy access to conversion values, start one simultaneous forward
search from the records of a minimum-size store $r$. Assign each reached
record the key of its first source in $X_r$. A collision between distinct
keys gives two walks ending at the same record. Append the same chosen
return walk to both and evaluate that suffix once. At least one starting
key changes, certifying that $r$ fails. If the search finishes without a
collision, every closed walk at $r$ preserves the starting key because each
registry record was initialized with its own key. An empty minimum fiber
forces all fibers in the component to be empty by totality.

Let $A$ be the lifted records reachable from the minimum store. On success
the search evaluates precisely
$\sum_{(v,x)\in A}\operatorname{outdeg}(v)$ table entries after $O(n+m)$
store-graph work. Failure adds at most $n-1$ probes for one return suffix.
Predecessors use $O(|A|)$ space with expected constant-time dictionary
operations. This can certify a small registry surrounded by large legacy
tables without expanding those tables. If only the minimum store is of
interest, independent forward searches of its keys also visit disjoint
reachable sets on a positive instance.

## All-record audit by terminal components

Build the graph of elements with vertices $(v,x)$ and transitions
$(u,x)\to(v,f_e(x))$. Keep just the transitions internal to a store
component. Walk lifting identifies a failing round trip at $x\in X_v$
with a walk upstairs from $(v,x)$ to another vertex of type $v$.
[`Maths.Transport.elementsGraph` and `liftWalk`](../../../Maths/Multitubes/ElementsGraph.lean#L86-L109)
[Closed-lift theorem](../../../Maths/Multitubes/ElementsGraph.lean#L157-L172)

**Criterion.** A record is fixed by every round trip exactly when its
element component is a sink and it is the sole record of its type in that
component. A sink keeps every lifted walk inside, and a second record of
the same type provides a changing loop by strong connectivity. If the
component has an exit, first reach the source of the exit and leave it.
There is a base walk from the exit's target type back to the record's
type. Its lift exists by totality and cannot reenter the original
component, since reentry would make the exit lie inside that component.

Compute SCCs, mark exits, and scan the records in type order to flag
repeated component IDs within each type. A reusable array indexed by
component ID suffices. This gives the unconditional linear audit by
standard graph traversal. An inward and outward tree per element SCC,
rooted at one exit source when there is an exit, permit witness extraction.
For a duplicate in a sink, travel via the tree root to a same-type peer.
For an exit, append a return via two store trees. These trees and one peer
pointer per flagged record use linear space. A query costs time
proportional to the returned edge list. A sink necessarily contains a
record of every type. The greatest domain closed under the internal maps
on which *every* store is flat is the union of sinks having exactly one
record of each type, since any closed domain containing a record contains
its entire forward orbit.
[Tarjan, linear-time strongly connected components](https://doi.org/10.1137/0201010)

## Largest domain with unambiguous registry readback

Choose a registry $r$, which may itself fail the whole-store audit. For
$y\in X_v$ let $A_v(y)=\{F(p)(y):p:v\to r\}$ within its store component.
Every such set is nonempty. Let $D_v=\{y:|A_v(y)|=1\}$ and write $R_v(y)$
for the unique key on $D_v$. For an edge $e:v\to w$,
$A_w(f_e(y))\subseteq A_v(y)$ by concatenation. Thus $D$ is closed under
every internal edge and $R_w f_e=R_v$ there. Every domain with unambiguous
readback is contained in $D$.

If $A_v(y)=\{x\}$, some route sends $y$ to $x$. Appending any registry
round trip shows $A_r(x)=\{x\}$, so $x\in D_r$. Set $P=D_r$ and choose one
ingress walk $i_v:r\to v$ for each type. Its restriction
$I_v=F(i_v)|_P$ maps $P$ into $D_v$ by forward closure and satisfies
$R_v I_v=1_P$. Every chosen return walk induces the same $R_v$ on $D_v$.
Thus $Q_v=I_vR_v$ is a projector on $D_v$ and, for every $p:v\to w$,

$$
Q_w F(p)|_{D_v}=I_wR_v=Q_w F(p)Q_v.
$$

The normalized maps $I_wR_v$ are inverse on the images of the projectors.
The formula is the Type instance of
[`Maths.categorical_compressed_map_eq`](../../../Maths/Graph/FlatPathFunctor.lean#L158-L178)
applied to the restricted transport $D$, which is flat at $r$ with fiber
$P$. The endpoint formula evaluates a normalized result in constant time from
the key and ingress tables. The operation takes endpoints
in the same store component. Parsing or checking a caller's particular
walk still costs time proportional to its length.
[`Maths.categorical_coreMap_comp_reverse`](../../../Maths/Graph/FlatPathFunctor.lean#L180-L208)

Compute the return index by reverse multi-source search from all registry
records. Retain at most two distinct keys per record and enqueue each
retained pair once. Every pair comes from a real walk. At termination a
record with a singleton label can only have successors labeled with the
same singleton. Indeed each retained successor label was propagated, and
a second distinct label would have persisted. Following a route to $r$
then proves all return keys agree. Every record in the registry's
component receives at least one label by totality and strong connectivity
of the store graph. For ambiguity, each pair stores one pointer to an
earlier pair and its edge. Following the pointers produces two actual
returns and their distinct keys in time proportional to their lengths.
At most two labels traverse each lifted edge. For ingress, propagate the
$|P|$ safe keys along one out-tree of the store graph. This uses at most
$N$ additional table entries because $I_v$ is injective for every $v$.

### An example with aliases and ambiguous readback

Let $X_r=\{0,1,2\}$ and $X_w=\{a,b,c,d,e\}$. Two outward maps take
$(0,1,2)$ to $(a,c,d)$ and $(b,c,d)$, respectively. Two return maps take
$(a,b,c,d,e)$ to $(0,0,0,2,1)$ and $(0,0,0,2,2)$. Key $1$ changes to $0$
on a round trip. The safe registry keys are $0,2$. The aliases $a,b$ both
read back as $0$, but a loop from $a$ through $r$ can end at $b$. The two
returns from $e$ disagree. On the safe domain normalized conversion picks
one alias using the chosen ingress.

Number the legacy records $a$ through $e$ from 0 to 4. The two aliases
have the same registry key, and the auditor can still exhibit a raw
round trip that changes the first alias.

```python
from round_trip_audit import RoundTripAudit

outgoing = [(0, 1, [0, 2, 3]), (0, 1, [1, 2, 3])]
returning = [(1, 0, [0, 0, 0, 2, 1]), (1, 0, [0, 0, 0, 2, 2])]
audit = RoundTripAudit([3, 5], outgoing + returning)
registry = audit.registry(0)
assert registry.return_keys(1, 0) == registry.return_keys(1, 1) == (0,)
assert set(registry.return_keys(1, 4)) == {1, 2}
assert audit.counterexample(1, 0) is not None
```

Even a whole flat registry can have two raw outward maps. Remove $c$ and
key $1$ in the example, and send $e$ to $0$ or $2$ on the two returns.
Both outward maps still exist, their composites with any return are
identity at the registry, and the returns still identify two distinct
aliases. A group-gain approach assumes reversing a conversion inverts
its action. Whole-store flatness at the registry gives a left inverse
along a return. A return that merges aliases cannot be inverted on the
warehouse fiber. [Zaslavsky, *Biased Graphs. I*, group gains](https://doi.org/10.1016/0095-8956(89)90063-4)

## Comparators and verification

- Independent per-record BFS can stop at the first failure and is useful
  for a few queries. On $n$ stores in a bidirectional ring with $k$ stable
  record lanes, it visits $kn^2$ states to answer all records. The terminal
  component scan visits $kn$ states and $2kn$ transitions. A generic
  reachability index can also check pairs, and already uses SCC reduction.
  The sink criterion eliminates the subsequent pair queries for this
  workload. [Yıldırım, Chaoji and Zaki, *GRAIL*, §§2–3](https://www.cs.rpi.edu/~zaki/PaperDir/VLDBJ12.pdf)
- Full registry reachability can compute the set of possible keys, for
  example with one reverse traversal per key or with a bitset for each
  record. The two-key cap is sufficient for uniqueness and preserves two
  traceable failures. If the full set of reachable keys is required, the
  cap discards information needed for that output.
- The explicit audit's worst-case table scan is necessary. Put identity
  maps on arbitrarily many parallel transitions in both directions
  between two two-record stores. Altering any one table entry changes a
  round trip via a reverse transition. A tester on the identity instance
  that skipped that entry could not distinguish these inputs. The lazy
  audit gains when the minimum store reaches only a small part of the
  table.

Run `python3 round_trip_audit_check.py` for exhaustive small and seeded
random comparisons of all statuses, normalized results, and replayed
witnesses against independent explicit reachability. The optional
`--benchmark` runs the bidirectional ring and a narrow-registry workload.
With 24 workspaces of 4,096 records each, the lazy whole-base audit made
192 conversion calls and the full audit read 98,400 entries. These are
different workloads. The full audit also answers all individual-record
round-trip queries.
[Implementation](round_trip_audit.py) · [Checker](round_trip_audit_check.py)
