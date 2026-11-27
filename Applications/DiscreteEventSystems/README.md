# Discrete-event systems and network calculus

This compiled capstone models a synchronization network as a max-plus timed event graph. Each
edge carries a delay, and the next firing time of an event is the maximum demand among its incoming
dependencies. The Lean development connects that operational recurrence directly to
`Maths.MaxAffineTransport.vertexOperator`.

The main theorem proves exact linear growth from an eigen-schedule. Its scope is intentional:
timed-network labels are floorless translations of slope one, so the update is additively
homogeneous. Every initial timing vector on a finite event set consequently remains within a
uniform constant of the linear schedule. General max-affine operators do not support the same
throughput conclusion. The reciprocal interpretation assumes a positive cycle time; the abstract
model permits real delays, while physical delay models ordinarily add nonnegativity assumptions.

The explicit two-event example satisfies

```text
a(n + 1) = max (a(n) + 2) (b(n) + 1)
b(n + 1) = max (a(n) + 4) (b(n) + 3).
```

The phase `(0, 2)` is certified to grow by exactly `3n`, giving cycle time `3` and nominal
throughput `1/3` event cycles per unit time. A checked perturbation raises the first self-delay to
four; synchronized phase `(0, 0)` then has cycle time `4`, so its certified throughput is `1/4`.

`CertifiedSchedule.lean` derives a phase from a maximizing cycle instead of assuming one. Given
a cycle-time bound attained at a vertex that reaches every event, it uses greatest shifted walk
weights to construct a schedule. On a finite globally reachable graph with a nonempty cycle, a
maximum-mean closed walk exists and yields such a schedule mathematically. The returned walk
directly records the attained mean and proves optimality against every phase satisfying the edge
demands at any proposed upper cycle time. This is an existence and certificate theorem, not an
executable optimizer.

For the two-event network, the second event's delay-three self-loop is the bottleneck. The rooted
construction gives phase `(-2, 0)`, a translate of `(0, 2)`, and proves both the cycle-time-three
schedule and the lower bound `3` for every competing feasible cycle time.

Build the capstone from this directory with `lake build`.

## Finite schedules with correlated delays

A supplier delay can lengthen several dependencies before two production paths rejoin.
The calendar algorithm charges that cause once across the schedule. Given a budget of distinct
causes, it computes the worst deadline lateness and how that value changes when each cause is
ruled out or required. The running time depends on how many causes the scan must remember
at once. [Algorithm, production example and exact scenario checks](algorithms/README.md)

## Restarting a periodic machine within its buffer limits

A connected circulation with zero total charge supplies exact transition counts for a
balanced period. The schedule can be stored as repeated words even when the counts are
large binary integers. Given the starting stock, the restart index computes all phases
of that period that satisfy the capacities throughout the cycle for every allowed value
of a fixed calibration. [Construction, phase queries and checks](algorithms/periodic-buffers.md)
