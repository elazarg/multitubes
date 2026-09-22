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

Build the capstone from this directory with `lake build`.
