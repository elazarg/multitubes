# Cellular sheaves and heterogeneous sensor fusion

This client treats a graph sheaf edge as a span of restriction maps between heterogeneous stalks:

```text
F(v) -> F(e) <- F(w),
```

Subdivision into a bipartite incidence graph turns the span into exact map transport. Taking the
pullback relation of the restrictions instead gives relation-labelled transport on the original
graph. Both descriptions recover the same compatible assignments; noninjective restrictions show
why compatibility need not determine a function or permit reconstruction.

The sensor-network development gives this compatibility condition a measured meaning. Each edge
compares two affine calibrations,

```text
sourceScale * sourceReading + offset = targetScale * targetReading.
```

Approximate consistency bounds the absolute discrepancy by an edge tolerance. Two signed linear
inequalities encode each bound. The rational assignment checker verifies proposed readings by
exact arithmetic, while the rational certificate checker verifies a Farkas obstruction that rules
out every real reading at the same tolerances.

The three-sensor example has unit scales and offsets `0`, `0`, and `1` around a directed triangle.
It has no exactly compatible reading. The checker accepts the reading
`(0, -1/3, -2/3)` at tolerance `1/3`, and a normalized obstruction proves that `1/3` is the least
nonnegative uniform tolerance.

Scales are arbitrary affine coefficients; the theory does not assume positivity or invertibility.
Consequently these results establish consistency and optimal tolerance, not reconstruction of a
hidden signal. The executable functions check supplied assignments and certificates. A general
solver that searches for either witness is not implemented.

Sheaf cohomology, topology, richer uncertainty models, and fusion algorithms remain outside the
current scope.
