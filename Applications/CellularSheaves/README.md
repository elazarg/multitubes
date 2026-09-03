# Cellular sheaves and heterogeneous sensor fusion

This client treats a graph sheaf edge as a span of restriction maps between heterogeneous stalks:

```text
F(v) -> F(e) <- F(w),
```

Subdivision into a bipartite incidence graph turns the span into exact map transport. Taking the
pullback relation of the restrictions instead gives relation-labelled transport on the original
graph. Both descriptions recover the same compatible assignments; noninjective restrictions show
why compatibility need not determine a function or permit reconstruction.

Sheaf cohomology, topology, uncertainty models, and fusion algorithms supply the domain-specific
structure.
