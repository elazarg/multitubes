# Riccati equations and filtering

This client treats covariance updates as directed transport across modes, sensor configurations,
or information states. Its matrix fibers are positive semidefinite covariance matrices in the
Löwner order. Heterogeneous prediction edges carry

```text
P ↦ A P Aᴴ + Q,
```

and local covariance bounds propagate along every compatible typed walk. The construction allows
the state dimension to vary between vertices.

The scalar specialization also includes the nonlinear observation update

```text
p ↦ p r / (p + r)
```

and its composition with affine prediction. This isolates the order-theoretic content of a scalar
Riccati step while keeping matrix inversion and analytic filtering assumptions separate.

The Löwner order is generally not a lattice, so this domain uses transport results based on order,
monotonicity, and composition without assuming lattice joins. Exact sections describe consistent
covariance families; lax and oplax sections describe one-sided covariance bounds. Statistical
model validity, matrix observation updates, contraction, and convergence require their own
analytic hypotheses.
