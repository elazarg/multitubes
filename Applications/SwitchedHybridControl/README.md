# Switched and hybrid control

Transport can model switched and hybrid certificates by taking fibers to candidate
Lyapunov or storage functions and edges to pullbacks along mode dynamics or resets. With the
orientation chosen for pullback, lax conditions express decrease. Dependent fibers cover
mode-dependent state spaces and noninvertible resets.

Stability, positivity, regularity, and finite certificate templates are supplied by control
theory; transport provides the compositional graph structure.

`ErrorBounds.lean` compares concrete and approximate executions with a local affine error law.
Compatible mode-dependent radii bound every shared finite execution. On finite graphs, bounded
radius synthesis is exactly a finite linear-inequality problem, and infeasibility has a
normalized certificate supported on at most the number of modes plus one rows. The worked
example uses heterogeneous state spaces and a noninjective reset, and also rejects an
incompatible upper budget. This rejection concerns the affine comparison model; it does not by
itself prove that the physical system is unsafe.

`WeightedError.lean` strengthens the finite-execution bound when a positive mode gauge makes
all normalized edge gains contractive. Excess over an invariant radius then decays geometrically
along every walk, even when an individual transition amplifies error. Its concrete affine example
uses real states, unit approximate states, the transitions `x ↦ 1 + 2x` and
`x ↦ 1 + x / 8`, invariant radii `3 / 2` and `4`, and gauge values `1` and `4`; the
machine-checked rate is `1 / 2` for every typed execution. The displayed invariant radii are
also proved pointwise least for this two-edge comparison.
