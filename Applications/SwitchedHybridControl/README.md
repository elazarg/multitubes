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
