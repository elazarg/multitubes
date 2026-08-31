# Quantum channels

This domain assigns an ordered operator space to each quantum system and a positive map to each
process edge. In the Schrödinger picture, Kraus maps push positive operators forward; their
Heisenberg duals pull observables backward. Exact sections describe compatible operators, while
one-sided sections describe certified upper or lower bounds in the Löwner order.

The separation between order and aggregation is essential here. Completely positive maps compose
and preserve order, but noncommuting observables generally have neither joins nor meets. Passing to
all scalar evaluation functions restores pointwise lattice operations while losing representation
by a single observable.

Complete positivity, tensor products, states, operator topology, and physical interpretation remain
part of the quantum application.

The independent Lake package in this directory constructs transport from heterogeneous finite
Kraus families. It also proves that the discard channel has no order residual, so its oplax
constraint cannot be reduced to lax transport by reversing the edge. Run `lake build` from this
directory to check the client.
