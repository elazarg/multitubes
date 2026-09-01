# Coalgebraic refinement

This client interprets directed transport for deterministic labeled coalgebras. A candidate
simulation is a relation between two state spaces. Its one-step lifting requires related
observations and relates the equally labeled successor states.

The lifting is a monotone operator on the complete lattice of relations. A simulation is its
post-fixed point, and the greatest simulation is its greatest fixed point. Reading the lifting as
a one-loop directed transport identifies simulations with oplax sections. The generic walk
calculus then propagates a one-step simulation certificate through every finite unfolding, while
the greatest simulation is transported exactly. In the deterministic setting it also coincides
with related observations after every finite label word.

The model permits different state and observation types on the two sides and an arbitrary
relation between observations. Nondeterministic, probabilistic, and other functor-specific
relation liftings require their own semantics; the transport and fixed-point organization does
not prescribe them.
