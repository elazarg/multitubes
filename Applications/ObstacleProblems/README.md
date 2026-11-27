# Obstacle problems and stopping games

This dossier interprets transport for lower and upper obstacle recurrences. Mixed
Bellman inequalities and a clamped fixed-point equation induce lower contact, continuation, and
upper contact regions; the regions are properties of a solution rather than an input edge
partition. Variational, stochastic, and stopping-time semantics remain domain-specific.

The independent client package proves existence and uniqueness when the affine slope is below one,
convergence under the absolute-slope contraction bound, and the lower-contact, continuation, or
upper-contact trichotomy for every solution.

## Solar generation and a finite battery

The battery's empty and full states are lower and upper obstacles. Specifying the load trace
and the generation per unit of installed capacity gives a scalar recurrence at every time.
When the battery saturates, incoming charge histories merge. A sweep uses these mergers to
construct exact import and spill curves across all generation ratings. A contractive periodic
trace uses the clamped fixed point as its initial charge.
[Algorithm, link to the Lean theorem and runnable CSV example](algorithms/README.md)

## A one-time change in supply

On a recorded trace, suppose an extra half kilowatt-hour arrives at one chosen hour. The
battery can finish the day at the same charge whether that energy served a later shortage
or spilled immediately. An index of the two obstacles calculates each quantity separately
for any intervention time, signed amount and deadline. [Derivation, implementation and
96-hour household example](algorithms/pulse-response.md)
