# Categorical data migration

This domain studies networks of schemas, instances, or query domains connected by data migrations.
At the predicate or subinstance level, direct image, inverse image, and universal image give ordered
transports related by adjunctions. Exact sections express route-consistent replicated data;
one-sided sections express containment guarantees.

Schemas as categories, instances as functors, natural transformations, Kan extensions, and query
semantics remain additional structure. Element transport does not replace their universal
properties.

## Which records survive every round trip?

In a network of total conversions, a legacy store may contain several aliases for the
same registry key. A flat registry is a retract of each store in its strongly connected
component. This lets one audit whole stores through a smallest store and compute
route-independent readback even when an outward conversion has several possible aliases
across different routes. A separate linear scan classifies individual records and gives
counterexample walks. [Algorithms, hypotheses and checks](algorithms/round-trip-audit.md)
