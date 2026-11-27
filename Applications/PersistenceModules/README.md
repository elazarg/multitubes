# Persistence modules and quiver data

This dossier views a quiver representation or persistence module as noninvertible transport:
vertices carry modules and arrows carry maps. An exact section is a compatible family, or a
set-level limit of the diagram. Barcode decomposition, interleavings, stability, and homological
invariants belong to persistence theory beyond this compatibility interpretation.

## Edge-deletion sensitivity

A rooted linear quiver can lose its only forward route into a subtree when an arrow is removed.
For example, let the outward arrow be the identity on two coordinates and the return arrow
project away the second coordinate. After the outward arrow fails, a fixed value at the root
leaves that second coordinate free in the subtree. The algorithm computes the section-space
dimension after every single failure in a shared tree sweep, including on rectangular maps.
[Derivation, Python implementation and examples](algorithms/README.md)
