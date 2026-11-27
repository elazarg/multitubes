# Mathematical morphology

Transport can model image or signal lattices with dilations, erosions, projections, and
analysis or synthesis maps on edges. Dilation–erosion adjunctions relate the two inequality
directions without requiring inverses, while multiresolution transforms can be represented by
transport between heterogeneous lattices.

Relation images and cores supply the dilation--erosion adjunction, while path closure constructs
least dilation envelopes. Structuring elements, signal semantics, topology, and numerical
algorithms supply the remaining morphological structure.

## Reconstructing a scan line after a strip fails

Several detectors can observe dilations of the same binary seed mask. Each required bright
pixel needs at least one seed in its reverse support. Every required dark pixel rules out all
seeds in its support. For certified interval supports, one index gives the minimum seed cost
after any contiguous strip becomes unavailable. It can also reconstruct a matching mask.
[Derivation, two-camera example and executable checks](algorithms/README.md)
