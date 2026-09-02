/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathematicalMorphology.RelationalTransport

/-!
# Relational mathematical morphology and transport

Relational dilation and erosion provide a small mathematical-morphology client for directed
transport.  A relation's existential image is dilation, while its universal core is erosion.
The image--core Galois connection reverses mixed erosion constraints without requiring a
relation to be functional or invertible.

## Main definitions

* `MathematicalMorphology.erosionTransport` - dependent erosion transport.
* `MathematicalMorphology.dilationTransport` - dependent dilation transport.

## Main results

* `MathematicalMorphology.mixedErosionLaxification_iff` - mixed erosion sections become
  lax dilation sections after reversing edges.
* `MathematicalMorphology.leastDilationEnvelope` - path closure is the least lax dilation
  family above prescribed lower data.
* `MathematicalMorphology.universal_core_image_not_inverse` - a relational dilation and
  erosion need not be inverse operations.
* `MathematicalMorphology.universalRelation_not_functional` - the concrete relation is not
  a function graph.
* `MathematicalMorphology.universalRelation_not_rightUnique` - one input has two outputs.

## Tags

mathematical morphology, dilation, erosion, relation, transport, Galois connection
-/

@[expose] public section

namespace MathematicalMorphology

export Maths (EdgeGraph EdgeMode Transport)

end MathematicalMorphology
