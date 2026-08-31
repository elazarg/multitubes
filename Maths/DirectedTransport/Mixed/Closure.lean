/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Closure
public import Maths.DirectedTransport.Mixed.AdjointOrder

/-!
# Complete-lattice closure for mixed directed transport

When the fibers are complete lattices, residuals turn mixed-polarity
constraints into ordinary lax constraints on the laxification graph.  The
least lax majorant there therefore gives a canonical least mixed majorant.
Only the maps on edges already in lax mode need a separate monotonicity
hypothesis: the Galois connections provide the remaining monotonicity.

## Main definitions

* `Maths.Transport.leastMixedMajorant` - the canonical least mixed section
  dominating prescribed lower data.

## Main results

* `Maths.Transport.leastMixedMajorant_isLeast` - the canonical majorant is a
  mixed section, dominates the lower data, and is below every such section.
* `Maths.Transport.exists_isMixedSection_between_iff_leastMixedMajorant_le` -
  a mixed section between lower and upper data exists exactly when the
  canonical majorant is below the upper data.

## Tags

directed transport, mixed polarity, laxification, closure, complete lattice
-/

@[expose] public section

noncomputable section

namespace Maths
namespace Transport

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} (T : Transport G Fiber)

section CompleteLattice

variable [∀ vertex : V, CompleteLattice (Fiber vertex)]
variable {mode : E → EdgeMode}
variable {residual : ∀ edge : LaxificationReverseEdge mode,
  Fiber (G.target edge.1) → Fiber (G.source edge.1)}

/-- The least lax majorant of the lower data after laxifying the mixed
transport using the supplied residual maps. -/
def leastMixedMajorant
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) : ∀ vertex : V, Fiber vertex :=
  (T.laxification mode residual).leastLaxMajorant
    (T.monotone_laxification_of_galoisConnection hlax hresidual) lower

/-- The canonical mixed majorant dominates the lower data, is a mixed section,
and is below every mixed section dominating that lower data. -/
theorem leastMixedMajorant_isLeast
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) :
    (∀ vertex, lower vertex ≤ T.leastMixedMajorant hlax hresidual lower vertex) ∧
      T.IsMixedSection mode (T.leastMixedMajorant hlax hresidual lower) ∧
      ∀ family : ∀ vertex, Fiber vertex,
        (∀ vertex, lower vertex ≤ family vertex) →
        T.IsMixedSection mode family →
        T.leastMixedMajorant hlax hresidual lower ≤ family := by
  have hmono := T.monotone_laxification_of_galoisConnection hlax hresidual
  have hleast := (T.laxification mode residual).leastLaxMajorant_isLeast hmono lower
  refine ⟨hleast.1, ?_, ?_⟩
  · apply (T.isMixedSection_iff_laxification_of_galoisConnection hresidual).mpr
    exact hleast.2.1
  · intro family hlower hfamily
    apply hleast.2.2 family hlower
    exact (T.isMixedSection_iff_laxification_of_galoisConnection hresidual).mp hfamily

/-- A mixed section between lower and upper data exists exactly when the
canonical mixed majorant of the lower data is below the upper data. -/
theorem exists_isMixedSection_between_iff_leastMixedMajorant_le
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower upper : ∀ vertex : V, Fiber vertex) :
    (∃ family, T.IsMixedSection mode family ∧ lower ≤ family ∧ family ≤ upper) ↔
      T.leastMixedMajorant hlax hresidual lower ≤ upper := by
  have hleast := T.leastMixedMajorant_isLeast hlax hresidual lower
  constructor
  · rintro ⟨family, hfamily, hlower, hupper⟩
    exact (hleast.2.2 family (fun vertex ↦ hlower vertex) hfamily).trans hupper
  · intro hupper
    refine ⟨T.leastMixedMajorant hlax hresidual lower, hleast.2.1,
      fun vertex ↦ hleast.1 vertex, hupper⟩

end CompleteLattice

end Transport
end Maths

end
