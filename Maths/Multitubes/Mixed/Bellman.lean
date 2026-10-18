/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure
public import Maths.Multitubes.Mixed.Order

/-!
# Bellman intervals for mixed-polarity transport

On complete-lattice fibers, the incoming constraints of a mixed-polarity section have two
canonical aggregations.  Lower demand is the incoming join of the transport restricted to its lax
and exact edges, and upper demand is the incoming meet of the transport restricted to its oplax
and exact edges.  Exact edges occur in both aggregations; the resulting two inequalities are
precisely equality on such an edge.

## Main definitions

* `Maths.Transport.lowerDemand` - the incoming join over the lax and exact edges.
* `Maths.Transport.upperDemand` - the incoming meet over the oplax and exact edges.

## Main results

* `Maths.Transport.edgeMap_le_lowerDemand` and `Maths.Transport.upperDemand_le_edgeMap` - an
  incoming compatible edge lies on the appropriate side of its demand.
* `Maths.Transport.lowerDemand_le_iff` and
  `Maths.Transport.le_upperDemand_iff` - the function-order forms of the
  incoming lower and upper constraints.
* `Maths.Transport.monotone_lowerDemand` and
  `Maths.Transport.monotone_upperDemand` - monotonicity inherited from the
  edge maps.
* `Maths.Transport.isMixedSection_iff_lowerDemand_le_and_le_upperDemand` -
  the pointwise Bellman interval characterization of ordered mixed sections.

## Tags

transport, mixed polarity, Bellman operator, complete lattice
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

/-- The join of the values transported into each vertex along its lax and exact edges: the
incoming join of the restriction to those edges. -/
def lowerDemand (mode : E → EdgeMode) : (∀ vertex : V, Fiber vertex) → ∀ vertex : V, Fiber vertex :=
  (T.restrictEdges {edge | (mode edge).IsLaxOrExact}).incomingSup

/-- The meet of the values transported into each vertex along its oplax and exact edges: the
incoming meet of the restriction to those edges. -/
def upperDemand (mode : E → EdgeMode) : (∀ vertex : V, Fiber vertex) → ∀ vertex : V, Fiber vertex :=
  (T.restrictEdges {edge | (mode edge).IsOplaxOrExact}).incomingInf

/-- Lower demand is monotone when every lax or exact edge transport is monotone. -/
theorem monotone_lowerDemand (mode : E → EdgeMode)
    (hmono : ∀ edge : E, (mode edge).IsLaxOrExact → Monotone (T.edgeMap edge)) :
    Monotone (T.lowerDemand mode) :=
  IsMonotone.monotone_incomingSup fun edge => hmono edge.1 edge.2

/-- Upper demand is monotone when every oplax or exact edge transport is monotone. -/
theorem monotone_upperDemand (mode : E → EdgeMode)
    (hmono : ∀ edge : E, (mode edge).IsOplaxOrExact → Monotone (T.edgeMap edge)) :
    Monotone (T.upperDemand mode) :=
  IsMonotone.monotone_incomingInf fun edge => hmono edge.1 edge.2

/-- A lax or exact edge transports below the lower demand at its target. -/
theorem edgeMap_le_lowerDemand {mode : E → EdgeMode} (family : ∀ vertex : V, Fiber vertex)
    {edge : E} (hmode : (mode edge).IsLaxOrExact) :
    T.edgeMap edge (family (G.source edge)) ≤ T.lowerDemand mode family (G.target edge) :=
  edgeMap_le_incomingSup (T := T.restrictEdges _) family ⟨edge, hmode⟩

/-- The upper demand at its target is below the transport along an oplax or exact edge. -/
theorem upperDemand_le_edgeMap {mode : E → EdgeMode} (family : ∀ vertex : V, Fiber vertex)
    {edge : E} (hmode : (mode edge).IsOplaxOrExact) :
    T.upperDemand mode family (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) :=
  incomingInf_le_edgeMap (T := T.restrictEdges _) family ⟨edge, hmode⟩

/-- The lower-demand inequality is equivalent to every lower-compatible edge
constraint, stated as an inequality in the edge's target fiber. -/
theorem lowerDemand_le_iff
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    T.lowerDemand mode family ≤ family ↔
      ∀ edge, EdgeMode.IsLaxOrExact (mode edge) →
        T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge) :=
  incomingSup_le_iff.trans Subtype.forall

/-- The upper-demand inequality is equivalent to every upper-compatible edge
constraint, stated as an inequality in the edge's target fiber. -/
theorem le_upperDemand_iff
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    family ≤ T.upperDemand mode family ↔
      ∀ edge, EdgeMode.IsOplaxOrExact (mode edge) →
        family (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) :=
  le_incomingInf_iff.trans Subtype.forall

/-- An ordered mixed section is exactly a pointwise interval between its lower
and upper incoming demands.  Exact edges are included in both demands. -/
theorem isMixedSection_iff_lowerDemand_le_and_le_upperDemand
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    T.IsMixedSection mode family ↔
      T.lowerDemand mode family ≤ family ∧ family ≤ T.upperDemand mode family := by
  constructor
  · intro hfamily
    constructor
    · apply (lowerDemand_le_iff T).mpr
      intro edge hmode
      rcases hmode with hmode | hmode
      · exact hfamily.lax hmode
      · exact (hfamily.exact hmode).le
    · apply (le_upperDemand_iff T).mpr
      intro edge hmode
      rcases hmode with hmode | hmode
      · exact hfamily.oplax hmode
      · exact (hfamily.exact hmode).ge
  · rintro ⟨hlower, hupper⟩
    have hlower' := (lowerDemand_le_iff T).mp hlower
    have hupper' := (le_upperDemand_iff T).mp hupper
    intro edge
    cases hmode : mode edge with
    | lax => exact hlower' edge (Or.inl hmode)
    | exact =>
        apply le_antisymm
        · exact hlower' edge (Or.inr hmode)
        · exact hupper' edge (Or.inr hmode)
    | oplax => exact hupper' edge (Or.inl hmode)

end CompleteLattice

end Transport
end Maths

end
