/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Mixed.Order
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Bellman intervals for mixed-polarity transport

On complete-lattice fibers, the incoming constraints of a mixed-polarity
section have two canonical aggregations.  Lower demand joins the transported
values supplied by lax and exact edges, while upper demand meets the values
supplied by oplax and exact edges.  Exact edges occur in both aggregations;
the resulting two inequalities are precisely equality on such an edge.

The definitions use subtypes of incoming edges.  Thus no finiteness or
decidable equality on vertices is required, and an empty incoming family has
the expected value `⊥` for lower demand and `⊤` for upper demand.

## Main definitions

* `Maths.Transport.IncomingLowerAt` and `Maths.Transport.IncomingUpperAt` -
  the subtypes of incoming edges contributing to each demand.
* `Maths.Transport.lowerDemand` - the join of incoming lower-compatible
  transported values.
* `Maths.Transport.upperDemand` - the meet of incoming upper-compatible
  transported values.

## Main results

* `Maths.Transport.le_lowerDemand` and `Maths.Transport.upperDemand_le` - an
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

/-- Incoming edges whose mode supplies a lower constraint. -/
abbrev IncomingLowerAt (mode : E → EdgeMode) (vertex : V) :=
  {edge : E // G.target edge = vertex ∧
    EdgeMode.IsLaxOrExact (mode edge)}

/-- Incoming edges whose mode supplies an upper constraint. -/
abbrev IncomingUpperAt (mode : E → EdgeMode) (vertex : V) :=
  {edge : E // G.target edge = vertex ∧
    EdgeMode.IsOplaxOrExact (mode edge)}

/-- The join of transported values contributed by incoming lax or exact edges. -/
def lowerDemand (mode : E → EdgeMode) (family : ∀ vertex : V, Fiber vertex)
    (vertex : V) : Fiber vertex :=
  ⨆ edge : IncomingLowerAt (G := G) mode vertex,
    fiberCast Fiber edge.property.1
      (T.edgeMap edge.1 (family (G.source edge.1)))

/-- The meet of transported values contributed by incoming oplax or exact edges. -/
def upperDemand (mode : E → EdgeMode) (family : ∀ vertex : V, Fiber vertex)
    (vertex : V) : Fiber vertex :=
  ⨅ edge : IncomingUpperAt (G := G) mode vertex,
    fiberCast Fiber edge.property.1
      (T.edgeMap edge.1 (family (G.source edge.1)))

/-- Lower demand is monotone when every edge transport is monotone. -/
theorem monotone_lowerDemand
    (mode : E → EdgeMode)
    (hmono : ∀ edge : E, (mode edge).IsLaxOrExact → Monotone (T.edgeMap edge)) :
    Monotone (T.lowerDemand mode) := by
  intro first second hle vertex
  refine iSup_mono fun edge ↦ ?_
  exact fiberCast_le_fiberCast edge.property.1
    (hmono edge.1 edge.property.2 (hle _))

/-- Upper demand is monotone when every edge transport is monotone. -/
theorem monotone_upperDemand
    (mode : E → EdgeMode)
    (hmono : ∀ edge : E, (mode edge).IsOplaxOrExact → Monotone (T.edgeMap edge)) :
    Monotone (T.upperDemand mode) := by
  intro first second hle vertex
  refine iInf_mono fun edge ↦ ?_
  exact fiberCast_le_fiberCast edge.property.1
    (hmono edge.1 edge.property.2 (hle _))

/-- A lower-compatible incoming edge is below the lower demand at its target. -/
theorem le_lowerDemand {mode : E → EdgeMode}
    {family : ∀ vertex : V, Fiber vertex} {vertex : V}
    {edge : E} (htarget : G.target edge = vertex)
    (hmode : EdgeMode.IsLaxOrExact (mode edge)) :
    fiberCast Fiber htarget (T.edgeMap edge (family (G.source edge))) ≤
      T.lowerDemand mode family vertex := by
  exact le_iSup (fun incoming : IncomingLowerAt (G := G) mode vertex ↦
    fiberCast Fiber incoming.property.1
      (T.edgeMap incoming.1 (family (G.source incoming.1))))
    ⟨edge, htarget, hmode⟩

/-- The upper demand at a target is below every upper-compatible incoming edge. -/
theorem upperDemand_le {mode : E → EdgeMode}
    {family : ∀ vertex : V, Fiber vertex} {vertex : V}
    {edge : E} (htarget : G.target edge = vertex)
    (hmode : EdgeMode.IsOplaxOrExact (mode edge)) :
    T.upperDemand mode family vertex ≤
      fiberCast Fiber htarget (T.edgeMap edge (family (G.source edge))) := by
  exact iInf_le (fun incoming : IncomingUpperAt (G := G) mode vertex ↦
    fiberCast Fiber incoming.property.1
      (T.edgeMap incoming.1 (family (G.source incoming.1))))
    ⟨edge, htarget, hmode⟩

/-- The lower-demand inequality is equivalent to every lower-compatible edge
constraint, stated as an inequality in the edge's target fiber. -/
theorem lowerDemand_le_iff
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    T.lowerDemand mode family ≤ family ↔
      ∀ edge, EdgeMode.IsLaxOrExact (mode edge) →
        T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge) := by
  constructor
  · intro h edge hmode
    exact (le_lowerDemand T rfl hmode).trans (h (G.target edge))
  · intro h vertex
    refine iSup_le fun incoming ↦ ?_
    rcases incoming with ⟨edge, htarget, hmode⟩
    simpa only [fiberCast_family] using
      fiberCast_le_fiberCast htarget (h edge hmode)

/-- The upper-demand inequality is equivalent to every upper-compatible edge
constraint, stated as an inequality in the edge's target fiber. -/
theorem le_upperDemand_iff
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    family ≤ T.upperDemand mode family ↔
      ∀ edge, EdgeMode.IsOplaxOrExact (mode edge) →
        family (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) := by
  constructor
  · intro h edge hmode
    exact (h (G.target edge)).trans (upperDemand_le T rfl hmode)
  · intro h vertex
    refine le_iInf fun incoming ↦ ?_
    rcases incoming with ⟨edge, htarget, hmode⟩
    simpa only [fiberCast_family] using
      fiberCast_le_fiberCast htarget (h edge hmode)

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
