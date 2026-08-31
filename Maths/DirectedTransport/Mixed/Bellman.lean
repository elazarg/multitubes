/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Order
public import Mathlib.Order.FixedPoints

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

* `Maths.Transport.lowerDemand` - the join of incoming lower-compatible
  transported values.
* `Maths.Transport.upperDemand` - the meet of incoming upper-compatible
  transported values.

## Main results

* `Maths.Transport.isMixedSection_iff_demands` - the pointwise Bellman
  interval characterization of ordered mixed sections.

## Tags

directed transport, mixed polarity, Bellman operator, complete lattice
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
abbrev LowerIncomingAt (mode : E → EdgeMode) (vertex : V) :=
  {edge : E // G.target edge = vertex ∧
    (mode edge = EdgeMode.lax ∨ mode edge = EdgeMode.exact)}

/-- Incoming edges whose mode supplies an upper constraint. -/
abbrev UpperIncomingAt (mode : E → EdgeMode) (vertex : V) :=
  {edge : E // G.target edge = vertex ∧
    (mode edge = EdgeMode.oplax ∨ mode edge = EdgeMode.exact)}

/-- The join of transported values contributed by incoming lax or exact edges. -/
def lowerDemand (mode : E → EdgeMode) (family : ∀ vertex : V, Fiber vertex)
    (vertex : V) : Fiber vertex :=
  ⨆ edge : LowerIncomingAt (G := G) mode vertex,
    fiberCast Fiber edge.property.1
      (T.edgeMap edge.1 (family (G.source edge.1)))

/-- The meet of transported values contributed by incoming oplax or exact edges. -/
def upperDemand (mode : E → EdgeMode) (family : ∀ vertex : V, Fiber vertex)
    (vertex : V) : Fiber vertex :=
  ⨅ edge : UpperIncomingAt (G := G) mode vertex,
    fiberCast Fiber edge.property.1
      (T.edgeMap edge.1 (family (G.source edge.1)))

/-- A lower-compatible incoming edge is below the lower demand at its target. -/
theorem le_lowerDemand {mode : E → EdgeMode}
    {family : ∀ vertex : V, Fiber vertex} {vertex : V}
    {edge : E} (htarget : G.target edge = vertex)
    (hmode : mode edge = EdgeMode.lax ∨ mode edge = EdgeMode.exact) :
    fiberCast Fiber htarget (T.edgeMap edge (family (G.source edge))) ≤
      T.lowerDemand mode family vertex := by
  exact le_iSup (fun incoming : LowerIncomingAt (G := G) mode vertex ↦
    fiberCast Fiber incoming.property.1
      (T.edgeMap incoming.1 (family (G.source incoming.1))))
    ⟨edge, htarget, hmode⟩

/-- The upper demand at a target is below every upper-compatible incoming edge. -/
theorem upperDemand_le {mode : E → EdgeMode}
    {family : ∀ vertex : V, Fiber vertex} {vertex : V}
    {edge : E} (htarget : G.target edge = vertex)
    (hmode : mode edge = EdgeMode.oplax ∨ mode edge = EdgeMode.exact) :
    T.upperDemand mode family vertex ≤
      fiberCast Fiber htarget (T.edgeMap edge (family (G.source edge))) := by
  exact iInf_le (fun incoming : UpperIncomingAt (G := G) mode vertex ↦
    fiberCast Fiber incoming.property.1
      (T.edgeMap incoming.1 (family (G.source incoming.1))))
    ⟨edge, htarget, hmode⟩

private theorem lowerDemand_le_of_isMixedSection
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex}
    (hfamily : T.IsMixedSection mode family) (vertex : V) :
    T.lowerDemand mode family vertex ≤ family vertex := by
  refine iSup_le fun incoming ↦ ?_
  rcases incoming with ⟨edge, htarget, hmode⟩
  rcases hmode with hmode | hmode
  · simpa only [fiberCast_family] using
      fiberCast_le_fiberCast htarget (hfamily.lax hmode)
  · simpa only [fiberCast_family] using
      (congrArg (fiberCast Fiber htarget) (hfamily.exact hmode)).le

private theorem isMixedSection_of_lowerDemand_le
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex}
    (hlower : ∀ vertex, T.lowerDemand mode family vertex ≤ family vertex)
    (hupper : ∀ vertex, family vertex ≤ T.upperDemand mode family vertex) :
    T.IsMixedSection mode family := by
  intro edge
  have htarget : G.target edge = G.target edge := rfl
  cases hmode : mode edge with
  | lax =>
      exact (le_lowerDemand T htarget (Or.inl hmode)).trans
        (hlower (G.target edge))
  | exact =>
      apply le_antisymm
      · exact (le_lowerDemand T htarget (Or.inr hmode)).trans
          (hlower (G.target edge))
      · exact (hupper (G.target edge)).trans
          (upperDemand_le T htarget (Or.inr hmode))
  | oplax =>
      exact (hupper (G.target edge)).trans
        (upperDemand_le T htarget (Or.inl hmode))

/-- An ordered mixed section is exactly a pointwise interval between its lower
and upper incoming demands.  Exact edges are included in both demands. -/
theorem isMixedSection_iff_demands
    {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex} :
    T.IsMixedSection mode family ↔
      (∀ vertex, T.lowerDemand mode family vertex ≤ family vertex) ∧
        (∀ vertex, family vertex ≤ T.upperDemand mode family vertex) := by
  constructor
  · intro hfamily
    exact ⟨lowerDemand_le_of_isMixedSection T hfamily,
      fun vertex ↦ by
        refine le_iInf fun incoming ↦ ?_
        rcases incoming with ⟨edge, htarget, hmode⟩
        rcases hmode with hmode | hmode
        · simpa only [fiberCast_family] using
            fiberCast_le_fiberCast htarget (hfamily.oplax hmode)
        · simpa only [fiberCast_family] using
            (congrArg (fiberCast Fiber htarget) (hfamily.exact hmode)).ge⟩
  · rintro ⟨hlower, hupper⟩
    exact isMixedSection_of_lowerDemand_le T hlower hupper

end CompleteLattice

end Transport
end Maths

end
