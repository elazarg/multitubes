/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Walk

/-!
# Adjoint reversal of mixed transport

An oplax constraint for a map can be read as a lax constraint after reversing
the edge, provided a residual map is supplied.  This file constructs the
reversed graph and proves the resulting reduction without assuming an order.
The relation-parametric theorem records exactly the three laws it uses:
reflexivity, the residual equivalence, and separation of the two relation
directions on an exact edge.

## Main definitions

* `Maths.Transport.LaxificationEdge` - the forward and reversed copies of
  the edges selected by a mixed polarity.
* `Maths.Transport.laxificationGraph` - the graph carrying those copies.
* `Maths.Transport.laxification` - the transport using original and residual
  maps.
* `Maths.Transport.IsResidualFor` - the relation equivalence that makes a
  residual reverse an oplax constraint.
* `Maths.Transport.IsExactSeparated` - the local separation law that recovers
  equality from the two constraints on an exact edge.

## Main results

* `Maths.Transport.isMixedSectionFor_laxification` - a mixed section gives an
  all-lax laxification section.
* `Maths.Transport.laxification_isMixedSectionFor` - an all-lax laxification
  section gives a mixed section.
* `Maths.Transport.isMixedSectionFor_iff_laxification` - mixed sections are
  exactly all-lax sections on the laxification graph.

## Tags

directed transport, mixed polarity, adjoint, residual, reversal
-/

@[expose] public section

namespace Maths

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF}

namespace Transport

/-- The forward copy of an edge whose mixed mode is lax or exact. -/
abbrev LaxificationForwardEdge (mode : E → EdgeMode) :=
  {edge : E // (mode edge).IsLaxOrExact}

/-- The reversed copy of an edge whose mixed mode is oplax or exact. -/
abbrev LaxificationReverseEdge (mode : E → EdgeMode) :=
  {edge : E // (mode edge).IsOplaxOrExact}

/-- Edges of the laxification graph: selected forward edges and selected
reversed edges.  Exact edges occur in both copies. -/
abbrev LaxificationEdge (mode : E → EdgeMode) :=
  LaxificationForwardEdge mode ⊕ LaxificationReverseEdge mode

/-- The graph obtained by retaining lax and exact edges and reversing oplax
and exact edges. -/
def laxificationGraph (G : EdgeGraph V E) (mode : E → EdgeMode) :
    EdgeGraph V (LaxificationEdge mode) where
  source edge := match edge with
    | Sum.inl edge => G.source edge.1
    | Sum.inr edge => G.target edge.1
  target edge := match edge with
    | Sum.inl edge => G.target edge.1
    | Sum.inr edge => G.source edge.1

/-- The source of a forward edge in the laxification graph. -/
@[simp] theorem laxificationGraph_source_forward
    (G : EdgeGraph V E) (mode : E → EdgeMode) (edge : LaxificationForwardEdge mode) :
    (laxificationGraph G mode).source (.inl edge) = G.source edge.1 :=
  rfl

/-- The target of a forward edge in the laxification graph. -/
@[simp] theorem laxificationGraph_target_forward
    (G : EdgeGraph V E) (mode : E → EdgeMode) (edge : LaxificationForwardEdge mode) :
    (laxificationGraph G mode).target (.inl edge) = G.target edge.1 :=
  rfl

/-- The source of a reversed edge in the laxification graph. -/
@[simp] theorem laxificationGraph_source_reverse
    (G : EdgeGraph V E) (mode : E → EdgeMode) (edge : LaxificationReverseEdge mode) :
    (laxificationGraph G mode).source (.inr edge) = G.target edge.1 :=
  rfl

/-- The target of a reversed edge in the laxification graph. -/
@[simp] theorem laxificationGraph_target_reverse
    (G : EdgeGraph V E) (mode : E → EdgeMode) (edge : LaxificationReverseEdge mode) :
    (laxificationGraph G mode).target (.inr edge) = G.source edge.1 :=
  rfl

/-- A residual map for the edge maps, expressed by the relation needed to
reverse an oplax constraint. -/
def IsResidualFor (T : Transport G Fiber)
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop)
    (mode : E → EdgeMode)
    (residual : ∀ edge : LaxificationReverseEdge mode,
      Fiber (G.target edge.1) → Fiber (G.source edge.1)) : Prop :=
  ∀ (edge : LaxificationReverseEdge mode)
    (sourcePoint : Fiber (G.source edge.1))
    (targetPoint : Fiber (G.target edge.1)),
    relation (G.target edge.1) targetPoint (T.edgeMap edge.1 sourcePoint) ↔
      relation (G.source edge.1) (residual edge targetPoint) sourcePoint

/-- The transport on the laxification graph, using an original map on forward
edges and its supplied residual map on reversed edges. -/
def laxification (T : Transport G Fiber)
    (mode : E → EdgeMode)
    (residual : ∀ edge : LaxificationReverseEdge mode,
      Fiber (G.target edge.1) → Fiber (G.source edge.1)) :
    Transport (laxificationGraph G mode) Fiber where
  edgeMap edge := match edge with
    | Sum.inl edge => T.edgeMap edge.1
    | Sum.inr edge => residual edge

/-- Laxification retains the original map on a forward edge. -/
@[simp] theorem laxification_edgeMap_forward (T : Transport G Fiber)
    (mode : E → EdgeMode)
    (residual : ∀ edge : LaxificationReverseEdge mode,
      Fiber (G.target edge.1) → Fiber (G.source edge.1))
    (edge : LaxificationForwardEdge mode) :
    (T.laxification mode residual).edgeMap (.inl edge) = T.edgeMap edge.1 :=
  rfl

/-- Laxification uses the supplied residual map on a reversed edge. -/
@[simp] theorem laxification_edgeMap_reverse (T : Transport G Fiber)
    (mode : E → EdgeMode)
    (residual : ∀ edge : LaxificationReverseEdge mode,
      Fiber (G.target edge.1) → Fiber (G.source edge.1))
    (edge : LaxificationReverseEdge mode) :
    (T.laxification mode residual).edgeMap (.inr edge) = residual edge :=
  rfl

variable {relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop}
variable {mode : E → EdgeMode}
variable {residual : ∀ edge : LaxificationReverseEdge mode,
  Fiber (G.target edge.1) → Fiber (G.source edge.1)}
variable {family : ∀ vertex : V, Fiber vertex}

/-- The exact-edge separation law used by the relation-parametric reduction.
It is stated only for the two endpoints of the supplied map, so it is weaker
than assuming a globally antisymmetric relation. -/
def IsExactSeparated (T : Transport G Fiber)
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop)
    (mode : E → EdgeMode) : Prop :=
  ∀ (edge : {edge : E // mode edge = .exact})
    (sourcePoint : Fiber (G.source edge.1))
    (targetPoint : Fiber (G.target edge.1)),
    relation (G.target edge.1) (T.edgeMap edge.1 sourcePoint) targetPoint →
      relation (G.target edge.1) targetPoint (T.edgeMap edge.1 sourcePoint) →
        T.edgeMap edge.1 sourcePoint = targetPoint

/-- A mixed section gives an all-lax section on the laxification graph.  The
only reflexivity needed is at the value selected by each exact edge. -/
theorem isMixedSectionFor_laxification
    (T : Transport G Fiber)
    (hreflexive : ∀ (edge : {edge : E // mode edge = .exact}),
      relation (G.target edge.1) (family (G.target edge.1)) (family (G.target edge.1)))
    (hresidual : T.IsResidualFor relation mode residual) :
    T.IsMixedSectionFor relation mode family →
      (T.laxification mode residual).IsMixedSectionFor relation (fun _ => .lax) family := by
  intro hfamily edge
  rcases edge with edge | edge
  · rcases edge.property with hmode | hmode
    · simpa [laxification, laxificationGraph, hmode] using hfamily.lax hmode
    · have heq := hfamily.exact hmode
      change relation (G.target edge.1)
        (T.edgeMap edge.1 (family (G.source edge.1))) (family (G.target edge.1))
      rw [heq]
      exact hreflexive ⟨edge.1, hmode⟩
  · rcases edge.property with hmode | hmode
    · have hconstraint := hfamily.oplax hmode
      have hconverted := (hresidual edge (family (G.source edge.1))
        (family (G.target edge.1))).mp hconstraint
      simpa [laxification, laxificationGraph] using hconverted
    · have heq := hfamily.exact hmode
      have hconstraint : relation (G.target edge.1) (family (G.target edge.1))
          (T.edgeMap edge.1 (family (G.source edge.1))) := by
        rw [heq]
        exact hreflexive ⟨edge.1, hmode⟩
      have hconverted := (hresidual edge (family (G.source edge.1))
        (family (G.target edge.1))).mp hconstraint
      simpa [laxification, laxificationGraph] using hconverted

/-- An all-lax section on the laxification graph gives a mixed section.  The
residual equivalence handles oplax edges, while exact edges use both copies
and `IsExactSeparated` to recover equality. -/
theorem laxification_isMixedSectionFor
    (T : Transport G Fiber)
    (hresidual : T.IsResidualFor relation mode residual)
    (hseparated : T.IsExactSeparated relation mode) :
    (T.laxification mode residual).IsMixedSectionFor relation (fun _ => .lax) family →
      T.IsMixedSectionFor relation mode family := by
  intro hfamily edge
  cases hmode : mode edge with
  | lax =>
    simpa [laxification, laxificationGraph] using
      hfamily (.inl ⟨edge, Or.inl hmode⟩)
  | exact =>
    have hforward := hfamily (.inl ⟨edge, Or.inr hmode⟩)
    have hreverse := hfamily (.inr ⟨edge, Or.inr hmode⟩)
    change relation (G.target edge) (T.edgeMap edge (family (G.source edge)))
      (family (G.target edge)) at hforward
    change relation (G.source edge)
      (residual ⟨edge, Or.inr hmode⟩ (family (G.target edge)))
      (family (G.source edge)) at hreverse
    have hbackward := (hresidual ⟨edge, Or.inr hmode⟩ (family (G.source edge))
      (family (G.target edge))).mpr hreverse
    exact hseparated ⟨edge, hmode⟩ (family (G.source edge)) (family (G.target edge))
      hforward hbackward
  | oplax =>
    have hconstraint := hfamily (.inr ⟨edge, Or.inl hmode⟩)
    have hconverted := (hresidual ⟨edge, Or.inl hmode⟩ (family (G.source edge))
      (family (G.target edge))).mpr hconstraint
    simpa [laxification, laxificationGraph] using hconverted

/-- Mixed constraints are equivalent to all-lax constraints after laxification.
The forward implication needs reflexivity only on exact-edge family values;
the reverse implication additionally uses exact-edge separation. -/
theorem isMixedSectionFor_iff_laxification
    (T : Transport G Fiber)
    (hreflexive : ∀ (edge : {edge : E // mode edge = .exact}),
      relation (G.target edge.1) (family (G.target edge.1)) (family (G.target edge.1)))
    (hresidual : T.IsResidualFor relation mode residual)
    (hseparated : T.IsExactSeparated relation mode) :
    T.IsMixedSectionFor relation mode family ↔
      (T.laxification mode residual).IsMixedSectionFor relation (fun _ => .lax) family := by
  constructor
  · exact isMixedSectionFor_laxification T hreflexive hresidual
  · exact laxification_isMixedSectionFor T hresidual hseparated

end Transport

end Maths
