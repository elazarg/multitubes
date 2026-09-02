/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Mixed.Adjoint
public import Maths.Multitube.Mixed.Order
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Ordered adjoint reversal

For partially ordered fibers, a left residual of each edge map is a
`GaloisConnection` in the direction needed to reverse an oplax constraint.
Antisymmetry then supplies the exact-edge separation law, so the general
relation-parametric theorem has a compact ordered form.

## Main results

* `Maths.Transport.IsMixedSection.isLaxSection_laxification_of_galoisConnection` -
  the preorder-level forward reduction.
* `Maths.Transport.isMixedSection_iff_laxification_of_galoisConnection` - the
  ordered reduction under edgewise Galois connections.
* `Maths.Transport.monotone_laxification_of_galoisConnection` - monotonicity
  of the transformed transport from the minimal remaining edge hypothesis.
* `Maths.Transport.not_exists_galoisConnection_left_of_witnesses` - a family
  of lower witnesses can rule out a left order adjoint.
* `Maths.Transport.not_exists_galoisConnection_right_of_witnesses` - a family
  of upper witnesses can rule out a right order adjoint.

## Tags

transport, mixed polarity, adjoint, residual, Galois connection, order
-/

@[expose] public section

namespace Maths

universe uV uE uF uα uβ uι

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF}
variable {α : Type uα} {β : Type uβ} {ι : Type uι}

namespace Transport

variable {T : Transport G Fiber}
variable {mode : E → EdgeMode}
variable {residual : ∀ edge : LaxificationReverseEdge mode,
  Fiber (G.target edge.1) → Fiber (G.source edge.1)}
variable {family : ∀ vertex : V, Fiber vertex}

/-- A family of lower witnesses can obstruct a left order adjoint.  Every
witness lies in the lower level set of `f` at `b`, while no common lower bound
of the witnesses lies in that level set. -/
theorem not_exists_galoisConnection_left_of_witnesses
    [Preorder α] [Preorder β]
    (f : α → β) (b : β) (w : ι → α)
    (hwitness : ∀ i, b ≤ f (w i))
    (hinfeasible : ∀ x, (∀ i, x ≤ w i) → ¬ b ≤ f x) :
    ¬ ∃ g : β → α, GaloisConnection g f := by
  rintro ⟨g, hadjoint⟩
  apply hinfeasible (g b)
  · intro i
    exact (hadjoint b (w i)).mpr (hwitness i)
  · exact (hadjoint b (g b)).mp le_rfl

/-- A family of upper witnesses can obstruct a right order adjoint.  Every
witness lies in the upper level set of `f` at `b`, while no common upper bound
of the witnesses lies in that level set. -/
theorem not_exists_galoisConnection_right_of_witnesses
    [Preorder α] [Preorder β]
    (f : α → β) (b : β) (w : ι → α)
    (hwitness : ∀ i, f (w i) ≤ b)
    (hinfeasible : ∀ x, (∀ i, w i ≤ x) → ¬ f x ≤ b) :
    ¬ ∃ g : β → α, GaloisConnection f g := by
  rintro ⟨g, hadjoint⟩
  apply hinfeasible (g b)
  · intro i
    exact (hadjoint (w i) b).mp (hwitness i)
  · exact (hadjoint (g b) b).mpr le_rfl

/-- In preordered fibers, a mixed section becomes a lax section on the
laxification graph.  This direction does not require antisymmetry. -/
theorem IsMixedSection.isLaxSection_laxification_of_galoisConnection
    [∀ vertex : V, Preorder (Fiber vertex)]
    (hfamily : T.IsMixedSection mode family)
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    (T.laxification mode residual).IsLaxSection family := by
  apply isMixedSectionFor_laxification T
    (fun edge => le_refl (family (G.target edge.1))) _ hfamily
  intro edge sourcePoint targetPoint
  exact (hresidual edge targetPoint sourcePoint).symm

/-- In partially ordered fibers, edgewise left residuals turn mixed sections
into all-lax sections on the laxification graph. -/
theorem isMixedSection_iff_laxification_of_galoisConnection
    [∀ vertex : V, PartialOrder (Fiber vertex)]
    (T : Transport G Fiber)
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    T.IsMixedSection mode family ↔
      (T.laxification mode residual).IsLaxSection family := by
  apply isMixedSectionFor_iff_laxification T
    (fun edge => le_refl (family (G.target edge.1)))
  · intro edge sourcePoint targetPoint
    exact (hresidual edge targetPoint sourcePoint).symm
  · intro edge sourcePoint targetPoint hforward hbackward
    exact le_antisymm hforward hbackward

/-- The laxification transport is monotone when original lax edges are
monotone and every reverse-compatible edge map has the supplied left
residual. -/
theorem monotone_laxification_of_galoisConnection
    [∀ vertex : V, Preorder (Fiber vertex)]
    (T : Transport G Fiber)
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    ∀ edge : LaxificationEdge mode,
      Monotone ((T.laxification mode residual).edgeMap edge) := by
  rintro (edge | edge)
  · rcases edge.property with hmode | hmode
    · exact hlax edge.1 hmode
    · exact (hresidual ⟨edge.1, Or.inr hmode⟩).monotone_u
  · exact (hresidual edge).monotone_l

end Transport

end Maths
