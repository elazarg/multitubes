/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Walk

/-!
# Ordered mixed directed transport

The order-theoretic surface of mixed directed transport uses the fiberwise
relation supplied by `LE`.  It identifies the ordinary lax and oplax section
predicates with constant-mode instances of the relation-parametric mixed
predicate.  The definitions themselves require no order laws; order laws
remain hypotheses of the walk results in
`Maths.DirectedTransport.Mixed.Walk`.

## Main definitions

* `Maths.Transport.IsMixedSection` - the ordered mixed-polarity predicate.

## Main results

* `Maths.Transport.IsMixedSection.lax`,
  `Maths.Transport.IsMixedSection.exact`, and
  `Maths.Transport.IsMixedSection.oplax` - the ordered constraint selected by
  an edge mode.
* `Maths.Transport.isMixedSection_const_lax_iff` and
  `Maths.Transport.isMixedSection_const_exact_iff` - constant-mode bridges for
  lax and exact edges.
* `Maths.Transport.isMixedSection_const_oplax_iff` - the constant-mode bridge for
  oplax edges.
* `Maths.Transport.IsMixedSection.walkMap_eq_of_exact` - exact transport along
  an exact-mode walk.
* `Maths.Transport.IsMixedSection.walkMap_le_of_lax_or_exact` and
  `Maths.Transport.IsMixedSection.le_walkMap_of_oplax_or_exact` - ordered walk
  propagation for the two inequality polarities.

## Tags

directed transport, mixed polarity, lax section, oplax section, order
-/

@[expose] public section

namespace Maths

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF}

namespace Transport

variable {T : Transport G Fiber}
variable {start finish : V} {mode : E → EdgeMode}
variable {family : ∀ vertex : V, Fiber vertex}

/-- A mixed-polarity section using the fiberwise `≤` relation. -/
def IsMixedSection [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (mode : E → EdgeMode)
    (family : ∀ vertex, Fiber vertex) : Prop :=
  T.IsMixedSectionFor (fun _ => (· ≤ ·)) mode family

/-- The lower inequality on a lax edge of an ordered mixed section. -/
theorem IsMixedSection.lax [∀ vertex : V, LE (Fiber vertex)]
    (hfamily : T.IsMixedSection mode family) {edge : E}
    (hmode : mode edge = .lax) :
    T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge) := by
  exact IsMixedSectionFor.lax hfamily hmode

/-- The equality on an exact edge of an ordered mixed section. -/
theorem IsMixedSection.exact [∀ vertex : V, LE (Fiber vertex)]
    (hfamily : T.IsMixedSection mode family) {edge : E}
    (hmode : mode edge = .exact) :
    T.edgeMap edge (family (G.source edge)) = family (G.target edge) := by
  exact IsMixedSectionFor.exact hfamily hmode

/-- The upper inequality on an oplax edge of an ordered mixed section. -/
theorem IsMixedSection.oplax [∀ vertex : V, LE (Fiber vertex)]
    (hfamily : T.IsMixedSection mode family) {edge : E}
    (hmode : mode edge = .oplax) :
    family (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) := by
  exact IsMixedSectionFor.oplax hfamily hmode

/-- A constant lax mode is the ordinary lax section predicate. -/
theorem isMixedSection_const_lax_iff [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) :
    T.IsMixedSection (fun _ : E => EdgeMode.lax) family ↔ T.IsLaxSection family := by
  rfl

/-- A constant exact mode is the ordinary exact section predicate. -/
theorem isMixedSection_const_exact_iff
    [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) :
    T.IsMixedSection (fun _ : E => EdgeMode.exact) family ↔ T.IsSection family := by
  rfl

/-- A constant oplax mode is the ordinary oplax section predicate. -/
theorem isMixedSection_const_oplax_iff [∀ vertex : V, LE (Fiber vertex)]
    (T : Transport G Fiber) (family : ∀ vertex, Fiber vertex) :
    T.IsMixedSection (fun _ : E => EdgeMode.oplax) family ↔ T.IsOplaxSection family := by
  rfl

/-- An exact-mode walk transports a mixed section exactly. -/
theorem IsMixedSection.walkMap_eq_of_exact
    [∀ vertex : V, LE (Fiber vertex)]
    (hfamily : T.IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsExact) :
    T.walkMap walk (family start) = family finish := by
  change T.IsMixedSectionFor (fun _ => (· ≤ ·)) mode family at hfamily
  exact hfamily.walkMap_eq_of_exact walk hmode

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A mixed section is transported below its terminal value along a walk whose
edges are all lax or exact. -/
theorem IsMixedSection.walkMap_le_of_lax_or_exact
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    T.walkMap walk (family start) ≤ family finish := by
  change T.IsMixedSectionFor (fun _ => (· ≤ ·)) mode family at hfamily
  apply hfamily.walkMap_rel_of_lax_or_exact
    (fun _ => le_rfl) (fun _ => le_trans)
  · intro edge x y hxy
    exact hmono edge hxy
  · exact hmode

/-- A mixed section is transported above its terminal value along a walk whose
edges are all oplax or exact. -/
theorem IsMixedSection.le_walkMap_of_oplax_or_exact
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hfamily : T.IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    family finish ≤ T.walkMap walk (family start) := by
  change T.IsMixedSectionFor (fun _ => (· ≤ ·)) mode family at hfamily
  apply hfamily.walkMap_rel_of_oplax_or_exact
    (fun _ => le_rfl) (fun _ => le_trans)
  · intro edge x y hxy
    exact hmono edge hxy
  · exact hmode

end Ordered

end Transport

end Maths
