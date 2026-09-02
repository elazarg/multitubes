/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Basic

/-!
# Mixed-polarity sections

An edge of a transport can impose a lower constraint, an equality, or
an upper constraint.  `Maths.EdgeMode` records this choice, while
`Maths.Transport.IsMixedSectionFor` applies it to an arbitrary relation on each
fiber.  Thus this layer needs neither order laws nor algebraic structure on the
edge maps.

## Main definitions

* `Maths.EdgeMode` - the three edge constraint polarities.
* `Maths.EdgeMode.satisfies` - the relation constraint selected by a polarity.
* `Maths.Transport.IsMixedSectionFor` - a mixed section for arbitrary
  fiberwise relations.

## Main results

* `Maths.Transport.IsMixedSectionFor.lax` - extract a lax constraint from a
  mixed section.
* `Maths.Transport.IsMixedSectionFor.exact` - extract an exact constraint from
  a mixed section.
* `Maths.Transport.IsMixedSectionFor.oplax` - extract an oplax constraint from
  a mixed section.
* `Maths.Transport.isMixedSectionFor_const_lax_iff` - the constant lax-mode
  specialization.
* `Maths.Transport.isMixedSectionFor_const_exact_iff` - the constant
  exact-mode specialization.
* `Maths.Transport.isMixedSectionFor_const_oplax_iff` - the constant
  oplax-mode specialization.
* `Maths.fiberCast_relation` - transport of an arbitrary fiberwise relation
  across an equality of vertices.

## Tags

transport, mixed section, lax section, oplax section, relation
-/

@[expose] public section

namespace Maths

universe uV uE uF

variable {V : Type uV} {E : Type uE}

/-- Transport a relation between two points across an equality of vertices. -/
theorem fiberCast_relation {Fiber : V → Type uF}
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop)
    {first second : V} (hvertex : first = second) {point other : Fiber first}
    (hrel : relation first point other) :
    relation second (fiberCast Fiber hvertex point) (fiberCast Fiber hvertex other) := by
  subst hvertex
  exact hrel

/-- The polarity of an edge constraint in a mixed section. -/
inductive EdgeMode : Type
  | /-- The transported source value is related to the target value. -/
    lax
  | /-- The transported source value equals the target value. -/
    exact
  | /-- The target value is related to the transported source value. -/
    oplax
  deriving DecidableEq

namespace EdgeMode

universe uX

variable {X : Type uX}

/-- Apply a relation in the direction prescribed by an edge mode.

For `lax`, the relation is tested from the transported value to the target
value.  For `oplax`, its arguments are reversed.  The `exact` mode ignores the
relation and requires equality. -/
def satisfies (mode : EdgeMode) (relation : X → X → Prop) (transported target : X) : Prop :=
  match mode with
  | .lax => relation transported target
  | .exact => transported = target
  | .oplax => relation target transported

/-- Lax satisfaction applies the relation in its given direction. -/
@[simp] theorem satisfies_lax (relation : X → X → Prop) (transported target : X) :
    EdgeMode.lax.satisfies relation transported target ↔ relation transported target :=
  by rfl

/-- Exact satisfaction is equality, independently of the relation. -/
@[simp] theorem satisfies_exact (relation : X → X → Prop) (transported target : X) :
    EdgeMode.exact.satisfies relation transported target ↔ transported = target :=
  by rfl

/-- Oplax satisfaction applies the relation in the reverse direction. -/
@[simp] theorem satisfies_oplax (relation : X → X → Prop) (transported target : X) :
    EdgeMode.oplax.satisfies relation transported target ↔ relation target transported :=
  by rfl

end EdgeMode

namespace Transport

variable {G : EdgeGraph V E} {Fiber : V → Type uF}
variable {T : Transport G Fiber}

/-- A family satisfying the edge constraint selected by `mode`, where
`relation vertex` compares points in the fiber over `vertex`.

The relation is used only for lax and oplax edges; exact edges impose literal
equality. -/
def IsMixedSectionFor (T : Transport G Fiber)
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop)
    (mode : E → EdgeMode) (family : ∀ vertex, Fiber vertex) : Prop :=
  ∀ edge : E, (mode edge).satisfies (relation (G.target edge))
    (T.edgeMap edge (family (G.source edge))) (family (G.target edge))

variable {relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop}
variable {mode : E → EdgeMode} {family : ∀ vertex, Fiber vertex}

/-- The lax relation on an edge of a mixed section. -/
theorem IsMixedSectionFor.lax (hfamily : T.IsMixedSectionFor relation mode family)
    {edge : E} (hmode : mode edge = .lax) :
    relation (G.target edge) (T.edgeMap edge (family (G.source edge)))
      (family (G.target edge)) := by
  simpa [IsMixedSectionFor, hmode] using hfamily edge

/-- The equality constraint on an edge of a mixed section. -/
theorem IsMixedSectionFor.exact (hfamily : T.IsMixedSectionFor relation mode family)
    {edge : E} (hmode : mode edge = .exact) :
    T.edgeMap edge (family (G.source edge)) = family (G.target edge) := by
  simpa [IsMixedSectionFor, hmode] using hfamily edge

/-- The oplax relation on an edge of a mixed section. -/
theorem IsMixedSectionFor.oplax (hfamily : T.IsMixedSectionFor relation mode family)
    {edge : E} (hmode : mode edge = .oplax) :
    relation (G.target edge) (family (G.target edge))
      (T.edgeMap edge (family (G.source edge))) := by
  simpa [IsMixedSectionFor, hmode] using hfamily edge

/-- A mixed section with every edge in lax mode is exactly an ordinary lax
section for the chosen fiberwise relation. -/
theorem isMixedSectionFor_const_lax_iff
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop) :
    T.IsMixedSectionFor relation (fun _ => .lax) family ↔
      ∀ edge : E, relation (G.target edge)
        (T.edgeMap edge (family (G.source edge))) (family (G.target edge)) := by
  rfl

/-- A mixed section with every edge in exact mode is exactly an exact section. -/
theorem isMixedSectionFor_const_exact_iff
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop) :
    T.IsMixedSectionFor relation (fun _ => .exact) family ↔ T.IsSection family := by
  rfl

/-- A mixed section with every edge in oplax mode is exactly the reversed
fiberwise relation on every edge. -/
theorem isMixedSectionFor_const_oplax_iff
    (relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop) :
    T.IsMixedSectionFor relation (fun _ => .oplax) family ↔
      ∀ edge : E, relation (G.target edge) (family (G.target edge))
        (T.edgeMap edge (family (G.source edge))) := by
  rfl

end Transport

end Maths
