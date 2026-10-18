/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Mixed.Basic

/-!
# Walk propagation for mixed-polarity sections

This file propagates mixed-polarity section constraints along typed walks.  An
exact walk transports the marked value by equality.  A walk whose edges are
only lax or exact transports it below the marked terminal value, while a walk
whose edges are only oplax or exact transports it above that value.  The
relations on the fibers need only be reflexive and transitive, and edge maps
need only preserve those relations.  Each statement is an instance of
`Maths.Transport.IsSectionFor.walkMap_rel`.

The polarity restriction is essential: with arbitrary relations there is no
endpoint comparison across a change from lax to oplax, or from oplax to lax.
For symmetric relations the distinction disappears, and arbitrary mixed walks
propagate the relation.

## Main definitions

* `Maths.EdgeMode.IsExact` - the exact edge predicate.
* `Maths.EdgeMode.IsLaxOrExact` - the lower-compatible edge predicate.
* `Maths.EdgeMode.IsOplaxOrExact` - the upper-compatible edge predicate.

## Main results

* `Maths.Transport.IsMixedSectionFor.walkMap_eq_of_exact` - exact transport
  along a walk consisting only of exact edges.
* `Maths.Transport.IsMixedSectionFor.walkMap_rel_of_lax_or_exact` - lower
  relation transport along a lax-or-exact walk.
* `Maths.Transport.IsMixedSectionFor.walkMap_rel_of_oplax_or_exact` - upper
  relation transport along an oplax-or-exact walk.
* `Maths.Transport.IsMixedSectionFor.walkMap_rel_of_symmetric` - relation
  transport along an arbitrary mixed walk when the relation is symmetric.

## Tags

transport, mixed polarity, walk, relation, lax section, oplax section
-/

@[expose] public section

namespace Maths

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF}

namespace EdgeMode

/-- An edge mode imposing an equality constraint. -/
def IsExact (mode : EdgeMode) : Prop := mode = .exact

/-- An edge mode imposing either a lax or an equality constraint. -/
def IsLaxOrExact (mode : EdgeMode) : Prop := mode = .lax ∨ mode = .exact

/-- An edge mode imposing either an oplax or an equality constraint. -/
def IsOplaxOrExact (mode : EdgeMode) : Prop := mode = .oplax ∨ mode = .exact

/-- Lax mode is not exact. -/
@[simp] theorem isExact_lax : ¬ EdgeMode.lax.IsExact := by simp [IsExact]

/-- Exact mode is exact. -/
@[simp] theorem isExact_exact : EdgeMode.exact.IsExact := by simp [IsExact]

/-- Oplax mode is not exact. -/
@[simp] theorem isExact_oplax : ¬ EdgeMode.oplax.IsExact := by simp [IsExact]

/-- Lax mode is lower-compatible. -/
@[simp] theorem isLaxOrExact_lax : EdgeMode.lax.IsLaxOrExact := by simp [IsLaxOrExact]

/-- Exact mode is lower-compatible. -/
@[simp] theorem isLaxOrExact_exact : EdgeMode.exact.IsLaxOrExact := by
  simp [IsLaxOrExact]

/-- Oplax mode is not lower-compatible. -/
@[simp] theorem isLaxOrExact_oplax : ¬ EdgeMode.oplax.IsLaxOrExact := by
  simp [IsLaxOrExact]

/-- Lax mode is not upper-compatible. -/
@[simp] theorem isOplaxOrExact_lax : ¬ EdgeMode.lax.IsOplaxOrExact := by
  simp [IsOplaxOrExact]

/-- Exact mode is upper-compatible. -/
@[simp] theorem isOplaxOrExact_exact : EdgeMode.exact.IsOplaxOrExact := by
  simp [IsOplaxOrExact]

/-- Oplax mode is upper-compatible. -/
@[simp] theorem isOplaxOrExact_oplax : EdgeMode.oplax.IsOplaxOrExact := by
  simp [IsOplaxOrExact]

end EdgeMode

namespace Transport

variable {T : Transport G Fiber}
variable {relation : ∀ vertex : V, Fiber vertex → Fiber vertex → Prop}
variable {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex}

variable {start finish : V}

/-- An exact mixed section is transported by equality along an exact walk.

No relation laws or preservation properties are required, since the proof uses
only the equality constraints on the edges of the walk. -/
theorem IsMixedSectionFor.walkMap_eq_of_exact
    (hfamily : T.IsMixedSectionFor relation mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsExact) :
    T.walkMap walk (family start) = family finish :=
  IsSectionFor.walkMap_rel (R := fun _ => Eq) (fun _ => rfl) (fun _ => Eq.trans)
    (fun _ => congrArg _) hfamily walk fun edge hedge _ hrel => by
      simpa [show mode edge = .exact from hmode edge hedge] using hrel

/-- A mixed section is transported below its terminal value along a walk whose
edges are all lax or exact.

The relation is assumed reflexive at the selected family values and transitive.
The sole map hypothesis is preservation of the corresponding relation on each
edge. -/
theorem IsMixedSectionFor.walkMap_rel_of_lax_or_exact
    (hrefl : ∀ vertex : V, relation vertex (family vertex) (family vertex))
    (htrans : ∀ vertex : V, ∀ {x y z}, relation vertex x y →
      relation vertex y z → relation vertex x z)
    (hpreserve : ∀ edge : E, ∀ {x y}, relation (G.source edge) x y →
      relation (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hfamily : T.IsMixedSectionFor relation mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    relation finish (T.walkMap walk (family start)) (family finish) :=
  IsSectionFor.walkMap_rel hrefl htrans hpreserve hfamily walk fun edge hedge _ hrel => by
    rcases hmode edge hedge with hmode | hmode
    · simpa [hmode] using hrel
    · simp only [hmode, EdgeMode.satisfies_exact] at hrel
      rw [hrel]
      exact hrefl _

/-- A mixed section is transported above its terminal value along a walk whose
edges are all oplax or exact.

The relation is assumed reflexive at the selected family values and transitive.
The sole map hypothesis is preservation of the corresponding relation on each
edge. -/
theorem IsMixedSectionFor.walkMap_rel_of_oplax_or_exact
    (hrefl : ∀ vertex : V, relation vertex (family vertex) (family vertex))
    (htrans : ∀ vertex : V, ∀ {x y z}, relation vertex x y →
      relation vertex y z → relation vertex x z)
    (hpreserve : ∀ edge : E, ∀ {x y}, relation (G.source edge) x y →
      relation (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hfamily : T.IsMixedSectionFor relation mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    relation finish (family finish) (T.walkMap walk (family start)) :=
  IsSectionFor.walkMap_rel (R := fun vertex x y => relation vertex y x) hrefl
    (fun vertex _ _ _ hxy hyz => htrans vertex hyz hxy) (fun edge _ _ hxy => hpreserve edge hxy)
    hfamily walk fun edge hedge _ hrel => by
      rcases hmode edge hedge with hmode | hmode
      · simpa [hmode] using hrel
      · simp only [hmode, EdgeMode.satisfies_exact] at hrel
        rw [hrel]
        exact hrefl _

/-- A mixed section propagates along every walk when the fiberwise relation is
symmetric.  In this setting lax and oplax constraints have the same content,
while exact constraints use reflexivity at the selected family values. -/
theorem IsMixedSectionFor.walkMap_rel_of_symmetric
    (hrefl : ∀ vertex : V, relation vertex (family vertex) (family vertex))
    (hsymm : ∀ vertex : V, ∀ {x y}, relation vertex x y → relation vertex y x)
    (htrans : ∀ vertex : V, ∀ {x y z}, relation vertex x y →
      relation vertex y z → relation vertex x z)
    (hpreserve : ∀ edge : E, ∀ {x y}, relation (G.source edge) x y →
      relation (G.target edge) (T.edgeMap edge x) (T.edgeMap edge y))
    (hfamily : T.IsMixedSectionFor relation mode family)
    (walk : G.Walk start finish) :
    relation finish (T.walkMap walk (family start)) (family finish) :=
  IsSectionFor.walkMap_rel hrefl htrans hpreserve hfamily walk fun edge _ _ hrel => by
    cases hmode : mode edge with
    | lax => simpa [hmode] using hrel
    | exact =>
        simp only [hmode, EdgeMode.satisfies_exact] at hrel
        rw [hrel]
        exact hrefl _
    | oplax => exact hsymm _ (by simpa [hmode] using hrel)

end Transport

end Maths
