/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure
public import Maths.Multitubes.Mixed.AdjointOrder

/-!
# Complete-lattice closure for mixed transport

When the fibers are complete lattices, residuals turn mixed-polarity
constraints into ordinary lax constraints on the laxification graph.  The
least lax majorant there therefore gives a canonical least mixed majorant.
Only the maps on edges already in lax mode need a separate monotonicity
hypothesis: the Galois connections provide the remaining monotonicity.

## Main definitions

* `Maths.Transport.leastMixedMajorant` - the canonical least mixed section
  dominating prescribed lower data.
* `Maths.Transport.leastMixedMajorantClosure` - the least-majorant construction
  bundled as a closure operator.

## Main results

* `Maths.Transport.leastMixedMajorant_isLeast` - the canonical majorant is a
  mixed section, dominates the lower data, and is below every such section.
* `Maths.Transport.exists_isMixedSection_between_iff_leastMixedMajorant_le` -
  a mixed section between lower and upper data exists exactly when the
  canonical majorant is below the upper data.
* `Maths.Transport.leastMixedMajorant_bot_isLeast` - the closure of bottom is
  the least mixed section.
* `Maths.Transport.leastMixedMajorant_eq_self_iff` - the closed points of the
  least-majorant operator are exactly the mixed sections.

## Tags

transport, mixed polarity, laxification, closure, complete lattice
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

/-- Least mixed majorant as a closure operator.  Its closed points are defined
to be the mixed sections. -/
def leastMixedMajorantClosure
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    ClosureOperator (∀ vertex : V, Fiber vertex) :=
  ClosureOperator.ofPred (T.leastMixedMajorant hlax hresidual)
    (T.IsMixedSection mode)
    (fun lower ↦ (T.leastMixedMajorant_isLeast hlax hresidual lower).1)
    (fun lower ↦ (T.leastMixedMajorant_isLeast hlax hresidual lower).2.1)
    (fun {lower family} hlower hfamily ↦
      (T.leastMixedMajorant_isLeast hlax hresidual lower).2.2 family
        (fun vertex ↦ hlower vertex) hfamily)

/-- Applying the bundled closure operator computes the least mixed majorant. -/
@[simp] theorem leastMixedMajorantClosure_apply
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) :
    T.leastMixedMajorantClosure hlax hresidual lower =
      T.leastMixedMajorant hlax hresidual lower :=
  rfl

/-- A family is fixed by least-majorant closure exactly when it is a mixed
section. -/
theorem leastMixedMajorant_eq_self_iff
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (family : ∀ vertex : V, Fiber vertex) :
    T.leastMixedMajorant hlax hresidual family = family ↔
      T.IsMixedSection mode family := by
  exact (T.leastMixedMajorantClosure hlax hresidual).isClosed_iff.symm

/-- The mixed closure of bottom is the least mixed section. -/
theorem leastMixedMajorant_bot_isLeast
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    IsLeast {family | T.IsMixedSection mode family}
      (T.leastMixedMajorant hlax hresidual ⊥) := by
  have hleast := T.leastMixedMajorant_isLeast hlax hresidual (⊥ : ∀ vertex, Fiber vertex)
  exact ⟨hleast.2.1, fun family hfamily ↦
    hleast.2.2 family (fun _ ↦ bot_le) hfamily⟩

/-- Complete-lattice mixed transport with the supplied residuals has a mixed
section. -/
theorem exists_isMixedSection_of_galoisConnection
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    ∃ family, T.IsMixedSection mode family :=
  ⟨T.leastMixedMajorant hlax hresidual ⊥,
    (T.leastMixedMajorant_bot_isLeast hlax hresidual).1⟩

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
