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

When the fibers are complete lattices, the least mixed section above prescribed lower data is the
infimum of all of them.  Residuals turn mixed-polarity constraints into ordinary lax constraints
on the laxification graph, so mixed sections form a Moore family and the infimum is itself a
mixed section: it is the least lax majorant on the laxification graph.  Only the maps on edges
already in lax mode need a separate monotonicity hypothesis: the Galois connections provide the
remaining monotonicity.

## Main definitions

* `Maths.Transport.leastMixedMajorant` - the canonical least mixed section
  dominating prescribed lower data.
* `Maths.Transport.leastMixedMajorantClosure` - the closure operator of the Moore family of mixed
  sections.

## Main results

* `Maths.Transport.leastMixedMajorant_eq_leastLaxMajorant` - the least mixed majorant is the least
  lax majorant of the laxification.
* `Maths.Transport.isMixedSection_sInf` - mixed sections form a Moore family.
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
variable (mode : E → EdgeMode) {residual : ∀ edge : LaxificationReverseEdge mode,
  Fiber (G.target edge.1) → Fiber (G.source edge.1)}

/-- The least mixed section dominating prescribed lower data: the infimum of all of them.  It is
intrinsic to the mixed constraints; residuals are needed only to show that it is itself a mixed
section (`Maths.Transport.leastMixedMajorant_isLeast`). -/
def leastMixedMajorant (lower : ∀ vertex : V, Fiber vertex) : ∀ vertex : V, Fiber vertex :=
  sInf {family | lower ≤ family ∧ T.IsMixedSection mode family}

variable {mode}

/-- The least mixed majorant is the least lax majorant on the laxification graph. -/
theorem leastMixedMajorant_eq_leastLaxMajorant
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) :
    T.leastMixedMajorant mode lower = (T.laxification mode residual).leastLaxMajorant lower :=
  congrArg sInf <| Set.ext fun _ =>
    and_congr_right' (T.isMixedSection_iff_laxification_of_galoisConnection hresidual)

/-- **Mixed sections form a Moore family**, given residuals for the oplax and exact edges and
monotone maps on the lax edges. -/
theorem isMixedSection_sInf
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    {families : Set (∀ vertex : V, Fiber vertex)}
    (hfamilies : ∀ family ∈ families, T.IsMixedSection mode family) :
    T.IsMixedSection mode (sInf families) :=
  (T.isMixedSection_iff_laxification_of_galoisConnection hresidual).2 <|
    isLaxSection_sInf (T.monotone_laxification_of_galoisConnection hlax hresidual)
      fun _ hfamily =>
        (T.isMixedSection_iff_laxification_of_galoisConnection hresidual).1 (hfamilies _ hfamily)

/-- The canonical mixed majorant dominates the lower data, is a mixed section,
and is below every mixed section dominating that lower data. -/
theorem leastMixedMajorant_isLeast
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) :
    IsLeast {family | lower ≤ family ∧ T.IsMixedSection mode family}
      (T.leastMixedMajorant mode lower) :=
  ⟨⟨le_sInf fun _ hfamily => hfamily.1, T.isMixedSection_sInf hlax hresidual fun _ h => h.2⟩,
    fun _ hfamily => sInf_le hfamily⟩

/-- Least mixed majorant as the closure operator of the Moore family of mixed sections. -/
def leastMixedMajorantClosure
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    ClosureOperator (∀ vertex : V, Fiber vertex) :=
  ClosureOperator.ofCompletePred (T.IsMixedSection mode) fun _ =>
    T.isMixedSection_sInf hlax hresidual

/-- Applying the bundled closure operator computes the least mixed majorant. -/
@[simp] theorem leastMixedMajorantClosure_apply
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower : ∀ vertex : V, Fiber vertex) :
    T.leastMixedMajorantClosure hlax hresidual lower = T.leastMixedMajorant mode lower :=
  (sInf_eq_iInf' _).symm

/-- A family is fixed by least-majorant closure exactly when it is a mixed
section. -/
theorem leastMixedMajorant_eq_self_iff
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (family : ∀ vertex : V, Fiber vertex) :
    T.leastMixedMajorant mode family = family ↔ T.IsMixedSection mode family := by
  rw [← T.leastMixedMajorantClosure_apply hlax hresidual]
  exact (T.leastMixedMajorantClosure hlax hresidual).isClosed_iff.symm

/-- The mixed closure of bottom is the least mixed section. -/
theorem leastMixedMajorant_bot_isLeast
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    IsLeast {family | T.IsMixedSection mode family} (T.leastMixedMajorant mode ⊥) := by
  have hleast := T.leastMixedMajorant_isLeast hlax hresidual (⊥ : ∀ vertex, Fiber vertex)
  exact ⟨hleast.1.2, fun _ hfamily ↦ hleast.2 ⟨bot_le, hfamily⟩⟩

/-- Complete-lattice mixed transport with the supplied residuals has a mixed
section. -/
theorem exists_isMixedSection_of_galoisConnection
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1)) :
    ∃ family, T.IsMixedSection mode family :=
  ⟨T.leastMixedMajorant mode ⊥, (T.leastMixedMajorant_bot_isLeast hlax hresidual).1⟩

/-- A mixed section between lower and upper data exists exactly when the
canonical mixed majorant of the lower data is below the upper data. -/
theorem exists_isMixedSection_between_iff_leastMixedMajorant_le
    (hlax : ∀ edge : E, mode edge = .lax → Monotone (T.edgeMap edge))
    (hresidual : ∀ edge : LaxificationReverseEdge mode,
      GaloisConnection (residual edge) (T.edgeMap edge.1))
    (lower upper : ∀ vertex : V, Fiber vertex) :
    (∃ family, T.IsMixedSection mode family ∧ lower ≤ family ∧ family ≤ upper) ↔
      T.leastMixedMajorant mode lower ≤ upper := by
  have hleast := T.leastMixedMajorant_isLeast hlax hresidual lower
  constructor
  · rintro ⟨family, hfamily, hlower, hupper⟩
    exact (hleast.2 ⟨hlower, hfamily⟩).trans hupper
  · intro hupper
    exact ⟨T.leastMixedMajorant mode lower, hleast.1.2, hleast.1.1, hupper⟩

end CompleteLattice

end Transport
end Maths

end
