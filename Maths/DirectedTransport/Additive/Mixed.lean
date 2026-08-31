/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Exact
public import Maths.DirectedTransport.Mixed.AdjointOrder

import Mathlib.Data.Finite.Sum

/-!
# Additive mixed-polarity transport

An additive edge label acts by translation.  A lax edge keeps its orientation,
an oplax edge is reversed and receives the negative label, and an exact edge
occurs in both copies.  Thus mixed additive sections are ordinary additive
potentials on the laxification graph.

## Main definitions

* `Maths.MixedAdditiveTransport.laxifiedWeight` - the signed label on the
  laxification graph.
* `Maths.MixedAdditiveTransport.translationResidual` - the subtraction residual
  for a reverse-compatible edge.
* `Maths.MixedAdditiveTransport.laxifiedTranslationTransport` - translation
  transport on the laxification graph.
* `Maths.MixedAdditiveTransport.mixedMaxIncomingWeight` - the unrooted incoming
  path envelope on the laxification graph.

## Main results

* `Maths.MixedAdditiveTransport.translationResidual_galoisConnection` - the
  residual/addition Galois connection.
* `Maths.MixedAdditiveTransport.isMixedSection_iff_isLaxSection_laxified` - the
  partial-order reduction to signed lax transport.
* `Maths.MixedAdditiveTransport.isMixedSection_iff_isPotential_laxified` - the
  mixed-section/potential correspondence.
* `Maths.MixedAdditiveTransport.exists_isMixedSection_iff_forall_laxified_closedWalk_nonpos` -
  the finite-edge cycle feasibility criterion.
* `Maths.MixedAdditiveTransport.mixedMaxIncomingWeight_isMixedSection` - the
  canonical mixed section supplied by the incoming envelope.
* `Maths.MixedAdditiveTransport.isGreatest_laxifiedIncomingWeights` - the
  path-envelope characterization.

## Tags

directed transport, additive transport, mixed polarity, potential, laxification
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MixedAdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {A : Type*} [AddCommGroup A]

/-- The signed additive label on a laxification edge: forward copies have the
original label, while reverse copies have its negative. -/
def laxifiedWeight (mode : E → EdgeMode) (weight : E → A) :
    Transport.LaxificationEdge mode → A
  | .inl edge => weight edge.1
  | .inr edge => -weight edge.1

/-- The forward copy retains the original additive label. -/
@[simp] theorem laxifiedWeight_forward (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationForwardEdge mode) :
    laxifiedWeight mode weight (.inl edge) = weight edge.1 :=
  rfl

/-- The reverse copy receives the negative additive label. -/
@[simp] theorem laxifiedWeight_reverse (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) :
    laxifiedWeight mode weight (.inr edge) = -weight edge.1 :=
  rfl

/-- The subtraction residual of an additive translation on a
reverse-compatible edge. -/
def translationResidual (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) : A → A :=
  fun point => point - weight edge.1

/-- The residual evaluates by subtracting the original edge label. -/
@[simp] theorem translationResidual_apply (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) (point : A) :
    translationResidual mode weight edge point = point - weight edge.1 :=
  rfl

/-- The subtraction residual is the left adjoint of addition in the orientation
used by the mixed laxification theorem. -/
theorem translationResidual_galoisConnection (mode : E → EdgeMode) (weight : E → A)
    [Preorder A] [IsOrderedAddMonoid A]
    (edge : Transport.LaxificationReverseEdge mode) :
    GaloisConnection (translationResidual mode weight edge)
      (fun point : A => point + weight edge.1) := by
  intro sourcePoint targetPoint
  exact sub_le_iff_le_add

/-- Translation transport on the laxification graph with the signed additive
label. -/
def laxifiedTranslationTransport (G : EdgeGraph V E) (mode : E → EdgeMode)
    (weight : E → A) :
    Transport (Transport.laxificationGraph G mode) (fun _ : V => A) :=
  CycleCoboundary.translationTransport
    (Transport.laxificationGraph G mode) (laxifiedWeight mode weight)

/-- A forward transformed edge acts by translation by its original label. -/
@[simp] theorem laxifiedTranslationTransport_edgeMap_forward
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationForwardEdge mode) (point : A) :
    (laxifiedTranslationTransport G mode weight).edgeMap (.inl edge) point =
      point + weight edge.1 := by
  rfl

/-- A reverse transformed edge acts by translation by the negative label. -/
@[simp] theorem laxifiedTranslationTransport_edgeMap_reverse
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) (point : A) :
    (laxifiedTranslationTransport G mode weight).edgeMap (.inr edge) point =
      point - weight edge.1 := by
  change point + -weight edge.1 = point - weight edge.1
  exact (sub_eq_add_neg _ _).symm

/-- The signed translation transport agrees with the generic laxification. -/
theorem laxifiedTranslationTransport_eq_laxification
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A) :
    laxifiedTranslationTransport G mode weight =
      (CycleCoboundary.translationTransport G weight).laxification mode
        (translationResidual mode weight) := by
  change Transport.mk _ = Transport.mk _
  rw [Transport.mk.injEq]
  funext edge
  cases edge with
  | inl edge => rfl
  | inr edge =>
      funext point
      change point + -weight edge.1 = point - weight edge.1
      exact (sub_eq_add_neg _ _).symm

/-- A mixed section is exactly a lax section of the signed translation
transport on the laxification graph. -/
theorem isMixedSection_iff_isLaxSection_laxified
    [PartialOrder A] [IsOrderedAddMonoid A]
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A) (potential : V → A) :
    (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential ↔
      (laxifiedTranslationTransport G mode weight).IsLaxSection potential := by
  rw [laxifiedTranslationTransport_eq_laxification]
  exact Transport.isMixedSection_iff_laxification_of_galoisConnection
    (CycleCoboundary.translationTransport G weight)
    (fun edge => translationResidual_galoisConnection mode weight edge)

/-- A mixed additive section is exactly an ordinary additive potential on the
laxification graph with its signed weighting. -/
theorem isMixedSection_iff_isPotential_laxified
    [LinearOrder A] [IsOrderedAddMonoid A]
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A) (potential : V → A) :
    (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential ↔
      MaxPlusPotential.IsPotential (Transport.laxificationGraph G mode)
        (laxifiedWeight mode weight) potential := by
  rw [isMixedSection_iff_isLaxSection_laxified]
  rfl

section Finite

variable [LinearOrder A] [IsOrderedAddMonoid A]

/-- The signed incoming path envelope on the laxification graph. -/
def mixedMaxIncomingWeight (G : EdgeGraph V E) (mode : E → EdgeMode)
    [Finite (Transport.LaxificationEdge mode)] (weight : E → A) (vertex : V) : A :=
  MaxPlusPotential.maxIncomingWeight
    (Transport.laxificationGraph G mode) (laxifiedWeight mode weight) vertex

/-- Every transformed walk is bounded by the incoming envelope when all
transformed closed walks have nonpositive weight. -/
theorem walkWeight_le_mixedMaxIncomingWeight
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤ 0)
    {start finish : V} (walk : (Transport.laxificationGraph G mode).Walk start finish) :
    MaxPlusPotential.walkWeight (laxifiedWeight mode weight) walk ≤
      mixedMaxIncomingWeight G mode weight finish := by
  exact MaxPlusPotential.walkWeight_le_maxIncomingWeight hcycle walk

/-- The incoming envelope is the greatest weight of a transformed walk ending
at the specified vertex, under the nonpositive closed-walk condition. -/
theorem isGreatest_laxifiedIncomingWeights
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤ 0)
    (vertex : V) :
    IsGreatest
      (MaxPlusPotential.incomingWeights (Transport.laxificationGraph G mode)
        (laxifiedWeight mode weight) vertex)
      (mixedMaxIncomingWeight G mode weight vertex) := by
  exact MaxPlusPotential.isGreatest_incomingWeights hcycle vertex

/-- The incoming envelope is a mixed section of the original additive
translation transport under the nonpositive transformed-cycle condition. -/
theorem mixedMaxIncomingWeight_isMixedSection
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤ 0) :
    (CycleCoboundary.translationTransport G weight).IsMixedSection mode
      (mixedMaxIncomingWeight G mode weight) := by
  apply (isMixedSection_iff_isPotential_laxified G mode weight _).2
  exact MaxPlusPotential.maxIncomingWeight_isPotential hcycle

/-- A mixed additive section exists exactly when every transformed closed walk
has nonpositive signed weight. -/
theorem exists_isMixedSection_iff_forall_laxified_closedWalk_nonpos
    (G : EdgeGraph V E) (mode : E → EdgeMode)
    [Finite (Transport.LaxificationEdge mode)] (weight : E → A) :
    (∃ potential : V → A,
      (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential) ↔
      ∀ (vertex : V)
        (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
        MaxPlusPotential.walkWeight (laxifiedWeight mode weight) cycle ≤ 0 := by
  rw [show (∃ potential : V → A,
      (CycleCoboundary.translationTransport G weight).IsMixedSection mode potential) ↔
      ∃ potential : V → A,
        MaxPlusPotential.IsPotential (Transport.laxificationGraph G mode)
          (laxifiedWeight mode weight) potential by
        simp only [isMixedSection_iff_isPotential_laxified]]
  exact MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos _

end Finite

end MixedAdditiveTransport

end

end Maths
