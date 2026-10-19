/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Exact
public import Maths.Multitubes.Mixed.AdjointOrder

import Mathlib.Basic.Finite.Sum

/-!
# Additive mixed-mode transport

An additive edge label acts by translation.  A lax edge keeps its orientation,
an oplax edge is reversed and receives the negative label, and an exact edge
occurs in both copies.  Thus mixed additive sections are ordinary additive
potentials on the laxification graph.

## Main definitions

* `Maths.AdditiveTransport.laxifiedWeight` - the signed label on the
  laxification graph.
* `Maths.AdditiveTransport.translationLowerAdjoint` - subtraction, the lower
  adjoint of a reverse-compatible edge.
* `Maths.AdditiveTransport.laxifiedTranslationTransport` - translation
  transport on the laxification graph.
* `Maths.AdditiveTransport.mixedMaxIncomingWeight` - the unrooted incoming
  path closure on the laxification graph.

## Main results

* `Maths.AdditiveTransport.translationLowerAdjoint_galoisConnection` - the
  subtraction/addition Galois connection.
* `Maths.AdditiveTransport.isMixedSection_iff_isLaxSection_laxified` - the
  partial-order reduction to signed lax transport.
* `Maths.AdditiveTransport.isMixedSection_iff_isPotential_laxified` - the
  mixed-section/potential correspondence.
* `Maths.AdditiveTransport.walkSum_eq_zero_of_exact`,
  `Maths.AdditiveTransport.walkSum_nonpos_of_lax_or_exact`, and
  `Maths.AdditiveTransport.walkSum_nonneg_of_oplax_or_exact` - the
  original-orientation cycle consequences.
* `Maths.AdditiveTransport.exists_isMixedSection_iff_forall_laxified_closedWalk_nonpos` -
  the finite-edge cycle feasibility criterion.
* `Maths.AdditiveTransport.mixedMaxIncomingWeight_isMixedSection` - the
  canonical mixed section supplied by the incoming envelope.
* `Maths.AdditiveTransport.isLeast_nonnegativeMixedSections` - the
  envelope is the least nonnegative mixed section.
* `Maths.AdditiveTransport.isGreatest_laxifiedIncomingWeights` - the
  path-closure characterization.

## Tags

transport, additive transport, mixed section, potential, laxification
-/

@[expose] public section

namespace Maths

noncomputable section

namespace AdditiveTransport

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

/-- Subtraction, the lower adjoint of an additive translation on a
reverse-compatible edge. -/
def translationLowerAdjoint (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) : A → A :=
  fun point => point - weight edge.1

/-- The lower adjoint subtracts the original edge label. -/
@[simp] theorem translationLowerAdjoint_apply (mode : E → EdgeMode) (weight : E → A)
    (edge : Transport.LaxificationReverseEdge mode) (point : A) :
    translationLowerAdjoint mode weight edge point = point - weight edge.1 :=
  rfl

/-- Subtraction is the lower adjoint of addition in the orientation
used by the mixed laxification theorem. -/
theorem translationLowerAdjoint_galoisConnection (mode : E → EdgeMode) (weight : E → A)
    [Preorder A] [IsOrderedAddMonoid A]
    (edge : Transport.LaxificationReverseEdge mode) :
    GaloisConnection (translationLowerAdjoint mode weight edge)
      (fun point : A => point + weight edge.1) := by
  intro sourcePoint targetPoint
  exact sub_le_iff_le_add

/-- Translation transport on the laxification graph with the signed additive
label. -/
def laxifiedTranslationTransport (G : EdgeGraph V E) (mode : E → EdgeMode)
    (weight : E → A) :
    Transport (Transport.laxificationGraph G mode) (fun _ : V => A) :=
  translationTransport
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
      (translationTransport G weight).laxification mode
        (translationLowerAdjoint mode weight) := by
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
    (translationTransport G weight).IsMixedSection mode potential ↔
      (laxifiedTranslationTransport G mode weight).IsLaxSection potential := by
  rw [laxifiedTranslationTransport_eq_laxification]
  exact Transport.isMixedSection_iff_laxification_of_galoisConnection
    (translationTransport G weight)
    (fun edge => translationLowerAdjoint_galoisConnection mode weight edge)

/-- A mixed additive section is exactly an ordinary additive potential on the
laxification graph with its signed weighting. -/
theorem isMixedSection_iff_isPotential_laxified
    [PartialOrder A] [IsOrderedAddMonoid A]
    (G : EdgeGraph V E) (mode : E → EdgeMode) (weight : E → A) (potential : V → A) :
    (translationTransport G weight).IsMixedSection mode potential ↔
      AdditiveTransport.IsPotential (Transport.laxificationGraph G mode)
        (laxifiedWeight mode weight) potential := by
  rw [isMixedSection_iff_isLaxSection_laxified]
  rfl

/-- An exact-mode closed walk has zero original signed weight. -/
theorem walkSum_eq_zero_of_exact
    [LE A] (mode : E → EdgeMode) {weight : E → A} {family : V → A}
    (hfamily : (translationTransport G weight).IsMixedSection mode family)
    {vertex : V} (cycle : G.Walk vertex vertex)
    (hmode : ∀ edge ∈ cycle.edges, (mode edge).IsExact) :
    walkSum weight cycle = 0 := by
  apply add_left_cancel (a := family vertex)
  simpa using hfamily.walkMap_eq_of_exact cycle hmode

section OrderedCycles

variable [Preorder A] [IsOrderedAddMonoid A]

/-- A closed walk using only lax or exact edges has nonpositive original
weight whenever a mixed section exists. -/
theorem walkSum_nonpos_of_lax_or_exact
    (mode : E → EdgeMode) {weight : E → A} {family : V → A}
    (hfamily : (translationTransport G weight).IsMixedSection mode family)
    {vertex : V} (cycle : G.Walk vertex vertex)
    (hmode : ∀ edge ∈ cycle.edges, (mode edge).IsLaxOrExact) :
    walkSum weight cycle ≤ 0 := by
  have hwalk := hfamily.walkMap_le_of_lax_or_exact
    (monotone_edgeMap_translationTransport weight) cycle hmode
  rw [walkMap_translationTransport] at hwalk
  apply le_of_add_le_add_left (a := family vertex)
  simpa using hwalk

/-- A closed walk using only oplax or exact edges has nonnegative original
weight whenever a mixed section exists. -/
theorem walkSum_nonneg_of_oplax_or_exact
    (mode : E → EdgeMode) {weight : E → A} {family : V → A}
    (hfamily : (translationTransport G weight).IsMixedSection mode family)
    {vertex : V} (cycle : G.Walk vertex vertex)
    (hmode : ∀ edge ∈ cycle.edges, (mode edge).IsOplaxOrExact) :
    0 ≤ walkSum weight cycle := by
  have hwalk := hfamily.le_walkMap_of_oplax_or_exact
    (monotone_edgeMap_translationTransport weight) cycle hmode
  rw [walkMap_translationTransport] at hwalk
  apply le_of_add_le_add_left (a := family vertex)
  simpa using hwalk

end OrderedCycles

section Finite

variable [LinearOrder A] [IsOrderedAddMonoid A]

/-- The signed incoming path closure on the laxification graph. -/
def mixedMaxIncomingWeight (G : EdgeGraph V E) (mode : E → EdgeMode)
    [Finite (Transport.LaxificationEdge mode)] (weight : E → A) (vertex : V) : A :=
  AdditiveTransport.maxIncomingWeight
    (Transport.laxificationGraph G mode) (laxifiedWeight mode weight) vertex

/-- Every transformed walk is bounded by the incoming envelope when all
transformed closed walks have nonpositive weight. -/
theorem walkSum_le_mixedMaxIncomingWeight
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      walkSum (laxifiedWeight mode weight) cycle ≤ 0)
    {start finish : V} (walk : (Transport.laxificationGraph G mode).Walk start finish) :
    walkSum (laxifiedWeight mode weight) walk ≤
      mixedMaxIncomingWeight G mode weight finish := by
  exact AdditiveTransport.walkSum_le_maxIncomingWeight hcycle walk

/-- The incoming envelope is the greatest weight of a transformed walk ending
at the specified vertex, under the nonpositive closed-walk condition. -/
theorem isGreatest_laxifiedIncomingWeights
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      walkSum (laxifiedWeight mode weight) cycle ≤ 0)
    (vertex : V) :
    IsGreatest
      (AdditiveTransport.incomingWeights (Transport.laxificationGraph G mode)
        (laxifiedWeight mode weight) vertex)
      (mixedMaxIncomingWeight G mode weight vertex) := by
  exact AdditiveTransport.isGreatest_incomingWeights hcycle vertex

/-- The incoming envelope is a mixed section of the original additive
translation transport under the nonpositive transformed-cycle condition. -/
theorem mixedMaxIncomingWeight_isMixedSection
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      walkSum (laxifiedWeight mode weight) cycle ≤ 0) :
    (translationTransport G weight).IsMixedSection mode
      (mixedMaxIncomingWeight G mode weight) := by
  apply (isMixedSection_iff_isPotential_laxified G mode weight _).2
  exact AdditiveTransport.maxIncomingWeight_isPotential hcycle

/-- The signed incoming path closure is the least nonnegative mixed section.
It is a maximum over path weights and simultaneously a minimum over normalized
feasible sections. -/
theorem isLeast_nonnegativeMixedSections
    (mode : E → EdgeMode) [Finite (Transport.LaxificationEdge mode)]
    {weight : E → A}
    (hcycle : ∀ (vertex : V)
      (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
      walkSum (laxifiedWeight mode weight) cycle ≤ 0) :
    IsLeast
      {potential : V → A | (0 : V → A) ≤ potential ∧
        (translationTransport G weight).IsMixedSection mode potential}
      (mixedMaxIncomingWeight G mode weight) := by
  have hleast := AdditiveTransport.isLeast_nonnegativePotentials hcycle
  constructor
  · exact ⟨hleast.1.1,
      (isMixedSection_iff_isPotential_laxified G mode weight _).2 hleast.1.2⟩
  · rintro potential ⟨hnonnegative, hfamily⟩
    exact hleast.2 ⟨hnonnegative,
      (isMixedSection_iff_isPotential_laxified G mode weight _).1 hfamily⟩

/-- A mixed additive section exists exactly when every transformed closed walk
has nonpositive signed weight. -/
theorem exists_isMixedSection_iff_forall_laxified_closedWalk_nonpos
    (G : EdgeGraph V E) (mode : E → EdgeMode)
    [Finite (Transport.LaxificationEdge mode)] (weight : E → A) :
    (∃ potential : V → A,
      (translationTransport G weight).IsMixedSection mode potential) ↔
      ∀ (vertex : V)
        (cycle : (Transport.laxificationGraph G mode).Walk vertex vertex),
        walkSum (laxifiedWeight mode weight) cycle ≤ 0 := by
  rw [show (∃ potential : V → A,
      (translationTransport G weight).IsMixedSection mode potential) ↔
      ∃ potential : V → A,
        AdditiveTransport.IsPotential (Transport.laxificationGraph G mode)
          (laxifiedWeight mode weight) potential by
        simp only [isMixedSection_iff_isPotential_laxified]]
  exact AdditiveTransport.exists_isPotential_iff_forall_closedWalk_nonpos _

end Finite

end AdditiveTransport

end

end Maths
