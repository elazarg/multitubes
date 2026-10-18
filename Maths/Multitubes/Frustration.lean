/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Symmetric
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat

/-!
# Frustration of unit-valued gains

An edge is frustrated under a switching function when its switched gain is not the identity.
The frustration index of a unit-valued gain on a finite graph is the least number of edges
frustrated under any switching.  It measures the distance from classical balance in two
equivalent ways.

* **Deletion equals switching.**  The edges a switching leaves frustrated can be deleted to
  leave a classically balanced gain, and conversely every deletion set leaving a balanced
  gain contains the frustrated edges of some switching.  So the frustration index is the least
  size of a deletion set restoring balance (`Maths.frustrationIndex_eq_sInf_deletion`).
* **Packing lower bound.**  Every switching frustrates an edge on each unbalanced closed
  walk of the symmetrization.  Closed walks using pairwise disjoint sets of edges therefore
  certify a lower bound on the frustration index (`Maths.le_frustrationIndex_of_disjoint`).

For signs and an all-negative gain the frustration index is the number of edges left uncut by
a maximum cut; in general it is not a cut quantity.  These are exact combinatorial statements;
no approximation or complexity claim is made.

## Main definitions

* `Maths.frustratedEdges`: the edges left non-trivial by a switching.
* `Maths.frustrationIndex`: the least number of frustrated edges over all switchings.

## Main results

* `Maths.hasTrivialCycleLabels_restrict_not_frustrated`: deleting the frustrated edges of any
  switching leaves a classically balanced gain.
* `Maths.exists_frustratedEdges_subset`: every deletion set leaving a balanced gain contains
  the frustrated edges of some switching.
* `Maths.frustrationIndex_eq_sInf_deletion`: the frustration index is the least size of a
  balancing deletion set.
* `Maths.exists_frustrated_mem_of_unbalanced`: every switching frustrates an edge on each
  unbalanced closed walk.
* `Maths.le_frustrationIndex_of_disjoint`: edge-disjoint unbalanced closed walks bound the
  frustration index from below.

## References

* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory Ser. B 47
  (1989), 32-52.

## Tags

gain graph, signed graph, frustration index, balance, switching
-/

@[expose] public section

namespace Maths

universe uV uE uM

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {M : Type uM} [Monoid M]

/-- The edges whose switched gain is not the identity. -/
def frustratedEdges (G : EdgeGraph V E) (gain : E → Mˣ) (η : V → Mˣ) : Set E :=
  {edge | switch G η (fun edge => (gain edge : M)) edge ≠ 1}

/-- The frustration index: the least number of edges frustrated under any switching. -/
noncomputable def frustrationIndex (G : EdgeGraph V E) (gain : E → Mˣ) : ℕ :=
  ⨅ η : V → Mˣ, (frustratedEdges G gain η).ncard

/-- In a group, `a * u * b⁻¹ = 1` exactly when `u = a⁻¹ * b`, read on unit values. -/
private theorem val_mul_mul_inv_eq_one_iff (a u b : Mˣ) :
    (a : M) * u * ((b⁻¹ : Mˣ) : M) = 1 ↔ (u : M) = ((a⁻¹ : Mˣ) : M) * b := by
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_one, Units.val_inj,
    Units.val_inj, mul_inv_eq_one, eq_inv_mul_iff_mul_eq]

/-- An edge is not frustrated exactly when its gain is the switching of the trivial gain by
the inverse function. -/
private theorem gain_eq_switch_inv_iff (gain : E → Mˣ) (η : V → Mˣ) (edge : E) :
    edge ∉ frustratedEdges G gain η ↔
      (gain edge : M) = switch G η⁻¹ 1 edge := by
  change ¬ (switch G η (fun edge => (gain edge : M)) edge ≠ 1) ↔ _
  rw [not_not, switch_apply, switch_apply, Pi.one_apply, mul_one, Pi.inv_apply, Pi.inv_apply,
    inv_inv]
  exact val_mul_mul_inv_eq_one_iff _ _ _

/-- **Deleting frustrated edges balances.**  Removing the edges a switching leaves frustrated
gives a gain that is balanced in the classical sense. -/
theorem hasTrivialCycleLabels_restrict_not_frustrated (gain : E → Mˣ) (η : V → Mˣ) :
    HasTrivialCycleLabels (G.restrictEdges (frustratedEdges G gain η)ᶜ).symmetrization
      (symmetricGain fun edge => gain edge.1) := by
  rw [hasTrivialCycleLabels_symmetricGain_iff]
  exact ⟨η⁻¹, funext fun edge => (gain_eq_switch_inv_iff gain η edge.1).mp edge.2⟩

/-- **Balancing deletions contain frustrated edges.**  If deleting a set of edges leaves a
classically balanced gain, some switching frustrates only edges of that set. -/
theorem exists_frustratedEdges_subset (gain : E → Mˣ) (deleted : Set E)
    (hbalanced : HasTrivialCycleLabels (G.restrictEdges deletedᶜ).symmetrization
      (symmetricGain fun edge => gain edge.1)) :
    ∃ η : V → Mˣ, frustratedEdges G gain η ⊆ deleted := by
  obtain ⟨θ, hθ⟩ := (hasTrivialCycleLabels_symmetricGain_iff _).mp hbalanced
  refine ⟨θ⁻¹, fun edge hfrustrated => ?_⟩
  by_contra hkept
  refine (gain_eq_switch_inv_iff gain θ⁻¹ edge).mpr ?_ hfrustrated
  rw [inv_inv]
  exact congrFun hθ ⟨edge, hkept⟩

/-- **Deletion equals switching.**  The frustration index is the least number of edges whose
deletion leaves a classically balanced gain. -/
theorem frustrationIndex_eq_sInf_deletion [Finite E] (gain : E → Mˣ) :
    frustrationIndex G gain =
      sInf {count | ∃ deleted : Set E, deleted.ncard = count ∧
        HasTrivialCycleLabels (G.restrictEdges deletedᶜ).symmetrization
          (symmetricGain fun edge => gain edge.1)} := by
  apply le_antisymm
  · apply le_csInf
    · refine ⟨_, Set.univ, rfl, fun vertex cycle => ?_⟩
      cases cycle with
      | nil => rfl
      | concat edge _ => exact absurd (Set.mem_univ _) edge.1.2
    · rintro count ⟨deleted, rfl, hbalanced⟩
      obtain ⟨η, hsubset⟩ := exists_frustratedEdges_subset gain deleted hbalanced
      exact (ciInf_le (OrderBot.bddBelow _) η).trans
        (Set.ncard_le_ncard hsubset (Set.toFinite _))
  · obtain ⟨η, hη⟩ := Nat.sInf_mem (Set.range_nonempty fun η : V → Mˣ =>
      (frustratedEdges G gain η).ncard)
    refine Nat.sInf_le ⟨frustratedEdges G gain η, ?_,
      hasTrivialCycleLabels_restrict_not_frustrated gain η⟩
    exact hη

/-- The frustration index is attained by some switching. -/
theorem exists_frustrationIndex_eq (gain : E → Mˣ) :
    ∃ η : V → Mˣ, (frustratedEdges G gain η).ncard = frustrationIndex G gain :=
  Nat.sInf_mem (Set.range_nonempty _)

/-- A walk whose every edge carries the trivial label has the trivial composite label. -/
private theorem walkLabel_eq_one_of_forall_mem {E' : Type*} {H : EdgeGraph V E'}
    {label : E' → M} {start finish : V} (walk : H.Walk start finish)
    (htrivial : ∀ edge ∈ walk.edges, label edge = 1) : walkLabel label walk = 1 := by
  induction walk with
  | nil => rfl
  | concat edge walkSoFar ih =>
      rw [walkLabel_concat, htrivial edge (by simp),
        ih fun e he => htrivial e (by simp [he]), one_mul]

/-- **Unbalanced closed walks meet every switching's frustration.**  Every switching frustrates
some edge traversed, in either orientation, by an unbalanced closed walk of the
symmetrization. -/
theorem exists_frustrated_mem_of_unbalanced (gain : E → Mˣ) (η : V → Mˣ) {base : V}
    (cycle : G.symmetrization.Walk base base)
    (hunbalanced : walkLabel (symmetricGain gain) cycle ≠ 1) :
    ∃ edge ∈ cycle.edges.map Prod.fst, edge ∈ frustratedEdges G gain η := by
  by_contra hnone
  push Not at hnone
  apply hunbalanced
  have hswitched : walkLabel (switch G.symmetrization η (symmetricGain gain)) cycle = 1 := by
    refine walkLabel_eq_one_of_forall_mem cycle fun edge hedge => ?_
    have hfirst := (gain_eq_switch_inv_iff gain η edge.1).mp
      (hnone edge.1 (List.mem_map_of_mem hedge))
    rw [switch_apply, Pi.one_apply, mul_one, Pi.inv_apply, Pi.inv_apply, inv_inv] at hfirst
    rcases edge with ⟨edge, _ | _⟩
    · change (η (G.target edge) : M) * gain edge * ((η (G.source edge))⁻¹ : Mˣ) = 1
      exact (val_mul_mul_inv_eq_one_iff _ _ _).mpr hfirst
    · have hunit : gain edge = (η (G.target edge))⁻¹ * η (G.source edge) :=
        Units.val_inj.mp (by rw [hfirst, Units.val_mul])
      change (η (G.source edge) : M) * (((gain edge)⁻¹ : Mˣ) : M) *
        ((η (G.target edge))⁻¹ : Mˣ) = 1
      rw [hunit, mul_inv_rev, inv_inv, ← Units.val_mul, ← Units.val_mul, ← mul_assoc,
        mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  rw [walkLabel_switch] at hswitched
  calc walkLabel (symmetricGain gain) cycle
      = Units.val (η base)⁻¹ *
          ((η base : M) * walkLabel (symmetricGain gain) cycle * Units.val (η base)⁻¹) *
            (η base : M) := by simp [mul_assoc]
    _ = 1 := by rw [hswitched]; simp

/-- **Packing lower bound.**  Unbalanced closed walks of the symmetrization traversing pairwise
disjoint sets of edges force at least that many frustrated edges under every switching, and
so bound the frustration index from below. -/
theorem le_frustrationIndex_of_disjoint [Finite E] (gain : E → Mˣ) {count : ℕ}
    (cycles : Fin count → Σ base, G.symmetrization.Walk base base)
    (hunbalanced : ∀ index, walkLabel (symmetricGain gain) (cycles index).2 ≠ 1)
    (hdisjoint : ∀ first second, first ≠ second → ∀ edge,
      edge ∈ (cycles first).2.edges.map Prod.fst →
        edge ∉ (cycles second).2.edges.map Prod.fst) :
    count ≤ frustrationIndex G gain := by
  obtain ⟨η, hη⟩ := exists_frustrationIndex_eq (G := G) gain
  rw [← hη]
  choose witness hmem hfrustrated using fun index =>
    exists_frustrated_mem_of_unbalanced gain η (cycles index).2 (hunbalanced index)
  have hinjective : Function.Injective witness := by
    intro first second hequal
    by_contra hne
    exact hdisjoint first second hne _ (hmem first) (hequal ▸ hmem second)
  calc count = (Set.range witness).ncard := by
        rw [Set.ncard_range_of_injective hinjective, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ ≤ (frustratedEdges G gain η).ncard :=
        Set.ncard_le_ncard (Set.range_subset_iff.mpr hfrustrated) (Set.toFinite _)

end Maths
