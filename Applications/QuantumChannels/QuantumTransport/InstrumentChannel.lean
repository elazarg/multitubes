/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantumTransport.Instruments
public import Mathlib.Algebra.Order.Star.Pi

/-!
# A finite measurement record as a channel

For a finite outcome type `I`, an observable on the classical record and quantum output is a
tuple of observables indexed by `I`. A finite instrument evaluates such a tuple by summing its
branches. Conversely, applying a unital completely positive map to an observable supported
at a single outcome recovers that branch.

## Main definitions

* `QuantumTransport.FiniteInstrument.channel` evaluates a tuple of outcome-dependent observables.

## Main results

* `QuantumTransport.FiniteInstrument.channelEquiv` identifies finite instruments with unital
  completely positive maps out of the finite product algebra.
* `QuantumTransport.FiniteInstrument.channel_sequential` evaluates a joint record by
  successive pullback.

## References

* F. Loregian and A. Lorenzin, *Monadicity of noncommutative measurable spaces over
  C*-algebras*, Theorem 7.6. https://arxiv.org/abs/2611.32363
-/

@[expose] public section

namespace QuantumTransport.FiniteInstrument

open scoped CStarAlgebra

variable {I A B : Type*} [Fintype I]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A channel on record-dependent observables, computed by summing the individual branches. -/
noncomputable def channel (p : FiniteInstrument I A B) : (I → A) →CP B where
  toFun x := ∑ i, p.branch i (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]
  map_cstarMatrix_nonneg' n m hm := by
    let ev (i : I) := Pi.evalNonUnitalStarAlgHom ℂ (fun _ : I => A) i
    let block (i : I) := (m.map (ev i)).map (p.branch i)
    have hblock (i : I) : 0 ≤ block i :=
      (p.branch i).map_cstarMatrix_nonneg _ (CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
        (ev i) n m hm)
    have heq : m.map (fun x => ∑ i, p.branch i (x i)) = ∑ i, block i := by
      ext j k
      let entry : CStarMatrix (Fin n) (Fin n) B →+ B :=
        { toFun x := x j k, map_zero' := rfl, map_add' _ _ := rfl }
      exact (map_sum entry block Finset.univ).symm
    exact heq.symm ▸ Finset.sum_nonneg (fun i _ => hblock i)

/-- A joint observable on two records can be evaluated by pulling back each record in turn. -/
theorem channel_sequential {J C : Type*} [Fintype J] [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (first : FiniteInstrument I B A)
    (second : FiniteInstrument J C B) (x : I × J → C) :
    (first.sequential second).channel x =
      first.channel (fun i => second.channel (fun j => x (i, j))) := by
  change ∑ ij : I × J, first.branch ij.1 (second.branch ij.2 (x ij)) =
    ∑ i, first.branch i (∑ j, second.branch j (x (i, j)))
  rw [Fintype.sum_prod_type]
  simp only [map_sum]

/-- An observable supported on one record evaluates to that branch applied to its value. -/
@[simp] theorem channel_single [DecidableEq I] (p : FiniteInstrument I A B) (i : I) (x : A) :
    p.channel (Pi.single i x) = p.branch i x := by
  change ∑ j, p.branch j ((Pi.single i x : I → A) j) = p.branch i x
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The observable supported at a single recorded outcome, as a nonunital *-homomorphism. -/
noncomputable def recordInclusion [DecidableEq I] (i : I) : A →⋆ₙₐ[ℂ] (I → A) :=
  { LinearMap.single ℂ (fun _ : I => A) i with
    map_zero' := (LinearMap.single ℂ (fun _ : I => A) i).map_zero
    map_mul' := Pi.single_mul (α := fun _ : I => A) i
    map_star' x := (Pi.star_single (R := fun _ : I => A) i x).symm }

open Classical in
/-- Restricting a channel to observables supported at each outcome recovers an instrument. -/
noncomputable def ofChannel (f : (I → A) →CP B) (hf : f 1 = 1) : FiniteInstrument I A B where
  branch i :=
    { f.toLinearMap.comp (LinearMap.single ℂ (fun _ : I => A) i) with
      map_cstarMatrix_nonneg' n m hm :=
        f.map_cstarMatrix_nonneg _ (CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
          (recordInclusion (A := A) i) n m hm) }
  normalized := by
    change ∑ i : I, f (Pi.single i (1 : A)) = 1
    rw [← map_sum]
    exact (congrArg f (Finset.univ_sum_single (1 : I → A))).trans hf

open Classical in
/-- Finite instruments correspond bijectively to unital completely positive maps on
outcome-indexed tuples. -/
noncomputable def channelEquiv :
    FiniteInstrument I A B ≃ {f : (I → A) →CP B // f 1 = 1} where
  toFun p := ⟨p.channel, p.normalized⟩
  invFun f := ofChannel f.1 f.2
  left_inv p := by
    apply FiniteInstrument.ext
    funext i
    exact DFunLike.ext _ _ (channel_single p i)
  right_inv f := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    change ∑ i : I, f.1 (Pi.single i (x i)) = f.1 x
    rw [← map_sum, Finset.univ_sum_single]

end QuantumTransport.FiniteInstrument
