/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantumTransport.Kraus
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Finite quantum instruments

An instrument assigns a completely positive map to each outcome. The effects of all outcomes
sum to the unit. Successive instruments record a pair of outcomes, and summing over the second
outcome recovers the effect of the first. On a graph of processes, branch maps pull observables
back along the reversed walk in the Heisenberg picture.

## Main definitions

* `QuantumTransport.FiniteInstrument` bundles the branches of a finite measurement.
* `QuantumTransport.FiniteInstrument.sequential` composes two measurements in physical order.
* `QuantumTransport.cpPullback` transports observables against the process direction.

## Main results

* `QuantumTransport.FiniteInstrument.sum_sequential_effect` forgets the second outcome.
* `QuantumTransport.cpPullback_walk_le` propagates an edgewise observable bound along a walk.

## References

* F. Loregian and A. Lorenzin, *Monadicity of noncommutative measurable spaces over
  C*-algebras*, Theorem 7.6 and Proposition 7.7. https://arxiv.org/abs/2611.32363
-/

@[expose] public section

namespace QuantumTransport

open Maths
open scoped CStarAlgebra Matrix

variable {A B C : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The Heisenberg operation with a single Kraus operator in a unital C*-algebra. -/
noncomputable def krausOperation (k : A) : A →CP A where
  toFun x := star k * x * k
  map_add' x y := by simp [mul_add, add_mul]
  map_smul' c x := by simp
  map_cstarMatrix_nonneg' n m hm := by
    let d : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (Matrix.diagonal fun _ => k)
    have heq : m.map (fun x => star k * x * k) = star d * m * d := by
      ext i j
      simp [d, CStarMatrix.mul_apply, CStarMatrix.star_apply, Matrix.diagonal_apply,
        apply_ite star, ite_mul]
    exact heq.symm ▸ star_left_conjugate_nonneg hm d

/-- Evaluating the operation conjugates the observable by the Kraus operator. -/
@[simp] theorem krausOperation_apply (k x : A) : krausOperation k x = star k * x * k := rfl

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- For square matrices the Heisenberg operation is the singleton Kraus map labelled by the
conjugate transpose. -/
theorem krausOperation_eq_krausMap {N : Type*} [Fintype N] [DecidableEq N]
    (k x : Matrix N N ℂ) : krausOperation k x = krausMap (fun _ : Unit => kᴴ) x := by
  simp [krausMap, Matrix.star_eq_conjTranspose]

/-- A finite family of completely positive branches whose effects sum to the identity. -/
@[ext] structure FiniteInstrument (I : Type*) [Fintype I] (A B : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] where
  /-- The observable pullback for a recorded outcome. -/
  branch : I → A →CP B
  /-- The total operation preserves the unit observable. -/
  normalized : ∑ i, branch i 1 = 1

namespace FiniteInstrument

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Measure with `first` and then `second`, retaining both outcomes in chronological order. -/
noncomputable def sequential (first : FiniteInstrument I B A) (second : FiniteInstrument J C B) :
    FiniteInstrument (I × J) C A where
  branch ij :=
    { (first.branch ij.1).toLinearMap.comp (second.branch ij.2).toLinearMap with
      map_cstarMatrix_nonneg' n m hm :=
        (first.branch ij.1).map_cstarMatrix_nonneg _ ((second.branch ij.2).map_cstarMatrix_nonneg
          m hm) }
  normalized := by
    change ∑ ij : I × J, first.branch ij.1 (second.branch ij.2 1) = 1
    rw [Fintype.sum_prod_type]
    simp only [← map_sum, second.normalized, first.normalized]

/-- The joint branch pulls an observable back through the later measurement first. -/
@[simp] theorem sequential_branch_apply (first : FiniteInstrument I B A)
    (second : FiniteInstrument J C B) (i : I) (j : J) (x : C) :
    (first.sequential second).branch (i, j) x = first.branch i (second.branch j x) := rfl

/-- Summing the joint effects over the second record recovers the first outcome effect. -/
theorem sum_sequential_effect (first : FiniteInstrument I B A)
    (second : FiniteInstrument J C B) (i : I) :
    ∑ j, (first.sequential second).branch (i, j) 1 = first.branch i 1 := by
  change ∑ j, first.branch i (second.branch j 1) = first.branch i 1
  rw [← map_sum, second.normalized]

end FiniteInstrument

section Walks

variable {V E : Type*} (G : EdgeGraph V E) (Fiber : V → Type*)
    [∀ v, CStarAlgebra (Fiber v)] [∀ v, PartialOrder (Fiber v)] [∀ v, StarOrderedRing (Fiber v)]
    (branch : ∀ e, Fiber (G.target e) →CP Fiber (G.source e))

/-- Heisenberg pullback of observables on a graph of completely positive processes. -/
def cpPullback : Transport G.reverse Fiber where
  edgeMap e := branch e

/-- Each local upper certificate bounds the observable pulled back along any forward walk. -/
theorem cpPullback_walk_le (b : ∀ v, Fiber v)
    (hb : ∀ e, branch e (b (G.target e)) ≤ b (G.source e))
    {s t : V} (w : G.Walk s t) : (cpPullback G Fiber branch).walkMap w.reverse (b t) ≤ b s := by
  have hm : (cpPullback G Fiber branch).IsMonotone := fun e => OrderHomClass.mono (branch e)
  have hs : (cpPullback G Fiber branch).IsLaxSection b := hb
  exact hs.walkMap_le hm w.reverse

end Walks

end QuantumTransport
