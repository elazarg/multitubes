/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Matrix.Mul

public import Maths.LinearProgramming.StandardForm

import Maths.LinearProgramming.FourierMotzkin

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear programming duality in standard form

The standard-form linear program is `max ⟪c, z⟫` over the nonnegative affine fiber
`0 ≤ z`, `A *ᵥ z = rhs`; its dual is `min ⟪rhs, y⟫` over the free vectors `y` on the rows
with `Aᵀ *ᵥ y ≥ c`. This file proves weak duality, strong duality, dual attainment and
complementary slackness for that pair.

Following the pattern of `Maths.Multitube.MaxAffine.Duality` and
`Maths.FiniteInequality.worstResidualAtMost_iff_normalizedDual_le`, strong duality
is stated as an exact *threshold* equivalence, not an equality of optima: for every
level `t`, the primal attains at least `t` exactly when the dual is bounded below by `t` (and
the primal is feasible). This sidesteps extended reals and attainment, and stays meaningful
when a side is unbounded or empty.

The primal-feasibility conjunct on the right is not decoration. If both programs are
infeasible then no `y` is dual feasible, so the dual bound holds vacuously at every level while
the primal attains none; that corner is exactly what the conjunct excludes.
`Maths.LinearProgramming.exists_scaledDual_of_not_exists_objective_ge` is the sharper,
hypothesis-free form behind it: the obstruction to reaching level `t` is always a *scaled* dual
vector `(y, lam)` with `lam ≥ 0`, which is a genuine dual point when `lam > 0` and a Farkas
certificate of primal infeasibility when `lam = 0`.

Everything here is proved over an arbitrary linearly ordered field, directly from
`Maths.LinearProgramming.theorem_of_alternative`; no topology and no completeness is
involved. Primal feasibility is membership in the standard-form fiber
`Maths.LinearProgramming.standardFeasibleSet` of
`Maths.LinearProgramming.StandardForm`, which is itself defined over an arbitrary
linearly ordered field.

## Main definitions

* `Maths.LinearProgramming.IsDualFeasible`: dual feasibility of `Aᵀ *ᵥ y ≥ c`.
* `Maths.LinearProgramming.ComplementarySlackness`: the complementary slackness
  relation between a primal and a dual vector.

## Main results

* `Maths.LinearProgramming.objective_le_of_isDualFeasible`: **weak duality**.
* `Maths.LinearProgramming.exists_scaledDual_of_not_exists_objective_ge`: an
  unreachable level is witnessed by a scaled dual vector.
* `Maths.LinearProgramming.exists_objective_ge_iff_feasible_and_forall_isDualFeasible`,
  `Maths.LinearProgramming.exists_objective_ge_iff_forall_isDualFeasible`: **strong
  duality**, as a threshold equivalence.
* `Maths.LinearProgramming.exists_isDualFeasible_objective_le_of_forall_le`: **dual
  attainment** - an attained primal optimum is matched by an attained dual optimum.
* `Maths.LinearProgramming.complementarySlackness_iff_objective_eq`,
  `Maths.LinearProgramming.complementarySlackness_iff_forall_ne_zero`:
  **complementary slackness**, and its support form.
* `Maths.LinearProgramming.forall_le_of_complementarySlackness`,
  `Maths.LinearProgramming.exists_isDualFeasible_complementarySlackness_of_forall_le`:
  complementary slackness is exactly a certificate of optimality.
* `Maths.LinearProgramming.isStandardOptimal_of_complementarySlackness`,
  `Maths.LinearProgramming.exists_isDualFeasible_complementarySlackness_of_standardOptimal`:
  the transfer of all of this to
  `Maths.LinearProgramming.IsStandardOptimal`.

## Tags

linear programming, duality, weak duality, strong duality, complementary slackness, Farkas
lemma
-/

open Finset Matrix

@[expose] public section

namespace Maths
namespace LinearProgramming

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Dual feasibility -/

/-- Dual feasibility for the standard-form program with objective `c`: the row vector `y`
satisfies `Aᵀ *ᵥ y ≥ c`, written out column by column. There is no sign constraint on `y`,
matching the equality constraints of the primal. -/
def IsDualFeasible {Row Col : Type*} [Fintype Row]
    (A : Matrix Row Col 𝕜) (c : Col → 𝕜) (y : Row → 𝕜) : Prop :=
  ∀ j, c j ≤ ∑ i, y i * A i j

omit [IsStrictOrderedRing 𝕜] in
/-- Expanding the primal objective through the constraint `A *ᵥ z = rhs`: the dual objective at
any `y` is the pairing of `z` with the dual slacks plus the primal objective. -/
theorem sum_dual_eq_of_mem_standardFeasibleSet
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {z : Col → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (y : Row → 𝕜) :
    ∑ i, y i * rhs i = ∑ j, (∑ i, y i * A i j) * z j := by
  have hr (i : Row) : rhs i = ∑ j, A i j * z j := by
    rw [← congrFun hz.2 i]
    simp [Matrix.mulVec, dotProduct]
  simp only [hr, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- **Weak duality**: the primal objective at any feasible point is at most the dual objective
at any dual feasible point. -/
theorem objective_le_of_isDualFeasible
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {c : Col → 𝕜} {z : Col → 𝕜} {y : Row → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (hy : IsDualFeasible A c y) :
    ∑ j, c j * z j ≤ ∑ i, y i * rhs i := by
  rw [sum_dual_eq_of_mem_standardFeasibleSet hz y]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy j) (hz.1 j)

/-! ### The scaled dual behind strong duality

An unreachable objective level is certified by a pair `(y, lam)` with `lam ≥ 0` solving the
*homogenized* dual `Aᵀ *ᵥ y ≥ lam • c`, `⟪rhs, y⟫ < lam * t`. This is what the theorem of the
alternative produces for the system `0 ≤ z`, `A *ᵥ z ≥ rhs`, `-A *ᵥ z ≥ -rhs`, `⟪c, z⟫ ≥ t`,
whose Farkas certificate splits into a nonnegative primal slack part, the difference of the two
sign copies of the equality rows, and the multiplier of the objective row. -/

/-- If no feasible point reaches objective level `t`, then some scaled dual pair `(y, lam)`
with `lam ≥ 0` witnesses that: `Aᵀ *ᵥ y ≥ lam • c` while `⟪rhs, y⟫ < lam * t`.

For `lam > 0` the rescaling `y / lam` is an honest dual feasible point beating the level; for
`lam = 0` the vector `y` is a Farkas certificate of primal infeasibility, which is the case the
theorem of the alternative allows when the fiber itself is empty. -/
theorem exists_scaledDual_of_not_exists_objective_ge
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) (t : 𝕜)
    (h : ¬ ∃ z, z ∈ standardFeasibleSet A rhs ∧ t ≤ ∑ j, c j * z j) :
    ∃ (y : Row → 𝕜) (lam : 𝕜), 0 ≤ lam ∧ (∀ j, lam * c j ≤ ∑ i, y i * A i j) ∧
      ∑ i, y i * rhs i < lam * t := by
  classical
  set e : Col ≃ Fin (Fintype.card Col) := Fintype.equivFin Col with he
  set M : (Col ⊕ Row ⊕ Row ⊕ Unit) → Fin (Fintype.card Col) → 𝕜 :=
    Sum.elim (fun j k => if e.symm k = j then 1 else 0)
      (Sum.elim (fun i k => A i (e.symm k))
        (Sum.elim (fun i k => -A i (e.symm k)) (fun _ k => c (e.symm k)))) with hM
  set bvec : (Col ⊕ Row ⊕ Row ⊕ Unit) → 𝕜 :=
    Sum.elim (fun _ => 0) (Sum.elim rhs (Sum.elim (fun i => -rhs i) (fun _ => t))) with hb
  -- The system is infeasible, since a solution would be a feasible point reaching level `t`.
  have hinf : ¬ IsFeasible M bvec := by
    rintro ⟨x, hx⟩
    have hcoord (j : Col) : rowEval M (Sum.inl j) x = x (e j) := by
      have hswap : ∑ j' : Col, (if j' = j then (1 : 𝕜) else 0) * x (e j')
          = ∑ k, (if e.symm k = j then (1 : 𝕜) else 0) * x k :=
        Fintype.sum_equiv e _ _ fun j' => by rw [Equiv.symm_apply_apply]
      simp only [rowEval, hM, Sum.elim_inl]
      rw [← hswap]
      simp
    have hrow (i : Row) : rowEval M (Sum.inr (Sum.inl i)) x = ∑ j, A i j * x (e j) := by
      simp only [rowEval, hM, Sum.elim_inl, Sum.elim_inr]
      exact (Fintype.sum_equiv e _ _ fun j => by rw [Equiv.symm_apply_apply]).symm
    have hrow' (i : Row) :
        rowEval M (Sum.inr (Sum.inr (Sum.inl i))) x = -∑ j, A i j * x (e j) := by
      simp only [rowEval, hM, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      exact congrArg Neg.neg
        (Fintype.sum_equiv e _ _ fun j => by rw [Equiv.symm_apply_apply]).symm
    have hobj : rowEval M (Sum.inr (Sum.inr (Sum.inr ()))) x = ∑ j, c j * x (e j) := by
      simp only [rowEval, hM, Sum.elim_inr]
      exact (Fintype.sum_equiv e _ _ fun j => by rw [Equiv.symm_apply_apply]).symm
    refine h ⟨fun j => x (e j), ⟨fun j => ?_, ?_⟩, ?_⟩
    · have := hx (Sum.inl j)
      rw [hcoord] at this
      simpa [hb] using this
    · funext i
      have h₁ := hx (Sum.inr (Sum.inl i))
      have h₂ := hx (Sum.inr (Sum.inr (Sum.inl i)))
      rw [hrow] at h₁
      rw [hrow'] at h₂
      simp only [hb, Sum.elim_inl, Sum.elim_inr] at h₁ h₂
      have : (A *ᵥ fun j => x (e j)) i = ∑ j, A i j * x (e j) := by
        simp [Matrix.mulVec, dotProduct]
      rw [this]
      linarith
    · have := hx (Sum.inr (Sum.inr (Sum.inr ())))
      rw [hobj] at this
      simpa [hb] using this
  -- Its Farkas certificate is the scaled dual pair.
  obtain ⟨u, hnn, hzero, hpos⟩ := (theorem_of_alternative M bvec).mp hinf
  have hd : (default : Unit) = () := rfl
  refine ⟨fun i => u (Sum.inr (Sum.inr (Sum.inl i))) - u (Sum.inr (Sum.inl i)),
    u (Sum.inr (Sum.inr (Sum.inr ()))), hnn _, fun j => ?_, ?_⟩
  · have hk := hzero (e j)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hk
    simp only [hM, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply,
      Finset.univ_unique, Finset.sum_singleton, hd] at hk
    have hind : ∑ j' : Col, u (Sum.inl j') * (if j = j' then (1 : 𝕜) else 0) = u (Sum.inl j) := by
      simp
    rw [hind] at hk
    have hsub : ∑ i, (u (Sum.inr (Sum.inr (Sum.inl i))) - u (Sum.inr (Sum.inl i))) * A i j
        = (∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * A i j)
          - ∑ i, u (Sum.inr (Sum.inl i)) * A i j := by
      simp [sub_mul, Finset.sum_sub_distrib]
    rw [show ∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * -A i j
        = -∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * A i j by simp [mul_neg]] at hk
    rw [hsub]
    have hu := hnn (Sum.inl j)
    linarith
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hpos
    simp only [hb, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero,
      zero_add, Finset.univ_unique, Finset.sum_singleton, hd] at hpos
    have hsub : ∑ i, (u (Sum.inr (Sum.inr (Sum.inl i))) - u (Sum.inr (Sum.inl i))) * rhs i
        = (∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * rhs i)
          - ∑ i, u (Sum.inr (Sum.inl i)) * rhs i := by
      simp [sub_mul, Finset.sum_sub_distrib]
    rw [show ∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * -rhs i
        = -∑ i, u (Sum.inr (Sum.inr (Sum.inl i))) * rhs i by simp [mul_neg]] at hpos
    rw [hsub]
    linarith

/-! ### Strong duality -/

/-- **Strong duality** in threshold form: a feasible point with objective at least `t` exists
exactly when the primal is feasible and every dual feasible vector has objective at least `t`.

The primal-feasibility conjunct is necessary: when both programs are infeasible the dual bound
holds vacuously at every level, while no primal point exists at all. -/
theorem exists_objective_ge_iff_feasible_and_forall_isDualFeasible
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) (t : 𝕜) :
    (∃ z, z ∈ standardFeasibleSet A rhs ∧ t ≤ ∑ j, c j * z j) ↔
      (∃ z, z ∈ standardFeasibleSet A rhs) ∧
        ∀ y, IsDualFeasible A c y → t ≤ ∑ i, y i * rhs i := by
  constructor
  · rintro ⟨z, hz, ht⟩
    exact ⟨⟨z, hz⟩, fun y hy => ht.trans (objective_le_of_isDualFeasible hz hy)⟩
  · rintro ⟨⟨z, hz⟩, hdual⟩
    by_contra hno
    obtain ⟨y, lam, hlam, hcol, hlt⟩ := exists_scaledDual_of_not_exists_objective_ge A rhs c t hno
    rcases hlam.lt_or_eq with hpos | hzero
    · -- A genuine dual point after rescaling by `lam`.
      have hinv : 0 < lam⁻¹ := inv_pos.mpr hpos
      have hfeas : IsDualFeasible A c fun i => lam⁻¹ * y i := by
        intro j
        have hsum : ∑ i, (lam⁻¹ * y i) * A i j = lam⁻¹ * ∑ i, y i * A i j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum]
        calc c j = lam⁻¹ * (lam * c j) := by
              rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
          _ ≤ lam⁻¹ * ∑ i, y i * A i j := mul_le_mul_of_nonneg_left (hcol j) hinv.le
      have hval : ∑ i, (lam⁻¹ * y i) * rhs i = lam⁻¹ * ∑ i, y i * rhs i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hge := hdual _ hfeas
      rw [hval] at hge
      have hstrict : lam⁻¹ * ∑ i, y i * rhs i < lam⁻¹ * (lam * t) :=
        mul_lt_mul_of_pos_left hlt hinv
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hstrict
      linarith
    · -- A Farkas certificate of primal infeasibility, contradicting the feasible `z`.
      have hcol' (j : Col) : 0 ≤ ∑ i, y i * A i j := by
        have := hcol j
        rw [← hzero] at this
        linarith
      have := sum_dual_eq_of_mem_standardFeasibleSet hz y
      have hnonneg : 0 ≤ ∑ j, (∑ i, y i * A i j) * z j :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hcol' j) (hz.1 j)
      rw [← hzero] at hlt
      simp only [zero_mul] at hlt
      linarith

/-- **Strong duality** for a feasible primal: a feasible point with objective at least `t`
exists exactly when every dual feasible vector has objective at least `t`. -/
theorem exists_objective_ge_iff_forall_isDualFeasible
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) (t : 𝕜)
    (hfeas : ∃ z, z ∈ standardFeasibleSet A rhs) :
    (∃ z, z ∈ standardFeasibleSet A rhs ∧ t ≤ ∑ j, c j * z j) ↔
      ∀ y, IsDualFeasible A c y → t ≤ ∑ i, y i * rhs i := by
  rw [exists_objective_ge_iff_feasible_and_forall_isDualFeasible]
  exact and_iff_right hfeas

/-! ### Dual attainment

When the primal optimum is attained, so is the dual optimum, and the two agree. The proof is a
second application of the theorem of the alternative, this time to the dual system
`Aᵀ *ᵥ y ≥ c`, `-⟪rhs, y⟫ ≥ -v` in the free variable `y`: its Farkas certificate is a
nonnegative `w` on the columns with `A *ᵥ w = mu • rhs` and `⟪c, w⟫ > mu * v`, which is either
a better feasible point (`mu > 0`) or an improving recession direction (`mu = 0`). -/

/-- **Dual attainment**: if `z` is feasible and maximizes the primal objective, then some dual
feasible `y` attains the same value.

Together with `Maths.LinearProgramming.objective_le_of_isDualFeasible` this pins the
dual objective at `y` to the primal optimum exactly. -/
theorem exists_isDualFeasible_objective_le_of_forall_le
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) {z : Col → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs)
    (hopt : ∀ w, w ∈ standardFeasibleSet A rhs → ∑ j, c j * w j ≤ ∑ j, c j * z j) :
    ∃ y, IsDualFeasible A c y ∧ ∑ i, y i * rhs i ≤ ∑ j, c j * z j := by
  classical
  set v : 𝕜 := ∑ j, c j * z j with hv
  set e : Row ≃ Fin (Fintype.card Row) := Fintype.equivFin Row with he
  set M : (Col ⊕ Unit) → Fin (Fintype.card Row) → 𝕜 :=
    Sum.elim (fun j k => A (e.symm k) j) (fun _ k => -rhs (e.symm k)) with hM
  set bvec : (Col ⊕ Unit) → 𝕜 := Sum.elim c (fun _ => -v) with hb
  by_cases hfeasible : IsFeasible M bvec
  · obtain ⟨x, hx⟩ := hfeasible
    refine ⟨fun i => x (e i), fun j => ?_, ?_⟩
    · have hxj := hx (Sum.inl j)
      simp only [hb, hM, Sum.elim_inl, rowEval] at hxj
      have hEq : ∑ i, x (e i) * A i j = ∑ k, A (e.symm k) j * x k :=
        Fintype.sum_equiv e _ _ fun i => by rw [Equiv.symm_apply_apply]; ring
      rw [hEq]
      exact hxj
    · have hxu := hx (Sum.inr ())
      simp only [hb, hM, Sum.elim_inr, rowEval] at hxu
      have hEq : ∑ i, x (e i) * rhs i = -∑ k, -rhs (e.symm k) * x k := by
        rw [← Finset.sum_neg_distrib]
        exact Fintype.sum_equiv e _ _ fun i => by rw [Equiv.symm_apply_apply]; ring
      rw [hEq]
      linarith
  · -- An infeasible dual system would produce a primal point beating the optimum.
    exfalso
    obtain ⟨w, hw_nn, hw_zero, hw_pos⟩ := (theorem_of_alternative M bvec).mp hfeasible
    set mu : 𝕜 := w (Sum.inr ()) with hmu
    have hmu_nn : 0 ≤ mu := hw_nn _
    have hrow (i : Row) : (A *ᵥ fun j => w (Sum.inl j)) i = mu * rhs i := by
      have hk := hw_zero (e i)
      rw [Fintype.sum_sum_type] at hk
      simp only [hM, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply, Finset.univ_unique,
        Finset.sum_singleton, show (default : Unit) = () from rfl] at hk
      have hcol : ∑ j, w (Sum.inl j) * A i j = mu * rhs i := by
        rw [hmu]
        linarith [hk]
      rw [← hcol]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hobj : mu * v < ∑ j, c j * w (Sum.inl j) := by
      rw [Fintype.sum_sum_type] at hw_pos
      simp only [hb, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton, show (default : Unit) = () from rfl] at hw_pos
      have hcomm : ∑ j, w (Sum.inl j) * c j = ∑ j, c j * w (Sum.inl j) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hcomm] at hw_pos
      rw [hmu]
      linarith
    rcases hmu_nn.lt_or_eq with hpos | hzero
    · -- Rescaling by `mu` gives a feasible point with a strictly larger objective.
      have hinv : 0 < mu⁻¹ := inv_pos.mpr hpos
      have hfeas : (fun j => mu⁻¹ * w (Sum.inl j)) ∈ standardFeasibleSet A rhs := by
        refine ⟨fun j => mul_nonneg hinv.le (hw_nn _), ?_⟩
        funext i
        have hsmul : (fun j => mu⁻¹ * w (Sum.inl j)) = mu⁻¹ • fun j => w (Sum.inl j) := rfl
        rw [hsmul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hrow i, ← mul_assoc,
          inv_mul_cancel₀ hpos.ne', one_mul]
      have hval : ∑ j, c j * (mu⁻¹ * w (Sum.inl j)) = mu⁻¹ * ∑ j, c j * w (Sum.inl j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hle := hopt _ hfeas
      rw [hval] at hle
      have hstrict : mu⁻¹ * (mu * v) < mu⁻¹ * ∑ j, c j * w (Sum.inl j) :=
        mul_lt_mul_of_pos_left hobj hinv
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hstrict
      linarith
    · -- A recession direction: `z + w` is feasible and strictly better.
      have hzero' : mu = 0 := hzero.symm
      have hfeas : (fun j => z j + w (Sum.inl j)) ∈ standardFeasibleSet A rhs := by
        refine ⟨fun j => add_nonneg (hz.1 j) (hw_nn _), ?_⟩
        funext i
        have hadd : (fun j => z j + w (Sum.inl j)) = z + fun j => w (Sum.inl j) := rfl
        rw [hadd, Matrix.mulVec_add, Pi.add_apply, hrow i, congrFun hz.2 i, hzero',
          zero_mul, add_zero]
      have hval : ∑ j, c j * (z j + w (Sum.inl j)) = v + ∑ j, c j * w (Sum.inl j) := by
        rw [hv, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hle := hopt _ hfeas
      rw [hval] at hle
      rw [hzero', zero_mul] at hobj
      linarith

/-! ### Complementary slackness -/

/-- The complementary slackness relation: at every column, either the primal variable vanishes
or the dual constraint is tight. -/
def ComplementarySlackness {Row Col : Type*} [Fintype Row]
    (A : Matrix Row Col 𝕜) (c : Col → 𝕜) (z : Col → 𝕜) (y : Row → 𝕜) : Prop :=
  ∀ j, z j * ((∑ i, y i * A i j) - c j) = 0

/-- Complementary slackness as a support condition: the dual constraint is tight at every
column where the primal variable is nonzero. -/
theorem complementarySlackness_iff_forall_ne_zero
    {Row Col : Type*} [Fintype Row]
    (A : Matrix Row Col 𝕜) (c : Col → 𝕜) (z : Col → 𝕜) (y : Row → 𝕜) :
    ComplementarySlackness A c z y ↔ ∀ j, z j ≠ 0 → ∑ i, y i * A i j = c j := by
  refine forall_congr' fun j => ?_
  constructor
  · intro h hz
    have := (mul_eq_zero.mp h).resolve_left hz
    linarith [this]
  · intro h
    by_cases hz : z j = 0
    · simp [hz]
    · rw [h hz, sub_self, mul_zero]

/-- **Complementary slackness**: for a feasible primal point and a dual feasible vector, the
two objectives agree exactly when complementary slackness holds.

By weak duality the difference of the two objectives is the pairing of the nonnegative primal
vector with the nonnegative dual slacks, so it vanishes exactly termwise. -/
theorem complementarySlackness_iff_objective_eq
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {c : Col → 𝕜} {z : Col → 𝕜} {y : Row → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (hy : IsDualFeasible A c y) :
    ComplementarySlackness A c z y ↔ ∑ j, c j * z j = ∑ i, y i * rhs i := by
  have hgap : (∑ i, y i * rhs i) - ∑ j, c j * z j
      = ∑ j, z j * ((∑ i, y i * A i j) - c j) := by
    rw [sum_dual_eq_of_mem_standardFeasibleSet hz y, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro hcs
    have : (∑ i, y i * rhs i) - ∑ j, c j * z j = 0 := by
      rw [hgap]
      exact Finset.sum_eq_zero fun j _ => hcs j
    linarith
  · intro heq
    have hsum : ∑ j, z j * ((∑ i, y i * A i j) - c j) = 0 := by
      rw [← hgap, heq, sub_self]
    have hterm : ∀ k ∈ (Finset.univ : Finset Col),
        0 ≤ z k * ((∑ i, y i * A i k) - c k) :=
      fun k _ => mul_nonneg (hz.1 k) (by linarith [hy k])
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum j (Finset.mem_univ j)

/-- Complementary slackness is a certificate of primal optimality: a feasible point that is
complementary to some dual feasible vector maximizes the objective. -/
theorem forall_le_of_complementarySlackness
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {c : Col → 𝕜} {z : Col → 𝕜} {y : Row → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (hy : IsDualFeasible A c y)
    (hcs : ComplementarySlackness A c z y) :
    ∀ w, w ∈ standardFeasibleSet A rhs → ∑ j, c j * w j ≤ ∑ j, c j * z j := by
  intro w hw
  rw [(complementarySlackness_iff_objective_eq hz hy).mp hcs]
  exact objective_le_of_isDualFeasible hw hy

/-- Conversely, an attained primal optimum is complementary to some dual feasible vector,
namely the dual optimum attained by
`Maths.LinearProgramming.exists_isDualFeasible_objective_le_of_forall_le`. -/
theorem exists_isDualFeasible_complementarySlackness_of_forall_le
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) {z : Col → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs)
    (hopt : ∀ w, w ∈ standardFeasibleSet A rhs → ∑ j, c j * w j ≤ ∑ j, c j * z j) :
    ∃ y, IsDualFeasible A c y ∧ ComplementarySlackness A c z y := by
  obtain ⟨y, hy, hle⟩ :=
    exists_isDualFeasible_objective_le_of_forall_le A rhs c hz hopt
  refine ⟨y, hy, (complementarySlackness_iff_objective_eq hz hy).mpr ?_⟩
  exact le_antisymm (objective_le_of_isDualFeasible hz hy) hle

/-! ### Optimality in the sense of `IsStandardOptimal`

The results above repackage into
`Maths.LinearProgramming.IsStandardOptimal`, and so combine with the extreme-point
theory of `Maths.LinearProgramming.StandardForm`: an optimum attained at an extreme
point is still certified by the same dual vector. -/

/-- Complementary slackness with a dual feasible vector certifies optimality of a feasible
point in the sense of `Maths.LinearProgramming.IsStandardOptimal`. -/
theorem isStandardOptimal_of_complementarySlackness
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Matrix Row Col 𝕜} {rhs : Row → 𝕜} {c : Col → 𝕜} {z : Col → 𝕜} {y : Row → 𝕜}
    (hz : z ∈ standardFeasibleSet A rhs) (hy : IsDualFeasible A c y)
    (hcs : ComplementarySlackness A c z y) :
    IsStandardOptimal A rhs c z :=
  ⟨hz, fun w hw => forall_le_of_complementarySlackness hz hy hcs w hw⟩

/-- Every standard-form optimum is complementary to some dual feasible vector, which therefore
attains the dual optimum. -/
theorem exists_isDualFeasible_complementarySlackness_of_standardOptimal
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Matrix Row Col 𝕜) (rhs : Row → 𝕜) (c : Col → 𝕜) {z : Col → 𝕜}
    (hz : IsStandardOptimal A rhs c z) :
    ∃ y, IsDualFeasible A c y ∧ ComplementarySlackness A c z y :=
  exists_isDualFeasible_complementarySlackness_of_forall_le A rhs c hz.1 hz.2

end LinearProgramming
end Maths
