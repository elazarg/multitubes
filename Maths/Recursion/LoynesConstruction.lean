/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Recursion.TransferSummary
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The pathwise Loynes construction for the reflected recursion

Lindley's representation `Maths.TransferSummary.reflectedIter_eq_sup'` writes the
reflected state at time `n` as a supremum over restart times `m ≤ n` of terms that depend on
both `m` and `n`. Reading the input *backwards from the observation time* removes the second
dependence: a restart `j` stages into the past contributes exactly `-pastService a g j`, a
quantity that does not mention the horizon at all. Consequently the finite-horizon values are
suprema of a fixed sequence over a growing index set, hence nondecreasing in the horizon
(`monotone_loynes`), and they converge as soon as they are bounded above
(`tendsto_loynes_ciSup`). Geometric retention together with a lower bound on the input is such
a bound, with the explicit value `C / (1 - ρ)` (`loynes_le`).

## Implementation notes

This is the deterministic skeleton of Loynes' construction and **not Loynes' theorem**. Loynes
studies the reflected recursion driven by a *stationary ergodic* input and concludes that, under
negative drift, the monotone limit is almost surely finite and is the unique stationary solution
of the recursion. Both halves of that conclusion -- almost-sure finiteness from negative drift,
and uniqueness of the stationary regime -- are probabilistic, resting on the ergodic theorem and
on the invariance of the input's law under the shift. Nothing below asserts either. What is
proved here is the pathwise fact that Loynes' argument rests on: for one fixed input sequence,
the finite-horizon values increase, and an explicit deterministic hypothesis makes them bounded.

The input is indexed *by age*: `a p` and `g p` are the retention and service of the stage `p`
steps before the observation time, so that the same sequence serves every horizon. The bridge
back to the forward-indexed recursion of the reflected orbit is `reversed`, and
`reflectedIter_reversed` identifies the two.

## Main definitions

* `Maths.TransferSummary.pastTransport` and
  `Maths.TransferSummary.pastService` -- the retention and the retention-weighted
  service accumulated over the last `j` stages, indexed by age.
* `Maths.TransferSummary.loynes` -- the finite-horizon Loynes value.
* `Maths.TransferSummary.reversed` -- an age-indexed input read forwards over a
  fixed horizon.

## Main results

* `Maths.TransferSummary.reflectedIter_reversed` -- the finite-horizon Loynes value
  is the reflected orbit of the reversed input started from `0`.
* `Maths.TransferSummary.monotone_loynes` and
  `Maths.TransferSummary.loynes_nonneg`.
* `Maths.TransferSummary.loynes_le` -- geometric retention and a lower bound on the
  service bound the whole construction by `C / (1 - ρ)`.
* `Maths.TransferSummary.tendsto_loynes_ciSup` -- monotone convergence of the
  bounded finite-horizon values.

## References

* R. M. Loynes, *The stability of a queue with non-independent inter-arrival and service
  times*, Math. Proc. Cambridge Philos. Soc. 58 (1962), 497-520.
* D. V. Lindley, *The theory of queues with a single server*, Math. Proc. Cambridge Philos.
  Soc. 48 (1952), 277-289.

## Tags

Lindley recursion, Loynes construction, reflection, monotone convergence
-/

@[expose] public section

noncomputable section

namespace Maths.TransferSummary

variable (a g : ℕ → ℝ)

/-! ## Age-indexed input -/

/-- The retention applied to a stage that occurred `j` steps in the past: the product of the
retentions of all the stages that have happened since. -/
def pastTransport (j : ℕ) : ℝ := ∏ p ∈ Finset.range j, a p

/-- The retention-weighted service accumulated over the last `j` stages, each stage's service
discounted by the retention that has acted on it since. -/
def pastService (j : ℕ) : ℝ := ∑ p ∈ Finset.range j, pastTransport a p * g p

/-- No stages have passed: nothing is retained. -/
@[simp] theorem pastTransport_zero : pastTransport a 0 = 1 := by simp [pastTransport]

/-- No stages have passed: nothing is served. -/
@[simp] theorem pastService_zero : pastService a g 0 = 0 := by simp [pastService]

/-- Reaching one stage further into the past multiplies in that stage's retention. -/
theorem pastTransport_succ (j : ℕ) :
    pastTransport a (j + 1) = pastTransport a j * a j := by
  rw [pastTransport, pastTransport, Finset.prod_range_succ]

/-- Reaching one stage further into the past adds that stage's discounted service. -/
theorem pastService_succ (j : ℕ) :
    pastService a g (j + 1) = pastService a g j + pastTransport a j * g j := by
  rw [pastService, pastService, Finset.sum_range_succ]

/-- Nonnegative retentions accumulate to a nonnegative transport. -/
theorem pastTransport_nonneg (ha : ∀ k, 0 ≤ a k) (j : ℕ) : 0 ≤ pastTransport a j :=
  Finset.prod_nonneg fun k _ => ha k

/-- An age-indexed input read forwards over the horizon `n`: stage `k` of the forward input is
the stage `n - (k + 1)` steps into the past. -/
def reversed (n : ℕ) (u : ℕ → ℝ) : ℕ → ℝ := fun k => u (n - (k + 1))

/-- The forward transport of a reversed input over the window `[k + 1, n)` is the age-indexed
transport over the last `n - (k + 1)` stages.  No relation between `k` and `n` is needed: past
the horizon both index sets are empty and the identity reads `1 = 1`. -/
theorem transport_reversed (k n : ℕ) :
    transport (reversed n a) (k + 1) n = pastTransport a (n - (k + 1)) := by
  refine Finset.prod_nbij' (fun i => n - (i + 1)) (fun p => n - (p + 1)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_range]
    omega
  · intro p hp
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Ico]
    omega
  · intro i hi
    rw [Finset.mem_Ico] at hi
    omega
  · intro p hp
    rw [Finset.mem_range] at hp
    omega
  · intro i _
    rfl

/-- The forward service of a reversed input over the window `[m, n)` is the age-indexed service
over the last `n - m` stages: it depends on the window only through its length.  As for the
transport, no relation between `m` and `n` is needed. -/
theorem service_reversed (m n : ℕ) :
    service (reversed n a) (reversed n g) m n = pastService a g (n - m) := by
  refine Finset.sum_nbij' (fun k => n - (k + 1)) (fun p => n - (p + 1)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  · intro p hp
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Ico]
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  · intro p hp
    rw [Finset.mem_range] at hp
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [transport_reversed a k n]
    rfl

/-! ## The finite-horizon Loynes values -/

/-- The **finite-horizon Loynes value** at horizon `n`: the largest, over restart times `j ≤ n`
stages into the past, of the negated retention-weighted service accumulated since. Because the
input is indexed by age, the terms of the supremum do not depend on `n`. -/
def loynes (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun j => -pastService a g j

/-- Each age-indexed restart contributes to the Loynes value at every large enough horizon. -/
theorem neg_pastService_le_loynes {j n : ℕ} (hjn : j ≤ n) :
    -pastService a g j ≤ loynes a g n :=
  Finset.le_sup' (fun j => -pastService a g j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjn))

/-- The Loynes value is the least bound on all its restart terms. -/
theorem loynes_le_iff {n : ℕ} {c : ℝ} :
    loynes a g n ≤ c ↔ ∀ j ≤ n, -pastService a g j ≤ c := by
  constructor
  · exact fun h j hjn => le_trans (neg_pastService_le_loynes a g hjn) h
  · exact fun h =>
      Finset.sup'_le _ (fun j => -pastService a g j) fun j hj =>
        h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- At horizon `0` the only restart is the present one, which contributes nothing. -/
@[simp] theorem loynes_zero : loynes a g 0 = 0 := by simp [loynes]

/-- The Loynes values are nonnegative: restarting at the present time contributes `0`. -/
theorem loynes_nonneg (n : ℕ) : 0 ≤ loynes a g n := by
  have h := neg_pastService_le_loynes a g (Nat.zero_le n)
  rwa [pastService_zero, neg_zero] at h

/-- **The finite-horizon Loynes values are nondecreasing.** This is the whole point of reading
the input by age: the supremum ranges over a growing index set of terms that do not move. -/
theorem monotone_loynes : Monotone (loynes a g) := fun _ _ hmn =>
  Finset.sup'_mono (fun j => -pastService a g j)
    (Finset.range_mono (Nat.succ_le_succ hmn)) Finset.nonempty_range_add_one

/-- **The finite-horizon Loynes value is a reflected orbit.** At horizon `n` it is the state
reached after `n` stages of the Lindley recursion driven by the input read forwards over that
horizon, started from `0`. Only nonnegative retention is used. -/
theorem reflectedIter_reversed (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    reflectedIter (reversed n a) (reversed n g) 0 n = loynes a g n := by
  have ha' : ∀ k, 0 ≤ reversed n a k := fun k => ha _
  rw [reflectedIter_eq_sup' _ _ ha' 0 n]
  refine le_antisymm
    (Finset.sup'_le _ (fun m => lindleyTerm (reversed n a) (reversed n g) 0 m n) fun m hm => ?_)
    (Finset.sup'_le _ (fun j => -pastService a g j) fun j hj => ?_)
  · rw [lindleyTerm_zero_state, service_reversed a g m n]
    exact neg_pastService_le_loynes a g (Nat.sub_le n m)
  · have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsub : n - (n - j) = j := by omega
    have hterm : lindleyTerm (reversed n a) (reversed n g) 0 (n - j) n = -pastService a g j := by
      rw [lindleyTerm_zero_state, service_reversed a g (n - j) n, hsub]
    rw [← hterm]
    exact Finset.le_sup' (fun m => lindleyTerm (reversed n a) (reversed n g) 0 m n)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n j)))

/-! ## Boundedness and convergence -/

variable {a}

/-- Retentions bounded by `ρ` make the accumulated transport geometric. -/
theorem pastTransport_le_pow {ρ : ℝ} (ha : ∀ k, 0 ≤ a k) (hρ : ∀ k, a k ≤ ρ) (j : ℕ) :
    pastTransport a j ≤ ρ ^ j := by
  have h := Finset.prod_le_prod (s := Finset.range j) (f := a) (g := fun _ => ρ)
    (fun k _ => ha k) fun k _ => hρ k
  simpa [pastTransport] using h

/-- Geometric retention keeps the total accumulated transport below `1 / (1 - ρ)`, uniformly in
the number of stages. -/
theorem sum_pastTransport_le {ρ : ℝ} (ha : ∀ k, 0 ≤ a k) (hρ : ∀ k, a k ≤ ρ) (hρ1 : ρ < 1)
    (j : ℕ) : ∑ p ∈ Finset.range j, pastTransport a p ≤ 1 / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := le_trans (ha 0) (hρ 0)
  have hsub : 0 < 1 - ρ := by linarith
  have hgeom : ∑ p ∈ Finset.range j, ρ ^ p = (1 - ρ ^ j) / (1 - ρ) := by
    rw [geom_sum_eq (by linarith) j, div_eq_div_iff (by linarith) (by linarith)]
    ring
  refine le_trans (Finset.sum_le_sum fun p _ => pastTransport_le_pow ha hρ p) ?_
  rw [hgeom, div_le_div_iff_of_pos_right hsub]
  have : 0 ≤ ρ ^ j := pow_nonneg hρ0 j
  linarith

/-- **Geometric retention and bounded input bound the whole construction.** If every retention
lies in `[0, ρ]` with `ρ < 1` and no stage serves less than `-C`, then every finite-horizon
Loynes value is at most `C / (1 - ρ)`. This is the deterministic stand-in for Loynes' negative
drift condition. -/
theorem loynes_le {ρ C : ℝ} (ha : ∀ k, 0 ≤ a k) (hρ : ∀ k, a k ≤ ρ) (hρ1 : ρ < 1)
    (hC : ∀ k, -C ≤ g k) (hC0 : 0 ≤ C) (n : ℕ) : loynes a g n ≤ C / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := le_trans (ha 0) (hρ 0)
  have hsub : 0 < 1 - ρ := by linarith
  refine (loynes_le_iff a g).mpr fun j _ => ?_
  have hlow : -(C * ∑ p ∈ Finset.range j, pastTransport a p) ≤ pastService a g j := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, pastService]
    refine Finset.sum_le_sum fun p _ => ?_
    have hT : 0 ≤ pastTransport a p := pastTransport_nonneg _ ha p
    nlinarith [mul_le_mul_of_nonneg_left (hC p) hT]
  have hbound : C * ∑ p ∈ Finset.range j, pastTransport a p ≤ C * (1 / (1 - ρ)) :=
    mul_le_mul_of_nonneg_left (sum_pastTransport_le ha hρ hρ1 j) hC0
  rw [mul_one_div] at hbound
  linarith

/-- The finite-horizon Loynes values of a geometrically retained, bounded input are bounded
above. -/
theorem bddAbove_range_loynes {ρ C : ℝ} (ha : ∀ k, 0 ≤ a k) (hρ : ∀ k, a k ≤ ρ) (hρ1 : ρ < 1)
    (hC : ∀ k, -C ≤ g k) (hC0 : 0 ≤ C) : BddAbove (Set.range (loynes a g)) := by
  refine ⟨C / (1 - ρ), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact loynes_le g ha hρ hρ1 hC hC0 n

/-- **Monotone convergence of the finite-horizon Loynes values.** Bounded above, the
nondecreasing finite-horizon values converge to their supremum. This is the deterministic
skeleton of Loynes' construction: the limit exists pathwise, for one fixed input sequence, with
no stationarity and no probability. It is not Loynes' theorem, which identifies the limit as the
unique stationary solution of the recursion under a stationary ergodic input. -/
theorem tendsto_loynes_ciSup (hbdd : BddAbove (Set.range (loynes a g))) :
    Filter.Tendsto (loynes a g) Filter.atTop (nhds (⨆ n, loynes a g n)) :=
  tendsto_atTop_ciSup (monotone_loynes a g) hbdd

end Maths.TransferSummary
