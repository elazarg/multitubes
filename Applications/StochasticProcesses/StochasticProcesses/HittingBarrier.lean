/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import StochasticProcesses.KernelTransport
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite-horizon hitting probabilities and barrier certificates

For a discrete-time probability kernel, `hitBy` recursively computes the probability of
visiting a target at the initial state or during the next `n` transitions. Its supremum over
finite horizons is `eventuallyHit`. This is an order-theoretic definition; no claim identifying
it with a measure on infinite trajectories is needed.

A nonnegative superharmonic barrier that is at least one on the target bounds every finite-horizon
hitting probability. Consequently it also bounds their supremum. A three-state trial illustrates
that the certificate can give the sharp, nontrivial bound `1 / 2`.

## Main definitions

* `StochasticProcesses.hitBy` - probability of hitting a target within a finite horizon.
* `StochasticProcesses.eventuallyHit` - supremum of all finite-horizon hitting probabilities.
* `StochasticProcesses.stoppedKernel` - a kernel made absorbing on the target.
* `StochasticProcesses.targetIndicator` - the extended-real indicator of the target.
* `StochasticProcesses.TrialState` - states of a one-step success-or-failure trial.
* `StochasticProcesses.trialKernel` - a fair one-step trial with absorbing outcomes.
* `StochasticProcesses.trialBarrier` - the exact hitting barrier for trial success.

## Main results

* `StochasticProcesses.hitBy_mono_horizon` - hitting probabilities increase with the horizon.
* `StochasticProcesses.hitBy_eq_expect_stopped` - finite-horizon hitting equals the target
  endpoint probability under the stopped kernel.
* `StochasticProcesses.hitBy_le_one` and `StochasticProcesses.eventuallyHit_le_one` - hitting
  values are bounded by one.
* `StochasticProcesses.hitBy_le_barrier` - a superharmonic barrier bounds finite-horizon hitting.
* `StochasticProcesses.eventuallyHit_le_barrier` - the barrier bounds the horizon supremum.
* `StochasticProcesses.eventuallyHit_trial_start` - the fair trial hits success with value `1 / 2`.

## Tags

probability, Markov kernel, hitting probability, superharmonic, barrier certificate
-/

noncomputable section

@[expose] public section

namespace StochasticProcesses

open scoped ENNReal

variable {S : Type*}

/-- The probability of visiting `target` at time zero or during the next `n` transitions. -/
def hitBy (k : S → PMF S) (target : S → Prop) [DecidablePred target] : ℕ → S → ℝ≥0∞
  | 0, state => if target state then 1 else 0
  | n + 1, state => if target state then 1 else expect (k state) (hitBy k target n)

/-- The supremum of the probabilities of hitting `target` within a finite horizon. -/
def eventuallyHit (k : S → PMF S) (target : S → Prop) [DecidablePred target] (state : S) :
    ℝ≥0∞ :=
  ⨆ n, hitBy k target n state

/-- The target indicator, valued in nonnegative extended reals. -/
def targetIndicator (target : S → Prop) [DecidablePred target] (state : S) : ℝ≥0∞ :=
  if target state then 1 else 0

/-- The kernel that leaves target states fixed and otherwise follows `k`. -/
def stoppedKernel (k : S → PMF S) (target : S → Prop) [DecidablePred target]
    (state : S) : PMF S :=
  if target state then PMF.pure state else k state

private theorem expect_one (p : PMF S) : expect p (fun _ => 1) = 1 := by
  unfold expect
  simp [p.tsum_coe]

private theorem iterateKernel_stopped_of_mem (k : S → PMF S) (target : S → Prop)
    [DecidablePred target] {state : S} (hstate : target state) (n : ℕ) :
    iterateKernel (stoppedKernel k target) n state = PMF.pure state := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateKernel, stoppedKernel, hstate, ih]

@[simp]
theorem hitBy_of_mem (k : S → PMF S) (target : S → Prop) [DecidablePred target]
    {state : S} (hstate : target state) (n : ℕ) : hitBy k target n state = 1 := by
  cases n <;> simp [hitBy, hstate]

@[simp]
theorem hitBy_zero_of_not_mem (k : S → PMF S) (target : S → Prop)
    [DecidablePred target] {state : S} (hstate : ¬ target state) :
    hitBy k target 0 state = 0 := by
  simp [hitBy, hstate]

/-- Increasing the finite horizon cannot decrease the hitting probability. -/
theorem hitBy_mono_horizon (k : S → PMF S) (target : S → Prop) [DecidablePred target] :
    ∀ n state, hitBy k target n state ≤ hitBy k target (n + 1) state := by
  intro n
  induction n with
  | zero =>
      intro state
      by_cases hstate : target state <;> simp [hitBy, hstate]
  | succ n ih =>
      intro state
      by_cases hstate : target state
      · simp [hitBy, hstate]
      · simp only [hitBy, hstate, ite_false]
        exact expect_mono (k state) ih

/-- Hitting by horizon `n` is exactly the endpoint target probability after `n` steps of the
kernel stopped on the target. This gives `hitBy` finite-path probability semantics. -/
theorem hitBy_eq_expect_stopped (k : S → PMF S) (target : S → Prop)
    [DecidablePred target] : ∀ n state,
    hitBy k target n state =
      expect (iterateKernel (stoppedKernel k target) n state) (targetIndicator target) := by
  intro n
  induction n with
  | zero =>
      intro state
      simp [hitBy, iterateKernel, targetIndicator]
  | succ n ih =>
      intro state
      rw [iterateKernel_succ, expect_bind]
      by_cases hstate : target state
      · rw [hitBy_of_mem k target hstate, stoppedKernel]
        simp only [hstate, ite_true, expect_pure]
        rw [iterateKernel_stopped_of_mem k target hstate]
        simp [targetIndicator, hstate]
      · simp only [hitBy, hstate, ite_false, stoppedKernel]
        exact congrArg (expect (k state)) (funext (ih))

/-- Every finite-horizon hitting probability is at most one. -/
theorem hitBy_le_one (k : S → PMF S) (target : S → Prop) [DecidablePred target]
    (n : ℕ) (state : S) : hitBy k target n state ≤ 1 := by
  rw [hitBy_eq_expect_stopped]
  calc
    expect (iterateKernel (stoppedKernel k target) n state) (targetIndicator target) ≤
        expect (iterateKernel (stoppedKernel k target) n state) (fun _ => 1) := by
      apply expect_mono
      intro finalState
      by_cases hfinal : target finalState <;> simp [targetIndicator, hfinal]
    _ = 1 := expect_one _

/-- The supremum of finite-horizon hitting probabilities is at most one. -/
theorem eventuallyHit_le_one (k : S → PMF S) (target : S → Prop)
    [DecidablePred target] (state : S) : eventuallyHit k target state ≤ 1 := by
  apply iSup_le
  intro n
  exact hitBy_le_one k target n state

/-- A superharmonic function that dominates one on the target bounds finite-horizon hitting. -/
theorem hitBy_le_barrier (k : S → PMF S) (target : S → Prop) [DecidablePred target]
    (barrier : S → ℝ≥0∞) (hone : ∀ state, target state → 1 ≤ barrier state)
    (hsuper : ∀ state, ¬ target state → expect (k state) barrier ≤ barrier state) :
    ∀ n state, hitBy k target n state ≤ barrier state := by
  intro n
  induction n with
  | zero =>
      intro state
      by_cases hstate : target state
      · simpa [hitBy, hstate] using hone state hstate
      · simp [hitBy, hstate]
  | succ n ih =>
      intro state
      by_cases hstate : target state
      · simpa [hitBy, hstate] using hone state hstate
      · simp only [hitBy, hstate, ite_false]
        exact (expect_mono (k state) ih).trans (hsuper state hstate)

/-- A superharmonic barrier bounds the supremum of all finite-horizon hitting probabilities. -/
theorem eventuallyHit_le_barrier (k : S → PMF S) (target : S → Prop)
    [DecidablePred target] (barrier : S → ℝ≥0∞)
    (hone : ∀ state, target state → 1 ≤ barrier state)
    (hsuper : ∀ state, ¬ target state → expect (k state) barrier ≤ barrier state)
    (state : S) : eventuallyHit k target state ≤ barrier state := by
  apply iSup_le
  intro n
  exact hitBy_le_barrier k target barrier hone hsuper n state

/-- States of a trial that starts undecided and then remains at success or failure. -/
inductive TrialState
  | start
  | success
  | failure
  deriving DecidableEq

/-- The uniform probability mass function on the two Boolean outcomes. -/
def fairCoin : PMF Bool :=
  PMF.ofFintype (fun _ => 1 / 2) (by
    rw [Fintype.sum_bool]
    exact ENNReal.add_halves 1)

/-- A fair transition from `start` to an absorbing success or failure state. -/
def trialKernel : TrialState → PMF TrialState
  | .start => fairCoin.bind fun outcome =>
      PMF.pure (if outcome then .success else .failure)
  | .success => PMF.pure .success
  | .failure => PMF.pure .failure

/-- The exact success barrier for the fair one-step trial. -/
def trialBarrier : TrialState → ℝ≥0∞
  | .start => 1 / 2
  | .success => 1
  | .failure => 0

private theorem expect_bernoulli_half (f : Bool → ℝ≥0∞) :
    expect fairCoin f = (1 / 2) * f true + (1 / 2) * f false := by
  simp [expect, fairCoin, tsum_fintype]

/-- The trial barrier is superharmonic away from success. -/
theorem trialBarrier_superharmonic (state : TrialState) (hstate : state ≠ .success) :
    expect (trialKernel state) trialBarrier ≤ trialBarrier state := by
  cases state with
  | start =>
      rw [trialKernel, expect_bind, expect_bernoulli_half]
      norm_num [trialBarrier]
  | success => exact (hstate rfl).elim
  | failure => simp [trialKernel, trialBarrier]

private theorem hitBy_trial_failure (n : ℕ) :
    hitBy trialKernel (fun state => state = .success) n .failure = 0 := by
  induction n with
  | zero => simp [hitBy]
  | succ n ih => simp [hitBy, trialKernel, ih]

/-- The probability of success in the fair trial is `1 / 2` at every positive horizon. -/
theorem hitBy_trial_start (n : ℕ) :
    hitBy trialKernel (fun state => state = .success) (n + 1) .start = 1 / 2 := by
  cases n with
  | zero =>
      simp [hitBy, trialKernel, expect_bind, expect_bernoulli_half]
  | succ n =>
      simp [hitBy, trialKernel, expect_bind, expect_bernoulli_half, hitBy_trial_failure]

/-- The finite-horizon supremum of success probabilities in the fair trial is exactly `1 / 2`. -/
theorem eventuallyHit_trial_start :
    eventuallyHit trialKernel (fun state => state = .success) .start = 1 / 2 := by
  apply le_antisymm
  · apply eventuallyHit_le_barrier trialKernel (fun state => state = .success) trialBarrier
    · intro state hstate
      subst state
      simp [trialBarrier]
    · exact trialBarrier_superharmonic
  · exact le_iSup_of_le 1 (le_of_eq (hitBy_trial_start 0).symm)

end StochasticProcesses
