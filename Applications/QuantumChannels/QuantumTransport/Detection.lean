/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantumTransport.Instruments

/-!
# Repeated detection and upper certificates

Repeatedly measuring a hit-or-continue instrument gives an increasing sequence of detection
effects. A positive pre-fixed point bounds all finite horizons. If the effect interval admits
increasing sequential suprema and the continuation map preserves them, the eventual detection
effect is the least positive pre-fixed point.

## Main definitions

* `QuantumTransport.detectionStep` counts an immediate hit and detection after continuation.
* `QuantumTransport.hitBy` is the effect for a first hit within a finite horizon.

## Main results

* `QuantumTransport.hitBy_succ_eq_add_firstHit` identifies the individual first-hit histories.
* `QuantumTransport.hitBy_add_survival` accounts for the outcomes at each horizon.
* `QuantumTransport.hitBy_le_barrier` verifies an upper bound at every horizon.
* `QuantumTransport.exists_eventualDetection` gives the least barrier under sequential
  completeness and normality on effects.
* `QuantumTransport.isGreatest_survival` identifies the complementary survival effect.
-/

@[expose] public section

namespace QuantumTransport

open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hit cont : A →CP A)

/-- One iteration counts an immediate hit and all subsequent hits after continuation. -/
def detectionStep (x : A) : A := hit 1 + cont x

/-- The effect of detecting a hit within the first `n` rounds. -/
def hitBy : ℕ → A
  | 0 => 0
  | n + 1 => detectionStep hit cont (hitBy n)

/-- A detection step preserves observable inequalities. -/
theorem detectionStep_mono : Monotone (detectionStep hit cont) :=
  fun _ _ h => add_le_add_right (OrderHomClass.mono cont h) _

/-- The detection effects increase with the horizon. -/
theorem hitBy_mono : Monotone (hitBy hit cont) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [hitBy, detectionStep] using (map_nonneg hit (zero_le_one : (0 : A) ≤ 1))
  | succ n ih => exact detectionStep_mono hit cont ih

/-- A positive observable that bounds one iteration bounds every finite horizon. -/
theorem hitBy_le_barrier {b : A} (hb : 0 ≤ b) (hstep : detectionStep hit cont b ≤ b) (n : ℕ) :
    hitBy hit cont n ≤ b := by
  induction n with
  | zero => exact hb
  | succ n ih => exact (detectionStep_mono hit cont ih).trans hstep

/-- A subunital total operation bounds every detection effect by the unit. -/
theorem hitBy_le_one (hn : hit 1 + cont 1 ≤ 1) (n : ℕ) : hitBy hit cont n ≤ 1 :=
  hitBy_le_barrier hit cont zero_le_one hn n

/-- The increase at round `n + 1` is the effect for `n` continuations followed by a hit. -/
theorem hitBy_succ_eq_add_firstHit (n : ℕ) :
    hitBy hit cont (n + 1) = hitBy hit cont n + (cont^[n]) (hit 1) := by
  induction n with
  | zero => simp [hitBy, detectionStep]
  | succ n ih =>
    change hit 1 + cont (hitBy hit cont (n + 1)) =
      hit 1 + cont (hitBy hit cont n) + (cont^[n + 1]) (hit 1)
    rw [ih, map_add, Function.iterate_succ_apply', add_assoc]

/-- Detection by round `n` and continuation through all `n` rounds exhaust the outcomes. -/
theorem hitBy_add_survival (hn : hit 1 + cont 1 = 1) (n : ℕ) :
    hitBy hit cont n + (cont^[n]) 1 = 1 := by
  induction n with
  | zero => simp [hitBy]
  | succ n ih =>
    change hit 1 + cont (hitBy hit cont n) + (cont^[n + 1]) 1 = 1
    rw [Function.iterate_succ_apply', add_assoc, ← map_add, ih, hn]

/-- If the step preserves the supremum of the detection sequence, that supremum is fixed
and is the least nonnegative upper certificate. -/
theorem hit_isLeast_barrier {h : A} (hs : IsLUB (Set.range (hitBy hit cont)) h)
    (hp : IsLUB (Set.range (fun n => detectionStep hit cont (hitBy hit cont n)))
      (detectionStep hit cont h)) :
    detectionStep hit cont h = h ∧ IsLeast {b | 0 ≤ b ∧ detectionStep hit cont b ≤ b} h := by
  have upper (n : ℕ) : hitBy hit cont n ≤ h := hs.1 (Set.mem_range_self n)
  have h0 : 0 ≤ h := upper 0
  have hf : detectionStep hit cont h = h := by
    apply le_antisymm
    · apply hp.2
      rintro _ ⟨n, rfl⟩
      exact upper (n + 1)
    · apply hs.2
      rintro _ ⟨n, rfl⟩
      exact (hitBy_mono hit cont (Nat.le_succ n)).trans (hp.1 (Set.mem_range_self n))
  refine ⟨hf, ⟨h0, hf.le⟩, ?_⟩
  rintro b ⟨hb, hstep⟩
  apply hs.2
  rintro _ ⟨n, rfl⟩
  exact hitBy_le_barrier hit cont hb hstep n

/-- Suprema of increasing sequences of effects and their preservation by the continuation
map suffice for the eventual detection effect to exist and be the least upper certificate. -/
theorem exists_eventualDetection (hn : hit 1 + cont 1 ≤ 1)
    (complete : ∀ u : ℕ → A, Monotone u → (∀ n, 0 ≤ u n ∧ u n ≤ 1) →
      ∃ h, IsLUB (Set.range u) h)
    (normal : ∀ (u : ℕ → A) (h : A), Monotone u → (∀ n, 0 ≤ u n ∧ u n ≤ 1) →
      IsLUB (Set.range u) h → IsLUB (Set.range (fun n => cont (u n))) (cont h)) :
    ∃ h, IsLUB (Set.range (hitBy hit cont)) h ∧ detectionStep hit cont h = h ∧
      IsLeast {b | 0 ≤ b ∧ detectionStep hit cont b ≤ b} h := by
  have hm := hitBy_mono hit cont
  have he (n : ℕ) : 0 ≤ hitBy hit cont n ∧ hitBy hit cont n ≤ 1 :=
    ⟨hm (Nat.zero_le n), hitBy_le_one hit cont hn n⟩
  obtain ⟨h, hs⟩ := complete _ hm he
  have hc := normal _ h hm he hs
  refine ⟨h, hs, hit_isLeast_barrier hit cont hs ⟨?_, ?_⟩⟩
  · rintro _ ⟨n, rfl⟩
    exact add_le_add_right (hc.1 (Set.mem_range_self n)) _
  · intro b hb
    have hcb : cont h ≤ b - hit 1 := by
      apply hc.2
      rintro _ ⟨n, rfl⟩
      apply le_sub_iff_add_le.mpr
      simpa [detectionStep, add_comm] using hb (Set.mem_range_self n)
    simpa [detectionStep, add_comm] using le_sub_iff_add_le.mp hcb

/-- The complement of the least detection barrier is fixed by continuation and dominates
every effect whose value cannot decrease on continuation. -/
theorem isGreatest_survival (hn : hit 1 + cont 1 = 1) {h : A}
    (hf : detectionStep hit cont h = h)
    (hmin : IsLeast {b | 0 ≤ b ∧ detectionStep hit cont b ≤ b} h) :
    cont (1 - h) = 1 - h ∧
      IsGreatest {d : A | 0 ≤ d ∧ d ≤ 1 ∧ d ≤ cont d} (1 - h) := by
  have dual (d : A) : detectionStep hit cont (1 - d) = 1 - cont d := by
    rw [detectionStep, map_sub, ← add_sub_assoc, hn]
  have hfixed : cont (1 - h) = 1 - h := by
    have hd := dual (1 - h)
    rw [sub_sub_cancel, hf] at hd
    simpa only [sub_sub_cancel] using congrArg (fun x : A => 1 - x) hd.symm
  have hu : h ≤ 1 := hmin.2 ⟨zero_le_one, hn.le⟩
  refine ⟨hfixed, ⟨sub_nonneg.mpr hu, sub_le_self _ hmin.1.1, hfixed.ge⟩, ?_⟩
  rintro d ⟨_, hd, hc⟩
  apply le_sub_comm.mp
  apply hmin.2
  exact ⟨sub_nonneg.mpr hd, (dual d).le.trans (sub_le_sub_left hc _)⟩

end QuantumTransport
