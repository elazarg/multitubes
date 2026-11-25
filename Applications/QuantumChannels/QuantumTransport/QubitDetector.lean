/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantumTransport.Detection
public import QuantumTransport.Discard
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A qubit detector with a dark state

The hit and continue Kraus operators are diagonal with entries `(3/5, 0)` and `(4/5, 1)`.
A bright qubit can be missed repeatedly. A dark qubit continues with certainty. The
finite-horizon effect is a geometric multiple of the bright projection, which is the sharp
eventual upper certificate. Pairing the effects with a density matrix gives detection
probabilities for arbitrary initial qubit states.

## Main definitions

* `QuantumTransport.QubitDetector.instrument` records a Boolean outcome at each measurement.

## Main results

* `QuantumTransport.QubitDetector.hitBy_eq` gives the finite-horizon detection effect.
* `QuantumTransport.QubitDetector.isLeast_barrier` identifies the sharp eventual certificate.
* `QuantumTransport.QubitDetector.tendsto_detectionProbability` gives the eventual detection
  probability as the initial bright population.
-/

@[expose] public section

namespace QuantumTransport.QubitDetector

open Matrix Filter
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- The hit operation detects the first coordinate with single-trial probability `9/25`. -/
noncomputable def hit : Matrix (Fin 2) (Fin 2) ℂ →CP Matrix (Fin 2) (Fin 2) ℂ :=
  krausOperation (diagonal fun i => if i = 0 then 3 / 5 else 0)

/-- The continuation operation attenuates the first coordinate and preserves the second. -/
noncomputable def cont : Matrix (Fin 2) (Fin 2) ℂ →CP Matrix (Fin 2) (Fin 2) ℂ :=
  krausOperation (diagonal fun i => if i = 0 then 4 / 5 else 1)

/-- The effect of reporting a hit in a single trial. -/
theorem hit_one : hit 1 = (9 / 25 : ℂ) • coordinateProjection (0 : Fin 2) := by
  simp only [hit, krausOperation_apply, star_eq_conjTranspose, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateProjection, diagonal_mul_diagonal,
      diagonal_apply, map_ofNat]

/-- The probability of continuing from the bright state is `16/25`. -/
theorem cont_bright : cont (coordinateProjection (0 : Fin 2)) =
    (16 / 25 : ℂ) • coordinateProjection (0 : Fin 2) := by
  simp only [cont, krausOperation_apply, star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateProjection, diagonal_mul_diagonal,
      diagonal_apply, map_ofNat]

/-- Hit and continue account for the entire unit effect. -/
theorem normalized : hit 1 + cont 1 = 1 := by
  rw [hit_one]
  simp only [cont, krausOperation_apply, star_eq_conjTranspose, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateProjection, diagonal_mul_diagonal,
      diagonal_apply, one_apply, map_ofNat]

/-- A finite instrument with `true` recording detection and `false` recording continuation. -/
noncomputable def instrument : FiniteInstrument Bool (Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix (Fin 2) (Fin 2) ℂ) where
  branch b := if b then hit else cont
  normalized := by simpa [Fintype.sum_bool, add_comm] using normalized

/-- The effect after `n` rounds is the bright projection times the chance of at least one hit. -/
theorem hitBy_eq (n : ℕ) :
    hitBy hit cont n = (1 - (16 / 25 : ℂ) ^ n) • coordinateProjection (0 : Fin 2) := by
  induction n with
  | zero => simp [hitBy]
  | succ n ih =>
    change hit 1 + cont (hitBy hit cont n) = _
    rw [hit_one, ih, LinearMapClass.map_smul, cont_bright, smul_smul, ← add_smul, pow_succ]
    congr 1
    ring

private theorem tendsto_missPower :
    Tendsto (fun n : ℕ => (16 / 25 : ℂ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num [norm_div])

/-- The finite detection effects converge to the bright projection. -/
theorem tendsto_hitBy :
    Tendsto (hitBy hit cont) atTop (𝓝 (coordinateProjection (0 : Fin 2))) := by
  simpa [funext hitBy_eq] using
    (tendsto_const_nhds (x := (1 : ℂ))).sub tendsto_missPower |>.smul
      (tendsto_const_nhds (x := coordinateProjection (0 : Fin 2)))

/-- The bright projection is the least positive observable that bounds one detection step. -/
theorem isLeast_barrier :
    IsLeast {b | 0 ≤ b ∧ detectionStep hit cont b ≤ b} (coordinateProjection (0 : Fin 2)) := by
  have hs := isLUB_of_tendsto_atTop (hitBy_mono hit cont) tendsto_hitBy
  have hfix : detectionStep hit cont (coordinateProjection (0 : Fin 2)) =
      coordinateProjection (0 : Fin 2) := by
    rw [detectionStep, hit_one, cont_bright, ← add_smul]
    norm_num
  refine ⟨⟨(coordinateProjection_posSemidef _).nonneg, hfix.le⟩, ?_⟩
  rintro b ⟨hb, hstep⟩
  exact hs.2 (Set.forall_mem_range.mpr (hitBy_le_barrier hit cont hb hstep))

/-- Pairing the finite detection effect with an initial matrix reads its bright population. -/
theorem trace_hitBy (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    (ρ * hitBy hit cont n).trace = (1 - (16 / 25 : ℂ) ^ n) * ρ 0 0 := by
  rw [hitBy_eq, Matrix.mul_smul, Matrix.trace_smul]
  simp [coordinateProjection, Matrix.trace, Matrix.mul_diagonal]

/-- The real detection probability at a finite horizon is a geometric fraction of the
initial bright population. -/
theorem detectionProbability_eq (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    (ρ * hitBy hit cont n).trace.re = (1 - (16 / 25 : ℝ) ^ n) * (ρ 0 0).re := by
  rw [trace_hitBy, ← Complex.re_ofReal_mul]
  push_cast
  rfl

/-- For a trace-one positive matrix, the eventual detection probability lies in `[0, 1]`. -/
theorem brightPopulation_mem_unitInterval (ρ : PositiveMatrix (Fin 2)) (hn : ρ.1.trace = 1) :
    (ρ.1 0 0).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hsecond : 0 ≤ (ρ.1 1 1).re := (ρ.2.diag_nonneg (i := 1)).1
  have hsum : (ρ.1 0 0).re + (ρ.1 1 1).re = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using congrArg Complex.re hn
  exact ⟨(ρ.2.diag_nonneg (i := 0)).1, by linarith⟩

/-- For every initial density matrix, the detection probability tends to its bright population.
The trace-pairing identity also holds for unnormalized initial matrices. -/
theorem tendsto_detectionProbability (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun n => (ρ * hitBy hit cont n).trace.re) atTop (𝓝 (ρ 0 0).re) := by
  simpa [Function.comp_def, trace_hitBy] using Complex.continuous_re.continuousAt.tendsto.comp
    (((tendsto_const_nhds (x := (1 : ℂ))).sub tendsto_missPower).mul
      (tendsto_const_nhds (x := ρ 0 0)))

end QuantumTransport.QubitDetector
