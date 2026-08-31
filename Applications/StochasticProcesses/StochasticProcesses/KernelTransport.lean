/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Expectation pullback as directed transport

A probability kernel maps a source state to a probability mass function on
the target states. Its expectation pullback maps target observables to source
observables. The pullback is contravariant, hence a forward kernel on `G` is
represented by a transport on `G.reverse`.

The expectation uses `ℝ≥0∞` observables and an unconditional `tsum`. The
one-loop graph keeps the path statement compact. The same edge map works for
heterogeneous state fibers; a general forward walk additionally needs the
reversed edge sequence in `G.reverse`.

## Main definitions

* `StochasticProcesses.expect` - weighted expectation.
* `StochasticProcesses.kernelStar` - expectation pullback of a PMF kernel.
* `StochasticProcesses.kernelPullbackTransport` - dependent pullback transport
  on a reversed graph.
* `StochasticProcesses.loopGraph` - the one-vertex, one-edge graph.
* `StochasticProcesses.kernelTransport` - the reversed pullback transport.
* `StochasticProcesses.loopWalk` - the walk with a prescribed number of
  loop edges.
* `StochasticProcesses.iterateKernel` - finite iteration of a homogeneous
  probability kernel.

## Main results

* `StochasticProcesses.expect_mono` - monotonicity of expectation.
* `StochasticProcesses.expect_bind` - expectation through one kernel bind.
* `StochasticProcesses.kernelStar_monotone` - monotonicity of pullback.
* `StochasticProcesses.kernelPullbackTransport_edgeMap_monotone` - monotonicity of
  every dependent pullback edge.
* `StochasticProcesses.isSection_iff_harmonic` - exact sections as harmonic
  observable families.
* `StochasticProcesses.isLaxSection_iff_superharmonic` - lax sections as
  superharmonic observable families.
* `StochasticProcesses.isOplaxSection_iff_subharmonic` - oplax sections as
  subharmonic observable families.
* `StochasticProcesses.walkMap_loopWalk_eq_iterate` - path-map identification.
* `StochasticProcesses.superharmonic_iterate_le` - the upper path bound.
* `StochasticProcesses.subharmonic_iterate_ge` - the lower path bound.

## Tags

probability, PMF, expectation, kernel, pullback, directed transport
-/

noncomputable section

@[expose] public section

namespace StochasticProcesses

open scoped ENNReal

open Maths

variable {S : Type*}

/-- The nonnegative extended-real expectation of an observable under a PMF. -/
def expect (p : PMF S) (f : S → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' s, p s * f s

/-- Pointwise order is preserved by expectation. -/
theorem expect_mono (p : PMF S) {f g : S → ℝ≥0∞}
    (hfg : ∀ s, f s ≤ g s) : expect p f ≤ expect p g := by
  unfold expect
  exact ENNReal.tsum_le_tsum fun s => mul_le_mul_right (hfg s) (p s)

/-- Expectation distributes through an arbitrary PMF bind. -/
theorem expect_bind {T : Type*}
    (p : PMF S) (k : S → PMF T) (f : T → ℝ≥0∞) :
    expect (p.bind k) f = expect p (fun s => expect (k s) f) := by
  unfold expect
  simp_rw [PMF.bind_apply]
  change (∑' t, (∑' s, p s * k s t) * f t) =
    ∑' s, p s * (∑' t, k s t * f t)
  calc
    (∑' t, (∑' s, p s * k s t) * f t) =
        ∑' t, ∑' s, (p s * k s t) * f t := by
      apply tsum_congr
      intro t
      rw [ENNReal.tsum_mul_right]
    _ = ∑' s, ∑' t, (p s * k s t) * f t := ENNReal.tsum_comm
    _ = ∑' s, p s * (∑' t, k s t * f t) := by
      apply tsum_congr
      intro s
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro t
      rw [mul_assoc]

/-- Expectation pullback along a probability kernel. -/
def kernelStar {T : Type*} (k : S → PMF T) (f : T → ℝ≥0∞) : S → ℝ≥0∞ :=
  fun s => expect (k s) f

/-- Pull back observables along every edge of a dependent probability kernel. -/
def kernelPullbackTransport {V E : Type*} (G : EdgeGraph V E)
    (State : V → Type*)
    (k : (edge : E) → State (G.source edge) → PMF (State (G.target edge))) :
    Transport G.reverse (fun vertex => State vertex → ℝ≥0∞) where
  edgeMap edge observable state := expect (k edge state) observable

/-- The one-vertex, one-edge graph used for homogeneous kernel iteration. -/
def loopGraph : EdgeGraph Unit Unit where
  source := fun _ => ()
  target := fun _ => ()

/-- Pullback transport for a homogeneous kernel, oriented on the reversed graph. -/
def kernelTransport (k : S → PMF S) :
    Transport loopGraph.reverse (fun _ : Unit => S → ℝ≥0∞) :=
  kernelPullbackTransport loopGraph (fun _ => S) (fun _ => k)

/-- Expectation pullback is monotone. -/
theorem kernelStar_monotone {T : Type*} (k : S → PMF T) :
    Monotone (kernelStar k) := by
  intro f g hfg s
  exact expect_mono (k s) hfg

/-- Every dependent expectation pullback edge is monotone. -/
theorem kernelPullbackTransport_edgeMap_monotone {V E : Type*}
    (G : EdgeGraph V E)
    (State : V → Type*)
    (k : (edge : E) → State (G.source edge) → PMF (State (G.target edge)))
    (edge : E) :
    Monotone ((kernelPullbackTransport G State k).edgeMap edge) := by
  intro f g hfg state
  exact expect_mono (k edge state) hfg

/-- Exact sections are precisely pointwise harmonic observable families. -/
theorem isSection_iff_harmonic {V E : Type*} (G : EdgeGraph V E)
    (State : V → Type*)
    (k : (edge : E) → State (G.source edge) → PMF (State (G.target edge)))
    (family : ∀ vertex, State vertex → ℝ≥0∞) :
    (kernelPullbackTransport G State k).IsSection family ↔
      ∀ edge state,
        expect (k edge state) (family (G.target edge)) =
          family (G.source edge) state := by
  constructor
  · intro h edge state
    have hpoint := congrFun (h edge) state
    simpa [kernelPullbackTransport] using hpoint
  · intro h edge
    funext state
    simpa [kernelPullbackTransport] using h edge state

/-- Lax sections are precisely pointwise superharmonic observable families. -/
theorem isLaxSection_iff_superharmonic {V E : Type*} (G : EdgeGraph V E)
    (State : V → Type*)
    (k : (edge : E) → State (G.source edge) → PMF (State (G.target edge)))
    (family : ∀ vertex, State vertex → ℝ≥0∞) :
    (kernelPullbackTransport G State k).IsLaxSection family ↔
      ∀ edge state,
        expect (k edge state) (family (G.target edge)) ≤
          family (G.source edge) state := by
  constructor
  · intro h edge state
    exact h edge state
  · intro h edge state
    exact h edge state

/-- Oplax sections are precisely pointwise subharmonic observable families. -/
theorem isOplaxSection_iff_subharmonic {V E : Type*} (G : EdgeGraph V E)
    (State : V → Type*)
    (k : (edge : E) → State (G.source edge) → PMF (State (G.target edge)))
    (family : ∀ vertex, State vertex → ℝ≥0∞) :
    (kernelPullbackTransport G State k).IsOplaxSection family ↔
      ∀ edge state,
        family (G.source edge) state ≤
          expect (k edge state) (family (G.target edge)) := by
  constructor
  · intro h edge state
    exact h edge state
  · intro h edge state
    exact h edge state

/-- The loop walk containing exactly `n` copies of the unique edge. -/
def loopWalk : ℕ → loopGraph.reverse.Walk () ()
  | 0 => .nil
  | n + 1 => (loopWalk n).concat () rfl

@[simp]
theorem loopWalk_zero : loopWalk 0 = (.nil : loopGraph.reverse.Walk () ()) :=
  rfl

@[simp]
theorem loopWalk_succ (n : ℕ) :
    loopWalk (n + 1) = (loopWalk n).concat () rfl :=
  rfl

/-- The PMF obtained by taking `n` forward steps of a homogeneous kernel. -/
def iterateKernel (k : S → PMF S) : ℕ → S → PMF S
  | 0, s => PMF.pure s
  | n + 1, s => (k s).bind (iterateKernel k n)

@[simp]
theorem iterateKernel_zero (k : S → PMF S) (s : S) :
    iterateKernel k 0 s = PMF.pure s :=
  rfl

theorem iterateKernel_succ (k : S → PMF S) (n : ℕ) (s : S) :
    iterateKernel k (n + 1) s = (k s).bind (iterateKernel k n) :=
  rfl

private theorem expect_congr {p : PMF S} {f g : S → ℝ≥0∞}
    (h : ∀ s, f s = g s) : expect p f = expect p g := by
  exact congrArg (expect p) (funext h)

/-- Repeated pullback equals expectation under the corresponding iterated PMF. -/
theorem walkMap_loopWalk_eq_iterate
    (k : S → PMF S) (f : S → ℝ≥0∞) (n : ℕ) (s : S) :
    (kernelTransport k).walkMap (loopWalk n) f s =
      expect (iterateKernel k n s) f := by
  induction n generalizing s with
  | zero => simp [iterateKernel, expect]
  | succ n ih =>
      rw [loopWalk_succ, Transport.walkMap_concat]
      simp only [kernelTransport, kernelPullbackTransport, fiberCast_const]
      change expect (k s) (fun s' =>
        (kernelTransport k).walkMap (loopWalk n) f s') = _
      rw [iterateKernel_succ, expect_bind]
      exact expect_congr (fun s' => ih s')

/-- A superharmonic observable bounds every iterated-kernel expectation above. -/
theorem superharmonic_iterate_le
    (k : S → PMF S) (f : S → ℝ≥0∞)
    (hsub : ∀ s, kernelStar k f s ≤ f s) :
    ∀ n s, expect (iterateKernel k n s) f ≤ f s := by
  intro n s
  let family : Unit → S → ℝ≥0∞ := fun _ => f
  have hfamily : (kernelTransport k).IsLaxSection family := by
    intro edge s'
    simpa [kernelTransport, kernelPullbackTransport, kernelStar, family, loopGraph]
      using hsub s'
  have hmono : ∀ edge, Monotone ((kernelTransport k).edgeMap edge) := by
    intro edge
    simpa [kernelTransport] using
      kernelPullbackTransport_edgeMap_monotone loopGraph (fun _ => S) (fun _ => k) edge
  have hwalk := hfamily.walkMap_le hmono
    (loopWalk n)
  have hs := hwalk s
  rw [walkMap_loopWalk_eq_iterate] at hs
  simpa [family] using hs

/-- A subharmonic observable bounds every iterated-kernel expectation below. -/
theorem subharmonic_iterate_ge
    (k : S → PMF S) (f : S → ℝ≥0∞)
    (hsub : ∀ s, f s ≤ kernelStar k f s) :
    ∀ n s, f s ≤ expect (iterateKernel k n s) f := by
  intro n s
  let family : Unit → S → ℝ≥0∞ := fun _ => f
  have hfamily : (kernelTransport k).IsOplaxSection family := by
    intro edge s'
    simpa [kernelTransport, kernelPullbackTransport, kernelStar, family, loopGraph]
      using hsub s'
  have hmono : ∀ edge, Monotone ((kernelTransport k).edgeMap edge) := by
    intro edge
    simpa [kernelTransport] using
      kernelPullbackTransport_edgeMap_monotone loopGraph (fun _ => S) (fun _ => k) edge
  have hwalk := hfamily.le_walkMap hmono
    (loopWalk n)
  have hs := hwalk s
  rw [walkMap_loopWalk_eq_iterate] at hs
  simpa [family] using hs

end StochasticProcesses
