/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Recursion.LoynesConstruction

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The two-sided reflection

The *two-sided reflection* keeps the state inside a band `[lo, hi]` rather than above a single
floor: one stage of the recursion is `x ↦ min hi (max lo (a * x - g))`, the Skorokhod problem on
an interval. In queueing terms the band is a finite buffer, the lower clamp forbidding a negative
backlog and the upper clamp discarding what the buffer cannot hold; the reflection at a single
floor is the infinite-buffer case, recovered exactly where the upper clamp does not bind
(`Maths.TransferSummary.bandIter_eq_floorIter`).

* A **clamped affine summary** `(lo, hi, shift, slope)` acts by
  `x ↦ min hi (max lo (shift + slope * x))`. When the outer slope is nonnegative, composition is
  again clamped affine, with the band of the composite the image of the inner band under the
  outer map (`Maths.TransferSummary.ClampedAffineSummary.apply_comp`): a word of
  arbitrary length in these maps still has four coefficients
  (`Maths.TransferSummary.ClampedAffineSummary.apply_foldr`). The two-sided class
  needs one coefficient more than the max-affine class and, like it, has no identity.

* The **two-sided orbit** `Maths.TransferSummary.bandIter` iterates the clamped
  affine step along sequences `a` and `g`. It lies in the band from the first stage on, is
  monotone in its initial state and antitone in the service sequence, exactly as the one-sided
  orbit is.

* A **Lindley-style representation** survives, in an inf-sup form. The one-sided state is a
  supremum over restart times because the state forgets its past at the floor; in the band it
  also forgets its past at the top, and the two kinds of restart interleave into an infimum of
  suprema (`Maths.TransferSummary.bandIter_eq_inf'_sup'`), of which the term that
  ignores the upper clamp entirely is Lindley's representation.

* The **backward construction** in the band converges with no drift condition at all
  (`Maths.TransferSummary.tendsto_pastBandIter_hi`,
  `Maths.TransferSummary.tendsto_pastBandIter_lo`): the band itself supplies the
  bound that the one-sided construction has to obtain from geometric retention and bounded
  service. Geometric retention is still what makes the limit *unique*
  (`Maths.TransferSummary.tendsto_pastBandIter_hi_ciSup`), and there it needs no
  hypothesis on the service.

## Main definitions

* `Maths.TransferSummary.ClampedAffineSummary` and
  `Maths.TransferSummary.ClampedAffineSummary.comp`.
* `Maths.TransferSummary.floorIter` -- the one-sided orbit above a general floor.
* `Maths.TransferSummary.bandIter` -- the two-sided orbit.
* `Maths.TransferSummary.bandRestart` -- the one-sided orbit that restarts from the
  top of the band.
* `Maths.TransferSummary.pastBandIter` -- the backward two-sided orbit.

## Main results

* `Maths.TransferSummary.ClampedAffineSummary.apply_comp`,
  `Maths.TransferSummary.ClampedAffineSummary.comp_assoc` and
  `Maths.TransferSummary.ClampedAffineSummary.apply_foldr` -- clamped affine words
  keep four coefficients.
* `Maths.TransferSummary.ClampedAffineSummary.apply_mem_Icc` and
  `Maths.TransferSummary.ClampedAffineSummary.not_exists_apply_eq_id`.
* `Maths.TransferSummary.bandIter_mem_Icc`,
  `Maths.TransferSummary.monotone_bandIter` and
  `Maths.TransferSummary.bandIter_le_of_le_service` -- confinement to the band,
  monotone in the initial state, antitone in the service sequence.
* `Maths.TransferSummary.bandIter_eq_floorIter` -- the two-sided orbit is the
  one-sided one wherever the upper clamp does not bind.
* `Maths.TransferSummary.floorIter_eq_sup'` -- Lindley's representation above a
  general floor.
* `Maths.TransferSummary.bandIter_eq_inf'` and
  `Maths.TransferSummary.bandIter_eq_inf'_sup'` -- the two-sided representation, as
  an infimum over upper restarts and in closed form.
* `Maths.TransferSummary.bandIter_reversed` -- the backward orbit is the forward
  orbit of the input read forwards.
* `Maths.TransferSummary.tendsto_pastBandIter_hi` and
  `Maths.TransferSummary.tendsto_pastBandIter_lo` -- convergence of the backward
  construction, with no condition on the input.
* `Maths.TransferSummary.pastBandIter_sub_le` and
  `Maths.TransferSummary.tendsto_pastBandIter_hi_ciSup` -- under geometric retention
  the two extreme backward orbits meet, and by
  `Maths.TransferSummary.tendsto_pastBandIter` the limit is then reached from every
  state of the band.

## Implementation notes

The upper clamp is what makes the representation an infimum of suprema rather than a supremum.
Pushing the affine stages to the right past the clamps turns a word into an alternating
composite of `max lo` and `min hi`, and no rearrangement collapses that to a single supremum:
the terms of the one-sided representation are not merely truncated at `hi`. What does survive is
the reading of the upper clamp as a restart. Hitting the top of the band forgets the past exactly
as hitting the floor does, so the state at time `n` is the *smallest*, over all times `m ≤ n` at
which the band's top may have been reached, of the one-sided state obtained by restarting from
`hi` at `m`; those one-sided states are themselves suprema, by the representation above a general
floor. This is why the inner supremum is packaged as `bandRestart` rather than as a supremum over
a two-index family: a restart time `m` bounds its own inner range, and indexing through the
shifted input keeps every supremum over a nonempty range.

As in the one-sided theory, the stationary regime under a stationary ergodic input is out of
scope rather than unwritten: nothing here identifies the pathwise limits of the backward
construction as a stationary solution, which is a statement about the law of the input under the
shift and needs measure theory that this file does not use.

## References

* L. Kruk, J. Lehoczky, K. Ramanan and S. Shreve, *An explicit formula for the Skorokhod map on
  `[0, a]`*, Ann. Probab. 35 (2007), 1740-1768, for the two-sided reflection map and its
  inf-sup formula.
* D. V. Lindley, *The theory of queues with a single server*, Math. Proc. Cambridge Philos.
  Soc. 48 (1952), 277-289, for the one-sided recursion this specializes.
* F. Baccelli and P. Bremaud, *Elements of Queueing Theory*, Springer, for the reflection and
  finite-buffer vocabulary.

## Tags

two-sided reflection, Skorokhod problem on an interval, finite buffer, band, Lindley recursion,
Loynes construction
-/

@[expose] public section

noncomputable section

namespace Maths.TransferSummary

/-! ## Clamped affine summaries -/

/-- Coefficients of a clamped affine self-map of the line: the map
`x ↦ min hi (max lo (shift + slope * x))`, which confines the state to the band `[lo, hi]`
instead of to the half-line above a single floor. -/
@[ext] structure ClampedAffineSummary where
  /-- The bottom of the band, the value the map never falls below. -/
  lo : ℝ
  /-- The top of the band, the value the map never rises above. -/
  hi : ℝ
  /-- The additive part of the affine branch. -/
  shift : ℝ
  /-- The multiplicative part of the affine branch. -/
  slope : ℝ

namespace ClampedAffineSummary

/-- The action of a clamped affine summary on the line. -/
def apply (f : ClampedAffineSummary) (x : ℝ) : ℝ := min f.hi (max f.lo (f.shift + f.slope * x))

/-- The action never rises above the top of the band. -/
theorem apply_le_hi (f : ClampedAffineSummary) (x : ℝ) : f.apply x ≤ f.hi := min_le_left _ _

/-- The action never falls below the bottom of the band, as soon as the band is nonempty. -/
theorem lo_le_apply {f : ClampedAffineSummary} (hf : f.lo ≤ f.hi) (x : ℝ) : f.lo ≤ f.apply x :=
  le_min hf (le_max_left _ _)

/-- **The action lands in the band.** -/
theorem apply_mem_Icc {f : ClampedAffineSummary} (hf : f.lo ≤ f.hi) (x : ℝ) :
    f.apply x ∈ Set.Icc f.lo f.hi :=
  ⟨lo_le_apply hf x, f.apply_le_hi x⟩

/-- A nonnegative slope makes the action monotone. The converse fails here, unlike for the
affine and max-affine summaries: a band that is a single point or empty collapses the action to
a constant, which is monotone at every slope. -/
theorem monotone_apply {f : ClampedAffineSummary} (hslope : 0 ≤ f.slope) : Monotone f.apply :=
  fun x y hxy => min_le_min le_rfl (max_le_max le_rfl (by nlinarith))

/-- **The upper clamp is inactive below the top of the band.** Where the affine branch does not
exceed `hi`, the clamped affine action agrees with the max-affine action of the same floor,
shift and slope: the two-sided reflection is the one-sided one until the band's top is
reached. -/
theorem apply_eq_maxAffine {f : ClampedAffineSummary} {x : ℝ}
    (hx : f.shift + f.slope * x ≤ f.hi) (hlo : f.lo ≤ f.hi) :
    f.apply x = (MaxAffineSummary.mk f.lo f.shift f.slope).apply x :=
  min_eq_right (max_le hlo hx)

/-- Chronological composition: `outer.comp inner` passes the state through `inner` first. The
band of the composite is the image of the band of `inner` under `outer`, and the affine branch
composes as an affine map. -/
def comp (outer inner : ClampedAffineSummary) : ClampedAffineSummary where
  lo := outer.apply inner.lo
  hi := outer.apply inner.hi
  shift := outer.shift + outer.slope * inner.shift
  slope := outer.slope * inner.slope

/-- Clamping twice is clamping once, into the band that the outer clamp cuts out of the inner
one. No relation between the two bands is needed: an empty band collapses the map to a
constant, and the identity holds there too. -/
theorem clamp_clamp (lo hi lo' hi' z : ℝ) :
    min hi (max lo (min hi' (max lo' z))) =
      min (min hi (max lo hi')) (max (min hi (max lo lo')) z) := by
  rw [max_min_distrib_left, ← max_assoc, ← min_assoc, max_min_distrib_right, ← min_assoc,
    min_eq_left (le_trans (min_le_left _ _) (le_max_left hi z))]

/-- **Coefficient composition represents composition of the actions**, under the nonnegativity
of the outer slope that lets it be pushed through the inner clamps. -/
theorem apply_comp {outer : ClampedAffineSummary} (hslope : 0 ≤ outer.slope)
    (inner : ClampedAffineSummary) (x : ℝ) :
    (outer.comp inner).apply x = outer.apply (inner.apply x) := by
  have hpush (u v : ℝ) : outer.shift + outer.slope * min u v =
      min (outer.shift + outer.slope * u) (outer.shift + outer.slope * v) := by
    rw [mul_min_of_nonneg _ _ hslope, min_add_add_left]
  have hpushmax (u v : ℝ) : outer.shift + outer.slope * max u v =
      max (outer.shift + outer.slope * u) (outer.shift + outer.slope * v) := by
    rw [mul_max_of_nonneg _ _ hslope, max_add_add_left]
  have hinner : outer.shift + outer.slope * inner.apply x =
      min (outer.shift + outer.slope * inner.hi)
        (max (outer.shift + outer.slope * inner.lo)
          (outer.shift + outer.slope * (inner.shift + inner.slope * x))) := by
    rw [apply, hpush, hpushmax]
  have hcomp : outer.shift + outer.slope * inner.shift + outer.slope * inner.slope * x =
      outer.shift + outer.slope * (inner.shift + inner.slope * x) := by ring
  change min (outer.apply inner.hi) (max (outer.apply inner.lo)
      (outer.shift + outer.slope * inner.shift + outer.slope * inner.slope * x)) =
    min outer.hi (max outer.lo (outer.shift + outer.slope * inner.apply x))
  rw [hcomp, hinner, clamp_clamp]
  rfl

/-- Nonnegative slopes are closed under composition. -/
theorem slope_comp_nonneg {outer inner : ClampedAffineSummary} (houter : 0 ≤ outer.slope)
    (hinner : 0 ≤ inner.slope) : 0 ≤ (outer.comp inner).slope :=
  mul_nonneg houter hinner

/-- Nonempty bands are closed under composition, as soon as the outer slope is nonnegative. -/
theorem lo_le_hi_comp {outer inner : ClampedAffineSummary} (houter : 0 ≤ outer.slope)
    (hinner : inner.lo ≤ inner.hi) : (outer.comp inner).lo ≤ (outer.comp inner).hi :=
  monotone_apply houter hinner

/-- Clamped affine coefficient composition is associative as soon as the outermost slope is
nonnegative; the inner slopes and the bands are unconstrained. -/
theorem comp_assoc {first : ClampedAffineSummary} (hfirst : 0 ≤ first.slope)
    (second third : ClampedAffineSummary) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  ext
  · exact apply_comp hfirst second third.lo
  · exact apply_comp hfirst second third.hi
  · change first.shift + first.slope * second.shift + first.slope * second.slope * third.shift =
      first.shift + first.slope * (second.shift + second.slope * third.shift)
    ring
  · change first.slope * second.slope * third.slope = first.slope * (second.slope * third.slope)
    ring

/-- **Words of arbitrary length keep four coefficients.** A list of nonnegative-slope clamped
affine summaries composes to a single such summary whose action is the composite of the
individual actions. -/
theorem apply_foldr (base : ClampedAffineSummary) :
    ∀ (l : List ClampedAffineSummary), (∀ f ∈ l, 0 ≤ f.slope) → ∀ x : ℝ,
      (l.foldr comp base).apply x = l.foldr (fun f y => f.apply y) (base.apply x)
  | [], _, x => rfl
  | f :: l, hl, x => by
    have hf : 0 ≤ f.slope := hl f (List.mem_cons_self ..)
    have hrest (g : ClampedAffineSummary) (hg : g ∈ l) : 0 ≤ g.slope :=
      hl g (List.mem_cons_of_mem _ hg)
    rw [List.foldr_cons, apply_comp hf, apply_foldr base l hrest x, List.foldr_cons]

/-- **No clamped affine summary acts as the identity.** The top of the band caps the map from
above at a finite value, which the identity does not. So the nonnegative-slope clamped affine
summaries form a semigroup and not a monoid. -/
theorem not_exists_apply_eq_id : ¬ ∃ f : ClampedAffineSummary, ∀ x, f.apply x = x := by
  rintro ⟨f, hf⟩
  have h := f.apply_le_hi (f.hi + 1)
  rw [hf] at h
  linarith

/-- Nonnegative-slope clamped affine summaries form a semigroup under composition. -/
instance instSemigroup : Semigroup {f : ClampedAffineSummary // 0 ≤ f.slope} where
  mul outer inner := ⟨outer.1.comp inner.1, slope_comp_nonneg outer.2 inner.2⟩
  mul_assoc first second third := Subtype.ext (comp_assoc first.2 second.1 third.1)

end ClampedAffineSummary

/-! ## The one-sided orbit above a general floor -/

variable (lo hi : ℝ) (a g : ℕ → ℝ)

/-- The **one-sided orbit** of the Lindley recursion reflected at a general floor,
`x ↦ max lo (a n * x - g n)`. The reflection at zero is the case `lo = 0`
(`floorIter_zero_floor`). -/
def floorIter (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => max lo (a n * floorIter x n - g n)

/-- The one-sided orbit starts at its initial state. -/
@[simp] theorem floorIter_zero (x : ℝ) : floorIter lo a g x 0 = x := rfl

/-- One stage of the one-sided orbit. -/
theorem floorIter_succ (x : ℝ) (n : ℕ) :
    floorIter lo a g x (n + 1) = max lo (a n * floorIter lo a g x n - g n) := rfl

/-- Reflecting at the floor `0` is the reflected orbit of the Lindley recursion. -/
theorem floorIter_zero_floor (x : ℝ) : ∀ n : ℕ, floorIter 0 a g x n = reflectedIter a g x n
  | 0 => rfl
  | n + 1 => by rw [floorIter_succ, floorIter_zero_floor x n, reflectedIter]

/-- After at least one stage the one-sided orbit dominates its floor. -/
theorem le_floorIter (x : ℝ) (n : ℕ) (hn : n ≠ 0) : lo ≤ floorIter lo a g x n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact le_max_left _ _

/-- The state the Lindley representation transports from a restart time, when the reflection is
at the floor `lo`: the initial state at time `0`, and the floor at every later time. -/
def floorRestartState (x : ℝ) (m : ℕ) : ℝ := if m = 0 then x else lo

/-- One term of Lindley's representation above the floor `lo`: the state at restart time `m`,
transported to time `n` and reduced by the service accumulated in between. -/
def floorTerm (x : ℝ) (m n : ℕ) : ℝ :=
  transport a m n * floorRestartState lo x m - service a g m n

/-- Restarting at a positive time `n` contributes the floor at time `n`. -/
theorem floorTerm_self (x : ℝ) (n : ℕ) (hn : n ≠ 0) : floorTerm lo a g x n n = lo := by
  simp [floorTerm, floorRestartState, hn]

/-- A Lindley term satisfies the one-sided recursion's affine branch in its end time. -/
theorem floorTerm_succ_right (x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    floorTerm lo a g x m (n + 1) = a n * floorTerm lo a g x m n - g n := by
  rw [floorTerm, floorTerm, transport_succ_right a hmn, service_succ_right a g hmn]
  ring

/-- **Lindley's representation above a general floor.** The one-sided state at time `n` is the
largest, over all restart times `m ≤ n`, of the state at `m` transported to `n` minus the
retention-weighted service accumulated after `m`, where the state at a positive restart time is
the floor. Only nonnegative retention is used. -/
theorem floorIter_eq_sup' (ha : ∀ k, 0 ≤ a k) (x : ℝ) :
    ∀ n : ℕ, floorIter lo a g x n =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => floorTerm lo a g x m n)
  | 0 => by simp [floorTerm, floorRestartState, transport, service]
  | n + 1 => by
    have hcongr (m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
        floorTerm lo a g x m (n + 1) = (fun y => a n * y - g n) (floorTerm lo a g x m n) :=
      floorTerm_succ_right lo a g x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have hsup (u v : ℝ) : a n * (u ⊔ v) - g n = (a n * u - g n) ⊔ (a n * v - g n) := by
      rw [mul_max_of_nonneg _ _ (ha n), max_sub_sub_right]
    have hright : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
          (fun m => floorTerm lo a g x m (n + 1)) =
        max lo (a n * (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun m => floorTerm lo a g x m n) - g n) := by
      have hins : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
            (fun m => floorTerm lo a g x m (n + 1)) =
          (insert (n + 1) (Finset.range (n + 1))).sup' (Finset.insert_nonempty _ _)
            (fun m => floorTerm lo a g x m (n + 1)) :=
        Finset.sup'_congr Finset.nonempty_range_add_one Finset.range_add_one fun _ _ => rfl
      rw [hins, Finset.sup'_insert (H := Finset.nonempty_range_add_one),
        floorTerm_self lo a g x (n + 1) n.succ_ne_zero,
        Finset.sup'_congr Finset.nonempty_range_add_one rfl hcongr]
      exact congrArg (max lo)
        (Finset.apply_sup'_eq_sup'_comp _ (fun y => a n * y - g n) hsup).symm
    rw [floorIter_succ, floorIter_eq_sup' ha x n, hright]

/-! ## The two-sided orbit -/

/-- The clamped affine summary of the two-sided reflected map `x ↦ min hi (max lo (a * x - g))`:
retention `a`, service `g`, band `[lo, hi]`. -/
def bandSummary (lo hi a g : ℝ) : ClampedAffineSummary := ⟨lo, hi, -g, a⟩

/-- The two-sided reflected summary acts by the two-sided reflected map. -/
@[simp] theorem apply_bandSummary (lo hi a g x : ℝ) :
    (bandSummary lo hi a g).apply x = min hi (max lo (a * x - g)) := by
  change min hi (max lo (-g + a * x)) = min hi (max lo (a * x - g))
  congr 2
  ring

/-- The slope of the two-sided reflected summary is its retention factor. -/
@[simp] theorem slope_bandSummary (lo hi a g : ℝ) : (bandSummary lo hi a g).slope = a := rfl

/-- The **two-sided reflected orbit**: the state is attenuated by the retention `a n`, reduced
by the service `g n`, and then confined to the band `[lo, hi]`, the lower clamp forbidding a
negative backlog and the upper clamp discarding what a finite buffer cannot hold. -/
def bandIter (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => min hi (max lo (a n * bandIter x n - g n))

/-- The two-sided orbit starts at its initial state. -/
@[simp] theorem bandIter_zero (x : ℝ) : bandIter lo hi a g x 0 = x := rfl

/-- Each stage of the two-sided orbit is one clamped affine summary action. -/
theorem bandIter_succ (x : ℝ) (n : ℕ) :
    bandIter lo hi a g x (n + 1) =
      (bandSummary lo hi (a n) (g n)).apply (bandIter lo hi a g x n) := by
  rw [apply_bandSummary]
  rfl

/-- **After at least one stage the two-sided orbit lies in the band.** -/
theorem bandIter_mem_Icc (hlh : lo ≤ hi) (x : ℝ) (n : ℕ) (hn : n ≠ 0) :
    bandIter lo hi a g x n ∈ Set.Icc lo hi := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ⟨le_min hlh (le_max_left _ _), min_le_left _ _⟩

/-- The two-sided orbit never rises above the top of the band, from the first stage on. -/
theorem bandIter_le (x : ℝ) (n : ℕ) (hn : n ≠ 0) : bandIter lo hi a g x n ≤ hi := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact min_le_left _ _

/-- The two-sided orbit is monotone in its initial state. -/
theorem monotone_bandIter (ha : ∀ k, 0 ≤ a k) :
    ∀ n : ℕ, Monotone fun x : ℝ => bandIter lo hi a g x n
  | 0 => fun _ _ hxy => hxy
  | n + 1 => fun x y hxy => by
    refine min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right ?_ _))
    exact mul_le_mul_of_nonneg_left (monotone_bandIter ha n hxy) (ha n)

/-- More service never leaves more backlog: the two-sided orbit is antitone in the service
sequence. -/
theorem bandIter_le_of_le_service {g' : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hg : ∀ k, g k ≤ g' k)
    (x : ℝ) : ∀ n : ℕ, bandIter lo hi a g' x n ≤ bandIter lo hi a g x n
  | 0 => le_rfl
  | n + 1 => by
    refine min_le_min le_rfl (max_le_max le_rfl (sub_le_sub ?_ (hg n)))
    exact mul_le_mul_of_nonneg_left (bandIter_le_of_le_service ha hg x n) (ha n)

/-- The two-sided orbit restarts from its own state: running `m + n` stages is running `n`
stages of the time-shifted data from the state reached at `m`. -/
theorem bandIter_add (x : ℝ) (m : ℕ) :
    ∀ n : ℕ, bandIter lo hi a g x (m + n) =
      bandIter lo hi (fun k => a (m + k)) (fun k => g (m + k)) (bandIter lo hi a g x m) n
  | 0 => rfl
  | n + 1 => by
    rw [← Nat.add_assoc, bandIter, bandIter, bandIter_add x m n]

/-- **The two-sided orbit is the one-sided one until the band's top is reached.** Where the
one-sided orbit above the same floor never exceeds `hi`, the upper clamp never binds and the two
orbits agree. This is the exact form of the statement that the one-sided reflection is the
infinite-buffer limit of the two-sided one. -/
theorem bandIter_eq_floorIter (x : ℝ) :
    ∀ n : ℕ, (∀ k ≤ n, floorIter lo a g x k ≤ hi) → bandIter lo hi a g x n = floorIter lo a g x n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bandIter, bandIter_eq_floorIter x n fun k hk => h k (Nat.le_succ_of_le hk),
      ← floorIter_succ]
    exact min_eq_right (h (n + 1) le_rfl)

/-! ## The two-sided Lindley representation -/

/-- The **upper restart** at time `m`: the state at time `n` of the one-sided orbit above the
floor `lo` that starts at time `m` from the top of the band, and from the initial state when
`m = 0`. Hitting the top of the band is what makes the state forget its past, exactly as
hitting the floor does in the one-sided recursion. -/
def bandRestart (x : ℝ) (m n : ℕ) : ℝ :=
  floorIter lo (fun k => a (m + k)) (fun k => g (m + k)) (if m = 0 then x else hi) (n - m)

/-- A positive restart time contributes the top of the band at that time. -/
theorem bandRestart_self (x : ℝ) (n : ℕ) (hn : n ≠ 0) : bandRestart lo hi a g x n n = hi := by
  simp [bandRestart, hn]

/-- An upper restart obeys the one-sided recursion in its end time, from its restart time
onwards. -/
theorem bandRestart_succ_right (x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    bandRestart lo hi a g x m (n + 1) =
      max lo (a n * bandRestart lo hi a g x m n - g n) := by
  have hstep : n + 1 - m = (n - m) + 1 := by omega
  have hidx : m + (n - m) = n := by omega
  rw [bandRestart, hstep, floorIter_succ, bandRestart]
  simp only [hidx]

/-- **The two-sided Lindley representation.** The two-sided reflected state at time `n` is the
smallest, over all upper restart times `m ≤ n`, of the one-sided state above the floor `lo`
obtained by restarting from the top of the band at time `m`. The restart time `m = n`
contributes `hi`, which is exactly the upper clamp; the restart time `m = 0` contributes the
one-sided orbit above `lo` from the initial state, so that term alone is Lindley's
representation and the terms `m > 0` are everything the upper clamp adds.

Only nonnegative retention is used, and neither `lo ≤ hi` nor any constraint on the initial
state is needed. -/
theorem bandIter_eq_inf' (ha : ∀ k, 0 ≤ a k) (x : ℝ) :
    ∀ n : ℕ, bandIter lo hi a g x n =
      (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one
        (fun m => bandRestart lo hi a g x m n)
  | 0 => by simp [bandRestart]
  | n + 1 => by
    have hcongr (m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
        bandRestart lo hi a g x m (n + 1) =
          (fun y => max lo (a n * y - g n)) (bandRestart lo hi a g x m n) :=
      bandRestart_succ_right lo hi a g x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have hinf (u v : ℝ) :
        max lo (a n * (u ⊓ v) - g n) = max lo (a n * u - g n) ⊓ max lo (a n * v - g n) := by
      rw [mul_min_of_nonneg _ _ (ha n), ← max_min_distrib_left, min_sub_sub_right]
    have hright : (Finset.range (n + 1 + 1)).inf' Finset.nonempty_range_add_one
          (fun m => bandRestart lo hi a g x m (n + 1)) =
        min hi (max lo (a n * (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one
          (fun m => bandRestart lo hi a g x m n) - g n)) := by
      have hins : (Finset.range (n + 1 + 1)).inf' Finset.nonempty_range_add_one
            (fun m => bandRestart lo hi a g x m (n + 1)) =
          (insert (n + 1) (Finset.range (n + 1))).inf' (Finset.insert_nonempty _ _)
            (fun m => bandRestart lo hi a g x m (n + 1)) :=
        Finset.inf'_congr Finset.nonempty_range_add_one Finset.range_add_one fun _ _ => rfl
      rw [hins, Finset.inf'_insert (H := Finset.nonempty_range_add_one),
        bandRestart_self lo hi a g x (n + 1) n.succ_ne_zero,
        Finset.inf'_congr Finset.nonempty_range_add_one rfl hcongr]
      exact congrArg (min hi)
        (Finset.apply_inf'_eq_inf'_comp _ (fun y => max lo (a n * y - g n)) hinf).symm
    rw [bandIter, bandIter_eq_inf' ha x n, hright]

/-- An upper restart is a supremum of Lindley terms: the one-sided representation, read in the
original time indices, of the orbit that restarts from the top of the band at time `m`. -/
theorem bandRestart_eq_sup' (ha : ∀ k, 0 ≤ a k) (x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    bandRestart lo hi a g x m n =
      (Finset.range (n - m + 1)).sup' Finset.nonempty_range_add_one
        (fun j => transport a (m + j) n * (if j = 0 then (if m = 0 then x else hi) else lo) -
          service a g (m + j) n) := by
  have hidx : m + (n - m) = n := by omega
  rw [bandRestart, floorIter_eq_sup' _ _ _ (fun k => ha (m + k))]
  refine Finset.sup'_congr _ rfl fun j _ => ?_
  rw [floorTerm, floorRestartState, transport_shift, service_shift, hidx]

/-- **The two-sided Lindley representation in closed form.** The two-sided reflected state at
time `n` is an infimum over upper restart times of suprema over lower restart times: the state
is transported from the top of the band at the upper restart `m` -- or from the initial state
when `m = 0` -- and from the floor at every lower restart between `m` and `n`, each contribution
reduced by the retention-weighted service accumulated since. The single term `m = 0` is
Lindley's representation `Maths.TransferSummary.reflectedIter_eq_sup'`; the terms
`m > 0` are what the upper clamp adds. -/
theorem bandIter_eq_inf'_sup' (ha : ∀ k, 0 ≤ a k) (x : ℝ) (n : ℕ) :
    bandIter lo hi a g x n =
      (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one (fun m =>
        (Finset.range (n - m + 1)).sup' Finset.nonempty_range_add_one
          (fun j => transport a (m + j) n * (if j = 0 then (if m = 0 then x else hi) else lo) -
            service a g (m + j) n)) := by
  rw [bandIter_eq_inf' lo hi a g ha x n]
  refine Finset.inf'_congr _ rfl fun m hm => ?_
  exact bandRestart_eq_sup' lo hi a g ha x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))

/-! ## The backward construction in the band -/

/-- The **backward two-sided orbit**: the state produced at the observation time by feeding `x`
into the recursion `n` stages earlier, the input being indexed by age as in the Loynes
construction. It is the composite of the `n` most recent stages, innermost stage oldest. -/
def pastBandIter : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => fun x => pastBandIter n (min hi (max lo (a n * x - g n)))

/-- Nothing has happened yet: the backward orbit at horizon `0` is the identity. -/
@[simp] theorem pastBandIter_zero (x : ℝ) : pastBandIter lo hi a g 0 x = x := rfl

/-- Reaching one stage further into the past prepends that stage. -/
theorem pastBandIter_succ (n : ℕ) (x : ℝ) :
    pastBandIter lo hi a g (n + 1) x =
      pastBandIter lo hi a g n (min hi (max lo (a n * x - g n))) := rfl

/-- **The backward orbit is the forward orbit of the input read forwards.** At horizon `n` it is
the two-sided reflected orbit driven by the age-indexed input read forwards over that horizon.
This is the two-sided analogue of
`Maths.TransferSummary.reflectedIter_reversed`. -/
theorem bandIter_reversed :
    ∀ (n : ℕ) (x : ℝ),
      bandIter lo hi (reversed n a) (reversed n g) x n = pastBandIter lo hi a g n x
  | 0, _ => rfl
  | n + 1, x => by
    have hshift (u : ℕ → ℝ) (k : ℕ) : reversed (n + 1) u (k + 1) = reversed n u k := by
      have h : n + 1 - (k + 2) = n - (k + 1) := by omega
      rw [reversed, reversed, h]
    have hzero (u : ℕ → ℝ) : reversed (n + 1) u 0 = u n := by
      rw [reversed, Nat.add_sub_cancel]
    have hpeel := bandIter_add lo hi (reversed (n + 1) a) (reversed (n + 1) g) x 1 n
    rw [Nat.add_comm 1 n] at hpeel
    rw [hpeel, bandIter, bandIter_zero, hzero, hzero]
    have hcongr : bandIter lo hi (fun k => reversed (n + 1) a (1 + k))
          (fun k => reversed (n + 1) g (1 + k)) (min hi (max lo (a n * x - g n))) n =
        bandIter lo hi (reversed n a) (reversed n g) (min hi (max lo (a n * x - g n))) n := by
      simp only [Nat.add_comm 1, hshift]
    rw [hcongr, bandIter_reversed n]
    rfl

/-- The backward orbit is monotone in the state fed into it. -/
theorem monotone_pastBandIter (ha : ∀ k, 0 ≤ a k) :
    ∀ n : ℕ, Monotone (pastBandIter lo hi a g n)
  | 0 => monotone_id
  | n + 1 => fun x y hxy => by
    refine monotone_pastBandIter ha n ?_
    exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right
      (mul_le_mul_of_nonneg_left hxy (ha n)) _))

/-- **After at least one stage the backward orbit lies in the band**, whatever state was fed
in. -/
theorem pastBandIter_mem_Icc (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    ∀ (n : ℕ), n ≠ 0 → ∀ x : ℝ, pastBandIter lo hi a g n x ∈ Set.Icc lo hi
  | 0, hn, _ => absurd rfl hn
  | n + 1, _, x => by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨le_min hlh (le_max_left _ _), min_le_left _ _⟩
    · exact pastBandIter_mem_Icc hlh ha n hn.ne' _

/-- **The backward orbit from the top of the band decreases with the horizon.** Each further
stage of the past can only bring the state down, because the stage's own output already lies
below the top of the band. A nonempty band is not needed here. -/
theorem antitone_pastBandIter_hi (ha : ∀ k, 0 ≤ a k) :
    Antitone fun n => pastBandIter lo hi a g n hi :=
  antitone_nat_of_succ_le fun n => by
    rw [pastBandIter_succ]
    exact monotone_pastBandIter lo hi a g ha n (min_le_left _ _)

/-- **The backward orbit from the bottom of the band increases with the horizon.** This is the
two-sided analogue of `Maths.TransferSummary.monotone_loynes`. -/
theorem monotone_pastBandIter_lo (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    Monotone fun n => pastBandIter lo hi a g n lo :=
  monotone_nat_of_le_succ fun n => by
    rw [pastBandIter_succ]
    exact monotone_pastBandIter lo hi a g ha n (le_min hlh (le_max_left _ _))

/-- Both extreme backward orbits stay in the band at every horizon. -/
theorem pastBandIter_mem_Icc_of_mem (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) {x : ℝ}
    (hx : x ∈ Set.Icc lo hi) (n : ℕ) : pastBandIter lo hi a g n x ∈ Set.Icc lo hi := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact hx
  · exact pastBandIter_mem_Icc lo hi a g hlh ha n hn.ne' x

/-- **The band makes boundedness automatic.** No drift condition is needed: the backward orbit
from the top of the band is bounded below by the bottom of the band. -/
theorem bddBelow_pastBandIter_hi (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    BddBelow (Set.range fun n => pastBandIter lo hi a g n hi) := by
  refine ⟨lo, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (pastBandIter_mem_Icc_of_mem lo hi a g hlh ha ⟨hlh, le_rfl⟩ n).1

/-- The backward orbit from the bottom of the band is bounded above by the top of the band. -/
theorem bddAbove_pastBandIter_lo (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    BddAbove (Set.range fun n => pastBandIter lo hi a g n lo) := by
  refine ⟨hi, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (pastBandIter_mem_Icc_of_mem lo hi a g hlh ha ⟨le_rfl, hlh⟩ n).2

/-- **Convergence of the two-sided backward construction from the top of the band.**
Unconditionally on the input, beyond nonnegative retention and a nonempty band: the confinement
that the band imposes replaces the geometric retention and bounded service that the one-sided
construction needs for `Maths.TransferSummary.tendsto_loynes_ciSup`. -/
theorem tendsto_pastBandIter_hi (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    Filter.Tendsto (fun n => pastBandIter lo hi a g n hi) Filter.atTop
      (nhds (⨅ n, pastBandIter lo hi a g n hi)) :=
  tendsto_atTop_ciInf (antitone_pastBandIter_hi lo hi a g ha)
    (bddBelow_pastBandIter_hi lo hi a g hlh ha)

/-- **Convergence of the two-sided backward construction from the bottom of the band**, again
with no condition on the input beyond nonnegative retention and a nonempty band. -/
theorem tendsto_pastBandIter_lo (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k) :
    Filter.Tendsto (fun n => pastBandIter lo hi a g n lo) Filter.atTop
      (nhds (⨆ n, pastBandIter lo hi a g n lo)) :=
  tendsto_atTop_ciSup (monotone_pastBandIter_lo lo hi a g hlh ha)
    (bddAbove_pastBandIter_lo lo hi a g hlh ha)

/-- The backward orbit from the bottom of the band is the smallest one started in the band. -/
theorem pastBandIter_lo_le (ha : ∀ k, 0 ≤ a k) {x : ℝ} (hx : x ∈ Set.Icc lo hi) (n : ℕ) :
    pastBandIter lo hi a g n lo ≤ pastBandIter lo hi a g n x :=
  monotone_pastBandIter lo hi a g ha n hx.1

/-- The backward orbit from the top of the band is the largest one started in the band. -/
theorem pastBandIter_le_hi (ha : ∀ k, 0 ≤ a k) {x : ℝ} (hx : x ∈ Set.Icc lo hi) (n : ℕ) :
    pastBandIter lo hi a g n x ≤ pastBandIter lo hi a g n hi :=
  monotone_pastBandIter lo hi a g ha n hx.2

/-- **One stage of the two-sided reflection contracts by its retention factor.** The clamps are
nonexpansive, so the whole stage is Lipschitz with the retention as its constant. -/
theorem bandStep_sub_le {c : ℝ} (hc : 0 ≤ c) {x y : ℝ} (hxy : x ≤ y) (d : ℝ) :
    min hi (max lo (c * y - d)) - min hi (max lo (c * x - d)) ≤ c * (y - x) := by
  have ht0 : 0 ≤ c * (y - x) := mul_nonneg hc (by linarith)
  have hy : c * y - d = (c * x - d) + c * (y - x) := by ring
  have hmax : max lo (c * y - d) ≤ max lo (c * x - d) + c * (y - x) := by
    rw [hy, ← max_add_add_right]
    exact max_le_max (by linarith) le_rfl
  have hmin : min hi (max lo (c * x - d) + c * (y - x)) ≤
      min hi (max lo (c * x - d)) + c * (y - x) := by
    rw [← min_add_add_right]
    exact min_le_min (by linarith) le_rfl
  have hstep := min_le_min (le_refl hi) hmax
  linarith

/-- **The backward orbit is Lipschitz with the accumulated retention as its constant.** -/
theorem pastBandIter_sub_le (ha : ∀ k, 0 ≤ a k) :
    ∀ (n : ℕ) {x y : ℝ}, x ≤ y →
      pastBandIter lo hi a g n y - pastBandIter lo hi a g n x ≤ pastTransport a n * (y - x)
  | 0, x, y, hxy => by simp
  | n + 1, x, y, hxy => by
    have hstep : min hi (max lo (a n * x - g n)) ≤ min hi (max lo (a n * y - g n)) :=
      min_le_min le_rfl (max_le_max le_rfl
        (sub_le_sub_right (mul_le_mul_of_nonneg_left hxy (ha n)) _))
    have hIH := pastBandIter_sub_le ha n hstep
    have hT : 0 ≤ pastTransport a n := pastTransport_nonneg _ ha n
    have hLip := bandStep_sub_le lo hi (ha n) hxy (g n)
    rw [pastBandIter_succ, pastBandIter_succ, pastTransport_succ]
    nlinarith

/-- **Geometric retention closes the band.** If every retention lies in `[0, ρ]` with `ρ < 1`,
the gap between the two extreme backward orbits vanishes. No condition on the service is needed:
the band already bounds the construction, so geometric retention is used only for uniqueness of
the limit, not for its existence. -/
theorem tendsto_pastBandIter_sub {ρ : ℝ} (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k)
    (hρ : ∀ k, a k ≤ ρ) (hρ1 : ρ < 1) :
    Filter.Tendsto
      (fun n => pastBandIter lo hi a g n hi - pastBandIter lo hi a g n lo) Filter.atTop
      (nhds 0) := by
  have hρ0 : 0 ≤ ρ := le_trans (ha 0) (hρ 0)
  have hpow : Filter.Tendsto (fun n : ℕ => ρ ^ n * (hi - lo)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (hi - lo)
  refine squeeze_zero (fun n => by linarith [monotone_pastBandIter lo hi a g ha n hlh])
    (fun n => le_trans (pastBandIter_sub_le lo hi a g ha n hlh) ?_) hpow
  exact mul_le_mul_of_nonneg_right (pastTransport_le_pow ha hρ n) (by linarith)

/-- **The two-sided Loynes limit under geometric retention.** The backward orbit from the top of
the band converges to the same limit as the one from the bottom. -/
theorem tendsto_pastBandIter_hi_ciSup {ρ : ℝ} (hlh : lo ≤ hi) (ha : ∀ k, 0 ≤ a k)
    (hρ : ∀ k, a k ≤ ρ) (hρ1 : ρ < 1) :
    Filter.Tendsto (fun n => pastBandIter lo hi a g n hi) Filter.atTop
      (nhds (⨆ n, pastBandIter lo hi a g n lo)) := by
  have h := (tendsto_pastBandIter_lo lo hi a g hlh ha).add
    (tendsto_pastBandIter_sub lo hi a g hlh ha hρ hρ1)
  rw [add_zero] at h
  simpa using h

/-- **A single limit for every initial state in the band.** When the two extreme backward orbits
converge to a common value, so does the backward orbit from any state of the band: the
construction then forgets its initial state entirely. -/
theorem tendsto_pastBandIter (ha : ∀ k, 0 ≤ a k) {x L : ℝ} (hx : x ∈ Set.Icc lo hi)
    (hlo : Filter.Tendsto (fun n => pastBandIter lo hi a g n lo) Filter.atTop (nhds L))
    (hhi : Filter.Tendsto (fun n => pastBandIter lo hi a g n hi) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => pastBandIter lo hi a g n x) Filter.atTop (nhds L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (pastBandIter_lo_le lo hi a g ha hx)
    (pastBandIter_le_hi lo hi a g ha hx)

end Maths.TransferSummary
