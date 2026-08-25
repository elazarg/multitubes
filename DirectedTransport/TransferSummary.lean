/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transfer summaries: affine, max-affine, and reflected

A one-dimensional *transfer summary* is a finite coefficient record that represents a self-map
of the line. Two classes are closed under composition, so a word of arbitrary length in them
still has a bounded number of coefficients.

* An **affine summary** `(shift, slope)` acts by `x ↦ shift + slope * x`. Composition is
  `(α, s) ∘ (α', s') = (α + s * α', s * s')`, an associative law with identity `(0, 1)`: a
  genuine monoid (`AffineSummary.instMonoid`). This is the coefficient presentation of the
  endomorphism monoid of the affine line; `AffineSummary.toAffineMapMonoidHom` exhibits it
  inside Mathlib's `Monoid (ℝ →ᵃ[ℝ] ℝ)`. Elsewhere these maps are called *weighted
  translations*, or the *`ax + b` monoid* (the `ax + b` group once `s ≠ 0`).

* A **max-affine summary** `(floor, shift, slope)` acts by `x ↦ max floor (shift + slope * x)`.
  When the outer slope is nonnegative, composition is again max-affine, with
  `(e, t, a) ∘ (e', t', a') = (max e (t + a * e'), t + a * t', a * a')`
  (`MaxAffineSummary.apply_comp`), and this law is associative
  (`MaxAffineSummary.comp_assoc`). The point worth making checkable is
  `MaxAffineSummary.apply_foldr`: a *word* of arbitrary length acts as the composite of the
  individual actions while still being summarized by three coefficients. There is no identity
  in this class (`MaxAffineSummary.not_exists_apply_eq_id`), so the nonnegative-slope summaries
  form a semigroup and not a monoid. These maps are also called *tropical affine maps*,
  monotone piecewise-affine maps with one breakpoint, or -- in optimal stopping -- one-step
  Snell or Bellman operators.

* The **reflected** (Lindley) map `x ↦ max 0 (a * x - g)` is the max-affine summary `(0, -g, a)`
  (`apply_reflectedSummary`). Iterating it along sequences `a` and `g` is the Lindley
  recursion, also known as the Skorokhod reflection at zero or the queueing workload/backlog
  recursion, with `a` a retention factor and `g` the service subtracted at each stage.
  `reflectedIter_eq_sup'` is Lindley's representation: the state at time `n` is the largest,
  over all restart times `m ≤ n`, of the state transported from `m` minus the
  retention-weighted service accumulated after `m`. In network calculus the same formula is
  the backlog bound.

## Main definitions

* `DirectedTransport.TransferSummary.AffineSummary` and its
  `DirectedTransport.TransferSummary.AffineSummary.instMonoid` instance.
* `DirectedTransport.TransferSummary.MaxAffineSummary` and
  `DirectedTransport.TransferSummary.MaxAffineSummary.comp`.
* `DirectedTransport.TransferSummary.reflectedIter` -- the reflected orbit.
* `DirectedTransport.TransferSummary.transport`,
  `DirectedTransport.TransferSummary.service`,
  `DirectedTransport.TransferSummary.lindleyTerm` -- the three ingredients of Lindley's
  representation.

## Main results

* `DirectedTransport.TransferSummary.AffineSummary.apply_comp`,
  `DirectedTransport.TransferSummary.AffineSummary.comp_assoc`,
  `DirectedTransport.TransferSummary.AffineSummary.apply_pow` -- affine words keep two
  coefficients.
* `DirectedTransport.TransferSummary.AffineSummary.monotone_apply_iff` -- monotone exactly at
  nonnegative slope.
* `DirectedTransport.TransferSummary.MaxAffineSummary.apply_comp`,
  `DirectedTransport.TransferSummary.MaxAffineSummary.comp_assoc`,
  `DirectedTransport.TransferSummary.MaxAffineSummary.apply_foldr` -- max-affine words keep
  three coefficients.
* `DirectedTransport.TransferSummary.MaxAffineSummary.monotone_apply_iff` and
  `DirectedTransport.TransferSummary.MaxAffineSummary.not_exists_apply_eq_id`.
* `DirectedTransport.TransferSummary.reflectedIter_eq_sup'` -- Lindley's representation.
* `DirectedTransport.TransferSummary.monotone_reflectedIter` and
  `DirectedTransport.TransferSummary.reflectedIter_le_of_le_service` -- monotone in the
  initial state, antitone in the service sequence.
* `DirectedTransport.TransferSummary.reflectedIter_add` -- the orbit restarts from its own
  state, and hence `DirectedTransport.TransferSummary.reflectedIter_eq_of_eq_zero`: once the
  orbit reflects to `0` the initial state is forgotten (regeneration at the end of a busy
  period), with the explicit post-regeneration formula
  `DirectedTransport.TransferSummary.reflectedIter_eq_sup'_of_eq_zero`.

## Implementation notes

The max-affine class of this file lacks an identity only because floors are finite: over floors
extended
by a bottom element the class becomes a monoid with identity `(⊥, 0, 1)`, in which the affine
summaries sit at the bottom floor and the max-affine summaries at the coerced floors. That
extension is `DirectedTransport.MaxAffineTransport.Label`, whose monoid instance on the
nonnegative-slope labels, action on the line, and two embeddings
`DirectedTransport.MaxAffineTransport.Label.ofAffine` and
`DirectedTransport.MaxAffineTransport.Label.ofMaxAffine` are stated there and not here: the
extended class needs the order structure of `WithBot ℝ`, whereas the classes of this file
need only the field, and every consumer of the extension already depends on both.

The stationary theory of the Lindley recursion under a stationary ergodic input (Loynes) is out
of scope, not merely unwritten. Its content -- almost-sure finiteness of the monotone limit
under negative drift, and uniqueness of the stationary solution -- is measure-theoretic and
ergodic, while this file is finite and order-theoretic and uses no measure theory. The
deterministic part of Loynes' argument, which does belong here, is the pathwise monotone
convergence of the finite-horizon suprema for one fixed input sequence:
`DirectedTransport.TransferSummary.tendsto_loynes_ciSup`. That statement is strictly weaker than
Loynes' theorem and is not a substitute for it.

## TODO

* The two-sided reflection, which keeps the state inside a band rather than above a single
  floor. The reflection at zero of this file is the one-sided case.

## References

* D. V. Lindley, *The theory of queues with a single server*, Math. Proc. Cambridge Philos.
  Soc. 48 (1952), 277-289, for the recursion and its representation.
* R. M. Loynes, *The stability of a queue with non-independent inter-arrival and service
  times*, Math. Proc. Cambridge Philos. Soc. 58 (1962), 497-520.
* F. Baccelli and P. Bremaud, *Elements of Queueing Theory*, Springer, for the reflection,
  busy-period and network-calculus vocabulary.

## Tags

transfer summary, affine map, max-affine map, tropical, Lindley recursion, Skorokhod
reflection, network calculus
-/

@[expose] public section

noncomputable section

namespace DirectedTransport.TransferSummary

/-! ## Affine summaries -/

/-- Coefficients of an affine self-map of the line: the map `x ↦ shift + slope * x`. Also known
as a weighted translation, or an element of the `ax + b` monoid. -/
@[ext] structure AffineSummary where
  /-- The additive part of the map. -/
  shift : ℝ
  /-- The multiplicative part of the map. -/
  slope : ℝ

namespace AffineSummary

/-- The action of an affine summary on the line. -/
def apply (f : AffineSummary) (x : ℝ) : ℝ := f.shift + f.slope * x

/-- Chronological composition: `outer.comp inner` passes the state through `inner` first. The
coefficient law is `(α, s) ∘ (α', s') = (α + s * α', s * s')`. -/
def comp (outer inner : AffineSummary) : AffineSummary where
  shift := outer.shift + outer.slope * inner.shift
  slope := outer.slope * inner.slope

/-- Coefficient composition represents composition of the actions. -/
@[simp] theorem apply_comp (outer inner : AffineSummary) (x : ℝ) :
    (outer.comp inner).apply x = outer.apply (inner.apply x) := by
  simp only [apply, comp]
  ring

/-- The identity summary `(0, 1)`. -/
def id : AffineSummary := ⟨0, 1⟩

/-- The identity summary acts as the identity map. -/
@[simp] theorem apply_id (x : ℝ) : id.apply x = x := by simp [apply, id]

/-- Composition of affine summaries is associative. -/
theorem comp_assoc (first second third : AffineSummary) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  ext <;> simp only [comp] <;> ring

/-- The identity summary is a left unit for composition. -/
theorem id_comp (f : AffineSummary) : id.comp f = f := by
  ext <;> simp [comp, id]

/-- The identity summary is a right unit for composition. -/
theorem comp_id (f : AffineSummary) : f.comp id = f := by
  ext <;> simp [comp, id]

/-- Affine summaries form a monoid under composition. -/
instance instMonoid : Monoid AffineSummary where
  mul := comp
  one := id
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

/-- Multiplication in the monoid is composition. -/
@[simp] theorem mul_eq_comp (outer inner : AffineSummary) : outer * inner = outer.comp inner := rfl

/-- The unit of the monoid is the identity summary. -/
@[simp] theorem one_eq_id : (1 : AffineSummary) = id := rfl

/-- Slopes multiply under composition. -/
@[simp] theorem slope_mul (outer inner : AffineSummary) :
    (outer * inner).slope = outer.slope * inner.slope := rfl

/-- The shift of a composite is the outer shift plus the outer slope times the inner shift. -/
@[simp] theorem shift_mul (outer inner : AffineSummary) :
    (outer * inner).shift = outer.shift + outer.slope * inner.shift := rfl

/-- **Words of arbitrary length keep two coefficients.** The `n`-th power of a summary acts as
the `n`-fold iterate of its action. -/
theorem apply_pow (f : AffineSummary) : ∀ (n : ℕ) (x : ℝ), (f ^ n).apply x = f.apply^[n] x
  | 0, x => by simp
  | n + 1, x => by
    rw [pow_succ, Function.iterate_succ_apply, mul_eq_comp, apply_comp, apply_pow f n]

/-- The slope of a power is the power of the slope. -/
@[simp] theorem slope_pow (f : AffineSummary) : ∀ n : ℕ, (f ^ n).slope = f.slope ^ n
  | 0 => rfl
  | n + 1 => by rw [pow_succ, slope_mul, slope_pow f n, pow_succ]

/-- The action is monotone exactly when the slope is nonnegative. -/
theorem monotone_apply_iff (f : AffineSummary) : Monotone f.apply ↔ 0 ≤ f.slope := by
  constructor
  · intro hmono
    have h := hmono (zero_le_one' ℝ)
    simp only [apply, mul_zero, mul_one, add_zero] at h
    linarith
  · intro hslope x y hxy
    have hmul := mul_le_mul_of_nonneg_left hxy hslope
    simp only [apply]
    linarith

/-- The action determines the coefficients: the representation is faithful. -/
theorem ext_of_apply {f g : AffineSummary} (h : ∀ x, f.apply x = g.apply x) : f = g := by
  have h0 := h 0
  have h1 := h 1
  simp only [apply, mul_zero, mul_one, add_zero] at h0 h1
  exact AffineSummary.ext h0 (by linarith)

/-- The affine self-map of `ℝ` presented by a summary. -/
def toAffineMap (f : AffineSummary) : ℝ →ᵃ[ℝ] ℝ where
  toFun := f.apply
  linear := f.slope • LinearMap.id
  map_vadd' p v := by
    simp only [apply, vadd_eq_add, LinearMap.smul_apply, LinearMap.id_coe, _root_.id_eq,
      smul_eq_mul]
    ring

/-- The affine map presented by a summary acts by the summary's action. -/
@[simp] theorem toAffineMap_apply (f : AffineSummary) (x : ℝ) : f.toAffineMap x = f.apply x := rfl

/-- Affine summaries are the coefficient presentation of the endomorphism monoid of the affine
line: composition of summaries is composition of affine maps. -/
def toAffineMapMonoidHom : AffineSummary →* (ℝ →ᵃ[ℝ] ℝ) where
  toFun := toAffineMap
  map_one' := by ext x; simp
  map_mul' outer inner := by ext x; simp

end AffineSummary

/-! ## Max-affine summaries -/

/-- Coefficients of a max-affine self-map of the line: the map
`x ↦ max floor (shift + slope * x)`. Also known as a tropical affine map, a monotone
piecewise-affine map with one breakpoint, or a one-step Snell or Bellman operator of a scalar
optimal-stopping problem. -/
@[ext] structure MaxAffineSummary where
  /-- The floor the map never falls below. -/
  floor : ℝ
  /-- The additive part of the affine branch. -/
  shift : ℝ
  /-- The multiplicative part of the affine branch. -/
  slope : ℝ

namespace MaxAffineSummary

/-- The action of a max-affine summary on the line. -/
def apply (f : MaxAffineSummary) (x : ℝ) : ℝ := max f.floor (f.shift + f.slope * x)

/-- Chronological composition: `outer.comp inner` passes the state through `inner` first. The
coefficient law is `(e, t, a) ∘ (e', t', a') = (max e (t + a * e'), t + a * t', a * a')`, which
represents composition of the actions exactly when the outer slope is nonnegative
(`apply_comp`). -/
def comp (outer inner : MaxAffineSummary) : MaxAffineSummary where
  floor := max outer.floor (outer.shift + outer.slope * inner.floor)
  shift := outer.shift + outer.slope * inner.shift
  slope := outer.slope * inner.slope

/-- **Coefficient composition represents composition of the actions**, under the nonnegativity
of the outer slope that lets it be pushed through the inner `max`. -/
theorem apply_comp {outer : MaxAffineSummary} (hslope : 0 ≤ outer.slope)
    (inner : MaxAffineSummary) (x : ℝ) :
    (outer.comp inner).apply x = outer.apply (inner.apply x) := by
  change max (max outer.floor (outer.shift + outer.slope * inner.floor))
      (outer.shift + outer.slope * inner.shift + outer.slope * inner.slope * x) =
    max outer.floor
      (outer.shift + outer.slope * max inner.floor (inner.shift + inner.slope * x))
  rw [mul_max_of_nonneg _ _ hslope, ← max_add_add_left, max_assoc]
  congr 2
  ring

/-- Slopes multiply under composition. -/
@[simp] theorem slope_comp (outer inner : MaxAffineSummary) :
    (outer.comp inner).slope = outer.slope * inner.slope := rfl

/-- Nonnegative slopes are closed under composition. -/
theorem slope_comp_nonneg {outer inner : MaxAffineSummary} (houter : 0 ≤ outer.slope)
    (hinner : 0 ≤ inner.slope) : 0 ≤ (outer.comp inner).slope :=
  mul_nonneg houter hinner

/-- Max-affine coefficient composition is associative as soon as the outermost slope is
nonnegative; the inner slopes are unconstrained. -/
theorem comp_assoc {first : MaxAffineSummary} (hfirst : 0 ≤ first.slope)
    (second third : MaxAffineSummary) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  have hdistrib : first.shift + first.slope *
        max second.floor (second.shift + second.slope * third.floor) =
      max (first.shift + first.slope * second.floor)
        (first.shift + first.slope * (second.shift + second.slope * third.floor)) := by
    rw [mul_max_of_nonneg _ _ hfirst, ← max_add_add_left]
  ext
  · change max (max first.floor (first.shift + first.slope * second.floor))
        (first.shift + first.slope * second.shift +
          first.slope * second.slope * third.floor) =
      max first.floor (first.shift + first.slope *
        max second.floor (second.shift + second.slope * third.floor))
    rw [hdistrib, max_assoc]
    congr 2
    ring
  · change first.shift + first.slope * second.shift + first.slope * second.slope * third.shift =
      first.shift + first.slope * (second.shift + second.slope * third.shift)
    ring
  · change first.slope * second.slope * third.slope =
      first.slope * (second.slope * third.slope)
    ring

/-- The action is monotone exactly when the slope is nonnegative. -/
theorem monotone_apply_iff (f : MaxAffineSummary) : Monotone f.apply ↔ 0 ≤ f.slope := by
  constructor
  · intro hmono
    by_contra hcon
    have hneg : f.slope < 0 := not_le.mp hcon
    -- Far enough to the left the affine branch dominates the floor, and there a negative slope
    -- is visibly decreasing.
    set c : ℝ := (f.floor - f.shift) / f.slope with hc
    have hbranch (y : ℝ) (hy : y ≤ c) : f.apply y = f.shift + f.slope * y := by
      refine max_eq_right ?_
      have hmul : f.slope * c ≤ f.slope * y := mul_le_mul_of_nonpos_left hy hneg.le
      rw [hc, mul_div_cancel₀ _ (ne_of_lt hneg)] at hmul
      linarith
    have hstep := hmono (show c - 1 ≤ c by linarith)
    rw [hbranch _ (by linarith), hbranch _ le_rfl] at hstep
    nlinarith
  · intro hslope x y hxy
    have hmul := mul_le_mul_of_nonneg_left hxy hslope
    exact max_le_max le_rfl (by linarith)

/-- The floor is never undercut: the action dominates its floor. -/
theorem floor_le_apply (f : MaxAffineSummary) (x : ℝ) : f.floor ≤ f.apply x := le_max_left _ _

/-- **No max-affine summary acts as the identity.** The floor caps the map from below at a
finite value, which the identity does not. So the nonnegative-slope summaries form a semigroup,
not a monoid; a literal identity would need the extended-real floor `-∞`. -/
theorem not_exists_apply_eq_id : ¬ ∃ f : MaxAffineSummary, ∀ x, f.apply x = x := by
  rintro ⟨f, hf⟩
  have h := f.floor_le_apply (f.floor - 1)
  rw [hf] at h
  linarith

/-- **Words of arbitrary length keep three coefficients.** A list of nonnegative-slope
summaries composes to a single summary whose action is the composite of the individual
actions. -/
theorem apply_foldr (base : MaxAffineSummary) :
    ∀ (l : List MaxAffineSummary), (∀ f ∈ l, 0 ≤ f.slope) → ∀ x : ℝ,
      (l.foldr comp base).apply x = l.foldr (fun f y => f.apply y) (base.apply x)
  | [], _, x => rfl
  | f :: l, hl, x => by
    have hf : 0 ≤ f.slope := hl f (List.mem_cons_self ..)
    have hrest (g : MaxAffineSummary) (hg : g ∈ l) : 0 ≤ g.slope :=
      hl g (List.mem_cons_of_mem _ hg)
    rw [List.foldr_cons, apply_comp hf, apply_foldr base l hrest x, List.foldr_cons]

/-- The slope of a word is the product of the letters' slopes: the third coefficient of a
composite is explicit in the letters. -/
theorem slope_foldr (base : MaxAffineSummary) :
    ∀ l : List MaxAffineSummary, (l.foldr comp base).slope = (l.map slope).prod * base.slope
  | [] => (one_mul _).symm
  | f :: l => by
    rw [List.foldr_cons, slope_comp, slope_foldr base l, List.map_cons, List.prod_cons,
      mul_assoc]

/-- Nonnegative-slope max-affine summaries form a semigroup under composition. -/
instance instSemigroup : Semigroup {f : MaxAffineSummary // 0 ≤ f.slope} where
  mul outer inner := ⟨outer.1.comp inner.1, slope_comp_nonneg outer.2 inner.2⟩
  mul_assoc first second third :=
    Subtype.ext (comp_assoc first.2 second.1 third.1)

end MaxAffineSummary

/-! ## The reflected (Lindley) recursion -/

/-- The max-affine summary of the reflected map `x ↦ max 0 (a * x - g)`: retention `a`, service
`g`, reflection floor `0`. -/
def reflectedSummary (a g : ℝ) : MaxAffineSummary := ⟨0, -g, a⟩

/-- The reflected summary acts by the reflected map. -/
@[simp] theorem apply_reflectedSummary (a g x : ℝ) :
    (reflectedSummary a g).apply x = max 0 (a * x - g) := by
  change max 0 (-g + a * x) = max 0 (a * x - g)
  congr 1
  ring

/-- The slope of the reflected summary is its retention factor. -/
@[simp] theorem slope_reflectedSummary (a g : ℝ) : (reflectedSummary a g).slope = a := rfl

variable (a g : ℕ → ℝ)

/-- The **reflected orbit** of the Lindley recursion `x ↦ max 0 (a n * x - g n)`: retention
`a n` attenuates the state carried into stage `n`, service `g n` discharges it, and the
reflection at zero forbids negative backlog. -/
def reflectedIter (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => max 0 (a n * reflectedIter x n - g n)

/-- The reflected orbit starts at its initial state. -/
@[simp] theorem reflectedIter_zero (x : ℝ) : reflectedIter a g x 0 = x := rfl

/-- Each stage of the reflected orbit is one max-affine summary action. -/
theorem reflectedIter_succ (x : ℝ) (n : ℕ) :
    reflectedIter a g x (n + 1) =
      (reflectedSummary (a n) (g n)).apply (reflectedIter a g x n) := by
  rw [apply_reflectedSummary]
  rfl

/-- After at least one stage the reflected orbit is nonnegative. -/
theorem reflectedIter_nonneg (x : ℝ) (n : ℕ) (hn : n ≠ 0) : 0 ≤ reflectedIter a g x n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact le_max_left _ _

/-- The retention transported across the window `[m, n)`. -/
def transport (m n : ℕ) : ℝ := ∏ k ∈ Finset.Ico m n, a k

/-- The retention-weighted service accumulated across the window `[m, n)`: each stage's service
is discounted by the retention that acts on it after that stage. -/
def service (m n : ℕ) : ℝ := ∑ k ∈ Finset.Ico m n, transport a (k + 1) n * g k

/-- The empty window transports nothing. -/
@[simp] theorem transport_self (m : ℕ) : transport a m m = 1 := by
  simp [transport]

/-- The empty window accumulates no service. -/
@[simp] theorem service_self (m : ℕ) : service a g m m = 0 := by
  simp [service]

/-- Extending the window by one stage multiplies the transport by that stage's retention. -/
theorem transport_succ_right {m n : ℕ} (hmn : m ≤ n) :
    transport a m (n + 1) = transport a m n * a n := by
  rw [transport, transport, Finset.prod_Ico_succ_top hmn]

/-- Extending the window by one stage attenuates the accumulated service and adds the new
stage's service. -/
theorem service_succ_right {m n : ℕ} (hmn : m ≤ n) :
    service a g m (n + 1) = a n * service a g m n + g n := by
  rw [service, service, Finset.sum_Ico_succ_top hmn, transport_self, one_mul,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := (Finset.mem_Ico.mp hk).2
  rw [transport_succ_right a hk']
  ring

/-- The state the Lindley representation transports from a restart time: the initial state at
time `0`, and the reflection floor `0` at every later time. -/
def restartState (x : ℝ) : ℕ → ℝ
  | 0 => x
  | _ + 1 => 0

/-- One term of Lindley's representation: the state at restart time `m`, transported to time
`n` and reduced by the service accumulated in between. -/
def lindleyTerm (x : ℝ) (m n : ℕ) : ℝ :=
  transport a m n * restartState x m - service a g m n

/-- Restarting at a positive time `n` contributes `0` at time `n`. -/
@[simp] theorem lindleyTerm_self (x : ℝ) (n : ℕ) (hn : n ≠ 0) : lindleyTerm a g x n n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [lindleyTerm, restartState]

/-- From the zero initial state every Lindley term is minus the accumulated service. -/
@[simp] theorem lindleyTerm_zero_state (m n : ℕ) :
    lindleyTerm a g 0 m n = -service a g m n := by
  cases m <;> simp [lindleyTerm, restartState]

/-- A Lindley term satisfies the reflected recursion's affine branch in its end time. -/
theorem lindleyTerm_succ_right (x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    lindleyTerm a g x m (n + 1) = a n * lindleyTerm a g x m n - g n := by
  rw [lindleyTerm, lindleyTerm, transport_succ_right a hmn, service_succ_right a g hmn]
  ring

/-- **Lindley's representation.** The reflected state at time `n` is the largest, over all
restart times `m ≤ n`, of the state at `m` transported to `n` minus the retention-weighted
service accumulated after `m`. The restart time `m = n` contributes `0`, which is exactly the
reflection. Only nonnegative retention is used; `a k ≤ 1` is never needed. In network calculus
this is the backlog bound. -/
theorem reflectedIter_eq_sup' (ha : ∀ k, 0 ≤ a k) (x : ℝ) :
    ∀ n : ℕ, reflectedIter a g x n =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun m => lindleyTerm a g x m n)
  | 0 => by simp [lindleyTerm, transport, restartState]
  | n + 1 => by
    have hcongr (m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
        lindleyTerm a g x m (n + 1) = (fun y => a n * y - g n) (lindleyTerm a g x m n) :=
      lindleyTerm_succ_right a g x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have hsup (u v : ℝ) :
        a n * (u ⊔ v) - g n = (a n * u - g n) ⊔ (a n * v - g n) := by
      rw [mul_max_of_nonneg _ _ (ha n), max_sub_sub_right]
    have hright : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
          (fun m => lindleyTerm a g x m (n + 1)) =
        max 0 (a n * (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun m => lindleyTerm a g x m n) - g n) := by
      have hins : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
            (fun m => lindleyTerm a g x m (n + 1)) =
          (insert (n + 1) (Finset.range (n + 1))).sup' (Finset.insert_nonempty _ _)
            (fun m => lindleyTerm a g x m (n + 1)) :=
        Finset.sup'_congr Finset.nonempty_range_add_one Finset.range_add_one fun _ _ => rfl
      rw [hins, Finset.sup'_insert (H := Finset.nonempty_range_add_one),
        lindleyTerm_self a g x (n + 1) n.succ_ne_zero,
        Finset.sup'_congr Finset.nonempty_range_add_one rfl hcongr]
      exact congrArg (max 0)
        (Finset.apply_sup'_eq_sup'_comp _ (fun y => a n * y - g n) hsup).symm
    rw [reflectedIter, reflectedIter_eq_sup' ha x n, hright]

/-- The reflected orbit is monotone in its initial state. -/
theorem monotone_reflectedIter (ha : ∀ k, 0 ≤ a k) :
    ∀ n : ℕ, Monotone fun x : ℝ => reflectedIter a g x n
  | 0 => fun _ _ hxy => hxy
  | n + 1 => fun x y hxy => by
    refine max_le_max le_rfl (sub_le_sub_right ?_ _)
    exact mul_le_mul_of_nonneg_left (monotone_reflectedIter ha n hxy) (ha n)

/-- More service never leaves more backlog: the reflected orbit is antitone in the service
sequence. -/
theorem reflectedIter_le_of_le_service {g' : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hg : ∀ k, g k ≤ g' k)
    (x : ℝ) : ∀ n : ℕ, reflectedIter a g' x n ≤ reflectedIter a g x n
  | 0 => le_rfl
  | n + 1 => by
    refine max_le_max le_rfl (sub_le_sub ?_ (hg n))
    exact mul_le_mul_of_nonneg_left (reflectedIter_le_of_le_service ha hg x n) (ha n)

/-- The reflected orbit restarts from its own state: running `m + n` stages is running `n`
stages of the time-shifted data from the state reached at `m`. -/
theorem reflectedIter_add (x : ℝ) (m : ℕ) :
    ∀ n : ℕ, reflectedIter a g x (m + n) =
      reflectedIter (fun k => a (m + k)) (fun k => g (m + k)) (reflectedIter a g x m) n
  | 0 => rfl
  | n + 1 => by
    rw [← Nat.add_assoc, reflectedIter, reflectedIter, reflectedIter_add x m n]

/-- **Regeneration at the end of a busy period.** Once two reflected orbits have both been
reflected down to `0` at some time `m`, they agree from `m` onwards: the initial state is
forgotten. -/
theorem reflectedIter_eq_of_eq_zero {x y : ℝ} {m : ℕ} (hx : reflectedIter a g x m = 0)
    (hy : reflectedIter a g y m = 0) {n : ℕ} (hmn : m ≤ n) :
    reflectedIter a g x n = reflectedIter a g y n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [reflectedIter_add a g x m d, reflectedIter_add a g y m d, hx, hy]

/-- **The busy period after a regeneration.** Once the orbit has reflected to `0` at time `m`,
its later values depend only on the service accumulated after `m`: they are the largest, over
restart times inside the window, of the negated retention-weighted service. -/
theorem reflectedIter_eq_sup'_of_eq_zero (ha : ∀ k, 0 ≤ a k) {x : ℝ} {m : ℕ}
    (hx : reflectedIter a g x m = 0) (d : ℕ) :
    reflectedIter a g x (m + d) =
      (Finset.range (d + 1)).sup' Finset.nonempty_range_add_one
        (fun j => -service (fun k => a (m + k)) (fun k => g (m + k)) j d) := by
  rw [reflectedIter_add a g x m d, hx,
    reflectedIter_eq_sup' _ _ (fun k => ha (m + k)) 0 d]
  exact Finset.sup'_congr _ rfl fun j _ => lindleyTerm_zero_state _ _ j d

end DirectedTransport.TransferSummary
