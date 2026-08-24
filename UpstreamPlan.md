# Upstream plan

Proposal, 2026-08-24. Revised 2026-08-24 after `LinearAlgebra/Duality.lean` and Gordan's
transposition theorem landed. Scoping note only — no migration is proposed as done.

Method copied from `kraft`'s `UpstreamPlan.md`, whose evidence base is a real mathlib PR review
([#34108](https://github.com/leanprover-community/mathlib4/pull/34108)) of this author's own
code. The four things that plan scores on — dependency, reusability, self-containment, size —
are what this one scores on too.

Claims are graded: **[V]** verified by reading the pinned snapshot / this library's source or by
a build, **[B]** believed but not mechanically checked.

## Headline judgement

**There is a real PR here, it is a good one, and it got materially stronger since the first
draft.** `DirectedTransport/LinearAlgebra/` now contains the finite matrix theorem of the
alternative, Gordan's transposition theorem, standard-form Farkas, extreme points as basic
feasible solutions, **and** the full duality package — weak duality, strong duality, dual
attainment, complementary slackness — all over an arbitrary linearly ordered field. mathlib has
none of it.

The argument is no longer just "mathlib is missing Farkas". mathlib's `ProperCone` file lists
four TODO items **[V, `Mathlib/Analysis/Convex/Cone/Basic.lean` lines 33-38]**:

> - Add `ConvexConeClass` that extends `SetLike` and replace the below instance
> - Define primal and dual cone programs and prove weak duality.
> - Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
> - Define linear programs and prove LP duality as a special case of cone duality.

**This library now answers the last three**, in the linear-programming case, from the ground up.
That is the pitch, and it writes itself.

The candidate is ~1500 lines of general LP content across four scalar-stratified pieces, plus
~125 lines that stay downstream.

## What changed since the first draft

| Item | First draft | Now |
|---|---|---|
| Gordan | PR 2, ~80 lines to write | **Written and compiling** as `exists_rowEval_pos_iff_not_hasBalancedCertificate`, with `HasBalancedCertificate` **[V]**. Statement-based name, docstringed "**Gordan's transposition theorem**" — the collision in §5(h) was handled correctly. |
| LP duality | Absent; noted only as mathlib's TODO | **`Duality.lean`, 513 lines** **[V]**, over `𝕜`. Two more TODO bullets answered. |
| Mining 1.3 (general-`𝕜` route) | Inspection-only **[B]**, flagged as the plan's main retreat risk | **Build-tested for the duality half** **[V]**. The risk is materially reduced. |
| `FourierMotzkin.lean` | 622 lines | 685 lines (Gordan) **[V]** |
| Total candidate | ~1350 lines | ~1920 lines **[V]** |

Nothing in the old plan turned out *wrong*. Two things are now weaker than stated, and both are
recorded honestly below: §5(b)'s worry about the algebraic/topological split has changed shape
rather than gone away (§5(c)), and the six-PR sequence undercounted the work.

## 1. What exactly ships

### Ships — `FourierMotzkin.lean` (685 lines), arbitrary linearly ordered field

Stated over `{𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, no `ℝ` anywhere **[V]**.

| Declaration | What it states | Upstream? |
|---|---|---|
| `rowEval`, `IsFeasible`, `IsCertificate`, `HasCertificate` | the system `A x ≥ b` and its Farkas certificate `u ≥ 0, uᵀA = 0, ⟨u,b⟩ > 0` | Yes, but **restate** — §5(a) |
| `feas_cert_disjoint` | the easy direction: the alternatives are disjoint | Yes |
| `ZeroRows`/`PosRows`/`NegRows`/`FMRowIndex`, `fmA`, `fmB` | the reduced system on `ZeroRows ⊕ (PosRows × NegRows)` | Implementation — `private`, or an internals section |
| `fm_feasible_of_feasible`, `feasible_of_fm_feasible` | feasibility transfers along the reduction both ways | Yes — "FM elimination preserves satisfiability" is independently citable **[B]** |
| `liftCoeff`, `liftCert`, `liftCert_nonneg`, `fm_cert_lift` | a reduced certificate lifts | Implementation |
| **`theorem_of_alternative`** | `¬ IsFeasible A b ↔ HasCertificate A b` over any linearly ordered field | **Yes — the foundation of the series** |
| `HasBalancedCertificate` | a nonzero nonnegative `u` annihilating every column | Yes |
| **`exists_rowEval_pos_iff_not_hasBalancedCertificate`** | **Gordan's transposition theorem**: `∃ x, ∀ i, 0 < rowEval A i x` ↔ no balanced certificate | **Yes** |

Stiemke, Ville and Motzkin's transposition theorem remain unattempted (`Mining.md` 3.2, SKETCH,
**[B]**) — same shape via block right-hand sides `(1, 0)`. List as follow-ups; do not promise.

### Ships — `Duality.lean` (513 lines), arbitrary linearly ordered field

The new material, and the most immediately *wanted* file in the candidate. Also `𝕜`-general
throughout, with only the last two corollaries over `ℝ` **[V]**.

| Declaration | What it states |
|---|---|
| `IsStandardFeasible` | `0 ≤ z ∧ A *ᵥ z = rhs` over `𝕜`. **See §5(c) — this must not ship alongside `standardFeasibleSet`** |
| `IsDualFeasible` | `Aᵀ *ᵥ y ≥ c`, no sign constraint on `y` |
| `sum_dual_eq_of_isStandardFeasible` | the objective expanded through the equality constraint |
| **`objective_le_of_isDualFeasible`** | **weak duality** |
| `exists_scaledDual_of_not_exists_objective_ge` | the sharp hypothesis-free form: an unreachable level is witnessed by a *scaled* dual `(y, lam)`, `lam ≥ 0` — a genuine dual point when `lam > 0`, a Farkas certificate of infeasibility when `lam = 0` |
| **`exists_objective_ge_iff_feasible_and_forall_isDualFeasible`**, `exists_objective_ge_iff_forall_isDualFeasible` | **strong duality**, as a threshold equivalence at every level `t` |
| **`exists_isDualFeasible_objective_le_of_forall_le`** | **dual attainment** |
| `ComplementarySlackness`, `complementarySlackness_iff_forall_ne_zero` | the relation, and its support form |
| **`complementarySlackness_iff_objective_eq`** | complementary slackness ⇔ zero duality gap |
| `forall_le_of_complementarySlackness`, `exists_isDualFeasible_complementarySlackness_of_forall_le` | complementary slackness is exactly a certificate of optimality |
| `mem_standardFeasibleSet_iff_isStandardFeasible`, `isStandardOptimal_of_complementarySlackness`, `exists_isDualFeasible_complementarySlackness_of_standardOptimal` | the `ℝ` transfer |

Two design choices are worth defending explicitly in the PR description, because both are
unusual and both are *right*:

- **Strong duality as a threshold equivalence, not an equality of optima.** For every level `t`,
  the primal reaches `t` iff the primal is feasible and every dual feasible point is `≥ t`
  **[V]**. This sidesteps extended reals and attainment entirely and stays meaningful when either
  side is unbounded or empty — which is why it works over `𝕜`, where there is no `sSup` to appeal
  to. A reviewer expecting `max = min` will ask; the answer is that `max = min` is not a theorem
  over a general ordered field, and the threshold form is the statement that is.
- **The primal-feasibility conjunct is load-bearing, not decoration.** If both programs are
  infeasible, no `y` is dual feasible, so the dual bound holds vacuously at every level while the
  primal attains none **[V, the file says so]**. Pre-empt this; it looks like a wart until
  explained.

### Ships — `StandardForm.lean` (597 lines), split by scalar regime

*Algebraic — should be generalized to `𝕜` before shipping (§5(c)):* `standardFeasibleSet` and its
unfolding lemmas, `convex_standardFeasibleSet`, `IsStandardCertificate`,
`not_isStandardCertificate_of_mem_standardFeasibleSet`,
**`exists_isStandardCertificate_of_not_nonempty`** (Farkas in standard form, hard direction —
reduces to `theorem_of_alternative` plus a division by the positive mass `t`, nothing topological
**[V]**), `not_nonempty_standardFeasibleSet_iff`, `nonempty_standardFeasibleSet_iff`,
`IsStandardOptimal`.

*Genuinely real:* `isClosed_standardFeasibleSet` (topology **[V]**),
`finiteDotContinuousLinearMap` (+`_apply`), and
**`exists_extreme_standardOptimal_of_standardOptimal`** — every attained linear optimum is
attained at an extreme point, *with no boundedness hypothesis*, via the exposed optimal face,
minimum total mass, and Krein–Milman **[V]**.

*In between — order-algebraic argument, generality of mathlib's convexity API over `𝕜` still
unchecked **[B]**:* `mulVec_eq_sum_supportColumns`, `eq_zero_of_extreme_standardFeasible`,
`linearIndependent_supportColumns_of_extreme_standardFeasible`,
`mem_extremePoints_standardFeasibleSet_of_linearIndependent`,
**`mem_extremePoints_standardFeasibleSet_iff`** (extreme points *are* basic feasible solutions)
and **`card_support_le_of_extreme_standardFeasible`** (support bounded by `Fintype.card Row`).

### Does not ship

**`NormalizedFarkas.lean` (125 lines).** A change of coordinates appending a mass row so a cone
becomes a bounded polytope; every theorem is `rfl`, a `simp` unfolding, or a one-liner delegating
to `StandardForm` **[V]**. Its only consumer is `FiniteInequality/Sparse.lean` **[V, grep]**. This
is `kraft`'s `detector_miss_of_pathBudget` case — a named-scenario adapter. It stays here, and
becomes a thin local file over `Mathlib` once the upstream lands.

## 2. The dependency boundary, verified

Checked against actual `import` lines **[V]**:

```
FourierMotzkin.lean    -> Mathlib only
StandardForm.lean      -> Mathlib + FourierMotzkin (private)
Duality.lean           -> Mathlib + StandardForm (public) + FourierMotzkin (private)
NormalizedFarkas.lean  -> StandardForm only
```

**Nothing reaches back into directed-transport.** In Lean a file cannot use what it does not
import, so the import list is proof. No blocker.

One note for §5(c): `Duality.lean` takes a **public** import of `StandardForm.lean`, and
`StandardForm.lean` is where the topology (`KreinMilman`, `ContinuousLinearMap.PiProd`,
`FiniteDimensional.Lemmas`) enters **[V]**. So the `𝕜`-general duality theory currently sits
downstream of Krein–Milman by import even though it uses none of it. That is exactly the import
shape `dupuisf` objected to in #34108, and it is a second, independent reason to do the split.

## 3. What mathlib already has

Searched the pinned `v4.33.1` snapshot (8311 files) for *farkas, fourier-motzkin, theorem of the
alternative, polyhedr, linear program, simplex method, stiemke, gordan, motzkin transposition,
extreme point*, and — new this revision — *complementary slackness, strong duality, weak duality,
dual feasible* **[V]**.

**What exists:**

- `Mathlib/Analysis/Convex/Cone/Dual.lean` — `ProperCone.hyperplane_separation` and
  `hyperplane_separation_point`, both docstringed "**Farkas' lemma**". Statement **[V]**: for a
  proper cone `C` in a locally convex real TVS and a disjoint compact convex `K`, there is
  `f : StrongDual ℝ E` nonnegative on `C`, negative on `K`. Proved from
  `geometric_hahn_banach_compact_closed`. Plus `dual_flip_dual`/`dual_dual_flip`.
- `Mathlib/Analysis/Convex/Cone/InnerDual.lean` — the same in a Hilbert space.
- `Mathlib/Analysis/Convex/Cone/Basic.lean` — `ProperCone`, and the four-item TODO quoted above.
- `Mathlib/Geometry/Convex/Cone/DualFinite.lean` — `PointedCone.DualFG` (H-cones), with
  Minkowski–Weyl named in the docstring and **not proved** **[V]**; its `dual_dual_flip` is the
  free triple-dual identity, not Farkas content **[V]**.
- `Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean` — a *meta* implementation over `ℚ`, with
  the equisatisfiability theorem asserted in a comment and never proved **[V]**. See §5(h).
- `Mathlib/Analysis/Convex/{Extreme,KreinMilman,Exposed,Independent}.lean` — the abstract
  extreme-point API.
- `Mathlib/Analysis/Convex/Caratheodory.lean` — Carathéodory, via *affine* independence in
  `convexHull`.
- `Mathlib/LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean` — mathlib does carry
  LP-adjacent matrix theory.

**Genuinely absent [V — no hits in 8311 files]:**

1. The finite matrix theorem of the alternative, in any form.
2. Any Farkas-type result over a general ordered field. Everything mathlib has is over `ℝ` via
   Hahn–Banach, unavailable over `ℚ` or an arbitrary `LinearOrderedField`.
3. **Weak duality, strong duality, dual attainment, complementary slackness — for linear programs
   or for anything else.** New this revision, and the sharpest finding of the pass: `weak duality`
   and `strong duality` occur **only** in the `Cone/Basic.lean` TODO, and `complementary
   slackness` / `ComplementarySlackness` / `IsDualFeasible` occur **nowhere at all, in any
   spelling** **[V]**. mathlib has no duality gap, no dual program, no slackness condition. This
   is a wholly empty corner.
4. Gordan's transposition theorem, Stiemke, Ville, Motzkin transposition. `Stiemke`, `Ville`,
   `Motzkin transposition`: zero occurrences **[V]**. Gordan needs care — mathlib spends the
   phrase "Gordan's lemma" on an unrelated result at `Mathlib/GroupTheory/Finiteness.lean` line
   626, in the `to_additive` docstring of `Submonoid.fg_eqLocusM` ("When `M` and `N` are `ℕ ^ k`,
   this is also known as a version of **Gordan's lemma**") **[V]**. That is Gordan's lemma on
   affine monoids, not the transposition theorem. The gap stands; the name does not — §5(h).
5. Minkowski–Weyl. Named in a docstring, not proved.
6. Polyhedra as such: no `Polyhedron`, no standard-form set, no basic feasible solution, no
   extreme-point characterization, no sparsity bound. Carathéodory is the nearest neighbour and is
   a different statement.
7. Linear programs, per mathlib's own TODO.

**Would we duplicate anything?** No. The one honest overlap is conceptual: over `ℝ`,
`ProperCone.hyperplane_separation_point` is the geometric form of the same idea. It does not imply
the matrix theorem without separately proving the relevant cone closed, and over `𝕜` it is
meaningless. **Address this head-on in the PR description** — a reviewer who greps "Farkas" finds
that file first.

## 4. Where it would live

Root namespace `DirectedTransport.LinearAlgebra` is dropped.

| Content | File | Namespace |
|---|---|---|
| FM elimination + theorem of the alternative, over `𝕜` | `Mathlib/LinearAlgebra/Matrix/Farkas/FourierMotzkin.lean` | `Matrix` |
| Gordan (later Stiemke/Ville/Motzkin) | `Mathlib/LinearAlgebra/Matrix/Farkas/Transposition.lean` | `Matrix` |
| Standard-form fiber + Farkas in standard form, over `𝕜` | `Mathlib/LinearAlgebra/Matrix/Farkas/StandardForm.lean` | `Matrix` |
| Weak/strong duality, dual attainment, complementary slackness, over `𝕜` | `Mathlib/LinearAlgebra/Matrix/LinearProgramming/Duality.lean` | `Matrix` |
| Closedness, extreme points = BFS, sparsity, attainment, over `ℝ` | `Mathlib/Analysis/Convex/Polyhedron/StandardForm.lean` | `Matrix` |

`Matrix` follows the convention `Matrix.IsTotallyUnimodular` establishes: predicates on a matrix
live in `Matrix`, used with dot notation — `A.standardFeasibleSet rhs`,
`Matrix.IsDualFeasible`. The alternative, a fresh `LinearProgramming` root namespace, is now more
attractive than it was: with a whole duality file in play, `LinearProgramming.IsDualFeasible` reads
better than `Matrix.IsDualFeasible`. **Ask on Zulip before PR 1** rather than deciding
unilaterally; a rename mid-review is expensive and mathlib naming is decided socially. **[B]**

## 5. What has to change first

**(a) Restate over `Matrix` and `mulVec` — still the largest single item.**
`FourierMotzkin.lean` uses `A : I → Fin n → 𝕜` with a bespoke
`rowEval A i x = ∑ j, A i j * x j` **[V]**, while `StandardForm.lean` and `Duality.lean` both use
`Matrix Row Col 𝕜`, `*ᵥ` and `dotProduct` **[V]**. The library is internally inconsistent about
this, and the inconsistency got *more* visible with `Duality.lean`, not less: the repository now
states three LP theorems in matrices and one in raw functions. A reviewer will ask. Touches every
statement in `FourierMotzkin.lean` and a good fraction of the proofs. Mechanical, but do it before
PR 1, not during review.

**(b) Generalize the column index from `Fin n` to an arbitrary `Fintype`.** The induction must run
on `Fin n` — that is the method — but the public statement should read
`{Col} [Fintype Col] (A : Matrix Row Col 𝕜)`, with the `Fin (card Col)` version as the private
engine. The row index is already abstract and the file docstring explains why **[V]**; the same
reasoning applies to columns. Small (a re-indexing wrapper), and now *required* rather than
merely desirable: `StandardForm` and `Duality` are both stated over an abstract `Col` **[V]**,
so without this the two halves of the candidate do not meet.

**(c) The scalar split — VERDICT: still necessary, but cheaper, better motivated, and no longer
the plan's main risk.** The team lead's reading was that `Duality.lean` living in its own
general-field file may make the `StandardForm.lean` split unnecessary. Having read the files: it
does not, and it has in fact created a new reason to do it. Plainly:

1. **The generality claim is now verified where it matters.** `Duality.lean` proves weak duality,
   strong duality, dual attainment and complementary slackness over `𝕜` and *compiles* **[V]**.
   `Mining.md` 1.3 was inspection-only; the duality half is now build-tested. The retreat risk
   in the first draft was overstated and should be downgraded.
2. **But `Duality.lean` bought that generality by defining a second feasibility predicate.** It
   introduces `IsStandardFeasible A rhs z : Prop` over `𝕜` **[V]**, whose relation to the existing
   `standardFeasibleSet A rhs : Set (Col → ℝ)` is `mem_standardFeasibleSet_iff_isStandardFeasible
   := Iff.rfl` **[V]**. Two names for one notion, definitionally equal, differing only in scalars
   and in `Set` versus `Prop`. **This is precisely the "why do we need both" objection #34108
   raised** **[V, from `kraft`'s record]**, and shipping both would invite it in the strongest
   possible form — the `Iff.rfl` is itself the evidence that they are the same thing.
3. **So the split is not avoided; it has been deferred into a duplication.** The upstream fix is
   the one the first draft proposed, and it is now a *smaller* job than it was: generalize
   `standardFeasibleSet` and `IsStandardOptimal` to `𝕜` in place — their definitions need only
   `[Fintype Col]` and the ordered field **[V]** — let the genuinely real theorems keep `ℝ`, and
   then **delete `IsStandardFeasible` entirely**, because `z ∈ A.standardFeasibleSet rhs` already
   says it. `Duality.lean`'s `Iff.rfl` bridge is proof that this substitution is sound.
4. **Independently, the import shape forces it anyway.** §2: `Duality.lean` publicly imports
   `StandardForm.lean`, so `𝕜`-general duality currently sits downstream of Krein–Milman by
   import while using none of it **[V]**.

Net: this item moves from "the plan's biggest technical risk" to "a known, bounded refactor with a
worked precedent." That is a real improvement, and the credit belongs to `Duality.lean`. The one
piece still genuinely unverified **[B]** is whether the extreme-point ⇔ BFS block generalizes —
it leans on mathlib's convexity API at a generality nobody has checked. That block, and only that
block, may have to stay over `ℝ`.

**(d) Add the bridge to mathlib's existing cone API — do this, do not skip it.** Direct transfer
of `kraft`'s most valuable review lesson: the `klFin`/`klDiv` compatibility lemma turned "here is
a second KL divergence" into "here is the elementary API, linked to the measure-theoretic one you
already have." The analogue is a lemma connecting the alternative over `ℝ` to `PointedCone.dual` /
`ProperCone.hyperplane_separation`, and — the prize — deriving **Minkowski–Weyl**
(`PointedCone.FG ↔ PointedCone.DualFG` in finite dimension), which `DualFinite.lean` explicitly
names as unproved **[V]**. Not estimated; a scoping question to answer before PR 3, not a
commitment. If it lands, the series stops being "a new corner of LP theory" and becomes "the
missing theorems in the cone files you already have."

**(e) `Set` / `Finset` at the boundary.** `dupuisf`'s rule: `Set` publicly, `Finset` internally
where sums and cardinality are needed. `standardFeasibleSet : Set (Col → ℝ)` is already right
**[V]**. Two fixes: `card_support_le_of_extreme_standardFeasible` is stated as
`Fintype.card {j : Col // z j ≠ 0} ≤ Fintype.card Row` **[V]** where mathlib would use
`Function.support z` with `Set.ncard` (or a `Finset` under `DecidableEq`) — probably offer both.
And per (c), prefer the `Set` membership `z ∈ A.standardFeasibleSet rhs` over the `Prop`-valued
`IsStandardFeasible` at the public boundary.

**(f) Naming.** `theorem_of_alternative` is not a mathlib name — it describes the theorem instead
of stating it. Mathlib would want `Matrix.not_isFeasible_iff_hasCertificate` (or
`exists_farkasCertificate_iff_not_isFeasible`), with "theorem of the alternative" surviving as
bolded docstring prose. Likewise `feas_cert_disjoint` → `not_hasCertificate_of_isFeasible`, and
the `fm*` abbreviations (`fmA`, `fmB`, `fmRowIndex`) are fine privately but not as public API.
`Duality.lean`'s names are already in the right style **[V]** —
`objective_le_of_isDualFeasible`, `complementarySlackness_iff_objective_eq`,
`exists_isDualFeasible_objective_le_of_forall_le` are all statement-based, and
`exists_rowEval_pos_iff_not_hasBalancedCertificate` shows the convention was applied
deliberately. Only `FourierMotzkin.lean` lags; fix it with (a).

**(g) Header and docstring style.** All four files carry the mathlib copyright header, `module` +
split `public import`/`import`, `@[expose] public section`, and full `## Main definitions` /
`## Main results` blocks **[V]**. `Mathlibify.md` gap 4 notes the `public import` classification
was spot-checked on 7 of 47 files, so these need a real audit — and §2 already found one edge
(`Duality.lean`'s public import of `StandardForm`) that (c) should remove. `Mathlibify.md` gaps 2
and 3 (`have h : ∀ a, …` → `have h (a : A) : …`; `:= by exact` → bare term) are repo-wide; their
share in these four files must be cleared before submission. Gap 5 (arithmetic-tactic density —
`Analysis/Convex` runs `linarith` at 2.63/1k against this library's 10.01/1k **[V, from
`Mathlibify.md`'s census]**) is relevant here specifically: the FM sign-case proofs and
`Duality.lean`'s rescaling arguments are `linarith`-dense **[V]**. Expect "should this be a named
lemma?".

**(h) Two live name collisions — pre-empt both.** Both are with existing mathlib names for
*different* theorems; in each case the fix is a statement-based declaration name plus a docstring
that names the classical theorem and says what it is not.

| Ours | Collides with | Status / treatment |
|---|---|---|
| Gordan's transposition theorem | `Mathlib/GroupTheory/Finiteness.lean` line 626 uses "**Gordan's lemma**" for `Submonoid.fg_eqLocusM` (affine monoids / toric geometry) **[V]** | **Already handled.** Landed as `exists_rowEval_pos_iff_not_hasBalancedCertificate`, docstringed "Gordan's transposition theorem" **[V]** — statement-based, no collision. One thing left: the docstring should add an explicit line distinguishing it from Gordan's lemma on affine monoids, so a reviewer meets the distinction pre-empted rather than raising it. Follow the same shape if Stiemke/Ville/Motzkin ever land. |
| Fourier–Motzkin elimination (PR 1) | `Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean`, a meta implementation over `ℚ` whose equisatisfiability theorem is stated only in a comment **[V]** | Less severe — different directory, `Mathlib.Tactic` unimported by anything mathematical. But a file of that name will already exist, so the PR description should say this is the *mathematical* counterpart of the procedure `linarith`'s oracle implements, and that the theorem the oracle's docstring asserts is now proved. That turns the collision into a selling point. |

Whoever runs the PRs should read this table before naming anything.

## 6. Sequencing and size

Line estimates are *post-rework* (after (a)–(c)). #34108 took a month of back-and-forth for ~400
lines **[V, from `kraft`'s record]** — that is the calibration. The first draft's six-PR sequence
undercounted; this is seven, and the total roughly doubled.

**PR 1 — FM elimination and the theorem of the alternative.** ~450 lines, no prerequisites.
The primal/certificate definitions, `feas_cert_disjoint`, the reduced system, both
feasibility-transfer directions, the certificate lift, and the alternative. One theorem, one
method, one narrative — the whole argument for the series. Largest PR in the plan; if a reviewer
asks for a split the seam is feasibility transfer versus certificate lifting, but do not split
pre-emptively, since the halves are meaningless apart.

**PR 2 — Gordan's transposition theorem.** ~80 lines. Needs PR 1. **Written and compiling
already** **[V]** — this is now a packaging job, not a proof job. Cheap, classically named,
independently notable, and it demonstrates that PR 1's statement is the usable form. Add the
disclaiming docstring line per §5(h) before opening.

**PR 3 — Farkas in standard form, over `𝕜`.** ~230 lines. Needs PR 1 and (b). `standardFeasibleSet`
generalized to `𝕜`, its unfolding lemmas, convexity, `IsStandardCertificate`, both directions,
both `iff` forms. Self-contained narrative ("the other classical statement of Farkas"), and the
point at which §5(d)'s bridge lemma should be attempted if at all.

**PR 4 — LP duality: weak, strong, dual attainment.** ~330 lines. Needs PR 3. `IsDualFeasible`,
`sum_dual_eq_of_isStandardFeasible`, weak duality, `exists_scaledDual_of_not_exists_objective_ge`,
both strong-duality forms, dual attainment. **This is the PR to lead the series' publicity with**
— it answers two of mathlib's four TODO bullets by name, and "mathlib has no LP duality at all" is
a one-sentence justification no reviewer will dispute. The two design choices flagged in §1
(threshold form; the feasibility conjunct) belong in the PR description, not discovered in review.
Note it depends on PR 3 only through `standardFeasibleSet`; if (c) is done properly there is no
topology anywhere in its import closure **[V, after the refactor]**.

**PR 5 — complementary slackness.** ~180 lines. Needs PR 4. The relation, its support form,
`complementarySlackness_iff_objective_eq`, and the two directions making it a certificate of
optimality. Separable from PR 4 with a clean narrative of its own, and small enough to review
fast. Split it out rather than shipping a 510-line duality PR.

**PR 6 — the standard-form fiber is a closed convex set.** ~90 lines. Needs PR 3. First `ℝ`-only
PR, first to import topology. Tiny, and worth keeping separate precisely so that it, not PR 3 or
PR 4, carries the topology imports.

**PR 7 — basic feasible solutions are the extreme points.** ~230 lines. Needs PR 3 (and PR 6 if
(c) retreats to `ℝ` here — the one place it might, §5(c)). Both directions, the `iff`, and the
sparsity corollary. Coherent as one concept; resist splitting, fallback seam is the `iff` versus
the sparsity corollary.

**PR 8 — every attained linear optimum is attained at an extreme point.** ~120 lines. Needs PR 6
and PR 7. The Krein–Milman argument with no boundedness hypothesis. Reviewers will read the
exposed-face / minimum-mass construction carefully; budget more than the line count suggests, as
`kraft` budgeted for `Divergence.Binary`.

| PR | Content | Lines | Needs | Scalars |
|---|---|---|---|---|
| 1 | FM elimination + theorem of the alternative | ~450 | — | `𝕜` |
| 2 | Gordan (written) | ~80 | 1 | `𝕜` |
| 3 | Farkas, standard form | ~230 | 1 | `𝕜` |
| 4 | Weak + strong duality, dual attainment | ~330 | 3 | `𝕜` |
| 5 | Complementary slackness | ~180 | 4 | `𝕜` |
| 6 | Standard fiber is closed | ~90 | 3 | `ℝ` |
| 7 | Extreme points = basic feasible solutions, sparsity | ~230 | 3 (6) | `𝕜`? |
| 8 | Optimum attained at an extreme point | ~120 | 6, 7 | `ℝ` |

PRs 6-8 form an independent `ℝ`/topology track that can run in parallel with PRs 4-5 under a
different reviewer, once PR 3 lands. Not proposed: `NormalizedFarkas.lean` (§1), and §7.

## 7. Secondary candidates

**Still only `LinearAlgebra/`.** Three files were re-examined this pass; all three are no, for
different reasons, and the reasons are worth recording.

**`Switching.lean` (164 lines) — a real gap in mathlib, but not shippable from here.** Zaslavsky
switching and balance for gain graphs, with the main theorem that on a strongly connected graph a
gain is balanced exactly when it is a switching of the trivial gain, plus the torsor-style
uniqueness measure **[V]**. Assessed properly, since it is the most plausible non-LP candidate:

- *Does mathlib have it?* **No.** Searched *gain graph, voltage graph, switching class, Zaslavsky,
  switching equivalence, balanced*: zero relevant hits **[V]**. The only `IsBalanced` in mathlib is
  `RootPairing.IsBalanced` in `LinearAlgebra/RootSystem/`, entirely unrelated **[V]**. mathlib has
  no gain graphs, no voltage graphs, no switching. Genuine gap, with a proper citation already in
  the file (Zaslavsky, *Biased graphs. I*, JCTB 47 (1989) §5) **[V]**.
- *So why not?* **It is blocked behind an infrastructure decision this plan recommends against.**
  `Switching.lean` imports `DirectedTransport.Basic` and `DirectedTransport.Exact`, and `Basic`
  imports `EdgeGraph` **[V]**. It is built on `EdgeGraph`, `Walk`, `walkLabel` and
  `HasTrivialCycleLabels` — none of which ship (see below). Upstreaming it means upstreaming
  `EdgeGraph` first, which would be rejected.
- *Verdict:* the shippable version is a rewrite over mathlib's `Quiver` (or `SimpleGraph` for the
  classical undirected case), which is a **new project, not an extraction**. Worth someone's time
  eventually; not this series, and not by porting this file. Also note the monoid-valued
  generalization — only *unit*-valued vertex functions switch **[V]** — is a genuine strengthening
  over the classical group-valued notion, and would be an argument in that future PR's favour, but
  it also invites "why not just state it for groups?", which needs an answer.

**`EdgeGraph.lean` (322 lines) — no, duplicates `Quiver.Path`.** An `EdgeGraph` is a `Quiver` with
`Hom a b := {e : E // source e = a ∧ target e = b}`, and `Walk` is `Quiver.Path`. Checked
`Mathlib/Combinatorics/Quiver/Path.lean` **[V]**: it already has `Path`, `length`, `length_nil`,
`length_cons`, `comp` with `comp_nil`/`nil_comp`/`comp_assoc`/`length_comp` and four injectivity
lemmas, `Hom.toPath`, `toList` with `toList_comp` and `isChain_toList_nonempty`, plus `Reachable`,
`mapPath`, and a whole `Quiver/` directory. `EdgeGraph.Walk.length`, `.append`, `.singleton`,
`.edges_isChain` are direct duplicates. What it adds — `edges : List E` over a *uniform* edge type,
`edgeMultiplicity`, `exists_splitAtEdge`, `VertexSplit`/`splice` — is real, and real precisely
because a uniform `E` makes the edge list homogeneous where a quiver's is dependent. Genuine design
difference, narrow, and proposing it means proposing a second path type alongside `Quiver.Path` —
the "why do we need both" objection again. Recommend against.

**`Additive/Condensation.lean` (234 lines) — no.** SCC decomposition of lax feasibility. Imports
`DirectedTransport.Additive.Potentials` and `DirectedTransport.SCC` **[V]**, i.e. it sits deep
inside the library's own theory rather than at its edge. It is a specialization of this library's
structure, exactly as `README.md` describes **[V]**. Not general-purpose material.

The remaining prerequisite-layer files (`Circulation`, `TransferSummary`, `ChargedRelation`,
`CyclicMaxAffine`, `InverseCoordinate`) and the rest of the theory proper are specializations too
**[V]**. Not candidates. No padding.

## Summary

- **Is there a PR?** Yes, and a stronger one than the first draft assessed. The candidate is now
  ~1920 lines covering the theorem of the alternative, Gordan, standard-form Farkas, full LP
  duality with complementary slackness, and extreme-point theory — the first four over an
  arbitrary linearly ordered field.
- **Strongest argument.** mathlib's `ProperCone` TODO asks for primal/dual cone programs, weak
  duality, strong duality, and linear programs with LP duality. This library answers the last
  three for LP. And mathlib's only "Farkas' lemma" is a Hahn–Banach separation statement over `ℝ`
  that cannot give the finite matrix theorem over `𝕜`. Sharpest single fact: **complementary
  slackness does not occur anywhere in mathlib, in any spelling.**
- **Biggest blocker.** Not dependencies — the boundary is clean. It is the pre-submission rework:
  restating `FourierMotzkin.lean` in `Matrix`/`mulVec`, generalizing the column index, and
  generalizing `standardFeasibleSet`/`IsStandardOptimal` to `𝕜` so `IsStandardFeasible` can be
  deleted rather than shipped beside them. Behind that sits the strategic risk that a reviewer
  asks for integration with `PointedCone`/`DualFG` rather than a parallel development — §5(d)
  proposes pre-empting it.
- **First PR.** PR 1: Fourier–Motzkin elimination and the theorem of the alternative, ~450 lines,
  `Mathlib/LinearAlgebra/Matrix/Farkas/FourierMotzkin.lean`. PR 4 (duality) is the one to lead the
  series' *publicity* with, but it cannot go first.
