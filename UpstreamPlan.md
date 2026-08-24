# Upstream plan

Proposal, 2026-08-24. Revised after `LinearAlgebra/Duality.lean` and Gordan's transposition
theorem landed, and again after the scalar split of `StandardForm.lean` landed (`c139fba`).
Scoping note only — no migration to mathlib is proposed as done.

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
| LP duality | Absent; noted only as mathlib's TODO | **`Duality.lean`, 499 lines** **[V]**, over `𝕜` with no `ℝ` at all. Two more TODO bullets answered. |
| Mining 1.3 (general-`𝕜` route) | Inspection-only **[B]**, flagged as the plan's main retreat risk | **Done and build-tested throughout** **[V]**. Risk retired — see §5(c). |
| The scalar split of `StandardForm.lean` | Specified as the largest remaining technical risk | **Landed in `c139fba`** **[V]**. Only two declarations still need `ℝ`. |
| Extreme points ⇔ basic feasible solutions over `𝕜` | **[B]**, "may have to stay over `ℝ`" | **[V]** — generalized, and it went through |
| `IsStandardFeasible` / `standardFeasibleSet` duplication | Identified as the strongest available objection to the series | **Gone.** `IsStandardFeasible` deleted **[V]** |
| `FourierMotzkin.lean` | 622 lines | 690 lines (Gordan) **[V]** |
| Total candidate | ~1350 lines | ~1933 lines **[V]** |

Nothing in either earlier draft turned out *wrong*. The one place the plan was too pessimistic is
now corrected: §5(c)'s `[B]`-graded worry that the extreme-point block might be stuck over `ℝ` did
not materialize. The one place it was too optimistic stands uncorrected: the PR sequence has grown
from six to eight, and the total roughly doubled.

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

### Ships — `Duality.lean` (499 lines), arbitrary linearly ordered field

The most immediately *wanted* file in the candidate. `𝕜`-general throughout **[V]** — and now
uniformly so: since `standardFeasibleSet` generalized, the `ℝ`-only transfer section and its
`Iff.rfl` bridge are gone, and primal feasibility is spelled `z ∈ standardFeasibleSet A rhs`
everywhere **[V]**.

| Declaration | What it states |
|---|---|
| `IsDualFeasible` | `Aᵀ *ᵥ y ≥ c`, no sign constraint on `y` |
| `sum_dual_eq_of_isStandardFeasible` | the objective expanded through the equality constraint |
| **`objective_le_of_isDualFeasible`** | **weak duality** |
| `exists_scaledDual_of_not_exists_objective_ge` | the sharp hypothesis-free form: an unreachable level is witnessed by a *scaled* dual `(y, lam)`, `lam ≥ 0` — a genuine dual point when `lam > 0`, a Farkas certificate of infeasibility when `lam = 0` |
| **`exists_objective_ge_iff_feasible_and_forall_isDualFeasible`**, `exists_objective_ge_iff_forall_isDualFeasible` | **strong duality**, as a threshold equivalence at every level `t` |
| **`exists_isDualFeasible_objective_le_of_forall_le`** | **dual attainment** |
| `ComplementarySlackness`, `complementarySlackness_iff_forall_ne_zero` | the relation, and its support form |
| **`complementarySlackness_iff_objective_eq`** | complementary slackness ⇔ zero duality gap |
| `forall_le_of_complementarySlackness`, `exists_isDualFeasible_complementarySlackness_of_forall_le` | complementary slackness is exactly a certificate of optimality |
| `isStandardOptimal_of_complementarySlackness`, `exists_isDualFeasible_complementarySlackness_of_standardOptimal` | optimality in the sense of `IsStandardOptimal`: complementary slackness certifies it, and every optimum carries such a certificate. Over `𝕜` **[V]** |

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

### Ships — `StandardForm.lean` (619 lines), already split by scalar regime

The split is no longer a proposal. It is a fact about the file **[V, read against `c139fba`]**,
and the algebraic side turned out **larger** than the first draft scoped: the entire extreme-point
theory generalized, which the plan had graded **[B]** and flagged as the one block that might be
stuck over `ℝ`.

*Over `𝕜` — `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, `[Fintype Col]` **[V]**:*
`standardFeasibleSet` and its unfolding lemmas (`mem_`, `nonneg_of_mem_`,
`mulVec_apply_of_mem_`), `convex_standardFeasibleSet`, `IsStandardCertificate`,
`not_isStandardCertificate_of_mem_standardFeasibleSet`,
**`exists_isStandardCertificate_of_not_nonempty`** (Farkas in standard form, hard direction —
reduces to `theorem_of_alternative` plus a division by the positive mass `t`, nothing topological),
`not_nonempty_standardFeasibleSet_iff`, `nonempty_standardFeasibleSet_iff`, `IsStandardOptimal`,
**and the whole basic-feasible-solution block**: `mulVec_eq_sum_supportColumns`,
`eq_zero_of_extreme_standardFeasible`,
`linearIndependent_supportColumns_of_extreme_standardFeasible`,
`mem_extremePoints_standardFeasibleSet_of_linearIndependent`,
**`mem_extremePoints_standardFeasibleSet_iff`** (extreme points *are* basic feasible solutions, now
`(standardFeasibleSet A rhs).extremePoints 𝕜 ↔ … LinearIndependent 𝕜 …`) and
**`card_support_le_of_extreme_standardFeasible`** (support bounded by `Fintype.card Row`, via
`fintype_card_le_finrank` over `𝕜`).

*Genuinely real — exactly two theorems plus one definition **[V]**:*
`isClosed_standardFeasibleSet` (topology), `finiteDotContinuousLinearMap` (+`_apply`, which is
continuous-linear-map API and real by construction), and
**`exists_extreme_standardOptimal_of_standardOptimal`** — every attained linear optimum is
attained at an extreme point, *with no boundedness hypothesis*, via the exposed optimal face,
minimum total mass, and Krein–Milman.

That two-declaration residue is the cleanest possible outcome for the upstream split: the
`ℝ`-and-topology file is small enough that it plausibly reviews in a single sitting.

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

**Re-verified after `c139fba`: the import shape is unchanged, and the note still stands.**
`Duality.lean` still takes a **public** import of `StandardForm.lean`, and `StandardForm.lean`
still imports `Mathlib.Analysis.Convex.KreinMilman`,
`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd`, `Mathlib.Data.Real.Basic` and
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` **[V]**. So `𝕜`-general duality still sits
downstream of Krein–Milman by import while using none of it — exactly the shape `dupuisf`
objected to in #34108.

**But the fix has changed character, and is now trivial.** Before the merge this needed the
generalization work; now the scalar boundary runs *inside* `StandardForm.lean` as a section
boundary, with only two theorems and one definition on the real side (§1). So the remaining step
is a pure file split at upstream time — no proof changes — after which PR 4 (duality) imports the
algebraic file only and its import closure contains no topology at all. This is now bookkeeping in
the sequencing (§6), not a technical risk. It is worth stating in the PR description that the
algebraic file has no topological dependency, because that is the kind of claim `dupuisf` checks.

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
| Extreme points = BFS, sparsity, over `𝕜` | `Mathlib/LinearAlgebra/Matrix/Farkas/BasicFeasible.lean` | `Matrix` |
| Closedness and Krein–Milman attainment, over `ℝ` | `Mathlib/Analysis/Convex/Polyhedron/StandardForm.lean` | `Matrix` |

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

**(c) The scalar split — DONE (`c139fba`). Risk retired.** This item was the plan's largest
remaining technical risk across two drafts. It has landed, and it landed better than the plan
predicted. Recording the reasoning as well as the outcome, because a mathlib reviewer reading this
plan should see *why* it had to happen — the argument is the same one they would have made.

*Why it had to happen.* `Duality.lean` originally bought its `𝕜`-generality by defining a second
feasibility predicate, `IsStandardFeasible A rhs z : Prop` over `𝕜`, whose relation to the
existing `standardFeasibleSet A rhs : Set (Col → ℝ)` was
`mem_standardFeasibleSet_iff_isStandardFeasible := Iff.rfl`. Two names for one notion,
definitionally equal, differing only in scalars and in `Set` versus `Prop`. That is precisely the
"why do we need both" objection #34108 raised **[V, from `kraft`'s record]**, and it would have
arrived in its strongest possible form, since the `Iff.rfl` is itself the proof that the two are
the same thing. The fix was not to justify the pair but to remove the need for it: generalize the
`Set` and let the `Prop` go.

*What landed **[V, verified against the merged files]**:*

1. `standardFeasibleSet`, `IsStandardOptimal`, `IsStandardCertificate`, the unfolding lemmas,
   `convex_standardFeasibleSet` and both directions of standard-form Farkas are over `𝕜`, needing
   only `[Fintype Col]` and `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`.
2. **The extreme-point ⇔ basic-feasible-solution block generalized too** — the item this plan
   graded **[B]** and named as the one place it might have to retreat to `ℝ`.
   `mem_extremePoints_standardFeasibleSet_iff`,
   `linearIndependent_supportColumns_of_extreme_standardFeasible`,
   `eq_zero_of_extreme_standardFeasible`, `mulVec_eq_sum_supportColumns` and
   `card_support_le_of_extreme_standardFeasible` are all over `𝕜`. mathlib's convexity API was
   general enough after all; `card_support_le_…` now goes through `fintype_card_le_finrank` at
   `(R := 𝕜) (M := Row → 𝕜)`. **Upgrade to [V].**
3. Only `isClosed_standardFeasibleSet` and `exists_extreme_standardOptimal_of_standardOptimal`
   still require `ℝ`, plus `finiteDotContinuousLinearMap` and its `_apply`, which are
   continuous-linear-map API.
4. `IsStandardFeasible` is deleted, its 19 uses in `Duality.lean` replaced by
   `z ∈ standardFeasibleSet A rhs`, and the `Iff.rfl` bridge is gone with it. `Duality.lean` now
   contains no `ℝ` at all **[V]**.
5. Nothing outside `DirectedTransport/LinearAlgebra/` needed touching.

*What this buys upstream.* The strongest available objection to the series is gone rather than
answered. The `ℝ`-and-topology residue is two theorems, which makes the real-scalar PR small
enough to review in one sitting (§6, PR 6/8). And the dependency order improved: PR 7 no longer
needs PR 6 (§6). The only thing left is the file split itself, which is now bookkeeping — see §2.

Net: this item moves from "the plan's biggest technical risk" to "done, verified, and no longer a
line item." Nothing in (c) remains **[B]**.

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
The second — preferring the `Set` membership `z ∈ standardFeasibleSet A rhs` over a `Prop`-valued
feasibility predicate at the public boundary — is **done** as part of (c) **[V]**, and is the
shape `dupuisf` asked for.

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

Line estimates are *post-rework* (after (a) and (b); (c) is done, so its share is now real line
counts rather than estimates). #34108 took a month of back-and-forth for ~400 lines **[V, from
`kraft`'s record]** — that is the calibration.

Two things changed here with `c139fba`. PR 3 no longer carries the generalization as prerequisite
work — it ships the file as it stands. And **the dependency order genuinely improved**: PR 7
(basic feasible solutions) no longer needs PR 6 (closedness), because it no longer needs `ℝ` at
all. That converts the sequence from one long chain into two tracks that fork after PR 3, with
only the final PR needing both.

```
PR 1 -> PR 2
  \--> PR 3 --> PR 4 --> PR 5          (algebraic track, all over 𝕜)
        |  \--> PR 7 -------\
        \----> PR 6 ---------> PR 8    (real track, topology only)
```

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

**PR 3 — Farkas in standard form, over `𝕜`.** ~200 lines. Needs PR 1 and (b). `standardFeasibleSet`,
its unfolding lemmas, convexity, `IsStandardCertificate`, both directions, both `iff` forms, and
`IsStandardOptimal`. **Already over `𝕜` [V]** — the generalization that was this PR's prerequisite
is done, so this is now an extraction, not a rewrite. Self-contained narrative ("the other
classical statement of Farkas"), and the point at which §5(d)'s bridge lemma should be attempted
if at all. This PR is the fork point of the sequence: PRs 4 and 6/7 all descend from it and are
independent of each other.

**PR 4 — LP duality: weak, strong, dual attainment.** ~330 lines. Needs PR 3. `IsDualFeasible`,
`sum_dual_eq_of_isStandardFeasible`, weak duality, `exists_scaledDual_of_not_exists_objective_ge`,
both strong-duality forms, dual attainment. **This is the PR to lead the series' publicity with**
— it answers two of mathlib's four TODO bullets by name, and "mathlib has no LP duality at all" is
a one-sentence justification no reviewer will dispute. The two design choices flagged in §1
(threshold form; the feasibility conjunct) belong in the PR description, not discovered in review.
It depends on PR 3 only through `standardFeasibleSet`, and after the file split of §2 there is no
topology anywhere in its import closure — the file itself now contains no `ℝ` at all **[V]**.

**PR 5 — complementary slackness.** ~180 lines. Needs PR 4. The relation, its support form,
`complementarySlackness_iff_objective_eq`, the two directions making it a certificate of
optimality, and the two `IsStandardOptimal` corollaries (over `𝕜` now, not `ℝ` **[V]**). Separable
from PR 4 with a clean narrative of its own, and small enough to review fast. Split it out rather
than shipping a ~500-line duality PR.

**PR 6 — the standard-form fiber is closed.** ~60 lines. Needs PR 3. `isClosed_standardFeasibleSet`
and `finiteDotContinuousLinearMap` (+`_apply`). First and only real-scalar infrastructure PR, and
smaller than the first draft estimated, since convexity went with PR 3. Worth keeping separate
precisely so that it, and nothing earlier, carries the topology imports.

**PR 7 — basic feasible solutions are the extreme points.** ~230 lines. Needs **PR 3 only** — the
dependency on PR 6 is gone, since the whole block generalized to `𝕜` **[V, §5(c)]**. Both
directions, the `iff`, and the
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
| 3 | Farkas, standard form | ~200 | 1 | `𝕜` |
| 4 | Weak + strong duality, dual attainment | ~320 | 3 | `𝕜` |
| 5 | Complementary slackness | ~180 | 4 | `𝕜` |
| 6 | Standard fiber is closed | ~60 | 3 | `ℝ` |
| 7 | Extreme points = basic feasible solutions, sparsity | ~230 | **3** | **`𝕜`** |
| 8 | Optimum attained at an extreme point | ~120 | 6, 7 | `ℝ` |

Once PR 3 lands, three things can run in parallel under different reviewers: PRs 4-5 (duality),
PR 7 (basic feasible solutions), and PR 6. Only PR 8 needs two inputs. Six of the eight PRs are
now entirely over `𝕜` and free of topology — worth saying out loud in the series description,
since import weight is what `dupuisf` reviewed on. Not proposed: `NormalizedFarkas.lean` (§1),
and §7.

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

- **Is there a PR?** Yes, and a stronger one than either earlier draft assessed. The candidate is
  ~1933 lines covering the theorem of the alternative, Gordan, standard-form Farkas, full LP
  duality with complementary slackness, and extreme-point theory — **all of it over an arbitrary
  linearly ordered field except two theorems** (`isClosed_standardFeasibleSet` and the
  Krein–Milman attainment result) **[V]**.
- **Strongest argument.** mathlib's `ProperCone` TODO asks for primal/dual cone programs, weak
  duality, strong duality, and linear programs with LP duality. This library answers the last
  three for LP. And mathlib's only "Farkas' lemma" is a Hahn–Banach separation statement over `ℝ`
  that cannot give the finite matrix theorem over `𝕜`. Sharpest single fact: **complementary
  slackness does not occur anywhere in mathlib, in any spelling.**
- **Biggest blocker.** Smaller than it was. Not dependencies — the boundary is clean; and no
  longer the scalar split, which has landed (§5(c)). What remains is the pre-submission rework of
  `FourierMotzkin.lean`: restating it in `Matrix`/`mulVec` (§5(a)) and generalizing the column
  index off `Fin n` (§5(b)). Both are mechanical and confined to one file. Behind that sits the
  one strategic risk left: a reviewer asking for integration with `PointedCone`/`DualFG` rather
  than a parallel development — §5(d) proposes pre-empting it.
- **First PR.** PR 1: Fourier–Motzkin elimination and the theorem of the alternative, ~450 lines,
  `Mathlib/LinearAlgebra/Matrix/Farkas/FourierMotzkin.lean`. PR 4 (duality) is the one to lead the
  series' *publicity* with, but it cannot go first.
