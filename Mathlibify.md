# Mathlibifying `directed-transport`

Investigation note, 2026-08-24. Goal: **mathlib style/structure compatibility**, measured
against what mathlib actually does rather than against folklore.

Method copied from the `kraft` project's `Mathlibify.md`, whose evidence base is a real mathlib
PR review of this author's own code. The single most important lesson carried over is
methodological: **census the pinned mathlib snapshot before "fixing" anything**, because
mathlib's practiced norms sometimes diverge from its stated ones, and a change that moves away
from real mathlib usage is a regression even when a style guide appears to endorse it. In
`kraft` that lesson killed a planned subscript pass over hypothesis names; here it kills a much
larger one (see gap #1 below).

## Evidence base

1. **mathlib PR [#34108](https://github.com/leanprover-community/mathlib4/pull/34108)** review
   comments, as recorded in `kraft`'s `Mathlibify.md` — reviewers `dupuisf`, `vlad902`.
2. **`kraft`'s own review-response commits** (`b3df162`, `cfa8ea0`, `dc259a8`, `d523e4f`,
   `292fea3`, `cf16fdc`, `2fe0408`, `f742ff9`), which show what maintainer feedback turned into
   in practice.
3. **The enforced linters**, read from the pinned `.lake/packages/mathlib/Mathlib/Tactic/Linter/`
   and enabled project-wide in `lakefile.toml`.
4. **A census of the pinned mathlib snapshot** (`v4.33.1`, 8311 files, 2,293,877 lines),
   normalized per 1000 lines so a 18k-line library can be compared with a 2.3M-line one.

## What the PR review actually asked for

- `vlad902`: subscripts for indexed mathematical **objects** (not hypothesis names); prefer
  `have h (a : A) : ...` over `have : ∀ a, ...`; prefer `.mp`/`.mpr` over `.1`/`.2` on `Iff`; a
  proof that is a single `by exact`/`by refine`/`by apply` should just be the term; drop explicit
  types Lean can infer; the 100-char limit is real.
- `dupuisf`: split `public import`s from private `import`s; a broadly useful `private` lemma
  should move to a more general file and become public; `Set` at the public boundary, `Finset`
  internally where sums and cardinality are needed.

## Census: this library vs the pinned mathlib snapshot

Rates are occurrences per 1000 lines, comments stripped.

| metric | mathlib | this library | verdict |
| --- | ---: | ---: | --- |
| bare `simp` | 28.64 | 18.53 | in line (lower) |
| `simp [...]` | 14.21 | 10.23 | in line (lower) |
| `simp only` | 12.12 | 13.41 | in line |
| `simpa` | 8.86 | 9.07 | in line |
| `.mp`/`.mpr` | 8.47 | 9.84 | in line |
| `h.1`/`h.2` on `Iff` | 5.12 | 7.75 | slightly higher |
| `obtain ⟨` | 6.86 | 6.82 | in line |
| `rcases` | 3.80 | 5.17 | slightly higher |
| `:= by refine` | 3.29 | 1.54 | in line |
| `:= by apply` | 1.98 | 2.09 | in line |
| **`have _ : ∀`** | **1.25** | **4.95** | **4x — real gap** |
| **`:= by exact`** | **0.15** | **0.82** | **5.5x — real gap** |
| `linarith` | 0.51 | 10.01 | see gap #5 |
| `nlinarith` | 0.06 | 2.69 | see gap #5 |
| `omega` | 0.09 | 1.43 | see gap #5 |

## Gap census

| # | Gap | Scope | Action |
|---|---|---|---|
| 1 | `simp` discipline | 337 bare `simp`, 186 `simp [...]`, 165 `simpa` | **None — resolved by inaction.** This looks like the biggest number in the repo and is the one item `kraft` explicitly deferred as "a large, diffuse migration". The census says otherwise: this library uses bare `simp` at 18.53/1k against mathlib's 28.64/1k, and `simp only` at 13.41 against 12.12. It is already *more* `simp only`-disciplined than mathlib. Converting these would move away from real mathlib usage, not toward it. |
| 2 | `have h : ∀ a, ...` instead of `have h (a : A) : ...` | 90 sites, 4x the mathlib rate | **Fix.** Directly named in the PR review, and the one proof-style metric where this library is genuinely out of line. |
| 3 | `:= by exact ...` as an entire proof | 15 sites, 5.5x the mathlib rate | **Fix.** Also directly named in the review; should be the bare term. |
| 4 | Import hygiene | Bulk port made every import `public import`; classification spot-checked on 7 of 47 files | **Fix.** `dupuisf`'s comment. An import is public only if a *public* declaration's signature needs it. Also prune imports already implied by another import's closure. |
| 5 | Arithmetic-tactic density | `linarith` 10.01/1k, `nlinarith` 2.69, `omega` 1.43 | **Judgement call, documented not mass-edited.** Compared against the closest mathlib subtree rather than the global average: `Analysis/Convex` runs `linarith` at 2.63/1k, so this library is still ~4x higher than the most inequality-heavy part of mathlib. Not a linter violation and not wrong, but the kind of thing a reviewer flags as "should this be a named lemma?". Treat as proof-mining opportunity in the files that concentrate it, not a sweep. |
| 6 | Dead code and dead hypotheses | Unmeasured | **Audit.** `kraft` review items 1/3/6 were largely this. Note its finding: a hypothesis or instance that *looks* unused may be load-bearing, so removal must be verified by a failing build, never by grep. |
| 7 | Long files | `MaxAffine/Basic.lean` 1073 lines; five more over 650 | **Assess only.** All are under the 1500-line linter limit. `kraft` split a file because it was two unrelated libraries sharing zero declarations, not because of length; apply that test, not a line count. |
| 8a | Docstring drift | 389 declarations named in `## Main definitions`/`## Main results`, all resolve | **None.** Checked mechanically against the compiled environment. This was `kraft`'s review item 4; this library does not have the problem. |
| 8b | Docstring **coverage** | 14 files have a module docstring but no `## Main results`, leaving 159 theorems unadvertised | **Fix.** Missed by the original census, which checked only that *claimed* names exist, never that the main results are claimed at all. Surfaced by the Phase 3 audit: 54 exported theorems have zero internal references precisely because they are terminal results nobody advertises. |
| 9 | Root-namespace leaks | 0 files | **None.** Checked; `kraft` had one (`Sum.lean`). |
| 10 | Object-level ASCII digit indices | 1 identifier (`elim0`, a mathlib name) | **None.** `kraft`'s gap #5 does not appear here. |
| 11 | Hypothesis-name digit suffixes | 80 occurrences | **None — resolved by inaction**, per `kraft`'s gap #6b: mathlib practice favours ASCII `h0`/`h1` over subscripts roughly 7:1. |
| 12 | Naming conventions | 892 theorems, 284 defs, 33 types | **None.** Apparent violations are all correct mathlib style: `def IsSimpleCycle : Prop` is rightly UpperCamelCase, `instMonoid` is rightly an instance name, `IsCoboundary.hasZeroCycleSums` is standard dot-notation. |
| 13 | Provenance leakage | 0 | **None.** No `MathUE`/`UniformEquilibrium`/`GameTheory` references, no repo archaeology of the kind `kraft` had to strip ("probe E57", `experiments/`). |

## Plan

**Phase 1 — the two real proof-style gaps.** Fix #2 (90 sites) and #3 (15 sites). Mechanical
per site but needs care: `have h : ∀ a, P a` becoming `have h (a : A) : P a` changes how `h` is
applied at every use site in that proof.

**Phase 2 — import hygiene (#4).** Per file: confirm every used declaration is directly
imported; downgrade `public import` to `import` where no public signature needs it; drop imports
already in another import's transitive closure. Verify each file individually.

**Phase 3 — dead-code audit (#6).** Unused hypotheses, unused private lemmas, duplicate `have`s,
dead branches. Every removal verified by rebuild.

**Phase 4 — assess #5 and #7.** Report rather than mass-edit.

Throughout: from-scratch rebuild (`rm -rf .lake/build && lake build`) must end at zero errors and
zero warnings, and the kernel-level axiom audit must continue to report zero declarations
depending on `sorryAx`.


## Phase 3 findings (dead-code audit)

Net removals: **zero**. Every candidate was a false positive, which is itself the result.

- **Unused hypotheses on public theorems: provably none.** Lean's default
  `linter.unusedVariables` does flag an unused *named* binder on a theorem (verified with a
  probe: `theorem probeA (x : ℝ) (hx : 0 < x) (hunused : 1 < x) : 0 ≤ x := le_of_lt hx` warns).
  The tree builds at zero warnings, so none exist. `kraft`'s review item 3 was exactly this; here
  it is closed by the compiler rather than by inspection.
- The same probe shows the linter does **not** flag an unused `have`, nor an unused instance
  argument. Those two categories are genuinely invisible and need manual work.
- **Unreferenced declarations: 100 found, none dead.** 43 are `@[simp]` lemmas (used via the simp
  set, never named), 1 is an instance found by typeclass resolution, and the remaining 54 are
  exported terminal results — the things the library exists to provide. Internal reference count
  is not a deadness test for a library's public API. Deleting them would have removed headline
  theorems such as `worstDirectedResidualAtMost_iff_simpleCycles_le`, which is the entire point of
  the file it sits in.
- **A safeguard of mine that was vacuous.** The audit brief said not to delete anything named in a
  `## Main definitions`/`## Main results` section. That offers no protection at all here: anything
  named in a docstring occurs at least twice and therefore cannot appear on an "occurs once" list.
  The 54 at-risk declarations are precisely the exported results that are *not* advertised. Hence
  gap #8b.
- **Unreferenced `have`s: 70 candidates, zero dead.** All are consumed implicitly from the local
  context by a following `linarith`/`field_simp`/`nlinarith`/`omega`/`positivity`. Verified by
  removal: deleting `have hsup := csSup_le …` in `Additive/Potentials.lean` makes the next line's
  `linarith` fail. This is `kraft`'s trap — grep says dead, the build says load-bearing.
- **Unused instance arguments: not closed.** No cheap decisive test exists (under the module
  system `#print` returns `<not imported>` for proof bodies, so only statements are visible).
  Four of the most suspicious cases were tested by removal and all four were load-bearing.
  Closing this properly is ~150 removal-plus-rebuild cycles with low expected yield.

## Import audit results

Audited by the two-step test, with step one automated (downgrade each `public import`, rebuild
that file) and step two by inspection (does the module's content appear in a public signature?).

Of 50 imports tested across `MaxAffine/` and the root files, **44 must stay public** and 2 were
downgraded. The audit's value is concentrated in the disagreements between the two steps: six
imports survived the mechanical downgrade yet genuinely belong in the public block, arriving only
through another import's closure — `Data.List.Rotate`, `Order.WithBot`, `Data.Fintype.Sum`,
`DirectedTransport.Basic` in `Exact.lean`, `GroupTheory.DedekindFinite`, and
`CategoryTheory.Types.Basic`. Two ran the other way, needing to *stay* public because an
`@[expose]`d definition body — not a signature — required them (`Archimedean.Real.Basic` for
`SupSet ℝ`, `Order.FixedPoints` for `OrderHom.lfp`). Neither step alone gets these right.

The root files came out with **no changes at all**: all ten are correctly all-public.
