# directed-transport

A Lean 4 library for **directed transport** on operator-labelled transition graphs.

## What this is

A directed multigraph supplies a control-flow skeleton: a vertex type, an edge type, and
`source`/`target` maps, with edges as data so parallel edges keep their identities
(`DirectedTransport.EdgeGraph`). Each vertex carries a state space - its **fiber** - and each edge
carries a map from the fiber over its source to the fiber over its target
(`DirectedTransport.Transport`).

A **walk** is an endpoint-indexed finite list of edges, so endpoint compatibility is part of the
type. A walk denotes the chronological composite of its edge maps (`Transport.walkMap`), and
concatenation denotes composition. A closed walk therefore denotes an endomorphism of the fiber
over its base vertex - its **holonomy**. A **section** is a vertex-indexed family that every edge
map carries to itself; on ordered fibers, a **lax section** asks only for an inequality.

The same structure reads several ways, and the library states results in whichever language is
sharpest for the argument:

- as a representation of the free path category of a quiver - spelled out in
  `DirectedTransport.Category`, where walks are morphisms and append is composition;
- as a discrete connection, with `walkMap` as parallel transport and holonomy as monodromy;
- as the action carried by a gain or voltage graph, in the sense of Zaslavsky, once labels are
  group-valued - though general monoid labels are one-directional and need not invert under edge
  reversal;
- as a labelled transition system transforming a per-state value, with `walkMap` as the
  denotational semantics of paths and a lax section as an inductive invariant or subsolution.

On top of that generic layer the library develops specializations, each of which fixes what the
fibers and edge maps are and asks when sections or lax sections exist:

- **exact** (`Exact.lean`, `SCC.lean`, `NormalForms.lean`, `PotentialRigidity.lean`) - equality of
  forward path maps, without assuming labels form a group; strongly connected and rooted-path
  normal forms, and rigidity of the resulting potentials;
- **additive** (`Additive/`) - additive potentials over a linearly ordered field, cycle sums and
  circulation duality, decomposition of feasibility over strongly connected components, and the
  max-plus spectral theory: Karp's cycle mean formula and existence of an eigenvector whose
  eigenvalue is the maximum cycle mean;
- **finite-inequality** (`FiniteInequality/`) - Farkas-style certificates for finite systems;
- **join-semidirect** (`JoinSemidirect.lean`) - labels `(floor, action)` acting by
  `x ↦ floor ⊔ action • x`, composing as a semidirect product;
- **max-affine** (`MaxAffine/`) - edges labelled by `x ↦ max floor (shift + slope * x)`, its
  duality theory and its scalar classifications;
- **gain graphs** (`Switching.lean`) - Zaslavsky's switching action on a monoid-valued labelling,
  balance as a switching invariant, and balance as switching-triviality.

`Closure.lean` supplies the complete-lattice machinery for the lax side: an explicit closure over
all directed walks, and a least lax majorant as the least fixed point of a Bellman operator.

This is a library, not a paper. Individual files state their own scope, and several say plainly
what they deliberately do not develop.

## Layout

Everything lives under `DirectedTransport/`.

**Prerequisite layer** - self-contained material the theory consumes, each usable on its own:

| File | Contents |
| --- | --- |
| `EdgeGraph.lean` | directed multigraphs and the finite-walk calculus |
| `Circulation.lean` | walk multiplicities as flows; conservation and integer charge |
| `TransferSummary.lean` | affine, max-affine, and reflected (Lindley) transfer summaries |
| `ChargedRelation.lean` | bounded path budgets are exactly bounded potentials |
| `CyclicMaxAffine.lean` | a cyclic max-affine system and its survival-weighted bound |
| `InverseCoordinate.lean` | linearizing rational recurrences in the reciprocal coordinate |
| `LinearAlgebra/` | Fourier–Motzkin elimination, the theorem of the alternative, standard-form LP, and LP duality |

**Theory proper** - `Basic.lean` and the other root files for the generic layer and its exact
specialization, then `Additive/`, `FiniteInequality/`, and `MaxAffine/`.

`DirectedTransport/All.lean` is the umbrella importing every module, and the root
`DirectedTransport.lean` re-exports it, so a bare `lake build` compiles the whole library.

## Building

Requires Lean `v4.33.1` (see `lean-toolchain`) and mathlib pinned to the matching `v4.33.1` tag;
`elan` will fetch the toolchain automatically.

```sh
lake exe cache get   # fetch prebuilt mathlib oleans; without this the first build takes hours
lake build
```

**Status.** The extraction is complete. A rebuild from scratch (with `.lake/build` removed)
compiles all 46 modules with zero errors and zero warnings. A kernel-level audit of the 1592
library declarations reports none depending on `sorryAx`, and the only axioms used across the
library are `propext`, `Classical.choice`, and `Quot.sound` - the same three mathlib itself
rests on.

Complete here means ported, building, and sorry-free; it does not mean finished as a mathlib
contribution. Imports have not been pruned to a strict minimal set, the `public import`
classification has been spot-checked rather than audited, and no judgement has been made about
which parts are upstream candidates.

## Style

Style is enforced by mathlib's own linters rather than a bespoke script: `lakefile.toml` turns on
the canonical `linter.style.*` implementations from `Mathlib.Tactic.Linter.*` project-wide, along
with `autoImplicit = false`. They cover the copyright header, the 100-character line limit, the
1500-line file limit, `fun` over `λ`, `<|` over `$`, `·` usage, `cases`/`induction`/`refine`/`show`
forms, whitespace, doc strings, and name checks. A build whose output contains `warning:` is a
failure.

Each option is set with a `weak.` prefix, deliberately. A linter option exists only once a file has
transitively imported the module registering it, so a plain setting would be a hard error in a file
with narrow imports; `weak.` makes it a no-op there instead. The trade-off is that a linter is
silently skipped in a file that does not import it, so a clean build of a narrowly-importing file
is not proof that every check ran.
