# directed-transport

A Lean 4 library for **directed transport** on operator-labelled transition graphs. The
library it builds is called `Maths`; this repository is where it lives.

## What this is

A directed multigraph supplies a control-flow skeleton: a vertex type, an edge type, and
`source`/`target` maps, with edges as data so parallel edges keep their identities
(`Maths.EdgeGraph`). Each vertex carries a state space - its **fiber** - and each edge
carries a map from the fiber over its source to the fiber over its target
(`Maths.Transport`).

A **walk** is an endpoint-indexed finite list of edges, so endpoint compatibility is part of the
type. A walk denotes the chronological composite of its edge maps (`Transport.walkMap`), and
concatenation denotes composition. A closed walk therefore denotes an endomorphism of the fiber
over its base vertex - its **holonomy**. A **section** is a vertex-indexed family that every edge
map carries to itself. A **lax section** and an **oplax section** orient that equality in opposite
directions. A **mixed-polarity section** selects lax, exact, or oplax behavior independently on
each edge, relative to an arbitrary fiberwise relation.

The same structure reads several ways, and the library states results in whichever language is
sharpest for the argument:

- as a representation of the free path category of a quiver - spelled out in
  `Maths.DirectedTransport.Category`, where walks are morphisms and append is composition;
- as a discrete connection, with `walkMap` as parallel transport and holonomy as monodromy;
- as the action carried by a gain or voltage graph, in the sense of Zaslavsky, once labels are
  group-valued - though general monoid labels are one-directional and need not invert under edge
  reversal;
- as a labelled transition system transforming a per-state value, with `walkMap` as the
  denotational semantics of paths and a lax section as an inductive invariant or subsolution.

On top of that generic layer the library develops structural extensions and specializations:

- **mixed polarity** (`Mixed/`) - relation-parametric lax, exact, and oplax edge constraints,
  propagation along walks with a consistent inequality polarity, residual reversal to ordinary
  lax transport when edgewise adjoints exist, least mixed majorants and bounded sandwich
  criteria in that residuated setting, a concise ordered interface, and a complete-lattice
  Bellman interval characterization without residuals;
- **exact** (`Exact.lean`, `SCC.lean`, `NormalForms.lean`, `PotentialRigidity.lean`) - equality of
  forward path maps, without assuming labels form a group; strongly connected and rooted-path
  normal forms, and rigidity of the resulting potentials;
- **additive** (`Additive/`) - finite-edge potential feasibility over ordered cancellative
  additive commutative monoids, cycle sums and circulation duality, decomposition over strongly
  connected components, and, over ordered fields, the max-plus spectral theory: Karp's cycle
  mean formula and an eigenvector whose eigenvalue is the maximum cycle mean;
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

The library is `Maths`, under which four groups depend on mathlib alone and on nothing else
here, and a fifth consumes all four. `scripts/check-layering.py` checks that boundary.

| Directory | Contents |
| --- | --- |
| `Maths/Graph/` | directed multigraphs and the finite-walk calculus; walk multiplicities as flows, with conservation and integer charge; Eulerian trails, infinite walks, zero-charge lassos; and charged relations, where bounded path budgets are exactly bounded potentials |
| `Maths/Recursion/` | affine, max-affine, and reflected (Lindley) transfer summaries and their fixed points; the Loynes and two-sided reflections; a cyclic max-affine system with its survival-weighted bound; and rational recurrences linearized in the reciprocal coordinate |
| `Maths/LinearProgramming/` | Fourier–Motzkin elimination, the theorem of the alternative, standard-form LP, and LP duality |
| `Maths/Algebra/` | the join-semidirect label algebra |
| `Maths/DirectedTransport/` | the theory proper: the generic and mixed-polarity layers, exact transport, and the `Additive/`, `FiniteInequality/`, and `MaxAffine/` specializations |

Namespaces stay shallow: the path carries the taxonomy, so `Maths/Graph/EdgeGraph.lean`
declares `Maths.EdgeGraph`. `Maths.lean` is the umbrella importing every module, so a bare
`lake build` compiles the whole library. Each group is also a Lake target of its own -
`MathsGraph`, `MathsRecursion`, `MathsLinearProgramming`, `MathsAlgebra`,
`MathsDirectedTransport` - so a group can be built without the rest.

## Building

Requires Lean `v4.33.1` (see `lean-toolchain`) and mathlib pinned to the matching `v4.33.1` tag;
`elan` will fetch the toolchain automatically. The only other dependency is
[`fixed-point-theorems`](https://github.com/elazarg/fixed-point-theorems-lean4), which supplies
Brouwer's theorem for the max-affine eigenproblem; nothing else in the library uses it, and the
linear-programming layer in particular depends on mathlib alone.

```sh
lake exe cache get   # fetch prebuilt mathlib oleans; without this the first build takes hours
lake build
```

**Status.** A rebuild from scratch (with `.lake/build` removed) compiles all library modules with
zero errors and zero warnings. A kernel-level audit of the 2454 library declarations reports
none depending on `sorryAx`, and the only axioms used across the library are `propext`,
`Classical.choice`, and `Quot.sound` - the same three mathlib itself rests on. Every one of the
810 names promised by a `## Main ...` docstring section resolves against the compiled
environment. `scripts/check.sh` runs all of this.

Complete here means building and sorry-free; it does not mean finished as a mathlib
contribution.

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
