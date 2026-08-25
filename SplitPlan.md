# Splitting the library under a `Maths` umbrella

Plan, 2026-08-25. Nothing here is executed yet.

The repository has grown from a single extracted subtree into 60 files and 2280 declarations,
and a good part of it is no longer about directed transport at all. This plan records the split
that the dependency graph already implies, a rename onto a `Maths` umbrella shared with the
author's other projects, and what to defer.

## The finding

The import graph was measured, not guessed. **Three groups depend on mathlib alone, are mutually
independent, and contain no directed transport.** A fourth consumes all three.

| group | files | lines | depends on |
| --- | ---: | ---: | --- |
| graph and walk combinatorics | 5 | 2391 | mathlib |
| scalar recursions | 6 | 3399 | mathlib |
| linear programming | 4 | 1933 | mathlib |
| directed transport proper | 44 | 18502 | all three |

Verified facts behind that table:

* `LinearAlgebra/` imports nothing else from the project. Its consumers are the three
  `FiniteInequality/` files and the umbrella.
* The scalar cluster is graph-free: `TransferSummary`, `AffineFixedPoint`, `LoynesConstruction`,
  `TwoSidedReflection` form a closed chain, and `InverseCoordinate` and `CyclicMaxAffine` are
  leaves. None mentions a graph.
* The graph cluster is transport-free: `EdgeGraph` → `Circulation` → {`EulerianTrail`,
  `InfiniteWalk`} → `ZeroChargeLasso`. No fibers, no edge maps.
* Everything else sits above: `Basic` is the only file that turns a graph into transport, and
  `Additive/`, `FiniteInequality/`, `MaxAffine/` are its specializations.

An earlier idea, splitting "generic" from "analysis", does **not** survive contact with the
data. The ten files touching `Mathlib.Analysis` or `Mathlib.Topology` fall into four unrelated
uses — convex geometry, elementary limits, one metric contraction, and exp/log/pow — spread
across `Additive/`, `MaxAffine/` and `LinearAlgebra/` alike. Cutting there would slice every
group. Dependency weight is not the right axis; subject matter is.

## The rename

Everything moves under a `Maths` umbrella, shared with the author's other projects. The
directory path carries the taxonomy; namespaces stay shallow, as in mathlib, where
`Mathlib/Analysis/Convex/Cone/Basic.lean` declares `ConvexCone` rather than repeating its path.

```
Maths/Graph/EdgeGraph.lean              namespace Maths.EdgeGraph
Maths/Graph/Circulation.lean            namespace Maths.EdgeGraph.Walk
Maths/Recursion/TransferSummary.lean    namespace Maths.TransferSummary
Maths/LinearProgramming/Farkas.lean     namespace Maths.LinearProgramming
Maths/DirectedTransport/Basic.lean      namespace Maths.DirectedTransport
```

So `DirectedTransport.MaxAffineTransport` becomes `Maths.MaxAffineTransport`, and
`DirectedTransport.EdgeGraph.Walk` becomes `Maths.EdgeGraph.Walk`: one umbrella swapped for
another, no deeper nesting than today.

`fixed-point-theorems` keeps its own namespace and is not brought under `Maths`.

## Two judgement calls

`ChargedRelation` (680 lines) and `JoinSemidirect` (132) are leaves that fit no group cleanly.

* `ChargedRelation` carries its own `Path` inductive and deliberately does not import
  `EdgeGraph`, so that it stands alone; that self-containedness was a stated design point when
  the `Closure` unification was declined. Its subject — bounded path budgets are exactly bounded
  potentials — is transport-adjacent but graph-free. Its only consumer is `Additive/Exact`.
  Either `Maths/Graph/` or `Maths/DirectedTransport/` is defensible.
* `JoinSemidirect` is a pure label algebra, `x ↦ floor ⊔ action • x` composing as a semidirect
  product, with no graph and no transport. Its only consumer is `MaxAffine/JoinSemidirect`.
  `Maths/Algebra/` would be the honest home, at the cost of a group holding one file.

Neither blocks the split; both should be decided when the move happens rather than argued in
advance.

## Library targets

Lake's `[[require]]` is package-level, so several `lean_lib` targets in one package share its
dependencies. Splitting therefore buys **build-target granularity and enforced roots**, not
dependency isolation. Since the dependencies here are all under the author's control, that is
the right trade: the value is in the logical boundary, not in what gets fetched.

Proposed targets, each buildable alone:

```
lean_lib Maths.Graph
lean_lib Maths.Recursion
lean_lib Maths.LinearProgramming
lean_lib Maths.DirectedTransport   -- requires the three above
lean_lib Maths                     -- umbrella importing everything
```

`Maths.LinearProgramming` earns its own target immediately: it is the material `UpstreamPlan.md`
scopes for mathlib, and a separate target makes "this layer depends on mathlib alone" a fact the
build checks rather than a claim the README makes.

## Sequencing

1. **Enforce the current layering first**, before moving anything: a check that `LinearAlgebra/`
   imports nothing outside itself, and that Brouwer stays confined to `MaxAffine/Eigenproblem`
   and `MaxAffine/Spectrum`. Cheap, and it turns two prose claims into build-checked ones. It
   also guards the move.
2. **Rename onto `Maths`** in one mechanical pass — module paths, namespaces, `All.lean`, and
   every docstring reference. The docstring-drift check must read 0 afterwards; at 711 names it
   is the instrument that proves the rename was complete.
3. **Create the three lower targets**, then the transport target, then the umbrella.
4. **Re-point `UpstreamPlan.md`**, whose file paths and namespace proposals all assume the
   current layout.

Steps 2 and 3 are separable: the rename is worthwhile even if the targets are never split, and
the targets can follow later without further churn.

## Deferred

* **Packaging.** Splitting into separate Lake *packages*, rather than libraries, is the only
  thing that would isolate dependencies for a consumer. Not worth doing while every dependency
  is under the author's control.
* **The analysis layer.** If the Cramer/parametric-basis theory lands, it brings real
  analyticity and a selection principle, and would be the first genuinely separable dependency
  cluster. That is the point at which a second package becomes worth its cost, and the
  `LinearAlgebra/` `## TODO` records the argument.
