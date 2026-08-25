# Splitting the library under a `Maths` umbrella

Executed 2026-08-25. This records the split the dependency graph implied, the rename onto a
`Maths` umbrella shared with the author's other projects, and what was deferred.

The repository had grown from a single extracted subtree into 63 files and 2307 declarations,
and a good part of it was no longer about directed transport at all.

## The finding

The import graph was measured, not guessed. **Three groups depend on mathlib alone, are mutually
independent, and contain no directed transport.** A fourth consumes all three.

| group | directory | files | lines | depends on |
| --- | --- | ---: | ---: | --- |
| graph and walk combinatorics | `Maths/Graph/` | 6 | 3068 | mathlib |
| scalar recursions | `Maths/Recursion/` | 6 | 3399 | mathlib |
| linear programming | `Maths/LinearProgramming/` | 4 | 1933 | mathlib |
| label algebra | `Maths/Algebra/` | 1 | 135 | mathlib |
| directed transport proper | `Maths/DirectedTransport/` | 45 | 19227 | all four |

Verified facts behind that table:

* The linear-programming group imports nothing else from the project. Its consumers are the
  three `FiniteInequality/` files and the umbrella. `scripts/check-layering.py` checks this.
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
across `Additive/`, `MaxAffine/` and `LinearProgramming/` alike. Cutting there would slice every
group. Dependency weight is not the right axis; subject matter is.

## The rename

Everything moves under a `Maths` umbrella, shared with the author's other projects. The
directory path carries the taxonomy; namespaces stay shallow, as in mathlib, where
`Mathlib/Analysis/Convex/Cone/Basic.lean` declares `ConvexCone` rather than repeating its path.

```
Maths/Graph/EdgeGraph.lean              namespace Maths.EdgeGraph
Maths/Graph/Circulation.lean            namespace Maths.EdgeGraph.Walk
Maths/Recursion/TransferSummary.lean    namespace Maths.TransferSummary
Maths/LinearProgramming/Duality.lean    namespace Maths.LinearProgramming
Maths/DirectedTransport/Basic.lean      namespace Maths.Transport
```

So `DirectedTransport.MaxAffineTransport` becomes `Maths.MaxAffineTransport`, and
`DirectedTransport.EdgeGraph.Walk` becomes `Maths.EdgeGraph.Walk`: one umbrella swapped for
another, no deeper nesting than today.

`fixed-point-theorems` keeps its own namespace and is not brought under `Maths`.

## Two judgement calls

`ChargedRelation` (680 lines) and `JoinSemidirect` (132) are leaves that fit no group cleanly.
**`ChargedRelation` went to `Maths/Graph/` and `JoinSemidirect` to `Maths/Algebra/`**, on the
reasoning below: a charged relation is a directed graph with edge weights whatever it imports,
and a group holding one honest file beats a file filed where it does not belong.

* `ChargedRelation` carries its own `Path` inductive and deliberately does not import
  `EdgeGraph`, so that it stands alone; that self-containedness was a stated design point when
  the `Closure` unification was declined. Its subject — bounded path budgets are exactly bounded
  potentials — is transport-adjacent but graph-free. Its only consumer is `Additive/Exact`.
  Either `Maths/Graph/` or `Maths/DirectedTransport/` is defensible.
* `JoinSemidirect` is a pure label algebra, `x ↦ floor ⊔ action • x` composing as a semidirect
  product, with no graph and no transport. Its only consumer is `MaxAffine/JoinSemidirect`.
  `Maths/Algebra/` would be the honest home, at the cost of a group holding one file.

This keeps `Maths/DirectedTransport/` meaning *has fibers and transport*, which is the sharper
invariant, and `Maths/Graph/` meaning *path combinatorics*, which `ChargedRelation` is.

## Library targets

Lake's `[[require]]` is package-level, so several `lean_lib` targets in one package share its
dependencies. Splitting therefore buys **build-target granularity and enforced roots**, not
dependency isolation. Since the dependencies here are all under the author's control, that is
the right trade: the value is in the logical boundary, not in what gets fetched.

Targets, each buildable alone, declared with `globs` in `lakefile.toml`:

```
lean_lib MathsGraph               globs = ["Maths.Graph.+"]
lean_lib MathsRecursion           globs = ["Maths.Recursion.+"]
lean_lib MathsLinearProgramming   globs = ["Maths.LinearProgramming.+"]
lean_lib MathsAlgebra             globs = ["Maths.Algebra.+"]
lean_lib MathsDirectedTransport   globs = ["Maths.DirectedTransport.+"]
lean_lib Maths                    -- umbrella importing everything
```

A target building alone is not by itself proof of isolation - it would also build a stray
upward import rather than reject it - so `scripts/check-layering.py` carries that claim.

`Maths.LinearProgramming` earns its own target immediately: it is the material `UpstreamPlan.md`
scopes for mathlib, and a separate target makes "this layer depends on mathlib alone" a fact the
build checks rather than a claim the README makes.

## Sequencing

1. **The layering check came first**, before anything moved, so the move was guarded rather
   than trusted. It gave the same answer after: the linear-programming group closed under
   project imports, and `FixedPointTheorems` reached from one file. Writing it first also found
   the claim was tighter than believed — `MaxAffine/Spectrum` reaches Brouwer transitively, so
   the entry point is `MaxAffine/Eigenproblem` alone.
2. **The rename** went in one mechanical pass over module paths, namespaces and docstrings. The
   drift check is what proved it complete, and it earned its keep: 54 docstring references named
   a *module* rather than a declaration, and the namespace rewrite had silently pointed every one
   of them at a path that no longer existed. The build does not read docstrings and would never
   have complained.
3. **The targets** were created in the same pass, `globs` being the shape Lake accepts here.
4. **`UpstreamPlan.md` was re-pointed** by hand: most of its `LinearAlgebra` mentions are
   mathlib's own paths, which a search-and-replace would have corrupted.

## Deferred

* **Packaging.** Splitting into separate Lake *packages*, rather than libraries, is the only
  thing that would isolate dependencies for a consumer. Not worth doing while every dependency
  is under the author's control.
* **The analysis layer.** If the Cramer/parametric-basis theory lands, it brings real
  analyticity and a selection principle, and would be the first genuinely separable dependency
  cluster. That is the point at which a second package becomes worth its cost, and the
  `## TODO` of `Maths/LinearProgramming/StandardForm.lean` records the argument.
