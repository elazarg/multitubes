# Multitubes

Multitubes is a Lean 4 library for compositional data and constraints on directed multigraphs.
It covers weighted graphs, gain graphs, and flow/circulation identities, then extends them to
graphs whose edges carry arbitrary transformations. It studies how edge data compose along
walks and what paths and cycles imply about potentials, sections, inequalities, fixed points,
and spectra.

The library starts with familiar graph constructions and progressively removes their customary
algebraic assumptions. It includes the classical group-valued gain-graph picture, but does not
require labels to form a group, edge actions to be invertible, or even all vertices to carry the
same type of value.

The Lean package is named `maths`, and its modules live under the `Maths` namespace.

## From weighted and gain graphs to path actions and constraints

The basic graph is a directed multigraph: edges are objects in their own right, so parallel edges
retain their identities. Its finite walks are indexed by both endpoints, making composability
part of the Lean type.

Several increasingly general kinds of edge data can be placed on this graph.

1. **Flows and additive weights.** A walk has an edge-multiplicity vector satisfying flow
   conservation up to its endpoints; a closed walk gives a circulation. If an edge has a weight
   `w e`, a walk has the sum of its edge weights. This leads to cycle sums, difference constraints,
   node potentials, circulation duality, and max-plus spectral theory.
2. **Gains.** If an edge has a label `g e` in a monoid, a walk has the ordered product of its edge
   labels. For group-valued labels this recovers the usual gain-graph and voltage-graph theory:
   balance, switching, and switching-triviality in the sense of Zaslavsky. The formalization also
   proves versions over monoids, using units exactly where inverses are mathematically needed.
3. **Operators.** An edge may act by an arbitrary function rather than by addition or a group
   action. Different vertices may carry different state spaces. Walk labels are then replaced by
   chronological composition of the edge functions.
4. **Relations and mixed constraints.** A chosen value at each vertex may satisfy an equality, a
   forward relation, or the reversed relation on each edge. The relation need not initially be an
   order; ordered, lattice, additive, and residuated results are built as later layers.

The central abstraction is an operator-labelled quiver. Let `G` be a directed multigraph. Each
vertex `v` has a type `F v`, called its fiber, and an edge `e : s → t` carries a function

```text
Tₑ : F s → F t.
```

A walk acts by composing its edge maps in traversal order. A closed walk therefore acts on the
fiber over its base vertex; this action is its holonomy.

A section chooses one value `x v : F v` at every vertex. Depending on the application, an edge
can require

```text
exact:  Tₑ (x s) = x t
lax:    Tₑ (x s) ≤ x t
oplax:  x t ≤ Tₑ (x s).
```

A mixed section chooses one of these three modes independently for each edge. More generally,
`≤` can be replaced by a fiberwise relation `R`; the core definition does not assume that `R` is
an order.

In the ordered picture, a pair of lax and oplax constraints bounds an admissible tube along an
edge, while exact compatibility is the zero-width case. The name *Multitubes* evokes the
interacting tubes of a branching quiver. This is an intuition, not an assumption: the underlying
path action needs no order, and the mixed-constraint layer can use an arbitrary relation.

According to the application, this same object can be read as:

- a representation of the free path category of a quiver;
- a discrete connection, with path transport and holonomy;
- a labelled transition system, with walks as compositional semantics;
- subsolutions, supersolutions, and inductive invariants;
- a gain or voltage graph when labels act on a common fiber;
- a system of additive difference constraints or feasible node potentials;
- a max-plus subeigenvector or eigenvector problem; or
- a max-affine or reflected scalar recurrence.

## Is this the library you are looking for?

It is likely a good fit if you need to formalize one of the following.

| Your problem | Relevant part of the library |
| --- | --- |
| Typed directed walks with parallel edges and composition | [`Maths.Graph.EdgeGraph`](Maths/Graph/EdgeGraph.lean) |
| Walk multiplicities, flow conservation, circulations, and Eulerian realization | [`Maths.Graph.Circulation`](Maths/Graph/Circulation.lean) and [`EulerianTrail`](Maths/Graph/EulerianTrail.lean) |
| Additive difference constraints and cycle feasibility | [`Additive.Potentials`](Maths/Multitubes/Additive/Potentials.lean) and [`Additive.Mixed`](Maths/Multitubes/Additive/Mixed.lean) |
| Gain-graph and voltage-graph switching and balance | [`Maths.Multitubes.Switching`](Maths/Multitubes/Switching.lean) |
| Max-plus cycle means, critical graphs, and eigenvectors | [`Additive.CycleMean`](Maths/Multitubes/Additive/CycleMean.lean), [`CriticalGraph`](Maths/Multitubes/Additive/CriticalGraph.lean), and [`Eigenvector`](Maths/Multitubes/Additive/Eigenvector.lean) |
| Functions between possibly different state spaces along edges | [`Maths.Multitubes.Basic`](Maths/Multitubes/Basic.lean) |
| Path independence, trivial holonomy, or exact-section normal forms | [`Maths.Multitubes.Exact`](Maths/Multitubes/Exact.lean) and [`NormalForms`](Maths/Multitubes/NormalForms.lean) |
| Least solutions of monotone graph inequalities | [`Maths.Multitubes.Closure`](Maths/Multitubes/Closure.lean) |
| Exact, lax, oplax, or per-edge mixed constraints | [`Maths.Multitubes.Mixed`](Maths/Multitubes/Mixed/Basic.lean) |
| Mixed constraints reducible through residuals or adjoints | [`Mixed.AdjointOrder`](Maths/Multitubes/Mixed/AdjointOrder.lean) and [`Mixed.Closure`](Maths/Multitubes/Mixed/Closure.lean) |
| Finite systems of inequalities and infeasibility certificates | [`Maths.Multitubes.FiniteInequality`](Maths/Multitubes/FiniteInequality/Basic.lean) |
| Maps of the form `x ↦ max a (b + c * x)` | [`Maths.Multitubes.MaxAffine`](Maths/Multitubes/MaxAffine/Basic.lean) |
| Affine, max-affine, Loynes, or two-sided clamped recurrences | [`Maths.Recursion`](Maths/Recursion/TransferSummary.lean) and [`ClampedAffineFixedPoint`](Maths/Recursion/ClampedAffineFixedPoint.lean) |
| Fourier–Motzkin elimination, Farkas alternatives, or LP duality | [`Maths.LinearProgramming`](Maths/LinearProgramming/FourierMotzkin.lean) |

This is not intended to replace a general-purpose graph-algorithms package: in particular, it is
not a max-flow/min-cut implementation. Its flow results concern walk multiplicities,
circulations, decomposition, and the certificates used by the transport theory. Likewise, the
core theory is discrete; continuous-time or analytic structure must be supplied by an
application-specific layer.

The [`Applications/`](Applications/) directory contains domain interpretations and downstream
client packages built on the reusable transport specializations. Max-plus and max-affine
transport belong to the library independently of the queueing, stopping, or control models that
may use them.

## How general is the infrastructure?

The assumptions increase only when the mathematics needs them.

| Layer | Required structure |
| --- | --- |
| Graphs, walks, transport, and holonomy | Arbitrary vertex and edge types; arbitrary fiber types and edge functions |
| Exact sections | Equality only |
| Mixed edge constraints | An arbitrary relation on each fiber |
| Propagation of lax or oplax constraints along walks | Preordered fibers and monotone edge maps |
| Path closure and least Bellman majorants | Complete-lattice fibers, with the relevant monotonicity or join preservation |
| Additive potential and cycle criteria | Ordered additive structure; finiteness and cancellation only where stated |
| Gain-graph switching | Monoid labels and unit-valued switching functions; groups recover the classical case |
| Max-affine theory | Real scalar maps with the hypotheses stated by each theorem |

In particular, the generic infrastructure is not restricted to group actions. Group-valued gain
graphs are one specialization. Exact transport works for arbitrary functions, including
noninvertible ones. Mixed transport does not require an order merely to state or manipulate its
edge constraints. Complete lattices, adjoints, finiteness, and scalar algebra enter in separate
theorems rather than in the definition of transport.

## What is formalized

The library includes the following theorem families.

- **Graphs, walks, and flows.** Typed finite walks retain edge identities and encode endpoint
  compatibility. Their edge multiplicities satisfy endpoint-corrected flow conservation; closed
  walks produce circulations. The graph layer also includes Eulerian realization, infinite
  walks, zero-charge lassos, and charged relations.
- **Additive potentials.** For finite edge types, potential feasibility is characterized by
  closed-walk weights under the stated ordered-cancellation assumptions. There are circulation
  duals, strongly connected decompositions, shortest cycle witnesses, quantitative defect
  bounds, and mixed-polarity cycle and path-envelope criteria.
- **Max-plus spectral theory.** The additive layer includes cycle means, Karp's formula, critical
  graphs, Kleene-star generators, subeigenvectors, and eigenvectors.
- **Gain graphs.** Monoid-valued walk labels compose in path order. Switching acts through
  unit-valued vertex functions, balance is switching-invariant, and under the stated connectivity
  hypothesis balance is equivalent to switching-triviality. Groups recover the classical case.
- **Operator-valued walk semantics.** Arbitrary edge functions compose chronologically.
  Transport respects concatenation, and exact, lax, and oplax edge constraints propagate along
  suitable walks.
- **Exact transport.** Trivial holonomy, path independence, rooted and strongly connected normal
  forms, categorical retract formulations, and rigidity of potentials are developed without
  assuming a group of labels.
- **Lax closure.** On complete lattices, joins over all incoming walks give an explicit least lax
  section when edge maps preserve the required joins. For merely monotone maps, a Bellman
  operator gives the least lax majorant as a least fixed point.
- **Mixed polarity.** Lax, exact, and oplax edges share one relation-parametric interface. When
  appropriate residuals exist, reversing and relabelling the oplax edges reduces the system to
  ordinary lax transport, yielding least-majorant and bounded-sandwich criteria. Separately, a
  complete-lattice Bellman interval characterizes mixed sections without assuming residuals.
- **Finite inequalities.** Farkas-style alternatives, quantitative certificates, arithmetic
  consequences, and sparse witnesses are provided for finite systems.
- **Max-affine transport.** Max-affine labels are closed under composition and support path
  summaries, scalar fixed-point classifications, contraction results, gauge feasibility,
  holonomy, duality, relaxation, cycle slack, and spectral results.
- **Related foundations.** Independent modules cover Eulerian trails, circulations, infinite
  walks, zero-charge lassos, charged relations, join-semidirect labels, reflected recurrences,
  Fourier–Motzkin elimination, and standard-form linear-programming duality.

Every source file begins with a module docstring listing its main definitions, results,
assumptions, and deliberate scope. Those docstrings are the most direct API guide once you have
chosen a topic from the table above.

## Using the library

Add the repository to a Lake project:

```toml
[[require]]
name = "maths"
git = "https://github.com/elazarg/multitubes"
rev = "main"
```

For a reproducible project, replace `main` with a commit hash. Then fetch dependencies and build:

```sh
lake update
lake exe cache get
lake build
```

Import only the layer you need. Module names follow the directory path, while declaration names
use shallow namespaces. For example, importing `Maths.Multitubes.Basic` exposes
`Maths.Transport`, and importing `Maths.Graph.EdgeGraph` exposes `Maths.EdgeGraph`.

The structural interface is intentionally narrow:

```lean
import Maths.Multitubes.Basic

#check Maths.EdgeGraph
#check Maths.Transport
#check Maths.Transport.walkMap_append
#check Maths.Transport.IsSection
#check Maths.Transport.IsLaxSection
#check Maths.Transport.IsOplaxSection
```

A complete one-edge example shows the shape of the definitions:

```lean
import Maths.Multitubes.Basic

open Maths

def oneEdgeGraph : EdgeGraph Bool Unit where
  source _ := false
  target _ := true

def successorTransport : Transport oneEdgeGraph (fun _ => Nat) where
  edgeMap _ := Nat.succ

example (x : Bool → Nat) :
    successorTransport.IsLaxSection x ↔ Nat.succ (x false) ≤ x true := by
  constructor
  · intro h
    simpa [oneEdgeGraph, successorTransport] using h ()
  · intro h edge
    cases edge
    simpa [oneEdgeGraph, successorTransport] using h
```

For mixed-polarity constraints:

```lean
import Maths.Multitubes.Mixed.Basic

#check Maths.EdgeMode
#check Maths.Transport.IsMixedSectionFor
```

For the finite-edge additive cycle criterion:

```lean
import Maths.Multitubes.Additive.Potentials

#check Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
```

Use `import Maths` only when you want the complete library. Narrow imports avoid unrelated
algebraic or analytic dependencies and make theorem search more focused.

## Repository layout

Five groups sit under the `Maths` namespace. The first four are reusable foundations built on
mathlib; the Multitubes layer consumes them.

| Directory | Contents |
| --- | --- |
| `Maths/Graph/` | Directed multigraphs, typed walks, circulations, Eulerian trails, infinite walks, zero-charge lassos, and charged relations |
| `Maths/Recursion/` | Affine, max-affine, and clamped-affine summaries, fixed points, and one-sided and two-sided reflections |
| `Maths/LinearProgramming/` | Fourier–Motzkin elimination, alternatives, standard-form LP, sparsity, and duality |
| `Maths/Algebra/` | The join-semidirect label algebra |
| `Maths/Multitubes/` | Generic, exact, lax, oplax, mixed, additive, finite-inequality, gain-graph, and max-affine transport |

The umbrella module [`Maths.lean`](Maths.lean) imports everything. Each group is also a separate
Lake target: `MathsGraph`, `MathsRecursion`, `MathsLinearProgramming`, `MathsAlgebra`, and
`MathsMultitubes`.

[`Applications/`](Applications/) contains domain dossiers. Selected dossiers also contain
independent downstream Lake packages; they import `Maths` without entering its module or
dependency graph.

## Building this repository

The project uses Lean `v4.33.1` and the matching mathlib release, as recorded in
`lean-toolchain` and `lakefile.toml`. The only additional dependency is
[`fixed-point-theorems`](https://github.com/elazarg/fixed-point-theorems-lean4), used for
Brouwer's theorem in the max-affine eigenproblem. No other module depends on it.

```sh
lake exe cache get
lake build
```

The first command downloads precompiled mathlib artifacts; building mathlib locally can take
substantially longer.

## Verification and maturity

The repository is a standalone research library rather than a finished mathlib contribution.
Its public APIs may continue to evolve as the theory develops.

[`scripts/check.sh`](scripts/check.sh) enforces a clean build with zero errors and zero warnings,
checks that no declaration depends on `sorryAx`, resolves names promised by module docstrings,
and checks style and dependency layering. The permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The code follows mathlib conventions, uses mathlib's style linters, and is licensed under the
[Apache License 2.0](LICENSE).
