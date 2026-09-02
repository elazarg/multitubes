/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

-- Label algebra
public import Maths.Algebra.JoinSemidirect

-- Graph and walk combinatorics
public import Maths.Graph.EdgeGraph
public import Maths.Graph.Circulation
public import Maths.Graph.EulerianTrail
public import Maths.Graph.InfiniteWalk
public import Maths.Graph.ZeroChargeLasso
public import Maths.Graph.ChargedRelation

-- Scalar recursions
public import Maths.Recursion.TransferSummary
public import Maths.Recursion.AffineFixedPoint
public import Maths.Recursion.LoynesConstruction
public import Maths.Recursion.TwoSidedReflection
public import Maths.Recursion.ClampedAffineFixedPoint
public import Maths.Recursion.InverseCoordinate
public import Maths.Recursion.CyclicMaxAffine

-- Linear programming: Fourier-Motzkin elimination and standard-form duality
public import Maths.LinearProgramming.FourierMotzkin
public import Maths.LinearProgramming.StandardForm
public import Maths.LinearProgramming.Duality
public import Maths.LinearProgramming.NormalizedFarkas

-- Transport: the structural theory
public import Maths.Multitube.Basic
public import Maths.Multitube.Mixed.Basic
public import Maths.Multitube.Mixed.Walk
public import Maths.Multitube.Mixed.Adjoint
public import Maths.Multitube.Mixed.Order
public import Maths.Multitube.Mixed.AdjointOrder
public import Maths.Multitube.Mixed.Bellman
public import Maths.Multitube.Category
public import Maths.Multitube.CategoricalRetracts
public import Maths.Multitube.CategoricalRetractAdapter
public import Maths.Multitube.Closure
public import Maths.Multitube.Mixed.Closure
public import Maths.Multitube.Exact
public import Maths.Multitube.SCC
public import Maths.Multitube.NormalForms
public import Maths.Multitube.PotentialRigidity
public import Maths.Multitube.Switching

-- Transport: finite inequality certificates
public import Maths.Multitube.FiniteInequality.Arithmetic
public import Maths.Multitube.FiniteInequality.Basic
public import Maths.Multitube.FiniteInequality.Quantitative
public import Maths.Multitube.FiniteInequality.Sparse

-- Transport: additive specialization and max-plus spectra
public import Maths.Multitube.Additive.Budget
public import Maths.Multitube.Additive.Circuits
public import Maths.Multitube.Additive.CirculationDecomposition
public import Maths.Multitube.Additive.Condensation
public import Maths.Multitube.Additive.CriticalGraph
public import Maths.Multitube.Additive.CycleMean
public import Maths.Multitube.Additive.Cycles
public import Maths.Multitube.Additive.Eigenvector
public import Maths.Multitube.Additive.Exact
public import Maths.Multitube.Additive.Mixed
public import Maths.Multitube.Additive.MixedQuantitative
public import Maths.Multitube.Additive.Potentials
public import Maths.Multitube.Additive.Quantitative
public import Maths.Multitube.Additive.ShortCycles

-- Transport: max-affine specialization
public import Maths.Multitube.MaxAffine.Additive
public import Maths.Multitube.MaxAffine.Arithmetic
public import Maths.Multitube.MaxAffine.Basic
public import Maths.Multitube.MaxAffine.Contraction
public import Maths.Multitube.MaxAffine.CycleSlack
public import Maths.Multitube.MaxAffine.Duality
public import Maths.Multitube.MaxAffine.Eigenproblem
public import Maths.Multitube.MaxAffine.Farkas
public import Maths.Multitube.MaxAffine.FixedPoint
public import Maths.Multitube.MaxAffine.GaugeFeasibility
public import Maths.Multitube.MaxAffine.GaugeHolonomy
public import Maths.Multitube.MaxAffine.JoinSemidirect
public import Maths.Multitube.MaxAffine.LeastEigenvalue
public import Maths.Multitube.MaxAffine.Paths
public import Maths.Multitube.MaxAffine.Relaxation
public import Maths.Multitube.MaxAffine.Scalar
public import Maths.Multitube.MaxAffine.Sections
public import Maths.Multitube.MaxAffine.Slopes
public import Maths.Multitube.MaxAffine.Sparse
public import Maths.Multitube.MaxAffine.Spectrum

/-!
# Maths

This umbrella imports the whole library.  Five groups sit under it.  The first four depend on
mathlib alone and on nothing else here; the fifth consumes all four.

`Maths.Graph` is the combinatorics of directed multigraphs with edge identities: typed walks,
flow conservation for walk edge multiplicities, Eulerian trails, infinite walks, zero-charge
lassos, and charged relations.  `Maths.Recursion` is the scalar theory of affine and max-affine
transfer summaries: their monoid completion, fixed points, the Loynes and two-sided reflections,
and the cyclic and inverse-coordinate estimates.  `Maths.LinearProgramming` is the theorem of the
alternative by Fourier-Motzkin elimination together with standard-form linear programming --
feasibility, optimality, extreme-point sparsity, and duality.  `Maths.Algebra` carries the
join-semidirect label algebra.

`Maths.Multitube` is the theory the other four serve: operator-labelled transition
graphs, their walks, holonomy, exact, lax, oplax, and mixed-polarity sections, with categorical and
strongly connected normal forms, complete-lattice closure, gain-graph switching and balance,
additive cycle and circulation duality with its max-plus spectral theory, finite inequality
certificates, and max-affine transport.

Import `Maths.Multitube.Basic` when only the structural walk semantics -- the
computational graph, walks, holonomy, and sections -- are required.
-/
