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
public import Maths.Multitubes.Basic
public import Maths.Multitubes.Mixed.Basic
public import Maths.Multitubes.Mixed.Walk
public import Maths.Multitubes.Mixed.Adjoint
public import Maths.Multitubes.Mixed.Order
public import Maths.Multitubes.Mixed.AdjointOrder
public import Maths.Multitubes.Mixed.Bellman
public import Maths.Multitubes.Category
public import Maths.Multitubes.CategoricalRetracts
public import Maths.Multitubes.CategoricalRetractAdapter
public import Maths.Multitubes.Closure
public import Maths.Multitubes.Relational
public import Maths.Multitubes.RelationalClosure
public import Maths.Multitubes.Mixed.Closure
public import Maths.Multitubes.Exact
public import Maths.Multitubes.SCC
public import Maths.Multitubes.NormalForms
public import Maths.Multitubes.PotentialRigidity
public import Maths.Multitubes.Switching

-- Transport: finite inequality certificates
public import Maths.Multitubes.FiniteInequality.Arithmetic
public import Maths.Multitubes.FiniteInequality.Basic
public import Maths.Multitubes.FiniteInequality.Quantitative
public import Maths.Multitubes.FiniteInequality.Sparse

-- Transport: additive specialization and max-plus spectra
public import Maths.Multitubes.Additive.Budget
public import Maths.Multitubes.Additive.Circuits
public import Maths.Multitubes.Additive.CirculationDecomposition
public import Maths.Multitubes.Additive.Condensation
public import Maths.Multitubes.Additive.CriticalGraph
public import Maths.Multitubes.Additive.CycleMean
public import Maths.Multitubes.Additive.Cycles
public import Maths.Multitubes.Additive.Eigenvector
public import Maths.Multitubes.Additive.Exact
public import Maths.Multitubes.Additive.Mixed
public import Maths.Multitubes.Additive.MixedQuantitative
public import Maths.Multitubes.Additive.Potentials
public import Maths.Multitubes.Additive.Quantitative
public import Maths.Multitubes.Additive.ShortCycles

-- Transport: max-affine specialization
public import Maths.Multitubes.MaxAffine.Additive
public import Maths.Multitubes.MaxAffine.Arithmetic
public import Maths.Multitubes.MaxAffine.Basic
public import Maths.Multitubes.MaxAffine.Contraction
public import Maths.Multitubes.MaxAffine.CycleSlack
public import Maths.Multitubes.MaxAffine.Duality
public import Maths.Multitubes.MaxAffine.Eigenproblem
public import Maths.Multitubes.MaxAffine.Farkas
public import Maths.Multitubes.MaxAffine.FixedPoint
public import Maths.Multitubes.MaxAffine.GaugeFeasibility
public import Maths.Multitubes.MaxAffine.GaugeHolonomy
public import Maths.Multitubes.MaxAffine.JoinSemidirect
public import Maths.Multitubes.MaxAffine.LeastEigenvalue
public import Maths.Multitubes.MaxAffine.Paths
public import Maths.Multitubes.MaxAffine.Relaxation
public import Maths.Multitubes.MaxAffine.Scalar
public import Maths.Multitubes.MaxAffine.Sections
public import Maths.Multitubes.MaxAffine.Slopes
public import Maths.Multitubes.MaxAffine.Sparse
public import Maths.Multitubes.MaxAffine.Spectrum

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

`Maths.Multitubes` is the theory the other four serve: operator-labelled transition
graphs, their walks, holonomy, exact, lax, oplax, and mixed-polarity sections, with categorical and
strongly connected normal forms, complete-lattice closure, gain-graph switching and balance,
additive cycle and circulation duality with its max-plus spectral theory, finite inequality
certificates, and max-affine transport.

Import `Maths.Multitubes.Basic` when only the structural walk semantics -- the
computational graph, walks, holonomy, and sections -- are required.
-/
