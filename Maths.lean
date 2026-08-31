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
public import Maths.Recursion.InverseCoordinate
public import Maths.Recursion.CyclicMaxAffine

-- Linear programming: Fourier-Motzkin elimination and standard-form duality
public import Maths.LinearProgramming.FourierMotzkin
public import Maths.LinearProgramming.StandardForm
public import Maths.LinearProgramming.Duality
public import Maths.LinearProgramming.NormalizedFarkas

-- Directed transport: the structural theory
public import Maths.DirectedTransport.Basic
public import Maths.DirectedTransport.Mixed.Basic
public import Maths.DirectedTransport.Mixed.Walk
public import Maths.DirectedTransport.Mixed.Order
public import Maths.DirectedTransport.Mixed.Bellman
public import Maths.DirectedTransport.Category
public import Maths.DirectedTransport.CategoricalRetracts
public import Maths.DirectedTransport.CategoricalRetractAdapter
public import Maths.DirectedTransport.Closure
public import Maths.DirectedTransport.Exact
public import Maths.DirectedTransport.SCC
public import Maths.DirectedTransport.NormalForms
public import Maths.DirectedTransport.PotentialRigidity
public import Maths.DirectedTransport.Switching

-- Directed transport: finite inequality certificates
public import Maths.DirectedTransport.FiniteInequality.Arithmetic
public import Maths.DirectedTransport.FiniteInequality.Basic
public import Maths.DirectedTransport.FiniteInequality.Quantitative
public import Maths.DirectedTransport.FiniteInequality.Sparse

-- Directed transport: additive specialization and max-plus spectra
public import Maths.DirectedTransport.Additive.Budget
public import Maths.DirectedTransport.Additive.Circuits
public import Maths.DirectedTransport.Additive.CirculationDecomposition
public import Maths.DirectedTransport.Additive.Condensation
public import Maths.DirectedTransport.Additive.CriticalGraph
public import Maths.DirectedTransport.Additive.CycleMean
public import Maths.DirectedTransport.Additive.Cycles
public import Maths.DirectedTransport.Additive.Eigenvector
public import Maths.DirectedTransport.Additive.Exact
public import Maths.DirectedTransport.Additive.Potentials
public import Maths.DirectedTransport.Additive.Quantitative
public import Maths.DirectedTransport.Additive.ShortCycles

-- Directed transport: max-affine specialization
public import Maths.DirectedTransport.MaxAffine.Additive
public import Maths.DirectedTransport.MaxAffine.Arithmetic
public import Maths.DirectedTransport.MaxAffine.Basic
public import Maths.DirectedTransport.MaxAffine.Contraction
public import Maths.DirectedTransport.MaxAffine.CycleSlack
public import Maths.DirectedTransport.MaxAffine.Duality
public import Maths.DirectedTransport.MaxAffine.Eigenproblem
public import Maths.DirectedTransport.MaxAffine.Farkas
public import Maths.DirectedTransport.MaxAffine.FixedPoint
public import Maths.DirectedTransport.MaxAffine.GaugeFeasibility
public import Maths.DirectedTransport.MaxAffine.GaugeHolonomy
public import Maths.DirectedTransport.MaxAffine.JoinSemidirect
public import Maths.DirectedTransport.MaxAffine.LeastEigenvalue
public import Maths.DirectedTransport.MaxAffine.Paths
public import Maths.DirectedTransport.MaxAffine.Relaxation
public import Maths.DirectedTransport.MaxAffine.Scalar
public import Maths.DirectedTransport.MaxAffine.Sections
public import Maths.DirectedTransport.MaxAffine.Slopes
public import Maths.DirectedTransport.MaxAffine.Sparse
public import Maths.DirectedTransport.MaxAffine.Spectrum

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

`Maths.DirectedTransport` is the theory the other four serve: operator-labelled transition
graphs, their walks, holonomy, exact, lax, oplax, and mixed-polarity sections, with categorical and
strongly connected normal forms, complete-lattice closure, gain-graph switching and balance,
additive cycle and circulation duality with its max-plus spectral theory, finite inequality
certificates, and max-affine transport.

Import `Maths.DirectedTransport.Basic` when only the structural walk semantics -- the
computational graph, walks, holonomy, and sections -- are required.
-/
