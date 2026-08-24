/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

-- Foundations: graphs, walks, and the label algebras
public import DirectedTransport.JoinSemidirect
public import DirectedTransport.EdgeGraph
public import DirectedTransport.Circulation
public import DirectedTransport.TransferSummary
public import DirectedTransport.ChargedRelation
public import DirectedTransport.CyclicMaxAffine
public import DirectedTransport.InverseCoordinate

-- Linear algebra: Fourier-Motzkin and standard-form LP duality
public import DirectedTransport.LinearAlgebra.Duality
public import DirectedTransport.LinearAlgebra.FourierMotzkin
public import DirectedTransport.LinearAlgebra.NormalizedFarkas
public import DirectedTransport.LinearAlgebra.StandardForm

-- Core structural theory
public import DirectedTransport.Basic
public import DirectedTransport.CategoricalRetractAdapter
public import DirectedTransport.CategoricalRetracts
public import DirectedTransport.Category
public import DirectedTransport.Closure
public import DirectedTransport.Exact
public import DirectedTransport.NormalForms
public import DirectedTransport.PotentialRigidity
public import DirectedTransport.SCC
public import DirectedTransport.Switching

-- Finite inequality certificates
public import DirectedTransport.FiniteInequality.Arithmetic
public import DirectedTransport.FiniteInequality.Basic
public import DirectedTransport.FiniteInequality.Quantitative
public import DirectedTransport.FiniteInequality.Sparse

-- Additive transport: cycles, circulations, potentials, and max-plus spectra
public import DirectedTransport.Additive.Circuits
public import DirectedTransport.Additive.CirculationDecomposition
public import DirectedTransport.Additive.Condensation
public import DirectedTransport.Additive.CycleMean
public import DirectedTransport.Additive.Cycles
public import DirectedTransport.Additive.Eigenvector
public import DirectedTransport.Additive.Exact
public import DirectedTransport.Additive.Potentials
public import DirectedTransport.Additive.Quantitative
public import DirectedTransport.Additive.ShortCycles

-- Max-affine transport
public import DirectedTransport.MaxAffine.Additive
public import DirectedTransport.MaxAffine.Arithmetic
public import DirectedTransport.MaxAffine.Basic
public import DirectedTransport.MaxAffine.CycleSlack
public import DirectedTransport.MaxAffine.Duality
public import DirectedTransport.MaxAffine.Farkas
public import DirectedTransport.MaxAffine.FixedPoint
public import DirectedTransport.MaxAffine.GaugeFeasibility
public import DirectedTransport.MaxAffine.GaugeHolonomy
public import DirectedTransport.MaxAffine.JoinSemidirect
public import DirectedTransport.MaxAffine.Paths
public import DirectedTransport.MaxAffine.Relaxation
public import DirectedTransport.MaxAffine.Scalar
public import DirectedTransport.MaxAffine.Sections
public import DirectedTransport.MaxAffine.Slopes
public import DirectedTransport.MaxAffine.Sparse

/-!
# Directed transport theory

This umbrella imports the whole library.  Import
`DirectedTransport.Basic` instead when only the structural walk semantics --
the computational graph, walks, holonomy, and sections -- are required.

The development covers the generic theory of exact and lax directed transport:
categorical and strongly connected normal forms, complete-lattice closure,
gain-graph switching and balance, additive cycle and circulation duality with
its max-plus spectral theory, finite inequality certificates, join-semidirect
labels, and max-affine transport.

The foundational layer supplies the carriers the theory runs on: directed
multigraphs with edge identities and their typed walks
(`DirectedTransport.EdgeGraph`), flow conservation for walk edge
multiplicities (`DirectedTransport.Circulation`), and the label algebras --
affine and max-affine transfer summaries
(`DirectedTransport.TransferSummary`), charged relations
(`DirectedTransport.ChargedRelation`), and the max-affine cyclic and
inverse-coordinate estimates.  `DirectedTransport.LinearAlgebra` carries the
duality used by the certificate theory: the theorem of the alternative by
Fourier-Motzkin elimination, and standard-form linear programming --
feasibility, optimality, extreme-point sparsity, and duality.
-/
