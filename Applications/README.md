# Applications

This directory records domain perspectives for Multitubes. Each subdirectory describes the
interpretation a domain can give to its path actions and constraints; domain-specific
developments may live in a separate project.

## Specializations and applications

A **specialization** adds reusable mathematical structure, such as additive weights, complete
lattices, adjoints, or max-affine maps. Its statements are independent of any particular field
and belong in the library.

An **application** supplies domain semantics and domain-specific mathematics. It may use the
library's specializations and can live in an independent Lake package under its dossier or in a
separate client project. Max-affine transport is a specialization, not an application: queueing,
stopping, and control are domains that can use it.

## Domains

| Dossier | Central interpretation |
| --- | --- |
| [Switched and hybrid control](SwitchedHybridControl/) | Lyapunov and storage along dynamics |
| [Riccati equations and filtering](RiccatiFiltering/) | Covariance transport in the Löwner order |
| [Program semantics](ProgramSemantics/) | Invariants, simulations, and predicate transformers |
| [Mathematical morphology](MathematicalMorphology/) | Adjoint morphology on image lattices |
| [Monotone co-design](MonotoneCoDesign/) | Relational functionality and resource feasibility |
| [Cellular sheaves](CellularSheaves/) | Compatible assignments across heterogeneous stalks |
| [Stochastic processes](StochasticProcesses/) | Observable pullback and martingale inequalities |
| [Resource theories](ResourceTheories/) | Monotones on networks of free conversions |
| [Quantum channels](QuantumChannels/) | Positive maps on ordered observables |
| [Data migration](DataMigration/) | Route consistency and adjoint migration |
| [Formal concept analysis](FormalConceptAnalysis/) | Transport among concept lattices |
| [Conic finance](ConicFinance/) | Replication and hedging under set-valued transfers |
| [Coalgebraic refinement](CoalgebraicRefinement/) | Simulations transported by relation liftings |
| [Games and model checking](GamesModelChecking/) | Progress measures and alternating fixed points |
| [Obstacle problems](ObstacleProblems/) | Contact and continuation for two-sided recurrences |
| [Persistence modules](PersistenceModules/) | Compatible elements in noninvertible diagrams |
| [Discrete-event systems](DiscreteEventSystems/) | Max-plus/min-plus closure and residuation |
| [Quantitative relations](QuantitativeRelations/) | Compositional error and privacy grades |
| [Web of trust](WebOfTrust/) | Provenance-aware endorsement and evidence closure |
