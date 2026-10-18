# Program semantics and abstract interpretation

Transport can model a control-flow graph whose fibers are concrete states, predicates,
expectations, or abstract domains. Lax sections express inductive invariants and conservative
analyses, while exact sections express compatible assignments. Forward and backward semantics can
be related by adjunctions, and fiberwise logical relations can express soundness of abstraction.

Programming-language semantics, computability, termination, and finite representations supply the
domain-specific structure.

`ProgramSemantics.FiniteReachability` provides an executable saturation analysis for finite
control locations and a common finite state type. It proves agreement with typed-walk execution
and the least direct-image predicate closure, and checks a noninjective Boolean reset example.
Dependent finite state fibers remain a possible extension of this finite-state interface.

`ProgramSemantics.AbstractAnalysis` lifts that finite saturation to infinite concrete state
spaces through an upper simulation. Its generic soundness theorem bounds concrete least closure
and every finite execution by the concretization of the computed abstract reachable states. The
worked parity domain analyzes natural-number instructions that add two or reset noninjectively to
zero, computes only the even cell, and thereby excludes every odd concrete result. The even cell
also contains unreachable values such as `2` at initialization, making the abstraction's loss of
precision explicit.

`ProgramSemantics.Octagon` treats the octagon domain's unit two-variable constraints `±x ± y ≤ c`.
Doubling each variable into a positive and a negative literal turns every constraint into two
edges of a skew-symmetric graph. Over a linearly ordered field the system is feasible exactly when
that graph admits a potential, equivalently when every closed walk has nonnegative total bound.
The integer case is different: `2x ≤ 1` and `-2x ≤ -1` pass the cycle test but have no integer
solution, which is checked in `integer_gap`. Integer tightening and closure algorithms are not
formalized.
