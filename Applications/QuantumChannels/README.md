# Quantum channels and measurements

The quantum client labels graph edges with positive maps and propagates observable inequalities
along walks in the Löwner order. [Kraus](QuantumTransport/Kraus.lean) treats heterogeneous matrix
spaces. [Discard](QuantumTransport/Discard.lean) proves that trace discard has neither a lower
nor an upper order adjoint in nontrivial finite dimension. Exact sections identify compatible
operators and one-sided sections certify upper or lower bounds. Noncommuting observables can
lack binary joins or meets. Passing to scalar evaluation functions gives pointwise lattice
operations, at the cost of representation by a single observable.

[Instruments](QuantumTransport/Instruments.lean) treats a finite measurement as a family of
completely positive branches whose effects sum to the unit. Sequential composition records the
outcomes in chronological order. Summing the joint effects over the second outcome recovers the
first outcome effect. [InstrumentChannel](QuantumTransport/InstrumentChannel.lean) proves the
finite-outcome C*-algebra version of Theorem 7.6. An instrument is equivalent to one unital
completely positive map on outcome-indexed observables. Testing a tuple supported on one
outcome recovers its branch. The Heisenberg pullback along a forward process walk applies
its observable maps in reverse order. The measurable counterpart of instrument composition is Proposition 7.7
of [Loregian and Lorenzin](https://arxiv.org/abs/2611.32363).

[Detection](QuantumTransport/Detection.lean) studies a repeated measurement with hit branch
`S` and continuation branch `C`. Starting from zero, iterate `H ↦ S(1) + C(H)` to get the
effect `Hₙ` for detection by round `n`. Its increment is the first-hit effect after exactly
`n` continuations. For a normalized instrument, `Hₙ + Cⁿ(1) = 1`. Any positive `B` with
`S(1) + C(B) ≤ B` bounds all horizons. Increasing sequential suprema of effects and their
preservation by `C` suffice for the eventual effect to exist and be the least such bound.
Its complement is the greatest effect `D` satisfying `D ≤ C(D)`, and continuation fixes it.

[QubitDetector](QuantumTransport/QubitDetector.lean) uses the Kraus operators
`diag(3/5, 0)` and `diag(4/5, 1)`. For an initial density matrix `ρ`, the probability of a hit
in the first `n` trials is `(1 − (16/25)ⁿ) ρ₀₀`. It tends to the initial bright population
`ρ₀₀`. The second basis state stays dark, and the bright projection is the least upper
certificate in the full matrix order.

Run `lake build` from this directory to check the client.
