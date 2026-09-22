# Stochastic processes and decision models

This client treats a probability kernel as a contravariant transport of
nonnegative extended-real observables. Harmonic observables are exact
sections, while superharmonic and subharmonic observables are lax and oplax
sections. The one-loop specialization proves the corresponding upper and
lower bounds for every finite iterate of the kernel. More generally, a typed
forward walk composes heterogeneous kernels, and its reversed pullback gives
the corresponding path expectation and section bounds.

Using `ℝ≥0∞` makes expectation unconditional, without finiteness or
integrability hypotheses.

`HittingBarrier` adds recursive probabilities for visiting a target by a finite
horizon and their supremum over all finite horizons. A superharmonic observable
that dominates one on the target is a machine-checked upper certificate for both.
The included fair three-state trial verifies a sharp, nontrivial bound of `1 / 2`.
Finite-horizon semantics are certified by identifying the recursion with the target
endpoint probability under the kernel stopped on the target; both finite values and
their supremum are proved at most one. No infinite-trajectory measure is constructed.
