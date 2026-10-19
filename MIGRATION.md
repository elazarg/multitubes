# Legacy name and imports

Multitubes was previously published as `directed-transport`, with its main modules under
`Maths.DirectedTransport`. The repository is now `multitubes`, and those modules are under
`Maths.Multitubes`; declaration namespaces such as `Maths.Transport` remain unchanged.

## Renamed declarations

| Former name | Current name |
| --- | --- |
| `Maths.MaxAffineTransport.holonomyApply` and its lemmas `holonomyApply_*` | `Maths.MaxAffineTransport.walkApply`, `walkApply_*` |
| `Maths.Transport.IsSectionWithBase` | `Maths.Transport.IsRootedSection` |
| `Maths.Transport.existsUnique_sectionWithBase_iff_pointwise_path_independence` | `Maths.Transport.existsUnique_isRootedSection_iff_pointwise_path_independence` |
| `Maths.Transport.eq_rootedSection_of_isSectionWithBase`, `rootedSection_isSectionWithBase` | `eq_rootedSection_of_isRootedSection`, `rootedSection_isRootedSection` |
| `Maths.MaxAffineTransport.exists_sparse_farkas_certificate` and its rational and integral forms | `exists_sparse_farkasCertificate`, `exists_sparse_rational_farkasCertificate`, `exists_sparse_integral_farkasCertificate` |
| `Maths.TransferSummary.transport` and its lemmas `transport_*` | `Maths.TransferSummary.retentionProd`, `retentionProd_*` |
| `Maths.TransferSummary.pastTransport` and its lemmas | `Maths.TransferSummary.pastRetentionProd` and its lemmas |
| `Maths.Transport.IsResidualFor` | `Maths.Transport.IsLowerAdjointFor` |
| `Maths.MixedAdditiveTransport.translationResidual` and its lemmas | `Maths.AdditiveTransport.translationLowerAdjoint` and its lemmas |
| Module `Maths.Multitubes.MaxAffine.CycleSlack` | `Maths.Multitubes.MaxAffine.CycleRelaxation` |
| `Maths.MaxAffineTransport.Label.HasCyclicSlack` and its lemmas `hasCyclicSlack_*` | `Maths.MaxAffineTransport.Label.IsCyclicRelaxationLevel`, `isCyclicRelaxationLevel_*` |
| `Maths.MaxAffineTransport.Label.cyclicSlackThreshold`, `expansiveCyclicSlackThreshold` | `cyclicRelaxationThreshold`, `expansiveCyclicRelaxationThreshold` |
| `Maths.MaxAffineTransport.Label.IsSlackChain` | `Maths.MaxAffineTransport.Label.IsRelaxedChain` |
| `Maths.MaxAffineTransport.suffixWeight`, `suffixWeightSum`, and their lemmas | `Maths.MaxAffineTransport.suffixSlope`, `suffixSlopeSum`, and their lemmas |
| Module `Maths.Multitubes.MaxAffine.AnchoredEigenvalue` | `Maths.Multitubes.MaxAffine.ReachableLowerBounds` |
| `Maths.LinearProgramming.IsCertificate`, `HasCertificate` | `Maths.LinearProgramming.IsFarkasCertificate`, `HasFarkasCertificate` |
| `Maths.exists_potential_or_nonnegative_incompatibility` | `Maths.FiniteInequality.exists_potential_or_farkasCertificate` |
| `Maths.not_nonnegative_incompatibility_of_potential` | `Maths.FiniteInequality.sum_mul_base_nonpos_of_potential` |
| `Maths.exists_potential_iff_no_nonnegative_incompatibility` | `Maths.FiniteInequality.exists_potential_iff_no_farkasCertificate` |
| `Maths.MaxAffineTransport.exists_isLaxSection_iff_no_nonnegative_certificate` | `Maths.MaxAffineTransport.exists_isLaxSection_iff_no_farkasCertificate'` |
| Namespaces `Maths.MaxPlusPotential`, `Maths.MixedAdditiveTransport`, `Maths.CycleCoboundary` | `Maths.AdditiveTransport`, with the same short names |
| `Maths.finiteInequalityMatrix`, `finiteInequalityMatrix_rowEval`, `finiteInequality_feasible_iff` | `Maths.FiniteInequality.finMatrix`, `rowEval_finMatrix`, `isFeasible_finMatrix_iff` |
| `Maths.exists_potential_or_bellmanResidual_obstruction` | `Maths.FiniteInequality.exists_potential_or_bellmanResidual_obstruction` |
| `Maths.IsStronglyConnectedAt G base` and its lemmas | `Maths.EdgeGraph.IsStronglyConnected G`, the base-free form of mathlib's `Quiver.IsStronglyConnected`; `IsStronglyConnectedAt.nonempty_walk` is the definition itself |
| Module `Maths.Multitubes.Additive.Circuits` | `Maths.Multitubes.Additive.SignedCycles` |
| `circuit` in the names of `Maths.AdditiveTransport` declarations, as in `circuitCoefficient`, `signedCircuitVector`, `IsGenuineSignedCircuit`, `exists_simpleSignedCircuit_decomposition` | `cycle`: `cycleCoefficient`, `signedCycleVector`, `IsGenuineSignedCycle`, `exists_simpleSignedCycle_decomposition` |

UniformEquilibrium, the original downstream client, may continue to refer to the former
repository and module paths until its integration is updated. This note is the temporary record
of that correspondence.
