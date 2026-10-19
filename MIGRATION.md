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

UniformEquilibrium, the original downstream client, may continue to refer to the former
repository and module paths until its integration is updated. This note is the temporary record
of that correspondence.
