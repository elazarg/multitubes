# Domain terminology audit

Baseline: `bead025`. The question is whether every abstract concept has an identified
domain-specific meaning or name. The answer is partial: the basic transport interfaces have
strong translations, several capstones now have formal semantic bridges, and the higher
constructions have uneven domain coverage. There is no justified concept-by-domain coverage
percentage: neither the concept inventory nor the applicable pairs had been fixed beforehand.

The reader-facing results are [Applications/CONCEPTS.md](../Applications/CONCEPTS.md) and
[the core dictionary](../Applications/THEORY_DICTIONARY.md).
They cover concept families and all 19 application dossiers, distinguishing proved adapters,
mathematical interpretations, and prospective applications. It is not a claim that every
declaration has a special name in every field. A missing familiar name can be harmless; a
missing interpretation or missing hypotheses can hide an actual application gap.

The subsequent [application-result transfer study](application-result-transfers-2026-09-22.md)
identifies known theorems that could move from application fields into transport and back.

## Findings

1. **The core dictionary is real.** Exact sheaf compatibility, harmonic and superharmonic
   observables, inductive predicates, least reachability, covariance bounds, and optimal
   max-plus schedules have explicit definitions or equivalence theorems in the applications.
   Their mathematical content is substantially more precise than a resemblance of terminology.
2. **Direction is part of the translation.** Control storage and stochastic expectation pull
   values back against physical transitions. Program direct image and morphological dilation
   go forward; predicate inverse image and erosion go backward. The word “lax” alone cannot
   determine whether a domain author would call a value an upper bound or a decreasing quantity.
3. **Aggregation changes the statement.** Edgewise exactness requires every equation. Bellman
   equality requires equality after joining incoming demands. Demands zero and one can have
   Bellman value one although the first edge is loose. Exact schedules should therefore be
   called eigen-schedules, not exact edge sections.
4. **Path closure needs its hypotheses.** Arbitrary-join preservation identifies the explicit
   join over walks with the least lax majorant. Mere monotonicity still gives the latter on
   complete lattices, but does not justify that identification. This matches the distinction
   between path and fixed-point solutions in
   [Cousot's abstract interpretation account](https://www.di.ens.fr/~cousot/AI/).
5. **Domain names sometimes overstate the model.** A transition-nonincreasing storage family
   alone does not prove stability; an expectation inequality is not a constructed martingale;
   an arbitrary Kraus family is not automatically trace preserving; nested fixed-point order
   is not edge polarity. The public dictionary records these qualifications next to the terms.
6. **The higher concepts need selective translation.** A categorical retract has a precise
   split-image meaning, but “sufficient statistic,” “consistency quotient,” and “lossless
   compression” require additional domain theorems. Likewise, a sparse obstruction need not
   be a minimum inconsistent subsystem, and a branch policy need not be a game strategy.
7. **Four dossiers have no compiled domain model.** Data migration, formal concept analysis,
   persistence modules, and resource theories have plausible dictionaries but no client
   formalizing their central category, context, persistence, or monoidal structures.

## A useful identification: sensor fitting

For an edge from sensor s to sensor t, write its residual as
`targetScale * x(t) - sourceScale * x(s) - offset`. The uniform-tolerance problem minimizes
the largest absolute residual over all readings. This is exactly the finite
**Chebyshev approximation**, **minimax affine fitting**, or **infinity-norm approximation**
objective described by [Boyd and Vandenberghe, slide 6.3][chebyshev]. The identification follows
by matching the objective; it is not a claim that a named external approximation interface
has been imported into Lean.

The current formal bridges are `isConsistent_iff_realRowInequalities` and
`exists_uniformlyConsistent_iff_worstResidual`. The minimum is attained, and matching primal
readings and normalized balanced dual weights certify it. Thus the sensor capstone is also a
checked finite minimax fitting result for this graph-structured affine matrix family.
It is not least-squares estimation, the Chebyshev-center problem, or a uniqueness theorem
for the fitted reading. For zero edges the objective has the natural value zero.

[chebyshev]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf

The phrase “sheaf consistency radius” needs more care. In
[Robinson's definition](https://arxiv.org/abs/1805.08927), the radius measures disagreement
of a supplied assignment. Here the minimum is over readings, and the discrepancy compares
the two endpoint restrictions directly. Identifying these constructions requires fixing the
assignment convention and discrepancy normalization; the names alone do not establish equality.

Dual balance cancels all reading variables. With unit source and target scales this has a
signed flow-conservation interpretation after combining the two row signs. With arbitrary
scales it is weighted linear balance, so an ordinary cycle-flow explanation is not automatic.
No new theorem or claim of literature novelty is made by these interpretations.

## Priorities after the dictionary

1. **Keep semantic adapters visible.** Each new application concept should supply its carrier,
   physical versus transport direction, domain predicate, formal bridge when available, and
   boundary conditions. Put familiar search terms in the application documentation rather than
   proliferating synonyms in the core API.
2. **Connect the sensor objective to a reusable approximation interface if one is needed.**
   The existing signed-row and worst-residual equivalences already justify the mathematics.
   A new norm-level adapter would improve discovery and interoperability; it need not reproduce
   the optimization proof. General scalar affine fitting beyond graph-structured rows remains
   a separate client of the existing finite-inequality theory.
3. **Interpret certificates at the level of the actual model.** Control certificates reject
   comparison-radius budgets; sensor certificates reject tolerance feasibility. Neither
   conclusion alone diagnoses a faulty physical subsystem. Support-minimal explanations,
   identifiability, and residual sensitivity are separate useful endpoints.
4. **Develop higher concepts where a domain question demands them.** Retract reduction could
   serve interface compression, and holonomy could serve loop consistency, but both need an
   explicit statement of what information or observable is preserved. Do not fill every empty
   dictionary cell with an analogy.
5. **Give prospective dossiers a semantic core before counting their terminology as proved.**
   A persistence section is a compatible family, not a barcode; an order adjunction is not by
   itself a formal context or a categorical data-migration construction.

## Changes and validation

Added a public concept and domain dictionary and linked it from the application index.
The new dictionary corrects the older landscape's unqualified path-closure identification
and unsupported compression terminology; the older local survey is not the current inventory.
Updated index descriptions to match implemented semantics. No Lean statement, definition, algorithm, or proof changes in this review.

`bash scripts/check.sh` passed from clean state; log:
`/tmp/multitubes-domain-dictionary-check.log`. All 84 core modules and 15 application packages
rebuilt with zero errors and warnings. All 16 kernel audits found zero sorry-dependent or
forbidden-axiom declarations. All 1,428 indexed names and 191 prose references resolved; layering,
checker regressions, line-length and option checks passed. Local Markdown links and named
application declarations were checked against their sources. `git diff --check` passed.
