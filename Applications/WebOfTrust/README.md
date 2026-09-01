# Web of trust

A web of trust can be read as directed transport of evidence. Vertices are identities, keys,
organizations, or trust contexts. An edge is an endorsement, certification, delegation, or
referral. Its map describes what evidence at the source can establish at the target; composing
edge maps gives the semantics of an endorsement chain.

The useful separation is between three operations:

- **transport**, which extends one piece of evidence across one endorsement;
- **constraint**, which requires a global assignment to retain every locally justified result;
- **aggregation**, which combines evidence arriving through different chains.

For set-valued evidence, a sound assignment is a lax section:

```text
transfer e (evidence at source e) ⊆ evidence at target e.
```

When transfers preserve arbitrary unions, path closure is the least sound assignment containing
the chosen root evidence. Membership in that closure has a direct certificate: some trusted
source and some typed endorsement chain transport a seed record to the requested record.

Evidence records may retain issuers, subjects, capabilities, signatures, confidence, and the
principals contributing to their provenance. This avoids collapsing the model prematurely to a
single score. Fibers may vary by trust context, and transfers may be noninvertible or relational.
Scalar attenuation and max-product trust remain available as simpler specializations.

The wider directed-transport vocabulary suggests further models. Holonomy describes circular
endorsement and possible self-amplification. Graded relations measure confidence loss along a
chain. Residuals support backward queries asking what source evidence would suffice for a target
claim. Exact, lax, and oplax modes can distinguish delegation, lower evidence guarantees, and
upper policy constraints; negative evidence should generally be represented explicitly rather
than identified with the opposite inequality.

Cryptographic validity, revocation, time, identity resolution, Sybil resistance, collusion, and
independence requirements are separate semantics. Policies such as requiring several distinct
introducers need evidence records that retain those introducers, or a richer aggregation layer;
they do not follow from scalar path propagation alone.
