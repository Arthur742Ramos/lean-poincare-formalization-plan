# Source history clarification

All three source snapshots and the original reports are retained byte-for-byte.
Frozen-001 was SOURCE REJECT for two composition-basepoint mismatches.
Frozen-002 received SOURCE-ONLY APPROVE in its sealed replacement report and
is superseded by frozen-003. Frozen-003 received final SOURCE-ONLY APPROVE,
report SHA-256 07c9bce974d0fe9b4bf4d7044263bdf520dfeecc018873078674c4481ee4c5fa.
All three remain uncompiled and unverified against exact Lean 4.33/db584.

The author's original handoff said: "Important: frozen-002 was only a superseded intermediate identity, not source-approved; only frozen-003 has SOURCE-ONLY APPROVE."
That historical assertion is incorrect: source-review/replacement-frozen-002/REVIEW.md
explicitly records its source-only approval. This note corrects the assertion
without editing any original author report, source manifest or review.

The author archive received before correction is
poincare-c2-c0-velocity-endpoint-source-reviewed-uncompiled-20261005.zip,
SHA-256 abca9899357a3f3e9f01225f65d793fe4d8198d4945a137431ecc6bb23aa8193,
186135 bytes. A later package is a separate historical identity; this note
does not rewrite the received package or promote source-only approval to
compiler or integration approval.

The author subsequently checked the sealed frozen-002 review, corrected the
handoff, and supplied a separate 190744-byte package, SHA-256
d1d4df3d1e2c524eefe26eeb19490e61a219a8fe68fd0a7970e10f987e0061b3.
The correction confirms frozen-002 SOURCE-ONLY APPROVE, report SHA-256
bf0f8e8e03ed5760ceadeed4edacb506f165b5ffb0befd1257d6a02337b9dc03.
The corrected author report/manifest are retained separately with CORRECTED-
AUTHOR prefixes; the original received records remain unchanged.
