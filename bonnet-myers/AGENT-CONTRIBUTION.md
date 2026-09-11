# Agent contribution and human oversight

## Agent role

Codex performed material proof-engineering and release-preparation work under
the human maintainer's direction. This included auditing the available Mathlib
and same-repository geometry APIs; developing the geodesic, Hopf--Rinow,
parallel-transport, broken-variation, second-variation, Ricci-comparison, and
compactness proof chain; designing the independent Challenge/Solution surface;
and preparing provenance, metadata, and reproducibility checks.

The agent is not a mathematical author and receives no priority. The theorem is
classical, and inherited infrastructure remains attributed to its recorded
repository source and Mathlib contributors.

## Human role

The declared human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human author team owns the mathematical statement
and attribution. Arthur Freitas Ramos selected and directed the theorem scope,
required an independent same-repository proof instead of an external wrapper,
and remains the responsible maintainer for the repository and any publication
decision. Package preparation and automated verification do not authorize
Palomar intake or registration.

## Verification boundary

Lean's kernel checks the implementation. Comparator checks that the Solution
proves the exact theorem and definition exposed by the Mathlib-only Challenge;
NanoDa independently replays the exported proof. Provenance and boundary
scripts additionally check the vendored source identity, Challenge isolation,
metadata, proof-hole policy, and advertised axiom set. These checks are
mechanical evidence, not independent human peer review.
