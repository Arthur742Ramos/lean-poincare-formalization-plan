# Agent contribution and human oversight

## Agent role

An OpenAI GPT-5-based Codex agent performed material proof engineering and
package preparation under
the maintainer's direction.  This included auditing Mathlib, the repository's
intrinsic Ricci-flow infrastructure, and the overlapping
`qinz1yang/differential-geometry` formalization; selecting the nonduplicative
positive-Einstein equality model; proving the scalar trace and quadratic
barrier identities; proving the exact positivity interval and endpoint metric
obstruction; constructing the Mathlib-only Challenge/Solution boundary; and
preparing deterministic provenance and verification checks.

The agent is not a mathematical author and receives no priority.  All inherited
code remains attributed to its recorded source.  The result is classical.

## Human role

The declared human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz.  Arthur Freitas Ramos is the responsible maintainer
and directed the milestone toward the Poincare/Ricci-flow roadmap.  The human
author team owns the statement, attribution, and any publication decision.
Package preparation does not itself authorize a Palomar intake or registry
publication, and no unrecorded independent human line-by-line review is
claimed.

## Verification boundary

Lean checks the proof term.  Comparator checks the selected theorem and all
Challenge definitions against the independent Challenge module, and NanoDa
replays the exported proof in a second kernel.  Additional scripts check the
Mathlib-only Challenge boundary, source inventory, immutable or reviewed blob
identity, metadata, proof-hole policy, and transitive axiom surface.  These are
mechanical safeguards, not mathematical peer review or editorial acceptance.
