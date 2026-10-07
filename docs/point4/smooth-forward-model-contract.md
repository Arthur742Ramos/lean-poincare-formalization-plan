# Separate smooth forward model contract

Status: additive interface and supporting lemmas with native development probes. The general smooth
target is OPEN. Canonical Point 4 remains OPEN with its original C² contract.

The selected name is
`RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel`.
Its expected Lean type is
`RicciFlow.SmoothForward.PointFourSmoothForwardModelContract`.
The target declaration is intentionally absent. No imported existence or
uniqueness certificate is an assumption of the expected type.

## Scope and comparison

| Item | Original closed-manifold target | Separate smooth forward target |
| --- | --- | --- |
| Initial metric | Spatial C² | Spatial smooth |
| Competitors | Original weak slice-wise C² class | Same jointly smooth class as solution |
| Time interval | Closed Icc | Half-open Ico |
| Initial derivative | Ordinary HasDerivAt | HasDerivWithinAt on Ici initialTime |
| Model | Arbitrary finite normed real model | Finite real inner-product model |
| Boundary hypothesis | BoundarylessManifold I M | Global I.Boundaryless |
| Rank | No rank restriction | Explicit NeZero finrank |
| Empty manifold | Included | Included; separate genuine construction supplied |
| Initial time | Arbitrary | Arbitrary; upstream zero-time shift remains a bridge |
| Ricci | Repository intrinsic chosen-Levi-Civita Ricci | Same tensor after inner-preserving smooth-to-C² downgrade |

Joint regularity means ContMDiffOn infinity of the metric coefficients in the
actual tangent-bundle chart trivializations, jointly on Ico time times chart
baseSet. The initial endpoint is included. The coefficients are quantified over
every fixed pair of model vectors; this avoids depending on one chosen finite
basis. The finite-basis expansion proving equivalence with upstream chartGramMatrix
is a real, currently unproved API bridge. Chart continuity follows directly from
this joint regularity and is not an additional competitor assumption.

No assertion is made at the terminal endpoint. The all-real metric-family index
does not assert all-real joint regularity, a past-time PDE, or an ordinary initial
derivative. A left metric splice is therefore unnecessary for this target.
Restriction to a shorter positive interval preserves the initial derivative
domain. Rank zero is explicitly excluded from the general model-scoped target;
existing rank-zero canonical results are not silently promoted to this new class.
Empty manifolds are not excluded and admit a constant-family construction by
eliminating the spatial hypotheses, including the PDE and uniqueness quantifiers.

## Qualified source evidence and open bridges

The exact upstream source is qinz1yang/differential-geometry at
8bd406e35c33a200e9b88895cf11ee8429194e15. The existence signature is in
DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/Existence.lean, lines 35–54;
the forward uniqueness signature is in Extension/Construction.lean, lines 125–156.
Both have nonzero finite rank and global model boundarylessness. Uniqueness uses
the real inner-product model and strong joint initial-endpoint regularity.
The upstream historical qualification is Lean 4.29 / Mathlib
8a178386ffc0f5fef0b77738bb5449d50efeea95, not the required Lean 4.33 / Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d port.

The remaining proof milestones are the native source-binding qualification
owned by the parent; exact 4.33 source port; finite-basis regularity equivalence;
literal smooth-to-C² metric and chosen-Levi-Civita Ricci identification; time
translation; and unconditional construction of the separately named package.
The 2,270-module upstream run need not be duplicated here. Its qualified endpoint
signatures do not close any of these bridges.

The proposed supporting modules expose downgrade preservation, interval
restriction, chart continuity, and the genuine empty-manifold package. These
supporting results cannot pass the general-target completion probe. Exact-head
independent mathematical/API review and source rebuild remain required before
publication or completion claims. Copied cache elaboration is development
evidence only. No canonical source, target name, audit, axiom allowlist, fixture
deadline, provenance entry, or historical failure has been changed.

## Native development verification

Official Lean 4.33.0, revision d8b18978322de05a8f3dba51ef03cf5461676c17,
compiled both new modules cleanly on the admitted desktop. The final regularity
source SHA256 is 2e46cea0e6587f803e7d01cda26ea5bdb439d6216ec44b574a87dcae414607a6;
the final contract source SHA256 is
b096fe0ff63b6adc19c344a2239183b3fdb0921cef5a128c30e5cac49da47e30.
The actual signature/axiom probe exited zero. Its six supporting results each
printed precisely propext, Classical.choice and Quot.sound. The completion
probe exited one with four unknown-target errors and no other diagnostics:
the general construction is absent at all tested universes.

These probes used isolated copies of existing artifacts. The required source
closure has 2,965 modules; source/object hashes and all actual compiler argv,
timestamps, exits, peak RSS, and owned process termination are retained in the
desktop task evidence. Inspected source blobs matched the pinned public Mathlib
and repository trees, but the existing artifacts' source binding is unqualified.
This is not a fresh full source rebuild, hosted Linux result or completion audit.
The earlier setup failures and the first failed downgrade elaboration remain
historical. Independent review approved the additive mathematical scope and the
repaired downgrade; exact final integration review and inherited gates remain
required. The separate completion auditor must run in a complete integration
root; its frozen hashes are not independent proof of source binding.
