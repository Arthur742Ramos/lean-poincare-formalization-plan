# Independent Bonnet--Myers formalization

This Lean project proves the classical Bonnet--Myers theorem for complete,
connected, smooth finite-dimensional real Riemannian manifolds. If the model
dimension is at least two and

```text
Ric(a,a) >= (n - 1) K g(a,a),   K > 0,
```

then the manifold is compact and its induced extended diameter is at most
`pi / sqrt K`.

The selected theorem is `BonnetMyersEntry.bonnet_myers` in `Solution.lean`.
Its exact independently auditable statement is `BonnetMyersEntry.completeStatement`
in `Challenge.lean`. The Challenge imports only Mathlib, defines the conclusion
using Mathlib's manifold, Riemannian-metric, covariant-derivative, curvature,
trace, completeness, compactness, and diameter vocabulary, and contains one
intentional theorem hole. The Solution imports the proof development and closes
that exact proposition.

## What is proved

The implementation constructs and verifies all geometric bridges required by
the statement rather than assuming them:

- the Levi--Civita connection and its actual curvature commutator;
- geodesic existence and continuation from the geodesic ODE;
- the induced Riemannian distance and a Hopf--Rinow minimizing segment from
  metric completeness;
- parallel transport and a global adapted orthonormal frame;
- chartwise broken variations, differentiation under the integral, and the
  second-variation/index-form identity;
- nonnegativity of the sine test fields along endpoint-minimizing geodesics;
- the Ricci trace contradiction for a geodesic longer than `pi / sqrt K`;
- the sharp diameter bound and compactness.

The theorem does not assert equality rigidity, sphere classification,
finiteness of the fundamental group, or the conjugate-point formulation.
The mathematical result is classical and no novelty or priority claim is made.

## Self-contained submission package

The Solution uses 19 unchanged source files from the same repository's
`curvature/` project at commit
`5db025e6d20d8aad714c3d116714545d1823fd8e`. They are vendored under
`vendor/curvature/` so the selected project builds inside a project-local
sandbox. `scripts/check-vendored.py` checks their exact Git blob identities.
These files provide connection, curvature, bundle-section, and smooth ODE
infrastructure; they do not contain a Bonnet--Myers theorem or its minimizing,
second-variation, Ricci-comparison, diameter, or compactness proof.

The superseded `qinz1yang/differential-geometry` wrapper is retained only as
historical text under `superseded-upstream-wrapper/` and is outside every Lean
library. The active proof neither imports nor copies that implementation.
See `PROVENANCE.md` and `AGENT-CONTRIBUTION.md`.

## Reproduction

Pinned Lean: **4.33.0**. Pinned Mathlib:
`db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
lake exe cache get
lake build
lake env lean --src-deps Challenge.lean
python3 scripts/check-challenge-boundary.py
python3 scripts/check-vendored.py
# With PyYAML==6.0.2 and jsonschema==4.25.1 installed:
python3 scripts/check-package.py
python3 scripts/check-axioms.py
bash scripts/verify-comparator.sh
```

On macOS, the last command requires the explicit local fallback
`PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1`; authoritative sandboxed replay requires
Linux Landlock. Local verification, hosted mechanical verification, editorial
review, intake, and public registration are separate states. Preparing this
package does not authorize a Palomar intake or registration.
The current submission endpoint is <https://submit.palomar-registry.org/>.

## Source

The theorem follows Sumner Byron Myers, “Riemannian manifolds with positive
mean curvature,” *Duke Mathematical Journal* 8(2) (1941), 401--404,
<https://doi.org/10.1215/S0012-7094-41-00832-3>. This project gives an
independent Lean proof of the classical result under the precise scope stated
above.
