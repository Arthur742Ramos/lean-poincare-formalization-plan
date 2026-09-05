# Verification of the geometric replacement

The selected theorem is `ContractedBianchi.contractedSecondBianchi`.
The current repair keeps the pointwise orthonormal statement but makes the
Challenge surface independent of the candidate-local `PoincareCurvature`
namespace. Use the final repository SHA recorded at submission time, including
any subsequent metadata corrections.

Verified locally during preparation:

- Solution and dependency build: passed (2,981 jobs).
- Canonical-style direct Lean compile of `Challenge.lean` with only the pinned
  dependency search paths: passed; the only warning is its intentional `sorry`.
- Comparator: passed for the replacement Challenge and Solution.
- NanoDa kernel: accepted the solution.
- Lean default kernel: accepted the solution.
- formalization.yaml: passed the published v0.4 JSON schema.
- MSC codes 53B20, 53C21, and 03B35: present in Palomar's taxonomy.
- The immutable contribution pointer contains the actual document.
- All ten unchanged vendored Lean modules match their recorded source blobs.
- One intentional Challenge proof hole; no Solution or dependency proof holes.

The Challenge imports only Mathlib/core-facing manifold interfaces. The local
`PoincareCurvature` closure is imported only by the Solution-side proof and is
not required to render the Challenge.

The local replay used the explicit macOS Landrun fallback. This does not
claim Linux isolation, Palomar-hosted verification, rendering, editorial
acceptance, or registration. The dedicated GitHub workflow runs the same
pinned verifier with real Landrun on Linux.

## Follow-up audit

The Linux workflow for `7f3a8968e8aad68cfe7ee73746ba8f9e2d348629`
[passed](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/33935112139),
including Comparator, NanoDa, and the Lean kernel. The subsequent documentation
correction makes clear that Solution proves the identity for the supplied
extensions; it does not choose the canonical extension.

`python3 scripts/check-challenge-boundary.py` passes locally. Its negative
control verifies that importing the local proof library fails, then compiles
the real Challenge successfully with the same dependency-only environment.
This regression check is also included in the Linux workflow. It checks
standalone compilation, not the full Palomar HTML renderer.

The anchoring hypothesis is present to identify the supplied fields with the
stated tangent vectors. The finite-sum identity holds more generally, so its
proof does not need anchoring or orthonormality. It does use the connection's
torsion-freeness, metric compatibility, and section regularity. Extension
independence and the Ricci/scalar differentiation bridge remain outside the
selected result; editorial acceptance has not been established.

## Reproduce

On Linux, from this directory:
```sh
lake build
bash scripts/verify-comparator.sh
```

On macOS, explicit development replay:
```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

Pinned tools used by the replay:

- Comparator: `68a064109f01c08f47c8edc9f51d6a2bbffaa188`
- Lean4Export: `15f6055e299ad5b89345e533cc2192f4cc00f659`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`

The verification scripts are copied from the parent project's committed
scripts at `fb31d872f0e70704beac780de9afa6d2b2e94090`; their project root is
resolved relative to their new standalone location.

## Submission identity

Repository: `Arthur742Ramos/lean-poincare-formalization-plan`.
Project directory: `contracted-bianchi`.
Comparator: `contracted-bianchi/comparator.json`.
Metadata: `contracted-bianchi/formalization.yaml`.
Existing ID: blank. Use the final metadata commit. The last resubmission attempt
was rate-limited and created no new intake.
