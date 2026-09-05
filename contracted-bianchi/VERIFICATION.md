# Verification of the geometric replacement

The selected theorem is `ContractedBianchi.contractedSecondBianchi`.
The current repair keeps the pointwise orthonormal statement but makes the
Challenge surface independent of the candidate-local `PoincareCurvature`
namespace. The final immutable commit is the commit containing this document;
the exact SHA is recorded by Git at submission time.

Verified locally during preparation:

- Standalone `lake build`: passed (2,981 jobs).
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
Existing ID: blank. Use the final metadata commit, not the implementation
commit above. No new Palomar intake was created by this preparation.
