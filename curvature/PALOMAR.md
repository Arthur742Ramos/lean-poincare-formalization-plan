# Palomar Submission 05

## Diffeomorphism transport of connections and curvature

This submission selects the repository's strongest currently proved
manifold-level transport family. For a bundled `C^2` self-diffeomorphism of a
smooth finite-dimensional manifold, the Comparator exposes:

- the tangent-map pushforward and inverse pullback;
- the explicit pulled-back covariant-derivative formula;
- the raw curvature commutator and its pointwise transport;
- the pointwise torsion transport formula;
- preservation of torsion-freeness and metric compatibility; and
- preservation of the Levi–Civita property under the explicit metric
  pullback-inner-product equation.

The exact selected theorems are:

- `PoincareCurvature.Palomar.curvatureAux_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.curvatureAux_pullbackCovariantDerivative_apply`;
- `PoincareCurvature.Palomar.torsion_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.isTorsionFree_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.isMetricCompatibleTangent_pullbackCovariantDerivative`; and
- `PoincareCurvature.Palomar.isLeviCivita_pullbackCovariantDerivative`.

`Challenge.lean` imports only Mathlib and displays the geometric formulas and
hypotheses. `Solution.lean` supplies the matching proofs from the repository's
fully proved `PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeTransport`
module. The mathematical relationship is a standard formalization/adaptation
of classical affine-connection and Riemannian naturality, documented in
`formalization.yaml`; this is not a claim of original mathematical discovery,
Ricci-flow PDE local existence, or Poincare-Conjecture completion.

The superseded coordinate metric-cone/gauge-reduction candidate is historical
only. `AGENT-CONTRIBUTION-04.md` marks that boundary explicitly; it is not the
meaning of the current four-file Comparator surface.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. Use:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`; and
- license: the repository-root `LICENSE` file.

This is a fresh submission for the new geometric transport commit. The prior
Palomar ID is not reused as the registration field.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

For the independent local Comparator/NanoDa replay:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

## External status

This document records local preparation and the intended submission fields.
Local checks do not imply hosted mechanical verification, renderability,
editorial review, registration, or public indexing.
