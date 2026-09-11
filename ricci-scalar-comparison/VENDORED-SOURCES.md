# Vendored curvature dependency inventory

Base repository snapshot:
`Arthur742Ramos/lean-poincare-formalization-plan` commit
`0cc7c31bf6e2dac5c0359a432f3d99803f563017`, directory `curvature/`.
The repository and this package are Apache-2.0 licensed.

`scripts/check-vendored.py` checks the complete 21-file inventory.  Nineteen
files must equal the immutable source Git blobs below.

| Path below `vendor/curvature/` | Source blob |
| --- | --- |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean` | `f51be67d184f62539a2eb048b6d0473f46de8e9b` |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceContinuousDeriv.lean` | `b8da09f25c38ce0da2587aeb886fade977788259` |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurck.lean` | `415fbf897d53cecd35a75cc8ef2a73e8d2928730` |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean` | `4b3105634f0cdd1bb29a51e3815f70af36582401` |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence.lean` | `3d430cddf9790bd71375727570118e3aed74e183` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean` | `5d8a958fbaeb2613f1bfe2e6e6eb020f01adbe00` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Along.lean` | `2cb0c3d13e7d871936b06934ab0524bc4b729fcb` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Bianchi.lean` | `8a485f4e3d713afd12016d09201f9d57981421a4` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Contractions.lean` | `bdd0708ef3bd896028b000907c5c7e801f1f6834` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Raw.lean` | `a9bbfe8933a38543c3568f185d219a7917032e26` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Sectional.lean` | `a92f67c5b271d398532722c13cb6b5a345a80fe1` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean` | `4b887b01c3d90ef1a2b645610f281829c12808a9` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/DowngradeNormFree.lean` | `cb6e05ec51e2933cc563cde4efc6bb1f90b880ac` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Existence.lean` | `6678aacea7247af23f8c24c7bbd2d631bc68d220` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` | `31a79f8cc30b8dbed94396a2575274effbd83f54` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean` | `61c3753bed4bae6d19225c6a46cc1ad7864443b7` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean` | `23d11ea8d2b19bafc1c758ce3107a908486ff1a2` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/HomBundleComp.lean` | `bfdbd06290f24aae86a50b3e7e8d9dff01b4addd` |
| `PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean` | `f250764aa6e576e55a1183e71ca8eafc3f3cfc8c` |

Two files have reviewed elaboration-only adaptations:

| Path | Base blob | Adapted blob |
| --- | --- | --- |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence/EinsteinAux.lean` | `a3cc9e8d6cdbb3892f9e580b7bec6ff7d3bd6713` | `448c02120d88d67c1378bc157fb2dbc8a05810a1` |
| `PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence/Einstein.lean` | `7d26eba94ed9b2d8af809732d72cc4e1770313d9` | `5f0345914aef49ec1b01e970f1279e8f245304e0` |

The exact diffs replace a private derivative helper with public `mvfderiv`
lemmas, disambiguate transported Riemannian inner-product instances, normalize
one real derivative proof, and remove one redundant tactic.  Public theorem
statements are unchanged.  These adapted files carry no proof holes or added
axioms.
