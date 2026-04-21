import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# PoincareCurvature.Basic

This package currently provides the first concrete curvature-theoretic layer of
the roadmap:

- the section-valued operation `∇_X σ`
- the raw curvature commutator `∇_X∇_Yσ - ∇_Y∇_Xσ - ∇_[X,Y]σ`
- the bundled curvature tensor `curvatureTensor`
- Ricci and scalar curvature contractions on the tangent bundle
- metric compatibility interfaces for Riemannian vector bundles
- torsion-free and Levi-Civita predicates for affine connections
- uniqueness of Levi-Civita connections, expressed as vanishing of the difference one-form

Levi-Civita existence, sectional curvature, and the Bianchi identities still
belong to later milestones.
-/
