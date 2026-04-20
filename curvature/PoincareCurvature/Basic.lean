import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw

/-!
# PoincareCurvature.Basic

This package currently provides the first concrete layer of the curvature roadmap:

- the section-valued operation `∇_X σ`
- the raw curvature commutator `∇_X∇_Yσ - ∇_Y∇_Xσ - ∇_[X,Y]σ`

The actual curvature tensor, Levi-Civita existence/uniqueness, metric compatibility,
and curvature contractions belong to later milestones.
-/
