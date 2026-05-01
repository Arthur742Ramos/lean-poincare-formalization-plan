-- Optional aggregate for the Ricci-flow local-existence scaffold.
-- Keep this out of the root target so routine `lake build PoincareCurvature`
-- iterations do not rebuild the heaviest research modules.
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothApproxClosure
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricGaugeFlow
import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOne
import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOneDeTurck
