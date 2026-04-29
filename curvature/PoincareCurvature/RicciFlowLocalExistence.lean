-- Optional aggregate for the Ricci-flow local-existence scaffold.
-- Keep this out of the root target so routine `lake build PoincareCurvature`
-- iterations do not rebuild the heaviest research modules.
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EndpointGaugeFlow
