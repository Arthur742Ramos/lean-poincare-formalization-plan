import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFixedBackgroundProducer

-- Print the complete inferred type to expose all geometric and source-space
-- premises, and check the proof's actual trusted axiom dependencies.
set_option pp.all false in
#check @RicciFlow.AnalyticPDE.exists_fixedBackground_actualLocalTensorHeat
#print axioms RicciFlow.AnalyticPDE.exists_fixedBackground_actualLocalTensorHeat
