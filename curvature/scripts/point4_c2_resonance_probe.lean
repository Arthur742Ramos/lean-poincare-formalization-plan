import PoincareCurvature.Analysis.C2Resonance

set_option format.width 180
set_option pp.universes true

#print axioms RicciFlow.C2Resonance.hasDerivAt_profile
#print axioms RicciFlow.C2Resonance.hasDerivAt_profileSlope
#print axioms RicciFlow.C2Resonance.resonant_profile_identity
#print axioms RicciFlow.C2Resonance.tendsto_profile_atBot

#eval IO.println "C2_RESONANCE_TYPES_BEGIN"
#check @RicciFlow.C2Resonance.hasDerivAt_profile
#check @RicciFlow.C2Resonance.hasDerivAt_profileSlope
#check @RicciFlow.C2Resonance.resonant_profile_identity
#check @RicciFlow.C2Resonance.tendsto_profile_atBot
#eval IO.println "C2_RESONANCE_TYPES_END"
