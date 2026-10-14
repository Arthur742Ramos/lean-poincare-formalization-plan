import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffinePullback

-- Source-only whole-signature and empty-dimension probe; native qualification pending.
open scoped BigOperators Topology
open RicciFlow.AnalyticPDE

abbrev ExpectedCertifiedAffineC2Pullback :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)), EuclideanBoundedC2Data m

def certifiedAffineC2PullbackFullSignatureAssignment : ExpectedCertifiedAffineC2Pullback :=
  @EuclideanBoundedC2Data.precompAffine

abbrev ExpectedAffineC2ValueIdentity :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ),
      (D.precompAffine a L).value x = D.value (a + L x)

def affineC2ValueIdentityFullSignatureAssignment : ExpectedAffineC2ValueIdentity :=
  @EuclideanBoundedC2Data.precompAffine_value_apply

abbrev ExpectedAffineC2FirstIdentity :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k : Fin m) (x : Fin m → ℝ),
      (D.precompAffine a L).first k x =
        ∑ p : Fin n, L (Pi.single k 1) p * D.first p (a + L x)

def affineC2FirstIdentityFullSignatureAssignment : ExpectedAffineC2FirstIdentity :=
  @EuclideanBoundedC2Data.precompAffine_first_apply

abbrev ExpectedAffineC2SecondIdentity :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k l : Fin m) (x : Fin m → ℝ),
      (D.precompAffine a L).second k l x =
        ∑ p : Fin n, ∑ q : Fin n,
          (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x)

def affineC2SecondIdentityFullSignatureAssignment : ExpectedAffineC2SecondIdentity :=
  @EuclideanBoundedC2Data.precompAffine_second_apply

abbrev ExpectedAffineC2ValueBound :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)),
      ‖(D.precompAffine a L).value‖ ≤ ‖D.value‖

def affineC2ValueBoundFullSignatureAssignment : ExpectedAffineC2ValueBound :=
  @EuclideanBoundedC2Data.norm_precompAffine_value_le

abbrev ExpectedAffineC2FirstBound :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k : Fin m),
      ‖(D.precompAffine a L).first k‖ ≤
        ∑ p : Fin n, |L (Pi.single k 1) p| * ‖D.first p‖

def affineC2FirstBoundFullSignatureAssignment : ExpectedAffineC2FirstBound :=
  @EuclideanBoundedC2Data.norm_precompAffine_first_le

abbrev ExpectedAffineC2SecondBound :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k l : Fin m),
      ‖(D.precompAffine a L).second k l‖ ≤
        ∑ p : Fin n, ∑ q : Fin n,
          |L (Pi.single k 1) p * L (Pi.single l 1) q| * ‖D.second p q‖

def affineC2SecondBoundFullSignatureAssignment : ExpectedAffineC2SecondBound :=
  @EuclideanBoundedC2Data.norm_precompAffine_second_le

-- The constructor permits empty source and target independently.
example {n : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin 0 → ℝ) →L[ℝ] (Fin n → ℝ)) : EuclideanBoundedC2Data 0 :=
  D.precompAffine a L

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) : EuclideanBoundedC2Data m :=
  D.precompAffine a L

example (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) : EuclideanBoundedC2Data 0 :=
  D.precompAffine a L

-- Empty-source transport still carries its actual derivative proof fields.
example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) (k : Fin m) (x : Fin m → ℝ) :
    HasDerivAt (fun r => (D.precompAffine a L).value (Function.update x k r))
      ((D.precompAffine a L).first k x) (x k) :=
  (D.precompAffine a L).hasDeriv_value k x

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) (k l : Fin m) (x : Fin m → ℝ) :
    HasDerivAt (fun r => (D.precompAffine a L).first l (Function.update x k r))
      ((D.precompAffine a L).second k l x) (x k) :=
  (D.precompAffine a L).hasDeriv_first k l x

set_option pp.universes false
set_option format.width 200
#check @EuclideanBoundedC2Data.precompAffine
#check @EuclideanBoundedC2Data.precompAffine_value_apply
#check @EuclideanBoundedC2Data.precompAffine_first_apply
#check @EuclideanBoundedC2Data.precompAffine_second_apply
#check @EuclideanBoundedC2Data.norm_precompAffine_value_le
#check @EuclideanBoundedC2Data.norm_precompAffine_first_le
#check @EuclideanBoundedC2Data.norm_precompAffine_second_le

-- Exactly the constructor with actual proof fields and its six mathematical readout/bound results.
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.precompAffine
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.precompAffine_value_apply
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.precompAffine_first_apply
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.precompAffine_second_apply
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.norm_precompAffine_value_le
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.norm_precompAffine_first_le
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.norm_precompAffine_second_le
