/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckLinearization

/-!
# Algebraic principal/remainder split of the conventional Ricci--DeTurck jet RHS

The existing finite-dimensional reaction uses the positive conventional vector
`W^k = g^{ab} (Gamma^k_ab - GammaBar^k_ab)`. The recovery gauge is negative.
This file proves a finite reaction identity, rather than a conditional solution
interface: the second-order part is exactly inverse-metric Hessian contraction,
and the remaining reaction depends only on the value and first-derivative slots.

A spatially varying fixed background also contributes `-g^{ab} d GammaBar^k_ab`
to each spatial derivative of W. Both corresponding Lie-derivative terms are
retained in the corrected algebraic RHS below. The background-first-jet slots
are explicit data; this file does not construct them from a manifold connection.

The symmetric invertible metric and the two Hessian-slot symmetries are explicit
hypotheses. `Jet2` and `Jet2Section` do not enforce derivative compatibility.
No identification with a manifold Levi--Civita derivative, no frozen Banach
Cauchy-generator identification, and no PDE or Point-4 closure is asserted.
-/

noncomputable section

open Matrix Finset
open scoped Topology

namespace RicciFlow.AnalyticPDE.GenuinePhiRD

variable {d : ℕ}

/-- Retain the value and first-derivative slots and set the Hessian slot to zero.
This is an algebraic projection, not a producer of a holonomic jet. -/
def firstOrderJet (j : Jet2 d d) : Jet2 d d := ⟨j.val, j.deriv1, 0⟩

/-- The algebraic pure Hessian slot of a jet. -/
def secondOrderJet (j : Jet2 d d) : Jet2 d d := ⟨0, 0, j.deriv2⟩

@[simp] theorem firstOrderJet_val (j : Jet2 d d) :
    (firstOrderJet j).val = j.val := rfl

@[simp] theorem firstOrderJet_deriv1 (j : Jet2 d d) :
    (firstOrderJet j).deriv1 = j.deriv1 := rfl

@[simp] theorem firstOrderJet_deriv2 (j : Jet2 d d) :
    (firstOrderJet j).deriv2 = 0 := rfl

@[simp] theorem secondOrderJet_val (j : Jet2 d d) :
    (secondOrderJet j).val = 0 := rfl

@[simp] theorem secondOrderJet_deriv1 (j : Jet2 d d) :
    (secondOrderJet j).deriv1 = 0 := rfl

@[simp] theorem secondOrderJet_deriv2 (j : Jet2 d d) :
    (secondOrderJet j).deriv2 = j.deriv2 := rfl

@[simp] theorem firstOrderJet_add_secondOrderJet (j : Jet2 d d) :
    firstOrderJet j + secondOrderJet j = j := by
  change (⟨j.val + 0, j.deriv1 + 0, 0 + j.deriv2⟩ : Jet2 d d) = j
  simp only [add_zero, zero_add]

@[simp] theorem firstOrderJet_idempotent (j : Jet2 d d) :
    firstOrderJet (firstOrderJet j) = firstOrderJet j := rfl

/-- The coordinate Hessian contraction with a fixed coefficient matrix.
A chart-to-generator identification is a separate theorem. -/
def jetPrincipalContraction (A : Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  ∑ p : Fin d, ∑ q : Fin d, A p q * (j.deriv2 p q) i k

/-- Cancellation of the actual second-jet-linear Ricci and conventional
DeTurck terms, before introducing any derivative or evolution interface. -/
theorem secondJetLinearReaction_eq_principal
    (j δj : Jet2 d d) (hj : j.val.det ≠ 0)
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (hS12 : ∀ a b c e : Fin d, (δj.deriv2 a b) c e = (δj.deriv2 b a) c e)
    (hS34 : ∀ a b c e : Fin d, (δj.deriv2 a b) c e = (δj.deriv2 a b) e c)
    (i k : Fin d) :
    -2 * dRicci2 (d := d) j δj i k + dCorrection2 (d := d) j δj i k =
      jetPrincipalContraction (invMetricOfJet j) δj i k := by
  have hinv : ∀ a b : Fin d,
      ∑ l : Fin d, j.val l a * invMetricOfJet j l b = if a = b then 1 else 0 :=
    fun a b => invMetricOfJet_contract j hj hgsymm a b
  rw [dRicci2_bridge, dCorrection2_bridge j δj hinv hgsymm]
  exact deturckPrincipalPart_identity (d := d)
    (invMetricOfJet j) (fun a b => j.val a b)
    (fun a b c e => (δj.deriv2 a b) c e)
    (fun p q => invMetricOfJet_symm j hj hgsymm p q) hinv hS12 hS34 i k

/-- The actual existing reaction evaluated after removing its Hessian slot.
It retains every zeroth/first-order Christoffel and background-symbol term. -/
def lowerOrderRDOfJet
    (Γbg : Fin d → Fin d → Fin d → ℝ) (j : Jet2 d d) (i k : Fin d) : ℝ :=
  phiRDOfJet Γbg (firstOrderJet j) i k

/-- Exact finite reaction split. The hypotheses are the algebraic symmetries
needed for cancellation; they do not certify that any section is holonomic. -/
theorem phiRDOfJet_eq_principal_add_lowerOrder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (hj : j.val.det ≠ 0)
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (hS12 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 b a) c e)
    (hS34 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 a b) e c)
    (i k : Fin d) :
    phiRDOfJet Γbg j i k =
      jetPrincipalContraction (invMetricOfJet j) j i k + lowerOrderRDOfJet Γbg j i k := by
  have hprincipal : -2 * dRicci2 (firstOrderJet j) (secondOrderJet j) i k +
      dCorrection2 (firstOrderJet j) (secondOrderJet j) i k =
      jetPrincipalContraction (invMetricOfJet j) j i k :=
    secondJetLinearReaction_eq_principal (firstOrderJet j) (secondOrderJet j)
      hj hgsymm hS12 hS34 i k
  have haff := congrFun (congrFun
    (phiRDMatrix_pureSecondJet_affine Γbg (firstOrderJet j) (secondOrderJet j)
      rfl rfl 1) i) k
  simp only [one_smul, firstOrderJet_add_secondOrderJet, Pi.add_apply] at haff
  change phiRDOfJet Γbg j i k = phiRDOfJet Γbg (firstOrderJet j) i k +
    (-2 * dRicci2 (firstOrderJet j) (secondOrderJet j) i k +
      dCorrection2 (firstOrderJet j) (secondOrderJet j) i k) at haff
  rw [hprincipal] at haff
  exact haff.trans (add_comm _ _)

/-- This remainder depends only on the value and first-derivative slots. -/
theorem lowerOrderRDOfJet_eq_of_val_deriv1
    (Γbg : Fin d → Fin d → Fin d → ℝ) (j j' : Jet2 d d)
    (hval : j.val = j'.val) (h1 : j.deriv1 = j'.deriv1) (i k : Fin d) :
    lowerOrderRDOfJet Γbg j i k = lowerOrderRDOfJet Γbg j' i k := by
  have heq : firstOrderJet j = firstOrderJet j' := by
    unfold firstOrderJet
    rw [hval, h1]
  unfold lowerOrderRDOfJet
  rw [heq]

/-- The two omitted background-first-jet contributions to the Lie derivative.
`Γbg1 m k a b` represents the spatial first-derivative slot in direction m.
The corrected RHS subtracts this expression, since W subtracts GammaBar. -/
def backgroundFirstJetLieTerm
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  ∑ l : Fin d,
    (j.val l k * (∑ a : Fin d, ∑ b : Fin d, invMetricOfJet j a b * Γbg1 i l a b) +
      j.val i l * (∑ a : Fin d, ∑ b : Fin d, invMetricOfJet j a b * Γbg1 k l a b))

/-- Corrected algebraic spatial derivative of the conventional W.
The product-rule lemma below explains the sign of the background-first-jet
slot. Identifying metric/Christoffel derivative slots is separate. -/
def derivDeTurckVectorWithBackgroundJetOfJet
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (m l : Fin d) : ℝ :=
  derivDeTurckVectorOfJet Γbg j m l -
    ∑ a : Fin d, ∑ b : Fin d, invMetricOfJet j a b * Γbg1 m l a b

/-- The actual three coordinate Lie-derivative contributions, using the
corrected spatial derivative of W. No target derivative identity is assumed. -/
def deTurckCorrectionWithBackgroundJetOfJet
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  ∑ l : Fin d,
    (valComp j l k * derivDeTurckVectorWithBackgroundJetOfJet Γbg Γbg1 j i l +
      valComp j i l * derivDeTurckVectorWithBackgroundJetOfJet Γbg Γbg1 j k l +
      deTurckVectorOfJet Γbg j l * deriv1Comp j l i k)

/-- Corrected coordinate jet RHS for a background with explicit first-jet
slots. The bridge from a geometric connection remains unproved here. -/
def phiRDWithBackgroundJetOfJet
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  -2 * ricciOfJet j i k + deTurckCorrectionWithBackgroundJetOfJet Γbg Γbg1 j i k

/-- Expanding the two actual Lie-derivative derivative-of-W contributions
isolates exactly the omitted background-first-jet terms, with negative sign. -/
theorem phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg Γbg1 j i k =
      phiRDOfJet Γbg j i k - backgroundFirstJetLieTerm Γbg1 j i k := by
  have hterm : ∀ l : Fin d,
      (valComp j l k * derivDeTurckVectorWithBackgroundJetOfJet Γbg Γbg1 j i l +
        valComp j i l * derivDeTurckVectorWithBackgroundJetOfJet Γbg Γbg1 j k l +
        deTurckVectorOfJet Γbg j l * deriv1Comp j l i k) =
      (valComp j l k * derivDeTurckVectorOfJet Γbg j i l +
        valComp j i l * derivDeTurckVectorOfJet Γbg j k l +
        deTurckVectorOfJet Γbg j l * deriv1Comp j l i k) -
      (j.val l k * (∑ a : Fin d, ∑ b : Fin d, invMetricOfJet j a b * Γbg1 i l a b) +
        j.val i l * (∑ a : Fin d, ∑ b : Fin d, invMetricOfJet j a b * Γbg1 k l a b)) := by
    intro l
    unfold derivDeTurckVectorWithBackgroundJetOfJet valComp
    ring
  unfold phiRDWithBackgroundJetOfJet deTurckCorrectionWithBackgroundJetOfJet
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  unfold phiRDOfJet deTurckCorrectionOfJet backgroundFirstJetLieTerm
  ring

@[simp] theorem backgroundFirstJetLieTerm_firstOrderJet
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) :
    backgroundFirstJetLieTerm Γbg1 (firstOrderJet j) i k =
      backgroundFirstJetLieTerm Γbg1 j i k := rfl

/-- Corrected lower-order reaction, which includes both background-first-jet
Lie contributions and is genuinely independent of the Hessian slot. -/
def lowerOrderRDWithBackgroundJetOfJet
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  phiRDWithBackgroundJetOfJet Γbg Γbg1 (firstOrderJet j) i k

theorem lowerOrderRDWithBackgroundJetOfJet_eq
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) :
    lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 j i k =
      lowerOrderRDOfJet Γbg j i k - backgroundFirstJetLieTerm Γbg1 j i k := by
  unfold lowerOrderRDWithBackgroundJetOfJet lowerOrderRDOfJet
  rw [phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm,
    backgroundFirstJetLieTerm_firstOrderJet]

theorem lowerOrderRDWithBackgroundJetOfJet_eq_of_val_deriv1
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j j' : Jet2 d d) (hval : j.val = j'.val)
    (h1 : j.deriv1 = j'.deriv1) (i k : Fin d) :
    lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 j i k =
      lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 j' i k := by
  have heq : firstOrderJet j = firstOrderJet j' := by
    unfold firstOrderJet
    rw [hval, h1]
  unfold lowerOrderRDWithBackgroundJetOfJet
  rw [heq]

/-- The corrected finite reaction still has the conventional inverse-metric
principal part. All background-first-jet terms are lower order. -/
theorem phiRDWithBackgroundJetOfJet_eq_principal_add_lowerOrder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (hj : j.val.det ≠ 0)
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (hS12 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 b a) c e)
    (hS34 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 a b) e c)
    (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg Γbg1 j i k =
      jetPrincipalContraction (invMetricOfJet j) j i k +
        lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 j i k := by
  rw [phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm,
    phiRDOfJet_eq_principal_add_lowerOrder Γbg j hj hgsymm hS12 hS34 i k,
    lowerOrderRDWithBackgroundJetOfJet_eq]
  ring

/-- The remainder after freezing the principal coefficient at A. It contains
the explicit quasilinear Hessian coefficient error and the lower-order reaction;
it is not itself a second-order-free map unless A equals the inverse metric. -/
def frozenCoefficientRemainderOfJet
    (A : Fin d → Fin d → ℝ)
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (i k : Fin d) : ℝ :=
  jetPrincipalContraction (fun p q => invMetricOfJet j p q - A p q) j i k +
    lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 j i k

/-- Exact frozen-principal-coefficient remainder identity for the corrected
algebraic jet RHS. This is the finite-dimensional split needed before a
chart/holonomic and generator bridge can be established. -/
theorem phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder
    (A : Fin d → Fin d → ℝ)
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (hj : j.val.det ≠ 0)
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (hS12 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 b a) c e)
    (hS34 : ∀ a b c e : Fin d, (j.deriv2 a b) c e = (j.deriv2 a b) e c)
    (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg Γbg1 j i k =
      jetPrincipalContraction A j i k + frozenCoefficientRemainderOfJet A Γbg Γbg1 j i k := by
  rw [phiRDWithBackgroundJetOfJet_eq_principal_add_lowerOrder Γbg Γbg1 j
    hj hgsymm hS12 hS34 i k]
  unfold frozenCoefficientRemainderOfJet jetPrincipalContraction
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Quantitative frozen-coefficient Hessian error. This is a finite-sum
estimate, without claiming any invariant region or smallness for a PDE solution. -/
theorem abs_frozenPrincipalError_le
    (A : Fin d → Fin d → ℝ) (j : Jet2 d d) (ε : ℝ)
    (hcoeff : ∀ p q : Fin d, |invMetricOfJet j p q - A p q| ≤ ε)
    (i k : Fin d) :
    |jetPrincipalContraction (fun p q => invMetricOfJet j p q - A p q) j i k| ≤
      ε * (∑ p : Fin d, ∑ q : Fin d, |(j.deriv2 p q) i k|) := by
  unfold jetPrincipalContraction
  calc
    |∑ p : Fin d, ∑ q : Fin d,
        (invMetricOfJet j p q - A p q) * (j.deriv2 p q) i k| ≤
        ∑ p : Fin d, ∑ q : Fin d,
          |(invMetricOfJet j p q - A p q) * (j.deriv2 p q) i k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ p : Fin d, ∑ q : Fin d, ε * |(j.deriv2 p q) i k| := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoeff p q) (abs_nonneg _)
    _ = ε * (∑ p : Fin d, ∑ q : Fin d, |(j.deriv2 p q) i k|) := by
      simp only [Finset.mul_sum]

@[simp] theorem phiRDWithBackgroundJetOfJet_zero
    (Γbg : Fin d → Fin d → Fin d → ℝ) (j : Jet2 d d) (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg 0 j i k = phiRDOfJet Γbg j i k := by
  rw [phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm]
  simp [backgroundFirstJetLieTerm]

/-- Ordinary product differentiation of the actual conventional contraction.
The primitive component derivative certificates are displayed explicitly;
there is no asserted chart or Levi--Civita derivative producer. In particular
background differentiation enters with a minus sign. -/
theorem hasDerivAt_conventionalContraction
    (A : ℝ → Fin d → Fin d → ℝ)
    (Γ Γbar : ℝ → Fin d → Fin d → Fin d → ℝ)
    (A1 : Fin d → Fin d → ℝ)
    (Γ1 Γbar1 : Fin d → Fin d → Fin d → ℝ)
    (t : ℝ)
    (hA : ∀ a b : Fin d, HasDerivAt (fun s => A s a b) (A1 a b) t)
    (hΓ : ∀ l a b : Fin d, HasDerivAt (fun s => Γ s l a b) (Γ1 l a b) t)
    (hΓbar : ∀ l a b : Fin d,
      HasDerivAt (fun s => Γbar s l a b) (Γbar1 l a b) t)
    (l : Fin d) :
    HasDerivAt
      (fun s => ∑ a : Fin d, ∑ b : Fin d, A s a b * (Γ s l a b - Γbar s l a b))
      (∑ a : Fin d, ∑ b : Fin d,
        (A1 a b * (Γ t l a b - Γbar t l a b) +
          A t a b * (Γ1 l a b - Γbar1 l a b))) t := by
  have h := HasDerivAt.sum (u := Finset.univ) fun a _ =>
    HasDerivAt.sum (u := Finset.univ) fun b _ =>
      (hA a b).mul ((hΓ l a b).sub (hΓbar l a b))
  have hfun :
      (∑ a : Fin d, ∑ b : Fin d,
        (fun s => A s a b) * ((fun s => Γ s l a b) - (fun s => Γbar s l a b))) =
      (fun s => ∑ a : Fin d, ∑ b : Fin d,
        A s a b * (Γ s l a b - Γbar s l a b)) := by
    funext s
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  rw [hfun] at h
  exact h

end RicciFlow.AnalyticPDE.GenuinePhiRD
