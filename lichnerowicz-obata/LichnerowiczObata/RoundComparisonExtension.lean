module

public import LichnerowiczObata.TwoPointExtension
public import LichnerowiczObata.RoundComparisonPoleLimits

/-! # Extending the punctured round comparison over both poles -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

def roundNorthPoint {R : ℝ} (hR : 0 < R) : Metric.sphere (0 : RoundAmbient P) R :=
  ⟨R • roundNorth, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      roundNorth_norm, mul_one]⟩

def roundSouthPoint {R : ℝ} (hR : 0 < R) : Metric.sphere (0 : RoundAmbient P) R :=
  ⟨-(R • roundNorth), by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      roundNorth_norm, mul_one]⟩

theorem roundNorthPoint_ne_southPoint {R : ℝ} (hR : 0 < R) :
    roundNorthPoint (P := P) hR ≠ roundSouthPoint hR := by
  intro he
  have hh := congrArg (fun x : Metric.sphere (0 : RoundAmbient P) R =>
    inner ℝ roundNorth (x : RoundAmbient P)) he
  change inner ℝ (roundNorth : RoundAmbient P) (R • roundNorth) =
    inner ℝ roundNorth (-(R • roundNorth)) at hh
  rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    roundNorth_norm] at hh
  norm_num at hh
  linarith

/-- Filling in the two limiting pole values extends a punctured round
comparison to a global homeomorphism. The conclusion retains the original
comparison on every regular sphere point. This is a topological result. -/
theorem exists_round_comparison_extension [FiniteDimensional ℝ P]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {R : ℝ} (hR : 0 < R) {U : Set M} (p q : M) (hpq : p ≠ q)
    (hU : U = {x : M | x ≠ p ∧ x ≠ q})
    (F : U ≃ₜ RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (G : RoundAmbient P → M)
    (hG : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      G (x.1 : RoundAmbient P) = (F.symm x : M))
    (hGc : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      ContinuousAt G (x.1 : RoundAmbient P))
    (hN : Tendsto (fun x => (F.symm x : M))
      (Filter.comap (fun x : RoundPuncturedSphere R (roundNorth : RoundAmbient P) =>
        (x.1 : RoundAmbient P)) (𝓝 (R • roundNorth))) (𝓝 p))
    (hS : Tendsto (fun x => (F.symm x : M))
      (Filter.comap (fun x : RoundPuncturedSphere R (roundNorth : RoundAmbient P) =>
        (x.1 : RoundAmbient P)) (𝓝 (-R • roundNorth))) (𝓝 q)) :
    ∃ H : Metric.sphere (0 : RoundAmbient P) R ≃ₜ M,
      H (roundNorthPoint hR) = p ∧ H (roundSouthPoint hR) = q ∧
      ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
        H x.1 = (F.symm x : M) := by
  let N := roundNorthPoint (P := P) hR
  let S := roundSouthPoint (P := P) hR
  have hNS : N ≠ S := roundNorthPoint_ne_southPoint hR
  have hreg : {x : Metric.sphere (0 : RoundAmbient P) R | x ≠ N ∧ x ≠ S} =
      {x : Metric.sphere (0 : RoundAmbient P) R |
        (x : RoundAmbient P) ≠ R • roundNorth ∧ (x : RoundAmbient P) ≠ -(R • roundNorth)} := by
    ext x
    simp only [mem_ofPred_eq, ne_eq, Subtype.ext_iff]
    rfl
  let A := Homeomorph.setCongr hreg
  let E := A.trans (F.symm.trans (Homeomorph.setCongr hU))
  let g := fun x : Metric.sphere (0 : RoundAmbient P) R => G (x : RoundAmbient P)
  have he : ∀ x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S},
      g x = (E x : M) := fun x => hG (A x)
  have hc : ∀ x, x ≠ N → x ≠ S → ContinuousAt g x := by
    intro x hxN hxS
    exact (hGc (A ⟨x, hxN, hxS⟩)).comp continuous_subtype_val.continuousAt
  have hn : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} => g x)
      (Filter.comap Subtype.val (𝓝 N)) (𝓝 p) := by
    have hi : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} =>
        ((A x).1 : RoundAmbient P)) (Filter.comap Subtype.val (𝓝 N)) (𝓝 (R • roundNorth)) :=
      continuous_subtype_val.continuousAt.tendsto.comp tendsto_comap
    have ht := hN.comp (tendsto_comap_iff.mpr hi)
    exact ht.congr' (Eventually.of_forall (fun x => (hG (A x)).symm))
  have hs : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} => g x)
      (Filter.comap Subtype.val (𝓝 S)) (𝓝 q) := by
    have hi : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} =>
        ((A x).1 : RoundAmbient P)) (Filter.comap Subtype.val (𝓝 S)) (𝓝 (-R • roundNorth)) := by
      rw [neg_smul]
      exact continuous_subtype_val.continuousAt.tendsto.comp tendsto_comap
    have ht := hS.comp (tendsto_comap_iff.mpr hi)
    exact ht.congr' (Eventually.of_forall (fun x => (hG (A x)).symm))
  obtain ⟨H, hHN, hHS, hH⟩ := exists_twoPointExtension_homeomorph g hNS hpq E he hc hn hs
  refine ⟨H, hHN, hHS, ?_⟩
  intro x
  exact hH (A.symm x)

end LichnerowiczObata
