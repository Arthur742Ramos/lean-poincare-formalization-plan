module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuity criteria for vector-bundle sections

This file adds repo-local `C^0` analogues of mathlib's local-frame smoothness
criteria for sections of finite-rank vector bundles.

The main point is that on an open trivializing set, continuity of a section is
equivalent to continuity of its local-frame coefficient functions. This is the
first bridge from continuous bundle sections to compact-space `ContinuousMap`
techniques, which are needed for later function-space work toward point 4.
-/

@[expose] public noncomputable section

open Bundle Module
open scoped Bundle Manifold ContDiff Topology

namespace PoincareCurvature

namespace Bundle.Trivialization

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι 𝕜 F) {s : Π x : M, V x} {t : Set M}

/-- Each section in the local frame induced by a compatible trivialization is continuous on the
trivialization domain. -/
lemma continuousOn_localFrame_baseSet [ContMDiffVectorBundle 1 F V I] (i : ι) :
    ContinuousOn (T% (e.localFrame b i)) e.baseSet := by
  simpa using
    (show ContinuousOn (T% (e.localFrame b i)) e.baseSet from
      (e.contMDiffOn_localFrame_baseSet (I := I) (n := (1 : WithTop ℕ∞)) b i).continuousOn)

/-- If a section is continuous on an open subset of a trivialization domain, then each local-frame
coefficient function is continuous there. -/
lemma continuousOn_localFrame_coeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) (hs : ContinuousOn (T% s) t) (i : ι) :
    ContinuousOn ((LinearMap.piApply (e.localFrame_coeff I b i)) s) t := by
  have hs' : CMDiff[t] (0 : WithTop ℕ∞) (T% s) := by
    rwa [contMDiffOn_zero_iff]
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_localFrame_coeff (I := I) (e := e) (b := b) (t := t)
      (k := (0 : WithTop ℕ∞)) ht ht' hs' i)

/-- On an open subset of a trivialization domain, a section is continuous iff each local-frame
coefficient function is continuous. -/
lemma continuousOn_iff_localFrame_coeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    ContinuousOn (T% s) t ↔
      ∀ i, ContinuousOn ((LinearMap.piApply (e.localFrame_coeff I b i)) s) t := by
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_iff_localFrame_coeff (I := I) (e := e) (b := b) (t := t)
      (k := (0 : WithTop ℕ∞)) ht ht')

/-- On a trivialization domain, a section is continuous iff each local-frame coefficient function is
continuous. -/
lemma continuousOn_baseSet_iff_localFrame_coeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] :
    ContinuousOn (T% s) e.baseSet ↔
      ∀ i, ContinuousOn ((LinearMap.piApply (e.localFrame_coeff I b i)) s) e.baseSet := by
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_baseSet_iff_localFrame_coeff (I := I) (e := e) (b := b)
      (s := s) (k := (0 : WithTop ℕ∞)))

/-- Package a continuous section, read in a compatible trivialization, as an `F`-valued continuous
map on a compact subset of the trivialization domain. -/
def coordContinuousMap (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) : C(K, F) where
  toFun x := (e ((T% s) x.1)).2
  continuous_toFun := by
    have htriv : ContinuousOn (fun y ↦ e ((T% s) y)) e.baseSet := by
      refine e.continuousOn.comp hs ?_
      intro y hy
      simpa [e.mem_source] using hy
    have hcoord : ContinuousOn (fun y ↦ (e ((T% s) y)).2) e.baseSet :=
      continuous_snd.comp_continuousOn htriv
    exact continuousOn_iff_continuous_restrict.mp (hcoord.mono hK)

@[simp]
lemma coordContinuousMap_apply (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (x : K) :
    coordContinuousMap (e := e) K hK hs x = (e ((T% s) x.1)).2 := rfl

/-- Package the coordinate change on a compact overlap piece as an `F`-valued endomorphism of
continuous coordinate maps. -/
def coordChangeContinuousMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u : C(K, F)) : C(K, F) where
  toFun x := e.coordChangeL 𝕜 e' x.1 (u x)
  continuous_toFun := by
    have hchg : ContinuousOn (fun b ↦ Trivialization.coordChangeL 𝕜 e e' b : M → F →L[𝕜] F) (e.baseSet ∩ e'.baseSet) :=
      continuousOn_coordChange (R := 𝕜) (e := e) (e' := e')
    have hchg' : Continuous fun x : K ↦ (Trivialization.coordChangeL 𝕜 e e' x.1 : F →L[𝕜] F) := by
      exact continuousOn_iff_continuous_restrict.mp (hchg.mono hK)
    exact hchg'.clm_apply u.continuous

@[simp]
lemma coordChangeContinuousMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u : C(K, F)) (x : K) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u x =
      e.coordChangeL 𝕜 e' x.1 (u x) := rfl

/-- Bundle the overlap coordinate change itself as an operator-valued continuous map. -/
def coordChangeLContinuousMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    C(K, F →L[𝕜] F) where
  toFun x := e.coordChangeL 𝕜 e' x.1
  continuous_toFun := by
    have hchg : ContinuousOn (fun b ↦ Trivialization.coordChangeL 𝕜 e e' b : M → F →L[𝕜] F)
        (e.baseSet ∩ e'.baseSet) :=
      continuousOn_coordChange (R := 𝕜) (e := e) (e' := e')
    exact continuousOn_iff_continuous_restrict.mp (hchg.mono hK)

@[simp]
lemma coordChangeLContinuousMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) (x : K) :
    coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x = e.coordChangeL 𝕜 e' x.1 :=
  rfl

/-- The compact overlap coordinate change, packaged as a continuous linear operator on `C(K, F)`. -/
def coordChangeContinuousLinearMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    C(K, F) →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK
      map_add' := by
        intro u v
        ext x
        simp [coordChangeContinuousMap, map_add]
      map_smul' := by
        intro c u
        ext x
        simp [coordChangeContinuousMap, map_smul] }
    ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖
    (fun u ↦ by
      refine (ContinuousMap.norm_le (f := coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u)
        (by positivity : 0 ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖ * ‖u‖)).mpr ?_
      intro x
      calc
        ‖coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u x‖ =
            ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x (u x)‖ := by
              rfl
        _ ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x‖ * ‖u x‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖ * ‖u‖ := by
              gcongr
              · exact (coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK).norm_coe_le_norm x
              · exact u.norm_coe_le_norm x)

@[simp]
lemma coordChangeContinuousLinearMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) (u : C(K, F)) :
    coordChangeContinuousLinearMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u :=
  by
    change coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u
    rfl

/-- On compact overlap pieces, the packaged coordinate maps from two trivializations are related
pointwise by the bundle coordinate change. -/
lemma coordContinuousMap_coordChangeL_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s) e'.baseSet) (x : K) :
    e.coordChangeL 𝕜 e' x.1 (coordContinuousMap (e := e) K (fun _ hy ↦ (hK hy).1) hs x) =
      coordContinuousMap (e := e') K (fun _ hy ↦ (hK hy).2) hs' x := by
  have hsymm : e.symm x.1 ((e ((T% s) x.1)).2) = s x.1 := by
    simpa using e.symm_apply_apply_mk (hK x.2).1 (s x.1)
  rw [e.coordChangeL_apply (R := 𝕜) e' (hK x.2)]
  simp [coordContinuousMap, hsymm]

/-- On compact overlap pieces, the packaged coordinate maps from two trivializations are related by
the coordinate-change operator as an equality of continuous maps. -/
lemma coordContinuousMap_coordChangeL
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s) e'.baseSet) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK
        (coordContinuousMap (e := e) K (fun _ hy ↦ (hK hy).1) hs) =
      coordContinuousMap (e := e') K (fun _ hy ↦ (hK hy).2) hs' := by
  ext x
  exact coordContinuousMap_coordChangeL_apply (𝕜 := 𝕜) (e := e) (e' := e')
    K hK hs hs' x

@[simp]
lemma coordChangeContinuousMap_zero
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (0 : C(K, F)) = 0 := by
  ext x
  simp [coordChangeContinuousMap]

@[simp]
lemma coordChangeContinuousMap_add
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u v : C(K, F)) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (u + v) =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u +
        coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK v := by
  ext x
  simp [coordChangeContinuousMap, map_add]

@[simp]
lemma coordChangeContinuousMap_smul
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (c : 𝕜) (u : C(K, F)) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (c • u) =
      c • coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u := by
  ext x
  simp [coordChangeContinuousMap, map_smul]

/-- The inclusion of one compact subset into a larger one, bundled as a continuous map. -/
def compactSubsetInclusion {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) : C(K, L) where
  toFun x := ⟨x.1, hKL x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
lemma compactSubsetInclusion_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (x : K) :
    compactSubsetInclusion hKL x = ⟨x.1, hKL x.2⟩ := rfl

/-- Restrict a continuous map on a compact set to a smaller compact subset. -/
def restrictToCompact {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) : C(K, F) :=
  u.comp (compactSubsetInclusion hKL)

@[simp]
lemma restrictToCompact_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) (x : K) :
    restrictToCompact hKL u x = u ⟨x.1, hKL x.2⟩ := rfl

@[simp]
lemma restrictToCompact_coordContinuousMap {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (hL : (L : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) :
    restrictToCompact hKL (coordContinuousMap (e := e) L hL hs) =
      coordContinuousMap (e := e) K (fun _ hx ↦ hL (hKL hx)) hs := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_zero {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) :
    restrictToCompact hKL (0 : C(L, F)) = 0 := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_add {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u v : C(L, F)) :
    restrictToCompact hKL (u + v) = restrictToCompact hKL u + restrictToCompact hKL v := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_smul {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (c : 𝕜) (u : C(L, F)) :
    restrictToCompact hKL (c • u) = c • restrictToCompact hKL u := by
  ext x
  rfl

/-- Restriction to a smaller compact set, packaged as a continuous linear map. -/
def restrictToCompactContinuousLinearMap {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) : C(L, F) →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := restrictToCompact hKL
      map_add' := by
        intro u v
        ext x
        rfl
      map_smul' := by
        intro c u
        ext x
        rfl }
    1
    (fun u ↦ by
      refine (ContinuousMap.norm_le (f := restrictToCompact hKL u)
        (by positivity : 0 ≤ (1 : ℝ) * ‖u‖)).mpr ?_
      intro x
      simpa [one_mul, restrictToCompact_apply] using u.norm_coe_le_norm ⟨x.1, hKL x.2⟩)

@[simp]
lemma restrictToCompactContinuousLinearMap_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) :
    restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) hKL u = restrictToCompact hKL u := by
  change restrictToCompact hKL u = restrictToCompact hKL u
  rfl

/-- Package the `i`-th local-frame coefficient of a continuous section as a continuous map on a
compact subset of a trivialization domain. -/
def localFrameCoeffContinuousMap
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (i : ι) : C(K, 𝕜) where
  toFun x := e.localFrame_coeff I b i x.1 (s x.1)
  continuous_toFun := by
    have hcoeff : ContinuousOn ((LinearMap.piApply (e.localFrame_coeff I b i)) s) e.baseSet :=
      (continuousOn_baseSet_iff_localFrame_coeff (I := I) (e := e) (b := b) (s := s)).mp hs i
    exact continuousOn_iff_continuous_restrict.mp (hcoeff.mono hK)

@[simp]
lemma localFrameCoeffContinuousMap_apply
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (i : ι) (x : K) :
    localFrameCoeffContinuousMap (I := I) (e := e) b K hK hs i x =
      e.localFrame_coeff I b i x.1 (s x.1) := rfl

/-- The pointwise local-frame reconstruction formula can be read directly from the packaged
coefficient maps on a compact subset of the trivialization domain. -/
lemma eq_sum_localFrameCoeffContinuousMap_smul
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] [Fintype ι]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (x : K) :
    s x.1 = ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) b K hK hs i x • e.localFrame b i x.1 := by
  simpa [localFrameCoeffContinuousMap] using
    (e.eq_sum_localFrame_coeff_smul (I := I) (b := b) (s := s) (x' := x.1) (hK x.2))

/-- On a compact subset of a trivialization domain, a continuous section is completely determined by
its packaged local-frame coefficient maps. -/
lemma eqOn_compact_iff_localFrameCoeffContinuousMap_eq
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] [Fintype ι]
    {s' : Π x : M, V x} (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s') e.baseSet) :
    (∀ x ∈ (K : Set M), s x = s' x) ↔
      ∀ i,
        localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i =
          localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i := by
  constructor
  · intro h i
    ext x
    simpa [localFrameCoeffContinuousMap] using
      (e.localFrame_coeff_congr (I := I) (b := b) (s := s) (s' := s') (x := x.1) (i := i)
        (h x.1 x.2))
  · intro h x hx
    let xK : K := ⟨x, hx⟩
    calc
      s x =
          ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i xK •
            e.localFrame b i x := by
            simpa [xK] using
              (eq_sum_localFrameCoeffContinuousMap_smul (I := I) (e := e) (b := b) (s := s)
                K hK hs xK)
      _ =
          ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i xK •
            e.localFrame b i x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hix :
                localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i xK =
                  localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i xK := by
              simpa using congrArg (fun f => f xK) (h i)
            rw [hix]
      _ = s' x := by
            symm
            simpa [xK] using
              (eq_sum_localFrameCoeffContinuousMap_smul (I := I) (e := e) (b := b) (s := s')
                K hK hs' xK)

section CoverCompatibility

/-- A family of compact coordinate maps, one on each compact trivializing piece. -/
abbrev CoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) := ∀ i, C(Kc i, F)

instance coordFamilyCompleteSpace {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts M) [CompleteSpace F] :
    CompleteSpace (CoordFamily (F := F) Kc) := by
  dsimp [CoordFamily]
  infer_instance

/-- Compatibility of a compact coordinate family on pairwise overlap pieces. -/
def CoordFamilyCompatible
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) : Prop :=
  ∀ i j,
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
      (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
    restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)

/-- The subtype of compact coordinate families satisfying the overlap compatibility relations. -/
def CompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :=
  {u : CoordFamily (F := F) Kc //
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)}

/-- Package a continuous section as a family of compact coordinate maps along a trivializing family. -/
def coordFamilyOfSection
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (hs : Continuous (T% s)) : CoordFamily (F := F) Kc :=
  fun i ↦ coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn

/-- The compact coordinate family associated to a continuous section satisfies the overlap
compatibility relations. -/
lemma coordFamilyOfSection_compatible
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1)
          (coordFamilyOfSection (s := s) et Kc hKc hs i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2)
        (coordFamilyOfSection (s := s) et Kc hKc hs j) := by
  intro i j
  simpa [coordFamilyOfSection] using
    (coordContinuousMap_coordChangeL (𝕜 := 𝕜) (e := et i) (e' := et j)
    (K := Ko i j) (hK := fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
    (s := s) hs.continuousOn hs.continuousOn)

/-- The compatible compact coordinate family associated to a continuous section. -/
def compatibleCoordFamilyOfSection
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    {u : CoordFamily (F := F) Kc //
      ∀ i j,
        coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
          (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
          (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
        restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)} :=
  ⟨coordFamilyOfSection (s := s) et Kc hKc hs,
    coordFamilyOfSection_compatible (s := s) et Kc hKc Ko hKo hs⟩

/-- A family of compact overlap defects, one for each ordered pair of compact pieces. -/
abbrev OverlapFamily {κ : Type*} (Ko : κ → κ → TopologicalSpace.Compacts M) :=
  ∀ i j, C(Ko i j, F)

instance overlapFamilyCompleteSpace {κ : Type*} [Fintype κ]
    (Ko : κ → κ → TopologicalSpace.Compacts M) [CompleteSpace F] :
    CompleteSpace (OverlapFamily (F := F) Ko) := by
  dsimp [OverlapFamily]
  infer_instance

/-- The overlap defect of a compact coordinate family: it vanishes exactly when the family is
compatible. -/
def coordFamilyCompatibilityError
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) : OverlapFamily (F := F) Ko :=
  fun i j ↦
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
      (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) -
    restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)

/-- Compatibility is equivalent to vanishing of the overlap defect family. -/
lemma coordFamilyCompatible_iff_coordFamilyCompatibilityError_eq_zero
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc} :
    CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u ↔
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u = 0 := by
  constructor
  · intro hu
    funext i j
    exact sub_eq_zero.mpr (hu i j)
  · intro hu i j
    exact sub_eq_zero.mp (congrArg (fun f => f i j) hu)

/-- The overlap defect is linear in the compact coordinate family. -/
def coordFamilyCompatibilityLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CoordFamily (F := F) Kc →ₗ[𝕜] OverlapFamily (F := F) Ko where
  toFun := coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  map_add' u v := by
    funext i j
    simp [coordFamilyCompatibilityError, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c u := by
    funext i j
    simp [coordFamilyCompatibilityError, sub_eq_add_neg, smul_add]

/-- The compact coordinate families satisfying the overlap equations form the kernel of the overlap
defect map. -/
def compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    Submodule 𝕜 (CoordFamily (F := F) Kc) :=
  (coordFamilyCompatibilityLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).ker

/-- Membership in the compatibility submodule is exactly the overlap compatibility condition. -/
lemma mem_compatibleCoordFamilySubmodule_iff
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc} :
    u ∈ compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo ↔
      CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u := by
  change coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u = 0 ↔
    CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u
  exact
    (coordFamilyCompatible_iff_coordFamilyCompatibilityError_eq_zero
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo (u := u)).symm

/-- The compact coordinate family of a continuous section lies in the compatibility kernel. -/
lemma coordFamilyOfSection_mem_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    coordFamilyOfSection (s := s) et Kc hKc hs ∈
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo := by
  rw [mem_compatibleCoordFamilySubmodule_iff]
  exact coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs

/-- The `(i,j)` overlap defect component, packaged as a continuous linear map on compact coordinate
families. -/
def coordFamilyCompatibilityComponentContinuousLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (i j : κ) : CoordFamily (F := F) Kc →L[𝕜] C(Ko i j, F) :=
  (coordChangeContinuousLinearMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)).comp
    ((restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) (fun _ hx ↦ (hKo i j hx).1)).comp
      (ContinuousLinearMap.proj i))
    -
  (restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) (fun _ hx ↦ (hKo i j hx).2)).comp
    (ContinuousLinearMap.proj j)

@[simp]
lemma coordFamilyCompatibilityComponentContinuousLinearMap_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (i j : κ) (u : CoordFamily (F := F) Kc) :
    coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
      i j u =
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j := by
  ext x
  simp [coordFamilyCompatibilityComponentContinuousLinearMap, coordFamilyCompatibilityError,
    restrictToCompact_apply]

/-- The full overlap defect map, packaged as a continuous linear map into the family of compact
overlap defects. -/
def coordFamilyCompatibilityContinuousLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CoordFamily (F := F) Kc →L[𝕜] OverlapFamily (F := F) Ko where
  toLinearMap := coordFamilyCompatibilityLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  cont := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    have hcomp : Continuous fun u ↦
      coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        i j u :=
      (coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        i j).continuous
    simpa [coordFamilyCompatibilityLinearMap, coordFamilyCompatibilityError] using hcomp

@[simp]
lemma coordFamilyCompatibilityContinuousLinearMap_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) (i j : κ) :
    coordFamilyCompatibilityContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j =
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j := rfl

/-- The compatibility kernel is closed because it is the kernel of a continuous linear map. -/
lemma isClosed_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    IsClosed
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) := by
  change IsClosed
    ((coordFamilyCompatibilityContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).ker :
      Set (CoordFamily (F := F) Kc))
  exact ContinuousLinearMap.isClosed_ker _

/-- The compatibility kernel is complete as soon as the ambient coordinate-family space is. -/
lemma isComplete_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [CompleteSpace (CoordFamily (F := F) Kc)] :
    IsComplete
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) := by
  exact (isClosed_compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).isComplete

instance compatibleCoordFamilySubmodule.completeSpace
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [CompleteSpace (CoordFamily (F := F) Kc)] :
    CompleteSpace (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) := by
  letI : IsClosed
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) :=
    isClosed_compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  infer_instance

/-- A total-space valued map whose first coordinate is always the base point determines a genuine
section. -/
noncomputable def sectionOfTotalSpaceMap (f : M → TotalSpace F V)
    (hf : ∀ x, (f x).1 = x) : Π x : M, V x :=
  fun x ↦ cast (congrArg V (hf x)) (f x).2

/-- The total-space map attached to `sectionOfTotalSpaceMap` is the original map. -/
lemma totalSpace_sectionOfTotalSpaceMap (f : M → TotalSpace F V) (hf : ∀ x, (f x).1 = x) :
    T% (sectionOfTotalSpaceMap (V := V) f hf) = f := by
  funext x
  refine Bundle.TotalSpace.ext (hf x).symm ?_
  change cast (congrArg V (hf x)) (f x).2 ≍ (f x).2
  exact (cast_heq_iff_heq (congrArg V (hf x)) (f x).2 (f x).2).2 HEq.rfl

/-- Read a compact coordinate family back as a total-space valued map on a single compact piece. -/
def totalSpaceMapOnCompactOfCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (u : CoordFamily (F := F) Kc) (i : κ) : C(Kc i, TotalSpace F V) where
  toFun x := ⟨x.1, (et i).symm x.1 (u i x)⟩
  continuous_toFun := by
    have hpair : Continuous fun x : Kc i ↦ (x.1, u i x) := continuous_subtype_val.prodMk (u i).continuous
    exact (et i).continuousOn_symm.comp_continuous hpair fun x ↦
      Set.mk_mem_prod (hKc i x.2) (Set.mem_univ _)

@[simp]
lemma totalSpaceMapOnCompactOfCoordFamily_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (u : CoordFamily (F := F) Kc) (i : κ) (x : Kc i) :
    totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x =
      ⟨x.1, (et i).symm x.1 (u i x)⟩ :=
  rfl

/-- On full compact overlaps, the local total-space maps reconstructed from a compatible coordinate
family agree. -/
lemma totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc}
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    {i j : κ} {x : M} (hxi : x ∈ (Kc i : Set M)) (hxj : x ∈ (Kc j : Set M)) :
    totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i ⟨x, hxi⟩ =
      totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u j ⟨x, hxj⟩ := by
  have hxKo : x ∈ (Ko i j : Set M) := by
    rw [hKoEq i j]
    exact ⟨hxi, hxj⟩
  let xKo : Ko i j := ⟨x, hxKo⟩
  have hcoord :
      (et i).coordChangeL 𝕜 (et j) x (u i ⟨x, hxi⟩) = u j ⟨x, hxj⟩ := by
    have h := congrArg (fun f ↦ f xKo) (hu i j)
    simpa [coordChangeContinuousMap_apply, restrictToCompact_apply, xKo] using h
  have hb : x ∈ (et i).baseSet ∩ (et j).baseSet := ⟨hKc i hxi, hKc j hxj⟩
  change (⟨x, (et i).symm x (u i ⟨x, hxi⟩)⟩ : TotalSpace F V) =
    ⟨x, (et j).symm x (u j ⟨x, hxj⟩)⟩
  apply congrArg (fun v ↦ (⟨x, v⟩ : TotalSpace F V))
  calc
      (et i).symm x (u i ⟨x, hxi⟩) =
          (et j).symm x ((et i).coordChangeL 𝕜 (et j) x (u i ⟨x, hxi⟩)) := by
            rw [(et i).coordChangeL_apply (R := 𝕜) (e' := et j) hb]
            simpa using ((et j).symm_apply_apply_mk hb.2 ((et i).symm x (u i ⟨x, hxi⟩))).symm
      _ = (et j).symm x (u j ⟨x, hxj⟩) := by rw [hcoord]

/-- Glue a compatible compact coordinate family into a total-space valued map on the base. -/
noncomputable def totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    M → TotalSpace F V :=
  Set.liftCover (fun i => (Kc i : Set M))
    (fun i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i)
    (fun _ _ _ hxi hxj =>
      totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hu hxi hxj)
    hcover

@[simp]
lemma totalSpaceMapOfCompatibleCoordFamily_of_mem
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {i : κ} {x : M} (hx : x ∈ (Kc i : Set M)) :
    totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover x =
      totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i ⟨x, hx⟩ := by
  simpa [totalSpaceMapOfCompatibleCoordFamily] using
    (Set.liftCover_of_mem
      (S := fun i => (Kc i : Set M))
      (f := fun i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i)
      (hf := fun i j x hxi hxj =>
        totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
          (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hu hxi hxj)
      (hS := hcover) (i := i) (x := x) hx)

@[simp]
lemma proj_totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) (x : M) :
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover x).1 =
      x := by
  have hx : x ∈ (⋃ i, (Kc i : Set M)) := by simp [hcover]
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  simpa [totalSpaceMapOnCompactOfCoordFamily] using
    congrArg Bundle.TotalSpace.proj
      (totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x) hxi)

/-- On a finite compact cover of a Hausdorff base, the glued total-space map is continuous. -/
lemma continuous_totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Continuous (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) := by
  let S : κ → Set M := fun i => (Kc i : Set M)
  let g : M → TotalSpace F V :=
    totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover
  let hlf : LocallyFinite S := locallyFinite_of_finite S
  refine hlf.continuous hcover ?_ ?_
  · intro i
    exact (Kc i).isCompact.isClosed
  · intro i
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict :
        (S i).restrict g =
          fun x : S i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x := by
      funext x
      exact totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x.1) x.2
    rw [hrestrict]
    simpa using (totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i).continuous

/-- Reconstruct a section from a compatible compact coordinate family on a covering compact
trivializing family. -/
noncomputable def sectionOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Π x : M, V x :=
  sectionOfTotalSpaceMap (V := V)
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
    (proj_totalSpaceMapOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)

@[simp]
lemma totalSpace_sectionOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) =
      totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover :=
  totalSpace_sectionOfTotalSpaceMap (V := V)
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
    (proj_totalSpaceMapOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)

/-- The reconstructed section has continuous total-space map on a finite compact cover of a Hausdorff
base. -/
lemma continuous_sectionOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Continuous (T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)) := by
  rw [totalSpace_sectionOfCompatibleCoordFamily]
  exact continuous_totalSpaceMapOfCompatibleCoordFamily
    (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover

/-- Reconstructing a section from a compatible compact coordinate family recovers that family. -/
lemma coordFamilyOfSection_sectionOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    coordFamilyOfSection
        (s := sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
        et Kc hKc
        (continuous_sectionOfCompatibleCoordFamily
          (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) =
      u := by
  funext i
  ext x
  have htx :
      T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) x.1 =
        totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x := by
    rw [totalSpace_sectionOfCompatibleCoordFamily]
    simpa using
      (totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x.1) x.2)
  have hcoord :
      (et i (totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x)).2 = u i x := by
    simpa [totalSpaceMapOnCompactOfCoordFamily] using
      congrArg Prod.snd ((et i).apply_mk_symm (hKc i x.2) (u i x))
  simpa [coordFamilyOfSection, coordContinuousMap, htx] using hcoord

/-- The zero coordinate family is compatible on overlaps. -/
lemma coordFamilyCompatible_zero
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (0 : C(Kc i, F))) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (0 : C(Kc j, F)) := by
  intro i j
  ext x
  simp

/-- Compatibility on overlaps is preserved by addition of coordinate families. -/
lemma coordFamilyCompatible_add
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {u v : CoordFamily (F := F) Kc}
    (hu : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j))
    (hv : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (v i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (v j)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) ((u + v) i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) ((u + v) j) := by
  intro i j
  ext x
  have hux := congrArg (fun f => f x) (hu i j)
  have hvx := congrArg (fun f => f x) (hv i j)
  simp [hux, hvx]

/-- Compatibility on overlaps is preserved by scalar multiplication. -/
lemma coordFamilyCompatible_smul
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {u : CoordFamily (F := F) Kc} (c : 𝕜)
    (hu : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) ((c • u) i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) ((c • u) j) := by
  intro i j
  ext x
  have hux := congrArg (fun f => f x) (hu i j)
  simp [hux]

/-- If two continuous sections have the same compact coordinate family, then they agree on the
union of the compact pieces. -/
lemma eqOn_iUnion_of_coordFamilyOfSection_eq
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    {s' : Π x : M, V x} (hs : Continuous (T% s)) (hs' : Continuous (T% s'))
    (hcoord : ∀ i,
      coordFamilyOfSection (s := s) et Kc hKc hs i =
        coordFamilyOfSection (s := s') et Kc hKc hs' i) :
    ∀ x ∈ (⋃ i, (Kc i : Set M)), s x = s' x := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hix :
      coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn xK =
        coordContinuousMap (e := et i) (Kc i) (hKc i) hs'.continuousOn xK := by
    simpa [coordFamilyOfSection, xK] using congrArg (fun f => f xK) (hcoord i)
  have hsymm :
      (et i).symm x (coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn xK) = s x := by
    simpa [coordContinuousMap, xK] using (et i).symm_apply_apply_mk (hKc i hxi) (s x)
  have hsymm' :
      (et i).symm x (coordContinuousMap (e := et i) (Kc i) (hKc i) hs'.continuousOn xK) = s' x := by
    simpa [coordContinuousMap, xK] using (et i).symm_apply_apply_mk (hKc i hxi) (s' x)
  rw [← hsymm, hix, hsymm']

/-- If the compact pieces cover the base, the compact coordinate family construction is injective. -/
lemma coordFamilyOfSection_injective
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    {s' : Π x : M, V x} (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (hs : Continuous (T% s)) (hs' : Continuous (T% s'))
    (hcoord : ∀ i,
      coordFamilyOfSection (s := s) et Kc hKc hs i =
        coordFamilyOfSection (s := s') et Kc hKc hs' i) :
    s = s' := by
  funext x
  exact eqOn_iUnion_of_coordFamilyOfSection_eq (et := et) (Kc := Kc) (hKc := hKc)
    (s := s) (s' := s') hs hs' hcoord x (by simp [hcover])

/-- Applying the reconstruction map to the compact coordinate family of a continuous section returns
the original section. -/
lemma sectionOfCompatibleCoordFamily_coordFamilyOfSection
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {s : Π x : M, V x} (hs : Continuous (T% s)) :
    sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        (coordFamilyOfSection (s := s) et Kc hKc hs)
        (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
        hKoEq hcover =
      s := by
  exact coordFamilyOfSection_injective
      (et := et) (Kc := Kc) (hKc := hKc)
      (s := sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        (coordFamilyOfSection (s := s) et Kc hKc hs)
        (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
        hKoEq hcover)
      (s' := s) (hcover := hcover)
      (continuous_sectionOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
      (coordFamilyOfSection (s := s) et Kc hKc hs)
      (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
      hKoEq hcover)
      hs
      (by
        intro i
        simpa using
          congrArg (fun f => f i)
            (coordFamilyOfSection_sectionOfCompatibleCoordFamily
              (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
              (coordFamilyOfSection (s := s) et Kc hKc hs)
              (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
              hKoEq hcover))

/-- On a finite compact trivializing cover of a Hausdorff base, continuous sections are equivalent
to compatible compact coordinate families. -/
noncomputable def continuousSectionEquivCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    {s : Π x : M, V x // Continuous (T% s)} ≃ CompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo where
  toFun s := compatibleCoordFamilyOfSection (𝕜 := 𝕜) (s := s.1) et Kc hKc Ko hKo s.2
  invFun u :=
    ⟨sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover,
      continuous_sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover⟩
  left_inv s := by
    apply Subtype.ext
    exact sectionOfCompatibleCoordFamily_coordFamilyOfSection
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover s.2
  right_inv u := by
    apply Subtype.ext
    exact coordFamilyOfSection_sectionOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover

/-- The predicate-style compatible coordinate family type is equivalent to the corresponding kernel
submodule. -/
noncomputable def compatibleCoordFamilyEquivSubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo where
  toFun u :=
    ⟨u.1, (mem_compatibleCoordFamilySubmodule_iff
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).2 u.2⟩
  invFun u :=
    ⟨u.1, (mem_compatibleCoordFamilySubmodule_iff
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).1 u.2⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl

/-- Combining the finite-cover reconstruction equivalence with the kernel packaging identifies
continuous sections with the closed compatibility kernel itself. -/
noncomputable def continuousSectionEquivCompatibleCoordFamilySubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    {s : Π x : M, V x // Continuous (T% s)} ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :=
  (continuousSectionEquivCompatibleCoordFamily
    (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover).trans
    (compatibleCoordFamilyEquivSubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)

/-- Bundled continuous sections, viewed relative to a fixed finite compact trivializing cover. The
cover data appears in the type so that later transported normed-space instances depend on the chosen
section-space model rather than on the raw subtype of continuous sections. -/
structure ContinuousSectionSpace
    (𝕜 : Type*)
    [NontriviallyNormedField 𝕜]
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) where
  toFun : Π x : M, V x
  continuous_toFun : Continuous (T% toFun)

namespace ContinuousSectionSpace

instance
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ} :
    CoeFun (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
      (fun _ => Π x : M, V x) :=
  ⟨ContinuousSectionSpace.toFun⟩

@[ext]
theorem ext
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    (h : ∀ x : M, s x = t x) :
    s = t := by
  cases s with
  | mk sf sc =>
    cases t with
    | mk tf tc =>
      have hfun : sf = tf := funext h
      cases hfun
      rfl

@[simp]
lemma continuous
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :
    Continuous (T% (s : Π x : M, V x)) := by
  simpa using s.continuous_toFun

/-- Forget the wrapper and recover the raw subtype of continuous sections. -/
def toSubtype
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover ≃
      {s : Π x : M, V x // Continuous (T% s)} where
  toFun s := ⟨s, s.continuous_toFun⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- The transported section space is equivalent to the closed compatibility-kernel submodule. -/
noncomputable def equivCompatibleCoordFamilySubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :=
  (toSubtype (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover).trans
    (continuousSectionEquivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover)

instance instAddCommGroup
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    AddCommGroup (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.addCommGroup

instance instModule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Module 𝕜 (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : AddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.module 𝕜

instance instNormedAddCommGroup
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedAddCommGroup (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  exact e.normedAddCommGroup

instance instNormedSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedSpace 𝕜 (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedSpace 𝕜
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedSpace
      (𝕜 := 𝕜) (R := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.normedSpace 𝕜

instance instCompleteSpace
    {κ : Type*} [Finite κ] [T2Space M] [CompleteSpace F]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    CompleteSpace (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  have hIso : Isometry e := by
    intro x y
    rfl
  exact (completeSpace_congr (e := e) hIso.isUniformEmbedding).2 inferInstance

/-- The coordinate-family representation of a continuous section as a continuous linear map. -/
noncomputable def toCompatibleCoordFamilySubmoduleContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      →L[𝕜] compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedSpace 𝕜
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedSpace
      (𝕜 := 𝕜) (R := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : AddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Module 𝕜
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instModule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : NormedSpace 𝕜
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedSpace (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  refine
    { toLinearMap :=
        { toFun := e
          map_add' := by
            intro s t
            change e (e.symm (e s + e t)) = e s + e t
            simp
          map_smul' := by
            intro c s
            change e (e.symm (c • e s)) = c • e s
            simp }
      cont := ?_ }
  have hIso : Isometry e := by
    intro s t
    rfl
  exact hIso.continuous

@[simp]
lemma toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    toCompatibleCoordFamilySubmoduleContinuousLinearMap
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s =
      equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s := rfl

/-- Read one compact coordinate component of a continuous section as a continuous linear map. -/
noncomputable def coordReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      →L[𝕜] F :=
  (ContinuousMap.evalCLM (R := 𝕜) (M := F) x).comp
    ((ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)))

@[simp]
lemma coordReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordReadoutContinuousLinearMap
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover i x s =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x := rfl

/-- Uniform control of every compact coordinate readout controls the transported finite-cover
section norm.  This is the basic bridge from fiberwise/local approximation estimates to the Banach
norm on `ContinuousSectionSpace`. -/
theorem dist_le_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) ≤ C) :
    dist s t ≤ C := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := by
    intro x y
    rfl
  rw [← he.dist_eq s t]
  change dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1) ≤ C
  rw [dist_pi_le_iff hC]
  intro i
  exact (ContinuousMap.dist_le hC).2 (hcoord i)

/-- Coordinatewise finite-cover Lipschitz estimates imply a `LipschitzOnWith` estimate for a
section-space map in the transported finite-cover norm.  This is the norm-level handoff needed when
local chart estimates control every compact coordinate readout of a vector field. -/
theorem lipschitzOnWith_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (hcoord : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
          ≤ (L : ℝ) * dist s t) :
    LipschitzOnWith L A stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro s hs t ht
  exact dist_le_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := A s) (t := A t)
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg)
    (fun i x => hcoord hs ht i x)

/-- A finite coordinate-family Lipschitz estimate gives the pointwise compact-coordinate
distance estimates expected by local chart handoffs. -/
theorem forall_coord_dist_le_of_coordFamily_lipschitzOnWith
    {κ : Type*} [Fintype κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (h : LipschitzOnWith L
      (fun s =>
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 :
            CoordFamily (F := F) Kc))
      stateSet) :
    ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet → ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
        ≤ (L : ℝ) * dist s t := by
  intro s hs t ht i x
  have hC : 0 ≤ (L : ℝ) * dist s t :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist := h.dist_le_mul s hs t ht
  have hi :
      dist
          (((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 :
              CoordFamily (F := F) Kc) i)
          (((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 :
              CoordFamily (F := F) Kc) i)
        ≤ (L : ℝ) * dist s t :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi x

/-- Time-parameterized version of
`ContinuousSectionSpace.lipschitzOnWith_of_forall_coord_dist_le`: coordinatewise finite-cover
estimates on each time slice produce the corresponding family of section-space Lipschitz
estimates. -/
theorem lipschitzOnWith_family_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (hcoord : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ (L : ℝ) * dist s t) :
    ∀ τ ∈ timeSet, LipschitzOnWith L (A τ) stateSet := by
  intro τ hτ
  exact lipschitzOnWith_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ) (L := L)
    (fun s hs t ht i x => hcoord τ hτ hs ht i x)

/-- Time-parameterized version of
`ContinuousSectionSpace.forall_coord_dist_le_of_coordFamily_lipschitzOnWith`: finite coordinate
readout Lipschitz estimates on each time slice give the pointwise coordinate estimates consumed by
preferred-cover chart builders. -/
theorem forall_coord_dist_le_family_of_coordFamily_lipschitzOnWith
    {κ : Type*} [Fintype κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (h : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun s =>
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 :
              CoordFamily (F := F) Kc))
        stateSet) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ (L : ℝ) * dist s t := by
  intro τ hτ
  exact forall_coord_dist_le_of_coordFamily_lipschitzOnWith
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ) (L := L) (h τ hτ)

/-- Strict coordinatewise control yields strict control in the transported finite-cover section
norm. -/
theorem dist_lt_of_forall_coord_dist_lt
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 < C)
    (hcoord : ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) < C) :
    dist s t < C := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := by
    intro x y
    rfl
  rw [← he.dist_eq s t]
  change dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1) < C
  rw [dist_pi_lt_iff hC]
  intro i
  exact (ContinuousMap.dist_lt_iff hC).2 (hcoord i)

/-- Fiberwise approximation estimates imply finite-cover section-space approximation when the
coordinate readouts are uniformly Lipschitz with respect to the chosen fiber distances.  This is the
bookkeeping form needed after bounding a finite trivializing family on compact sets. -/
theorem dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    {κ : Type*} [Finite κ] [T2Space M]
    [∀ x, PseudoMetricSpace (V x)]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {L η C : ℝ} (hL : 0 < L) (hC : 0 < C) (hLC : L * η < C)
    (hfiber : ∀ x : M, dist (s x) (t x) < η)
    (hcoordLip : ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ L * dist (s x.1) (t x.1)) :
    dist s t < C := by
  refine dist_lt_of_forall_coord_dist_lt
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := s) (t := t) hC ?_
  intro i x
  exact lt_of_le_of_lt (hcoordLip i x)
    ((mul_lt_mul_of_pos_left (hfiber x.1) hL).trans hLC)

/-- A fiberwise approximation theorem upgrades to approximation in the transported finite-cover
section norm once the finite coordinate readouts satisfy a uniform Lipschitz estimate. -/
theorem exists_dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    {κ : Type*} [Finite κ] [T2Space M]
    [∀ x, PseudoMetricSpace (V x)]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {P : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover → Prop}
    {L : ℝ} (hL : 0 < L)
    (happrox : ∀ η > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover,
        P u ∧ ∀ x : M, dist (s x) (u x) < η)
    (hcoordLip : ∀ u,
      P u →
      ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover u).1 i x)
          ≤ L * dist (s x.1) (u x.1)) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover,
        P u ∧ dist s u < ε := by
  intro ε hε
  let η : ℝ := ε / L / 2
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hLη : L * η < ε := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have hcalc : L * η = ε / 2 := by
      dsimp [η]
      field_simp [hLne]
    rw [hcalc]
    linarith
  rcases happrox η hηpos with ⟨u, huP, hufiber⟩
  refine ⟨u, huP, ?_⟩
  exact dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := s) (t := u) hL hε hLη hufiber (hcoordLip u huP)

/-- Two finite-cover section-space points are equal when all compact coordinate readouts agree. -/
theorem eq_of_coordReadout_eq
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    (hcoord : ∀ i (x : Kc i),
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) :
    s = t := by
  apply (equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover).injective
  apply Subtype.ext
  funext i
  ext x
  exact hcoord i x

end ContinuousSectionSpace

end CoverCompatibility

end

namespace ContinuousSectionSpace

section TrivializationOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The compact coordinate readouts of two sections are Lipschitz with the op-norm of the
corresponding fiber trivialization. This turns a uniform bound on a finite family of
trivialization maps into the `hcoordLip` hypothesis used by the fiberwise approximation bridge. -/
theorem coord_dist_le_of_trivialization_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {L : ℝ}
    (hL : ∀ i (x : Kc i), ‖(et i).continuousLinearMapAt 𝕜 x.1‖ ≤ L)
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ L * dist (s x.1) (t x.1) := by
  intro i x
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have hx : x.1 ∈ (et i).baseSet := hKc i x.2
  have hscoord :
      ((e s).1 i x) = (et i).continuousLinearMapAt 𝕜 x.1 (s x.1) := by
    simp [e, equivCompatibleCoordFamilySubmodule, toSubtype,
      continuousSectionEquivCompatibleCoordFamilySubmodule,
      continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
      compatibleCoordFamilyOfSection, coordFamilyOfSection, coordContinuousMap,
      Bundle.Trivialization.linearMapAt_apply, hx]
  have htcoord :
      ((e t).1 i x) = (et i).continuousLinearMapAt 𝕜 x.1 (t x.1) := by
    simp [e, equivCompatibleCoordFamilySubmodule, toSubtype,
      continuousSectionEquivCompatibleCoordFamilySubmodule,
      continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
      compatibleCoordFamilyOfSection, coordFamilyOfSection, coordContinuousMap,
      Bundle.Trivialization.linearMapAt_apply, hx]
  calc
    dist ((e s).1 i x) ((e t).1 i x)
        = dist ((et i).continuousLinearMapAt 𝕜 x.1 (s x.1))
            ((et i).continuousLinearMapAt 𝕜 x.1 (t x.1)) := by rw [hscoord, htcoord]
    _ ≤ ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * dist (s x.1) (t x.1) :=
      ContinuousLinearMap.dist_le_opNorm ((et i).continuousLinearMapAt 𝕜 x.1) (s x.1) (t x.1)
    _ ≤ L * dist (s x.1) (t x.1) := by
      exact mul_le_mul_of_nonneg_right (hL i x) dist_nonneg

/-- The compact coordinate readout of a section at a point of its trivializing piece is the
trivialization's fiberwise linear map applied to the pointwise value.  This is the named form of the
`hscoord`/`htcoord` computation used throughout the finite-cover norm bridge. -/
theorem coord_apply
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x =
      (et i).continuousLinearMapAt 𝕜 x.1 (s x.1) := by
  have hx : x.1 ∈ (et i).baseSet := hKc i x.2
  simp [equivCompatibleCoordFamilySubmodule, toSubtype,
    continuousSectionEquivCompatibleCoordFamilySubmodule,
    continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
    compatibleCoordFamilyOfSection, coordFamilyOfSection, coordContinuousMap,
    Bundle.Trivialization.linearMapAt_apply, hx]

/-- Inversion of `coord_apply`: on a trivializing piece the pointwise value of a section is
recovered from its compact coordinate readout by the trivialization's backwards fiber map. -/
theorem apply_eq_symmL_coord
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    {i : κ} {x : M} (hi : x ∈ (Kc i : Set M)) :
    s x =
      (et i).symmL 𝕜 x
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i ⟨x, hi⟩) := by
  have hx : x ∈ (et i).baseSet := hKc i hi
  rw [coord_apply s i ⟨x, hi⟩]
  exact ((et i).symmL_continuousLinearMapAt hx (s x)).symm

/-- The algebraic zero section evaluates pointwise to zero. -/
@[simp]
theorem zero_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (x : M) :
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) hi]
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  rw [he0]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply, map_zero]

end TrivializationOpNorm

end ContinuousSectionSpace

end Bundle.Trivialization

end PoincareCurvature
