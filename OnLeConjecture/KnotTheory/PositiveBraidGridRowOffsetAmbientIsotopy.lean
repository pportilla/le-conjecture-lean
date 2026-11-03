/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRowOffsetInterpolation

/-! # Native ambient independence of the row-offset choice

The source cylinder embedding is fixed. A native ambient diffeotopy follows the
convex interpolation of two admissible offsets at every time. Common offset
values give curve points fixed throughout the ambient motion.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance offsetAmbientRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance offsetAmbientRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- Any two admissible row offsets of the same native cylinder embedding are
joined by an actual ambient diffeotopy following their convex interpolation.
Every source curve point where the offsets agree is fixed at every time. -/
theorem exists_positiveGridRowOffset_choice_diffeotopy (i : Fin 2)
    {F : Circle → Circle × ℂ}
    (hF : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F)
    (hFi : Function.Injective F)
    (hFd : ∀ v, Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) F v))
    {q₀ q₁ : ℂ × ℝ → ℝ} (hqs₀ : ContDiff ℝ ∞ q₀) (hqs₁ : ContDiff ℝ ∞ q₁)
    (hq₀ : LipschitzWith (1 / 2) q₀) (hq₁ : LipschitzWith (1 / 2) q₁)
    (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ v, (A v : EuclideanSpace ℂ (Fin 2)) =
      planeSolidTorusMap i (positiveGridRowShearCylinder q₀ 1 (F v)))
    (hB : ∀ v, (B v : EuclideanSpace ℂ (Fin 2)) =
      planeSolidTorusMap i (positiveGridRowShearCylinder q₁ 1 (F v))) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ t : unitInterval, ∀ v,
        (Φ (t, A v) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder
            (positiveGridRowOffsetInterpolation q₀ q₁ t) 1 (F v))) ∧
      (∀ v, Φ.final (A v) = B v) ∧
      ∀ v, q₀ (((F v).1 : ℂ), (F v).2.re) = q₁ (((F v).1 : ℂ), (F v).2.re) →
        ∀ t : unitInterval, Φ (t, A v) = A v := by
  let H : Circle × ℝ → Circle × ℂ := fun p => positiveGridRowShearCylinder
    (positiveGridRowOffsetInterpolation q₀ q₁ p.2) 1 (F p.1)
  have hFc : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : Circle × ℝ => F p.1) := hF.comp contMDiff_fst
  have hcoord : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun p : Circle × ℝ => (((F p.1).1 : ℂ), (F p.1).2.re)) :=
    (contMDiff_coe_sphere.comp hFc.fst).prodMk_space
      (Complex.reCLM.contDiff.comp_contMDiff hFc.snd)
  have hQ : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun p : Circle × ℝ => positiveGridRowOffsetInterpolation q₀ q₁ p.2
        (((F p.1).1 : ℂ), (F p.1).2.re)) :=
    (positiveGridRowOffsetInterpolation_contDiff hqs₀ hqs₁).contMDiff.comp
      (contMDiff_snd.prodMk_space hcoord)
  have hH : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ H := by
    simp only [H, positiveGridRowShearCylinder, positiveGridRowShear_one]
    exact hFc.fst.prodMk (hFc.snd.add (Complex.ofRealCLM.contDiff.comp_contMDiff hQ))
  have hHs (s : ℝ) : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (fun v => H (v, s)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hHi (s : ℝ) : Function.Injective (fun v => H (v, s)) :=
    (positiveGridRowShearCylinder_injective
      (positiveGridRowOffsetInterpolation_lipschitz hq₀ hq₁ s) 1).comp hFi
  have hHd (s : ℝ) (v : Circle) : Function.Injective
      (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) (fun v => H (v, s)) v) := by
    have hqss : ContDiff ℝ ∞ (positiveGridRowOffsetInterpolation q₀ q₁ s) :=
      (positiveGridRowOffsetInterpolation_contDiff hqs₀ hqs₁).comp
        (contDiff_const.prodMk contDiff_id)
    have hshear : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (positiveGridRowShearCylinder (positiveGridRowOffsetInterpolation q₀ q₁ s) 1) :=
      (positiveGridRowShearCylinder_contMDiff hqss).comp
        (contMDiff_id.prodMk contMDiff_const)
    change Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ))
      (positiveGridRowShearCylinder (positiveGridRowOffsetInterpolation q₀ q₁ s) 1 ∘ F) v)
    rw [mfderiv_comp v (hshear.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (positiveGridRowShearCylinder_mfderiv_injective hqss
      (positiveGridRowOffsetInterpolation_lipschitz hq₀ hq₁ s) 1 _).comp (hFd v)
  let K : Circle × ℝ → EuclideanSpace ℂ (Fin 2) := fun p => planeSolidTorusMap i (H p)
  have hK : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K :=
    (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp hH
  have hKn (s : ℝ) (v : Circle) : ‖K (v, s)‖ = 1 := planeSolidTorusMap_norm i _
  have hKi (s : ℝ) : Function.Injective (fun v : Circle => K (v, s)) :=
    (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.injective.comp (hHi s)
  have hKd (s : ℝ) (v : Circle) : Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K (v, s)) v) := by
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (planeSolidTorusMap i ∘ (fun v => H (v, s))) v)
    rw [mfderiv_comp v
      ((planeSolidTorusMap_isSmoothEmbedding i).contMDiff.mdifferentiableAt (by simp))
      ((hHs s).mdifferentiableAt (by simp))]
    exact (positiveGridSolidTorus_mfderiv_injective i _).comp (hHd s v)
  let G : ℝ × Circle → EuclideanSpace ℂ (Fin 2) := fun p => K (p.2, p.1)
  have hG : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ G :=
    hK.comp (contMDiff_snd.prodMk contMDiff_fst)
  have ha : ∀ s ≤ 0, ∀ v, G (s, v) = G (0, v) := by
    intro s hs v
    simp only [G, K, H, positiveGridRowOffsetInterpolation_of_nonpos _ _ hs,
      positiveGridRowOffsetInterpolation_zero]
  have hb : ∀ s, 1 ≤ s → ∀ v, G (s, v) = G (1, v) := by
    intro s hs v
    simp only [G, K, H, positiveGridRowOffsetInterpolation_of_one_le _ _ hs,
      positiveGridRowOffsetInterpolation_one]
  obtain ⟨X, hX, hcX, hderiv⟩ := exists_compact_motion_velocity hG hKi hKd ha hb
  obtain ⟨Φ, hΦ⟩ := exists_sphereDiffeotopy_of_velocity_extension (n := 3) hX hcX
    (fun s v => G (s, v)) hKn hderiv
  have hAeq (v : Circle) : A v = ⟨G (0, v), by
      simpa only [Metric.mem_sphere, dist_zero_right] using hKn 0 v⟩ := by
    apply Subtype.ext
    simpa only [G, K, H, positiveGridRowOffsetInterpolation_zero] using hA v
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro s v
    rw [hAeq]
    exact hΦ s v
  · intro v
    apply Subtype.ext
    rw [TauCeti.Diffeotopy.final_apply, hAeq]
    exact (hΦ 1 v).trans (by
      simpa [G, K, H] using (hB v).symm)
  · intro v hv s
    apply Subtype.ext
    rw [hAeq, hΦ s v]
    dsimp only [G, K, H]
    rw [positiveGridRowOffsetInterpolation_shear_fixed (F v) hv s,
      positiveGridRowOffsetInterpolation_zero]

end OnLeConjecture.KnotTheory
