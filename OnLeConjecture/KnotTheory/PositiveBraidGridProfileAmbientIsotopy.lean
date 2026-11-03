/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridProfileCircle

/-! # Ambient extension of the actual relative profile interpolation

A native ambient diffeotopy follows the actual convex profile motion at every
time. The same row shear is applied after the controlled pre-shear graphs.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance profileAmbientRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance profileAmbientRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The native ambient diffeotopy follows the actual convex profile interpolation
at every time, from the same supplied sheared initial embedding. -/
theorem exists_positiveRoundedWord_profileInterpolation_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    (i : Fin 2) {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hla₁ : ∀ j t, dist (l₁ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₁ : ∀ j t, dist (u₁ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hqlip : LipschitzWith (1 / 2) q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (σ k) 1
            (positiveRoundedWordPeriodTime w θ))))) :
    ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder q 1
            (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₁ u₁ (σ k) 1
              (positiveRoundedWordPeriodTime w θ))))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ t : unitInterval, ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (Φ (t, A (braidCircleSheet m k θ)) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) t
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        ∀ v, Φ.final (A v) = B v := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨F, hF, he⟩ := exists_positiveRoundedWordProfileInterpolation_circle_family hm w σ hσ
    hl₀ hu₀ hl₁ hu₁ hU' hls₀ hus₀ hls₁ hus₁
  have hreg := positiveRoundedWordProfileInterpolation_circle_regular hm w σ hσ hU
    hl₀ hu₀ hl₁ hu₁ hla₀ hua₀ hla₁ hua₁ hls₀ hus₀ hls₁ hus₁ he
  let H : Circle × ℝ → Circle × ℂ := fun p => positiveGridRowShearCylinder q 1 (F p)
  have hH : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ H :=
    (positiveGridRowShearCylinder_contMDiff hqs).comp (hF.prodMk contMDiff_const)
  let K : Circle × ℝ → EuclideanSpace ℂ (Fin 2) := fun p => planeSolidTorusMap i (H p)
  have hK : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K :=
    (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp hH
  have hKn (s : ℝ) (v : Circle) : ‖K (v, s)‖ = 1 := planeSolidTorusMap_norm i _
  have hKi (s : ℝ) : Function.Injective (fun v : Circle => K (v, s)) :=
    (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.injective.comp
      ((positiveGridRowShearCylinder_injective hqlip 1).comp (hreg s).1.injective)
  have hKd (s : ℝ) (v : Circle) : Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K (v, s)) v) := by
    have hFs : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (fun v : Circle => F (v, s)) :=
      hF.comp (contMDiff_id.prodMk (contMDiff_const (c := s)))
    have hShear : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (positiveGridRowShearCylinder q 1) :=
      (positiveGridRowShearCylinder_contMDiff hqs).comp
        (contMDiff_id.prodMk (contMDiff_const (c := (1 : ℝ))))
    have hHs : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (fun v : Circle => H (v, s)) :=
      hH.comp (contMDiff_id.prodMk (contMDiff_const (c := s)))
    rw [show (fun v => K (v, s)) = planeSolidTorusMap i ∘ (fun v => H (v, s)) from rfl,
      mfderiv_comp v
        ((planeSolidTorusMap_isSmoothEmbedding i).contMDiff.mdifferentiableAt (by simp))
        (hHs.mdifferentiableAt (by simp))]
    apply (positiveGridSolidTorus_mfderiv_injective i _).comp
    rw [show (fun v => H (v, s)) = positiveGridRowShearCylinder q 1 ∘
      (fun v => F (v, s)) from rfl,
      mfderiv_comp v (hShear.mdifferentiableAt (by simp)) (hFs.mdifferentiableAt (by simp))]
    exact (positiveGridRowShearCylinder_mfderiv_injective hqs hqlip 1 _).comp ((hreg s).2 v)
  have hKstationary (s : ℝ) (v : Circle) :
      (s ≤ 0 → K (v, s) = K (v, 0)) ∧ (1 ≤ s → K (v, s) = K (v, 1)) := by
    obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
    have hθ' := And.intro hθ.1 hθ.2.le
    change (s ≤ 0 → planeSolidTorusMap i (positiveGridRowShearCylinder q 1
      (F (braidCircleSheet m k θ, s))) = _) ∧ _
    constructor <;> intro hs
    · dsimp only [K, H]
      rw [he k θ s hθ', he k θ 0 hθ']
      simp only [positiveRoundedWordProfileInterpolation,
        positiveGridProfileInterpolation_of_nonpos _ _ hs, positiveGridProfileInterpolation_zero]
    · dsimp only [K, H]
      rw [he k θ s hθ', he k θ 1 hθ']
      simp only [positiveRoundedWordProfileInterpolation,
        positiveGridProfileInterpolation_of_one_le _ _ hs, positiveGridProfileInterpolation_one]
  let G : ℝ × Circle → EuclideanSpace ℂ (Fin 2) := fun p => K (p.2, p.1)
  have hG : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ G :=
    hK.comp (contMDiff_snd.prodMk contMDiff_fst)
  obtain ⟨X, hX, hcX, hderiv⟩ := exists_compact_motion_velocity hG hKi hKd
    (fun s hs v => (hKstationary s v).1 hs) (fun s hs v => (hKstationary s v).2 hs)
  obtain ⟨Φ, hΦ⟩ := exists_sphereDiffeotopy_of_velocity_extension (n := 3) hX hcX
    (fun s v => G (s, v)) hKn hderiv
  have hA₀ (v : Circle) : (A v : EuclideanSpace ℂ (Fin 2)) = K (v, 0) := by
    obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
    rw [hA k θ ⟨hθ.1, hθ.2.le⟩]
    dsimp only [K, H]
    rw [he k θ 0 ⟨hθ.1, hθ.2.le⟩]
    simp only [positiveRoundedWordProfileInterpolation, positiveGridProfileInterpolation_zero]
  have hmem (v : Circle) : K (v, 1) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hKn 1 v
  let B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
    TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (Set.codRestrict (fun v : Circle => K (v, 1))
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) hmem)
    (isSmoothEmbedding_codRestrict_unit_sphere (n := 3)
      (hK.comp (contMDiff_id.prodMk contMDiff_const)) hmem (hKd 1)
      ((hK.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
        (hKi 1)).isEmbedding)
  have hBcoe (v : Circle) : (B v : EuclideanSpace ℂ (Fin 2)) = K (v, 1) := by
    simp only [B, TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply]
    rfl
  refine ⟨B, ?_, Φ, ?_, ?_⟩
  · intro k θ hθ
    rw [hBcoe]
    dsimp only [K, H]
    rw [he k θ 1 hθ]
    simp only [positiveRoundedWordProfileInterpolation, positiveGridProfileInterpolation_one]
  · intro s k θ hθ
    have hh := hΦ s (braidCircleSheet m k θ)
    have hAA : A (braidCircleSheet m k θ) = ⟨G (0, braidCircleSheet m k θ), by
        simpa only [Metric.mem_sphere, dist_zero_right] using hKn 0 (braidCircleSheet m k θ)⟩ :=
      Subtype.ext (hA₀ _)
    rw [hAA]
    change _ = planeSolidTorusMap i (positiveGridRowShearCylinder q 1 _)
    rw [hh]
    dsimp only [G, K, H]
    rw [he k θ s hθ]
  · intro v
    apply Subtype.ext
    have hh := hΦ 1 v
    have hAA : A v = ⟨G (0, v), by
        simpa only [Metric.mem_sphere, dist_zero_right] using hKn 0 v⟩ := Subtype.ext (hA₀ v)
    rw [TauCeti.Diffeotopy.final_apply, hAA]
    rw [hBcoe]
    exact hh

/-- For two admissible profile pairs supported at the same own vertices, the
ambient extension follows their convex interpolation and fixes every curve
point outside those original own-corner parameter supports at every time. -/
theorem exists_positiveRoundedWord_own_profile_relative_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    (i : Fin 2) {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1 / 48)
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hla₁ : ∀ j t, dist (l₁ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₁ : ∀ j t, dist (u₁ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hqlip : LipschitzWith (1 / 2) q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (σ k) 1
            (positiveRoundedWordPeriodTime w θ))))) :
    ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder q 1
            (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₁ u₁ (σ k) 1
              (positiveRoundedWordPeriodTime w θ))))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ t : unitInterval, ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (Φ (t, A (braidCircleSheet m k θ)) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) t
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        (∀ v, Φ.final (A v) = B v) ∧
        ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (¬ ∃ j c o, PositiveRoundedWordOwnCornerParameter w δ (σ k)
            (positiveRoundedWordPeriodTime w θ) j c o) →
          ∀ t : unitInterval, Φ (t, A (braidCircleSheet m k θ)) = A (braidCircleSheet m k θ) := by
  have hlc₀ (j) := (hl₀ j).mono
    (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc₀ (j) := (hu₀ j).mono
    (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  have hlc₁ (j) := (hl₁ j).mono
    (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc₁ (j) := (hu₁ j).mono
    (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  obtain ⟨B, hB, Φ, hΦ, hfinal⟩ := exists_positiveRoundedWord_profileInterpolation_diffeotopy
    hm w σ hσ i (positiveGridRoundingCornerNeighborhood_subset hδ) hlc₀ huc₀ hlc₁ huc₁
      hla₀ hua₀ hla₁ hua₁ hls₀ hus₀ hls₁ hus₁ hqs hqlip A hA
  refine ⟨B, hB, Φ, hΦ, hfinal, ?_⟩
  intro k θ hθ hout s
  apply Subtype.ext
  rw [hΦ s k θ hθ,
    positiveRoundedWordProfileInterpolation_fixed_outside_own_corners w hδ hl₀ hu₀ hl₁ hu₁
      (σ k) s (positiveRoundedWordPeriodTime_mem w hθ) hout,
    hA k θ hθ]

/-- Any independently supplied terminal embedding with the exact fixed profile
formula is reached by the same relative ambient profile interpolation. -/
theorem exists_positiveRoundedWord_own_profile_relative_diffeotopy_to_embedding {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    (i : Fin 2) {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1 / 48)
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hla₁ : ∀ j t, dist (l₁ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₁ : ∀ j t, dist (u₁ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hqlip : LipschitzWith (1 / 2) q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (σ k) 1
            (positiveRoundedWordPeriodTime w θ)))))
    (B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hB : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₁ u₁ (σ k) 1
            (positiveRoundedWordPeriodTime w θ))))) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ t : unitInterval, ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (Φ (t, A (braidCircleSheet m k θ)) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder q 1
            (positiveRectilinearCylinderPoint w
              (positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) t
                (positiveRoundedWordPeriodTime w θ))))) ∧
      (∀ v, Φ.final (A v) = B v) ∧
      ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (¬ ∃ j c o, PositiveRoundedWordOwnCornerParameter w δ (σ k)
          (positiveRoundedWordPeriodTime w θ) j c o) →
        ∀ t : unitInterval, Φ (t, A (braidCircleSheet m k θ)) = A (braidCircleSheet m k θ) := by
  obtain ⟨B', hB', Φ, hΦ, hfinal, hfixed⟩ :=
    exists_positiveRoundedWord_own_profile_relative_diffeotopy hm w σ hσ i hδ
      hl₀ hu₀ hl₁ hu₁ hla₀ hua₀ hla₁ hua₁ hls₀ hus₀ hls₁ hus₁ hqs hqlip A hA
  refine ⟨Φ, hΦ, ?_, hfixed⟩
  intro v
  rw [hfinal]
  obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
  exact Subtype.ext ((hB' k θ ⟨hθ.1, hθ.2.le⟩).trans (hB k θ ⟨hθ.1, hθ.2.le⟩).symm)

end OnLeConjecture.KnotTheory
