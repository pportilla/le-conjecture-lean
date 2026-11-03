/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DifferentialTopology.SmoothMotionTrack
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A compactly supported velocity extension of a stationary motion

The smooth velocity on the embedded track extends over a compact time
window by local retractions and a partition of unity. Multiplication by
a smooth time cutoff gives compact support and preserves the velocity
along the entire motion, which is stationary outside the unit interval.
-/

public noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.DifferentialTopology

variable {E V H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {G : ℝ × M → E}

omit [FiniteDimensional ℝ E] [CompleteSpace V] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The velocity used in the extension is the actual derivative of the motion. -/
theorem hasDerivAt_motionTimeVelocity
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G) (t : ℝ) (x : M) :
    HasDerivAt (fun s => G (s, x)) (motionTimeVelocity G (t, x)) t := by
  have hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s => G (s, x)) :=
    hG.comp (contMDiff_id.prodMk contMDiff_const)
  exact (hc.contDiff.differentiable (by simp) t).hasDerivAt

omit [FiniteDimensional ℝ E] [CompleteSpace V] [IsManifold I ∞ M] [I.Boundaryless] in
/-- Stationarity before time zero forces the time velocity to vanish there. -/
theorem motionTimeVelocity_zero_of_neg
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G)
    (ha : ∀ t ≤ 0, ∀ x, G (t, x) = G (0, x)) {t : ℝ} (ht : t < 0) (x : M) :
    motionTimeVelocity G (t, x) = 0 := by
  have hconst : HasDerivAt (fun s => G (s, x)) 0 t :=
    (hasDerivAt_const t (G (0, x))).congr_of_eventuallyEq (by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact ha s hs.le x)
  exact (hasDerivAt_motionTimeVelocity hG t x).unique hconst

omit [FiniteDimensional ℝ E] [CompleteSpace V] [IsManifold I ∞ M] [I.Boundaryless] in
/-- Stationarity after time one forces the time velocity to vanish there. -/
theorem motionTimeVelocity_zero_of_one_lt
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G)
    (hb : ∀ t, 1 ≤ t → ∀ x, G (t, x) = G (1, x)) {t : ℝ} (ht : 1 < t) (x : M) :
    motionTimeVelocity G (t, x) = 0 := by
  have hconst : HasDerivAt (fun s => G (s, x)) 0 t :=
    (hasDerivAt_const t (G (1, x))).congr_of_eventuallyEq (by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact hb s hs.le x)
  exact (hasDerivAt_motionTimeVelocity hG t x).unique hconst

/-- A smooth stationary motion of a compact source with injective immersed
slices admits a jointly smooth compactly supported ambient velocity field.
No ambient vector field or extension is supplied as a hypothesis. -/
theorem exists_compact_motion_velocity [CompactSpace M]
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G)
    (hi : ∀ t, Function.Injective (fun x => G (t, x)))
    (hd : ∀ t x, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => G (t, y)) x))
    (ha : ∀ t ≤ 0, ∀ x, G (t, x) = G (0, x))
    (hb : ∀ t, 1 ≤ t → ∀ x, G (t, x) = G (1, x)) :
    ∃ X : ℝ → E → E, ContDiff ℝ ∞ (Function.uncurry X) ∧
      HasCompactSupport (Function.uncurry X) ∧
      ∀ t x, HasDerivAt (fun s => G (s, x)) (X t (G (t, x))) t := by
  let track := TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (fun p => (p.1, G p))
    (isSmoothEmbedding_motion_track hG hi hd)
  let velocity : C^∞⟮𝓘(ℝ).prod I, ℝ × M; 𝓘(ℝ, E), E⟯ :=
    ⟨motionTimeVelocity G, motionTimeVelocity_contMDiff hG⟩
  obtain ⟨Y, hY, hcY, -⟩ := track.exists_contMDiffMap_extension_hasCompactSupport
    velocity (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M)))
    isOpen_univ (subset_univ _) (K := Icc (-1) 2 ×ˢ univ)
  have hYdiff : ContDiff ℝ ∞ (fun p : ℝ × E => Y p) := by
    apply contMDiff_iff_contDiff.mp
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact Y.contMDiff
  have hYon (t : ℝ) (ht : t ∈ Icc (-1) 2) (x : M) :
      Y (t, G (t, x)) = motionTimeVelocity G (t, x) := by
    simpa only [Function.comp_apply, track, TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply,
      velocity, ContMDiffMap.coeFn_mk] using
        hY (show (t, x) ∈ Icc (-1) 2 ×ˢ univ from ⟨ht, mem_univ x⟩)
  let χ : ℝ → ℝ := fun t => Real.smoothTransition (t + 1) * Real.smoothTransition (2 - t)
  have hχ : ContDiff ℝ ∞ χ := by fun_prop
  let X : ℝ → E → E := fun t y => χ t • Y (t, y)
  refine ⟨X, (hχ.comp contDiff_fst).smul hYdiff, hcY.smul_left, ?_⟩
  intro t x
  apply (hasDerivAt_motionTimeVelocity hG t x).congr_deriv
  change motionTimeVelocity G (t, x) = χ t • Y (t, G (t, x))
  by_cases ht : t ∈ Icc (-1) 2
  · rw [hYon t ht x]
    by_cases hunit : t ∈ Icc 0 1
    · have hone : χ t = 1 := by
        dsimp only [χ]
        rw [Real.smoothTransition.one_of_one_le (by linarith [hunit.1]),
          Real.smoothTransition.one_of_one_le (by linarith [hunit.2]), one_mul]
      rw [hone, one_smul]
    · have hzero : motionTimeVelocity G (t, x) = 0 := by
        rcases lt_or_ge t 0 with hneg | hnonneg
        · exact motionTimeVelocity_zero_of_neg hG ha hneg x
        · exact motionTimeVelocity_zero_of_one_lt hG hb
            (lt_of_not_ge (fun hle => hunit ⟨hnonneg, hle⟩)) x
      rw [hzero, smul_zero]
  · have hzero : χ t = 0 := by
      dsimp only [χ]
      rcases lt_or_ge t (-1) with hneg | hnonneg
      · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      · have hlarge : 2 < t := lt_of_not_ge (fun hle => ht ⟨hnonneg, hle⟩)
        rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - t ≤ 0), mul_zero]
    rw [hzero, zero_smul]
    rcases lt_or_ge t 0 with hneg | hnonneg
    · exact motionTimeVelocity_zero_of_neg hG ha hneg x
    · exact motionTimeVelocity_zero_of_one_lt hG hb
        (by have : 2 < t := lt_of_not_ge (fun hle => ht ⟨by linarith, hle⟩); linarith) x

end OnLeConjecture.DifferentialTopology
