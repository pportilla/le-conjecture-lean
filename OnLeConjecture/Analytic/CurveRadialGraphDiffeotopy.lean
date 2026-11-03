/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveRadialGraphMotion
public import OnLeConjecture.Analytic.PlaneMilnorBoundarySmooth
public import OnLeConjecture.DifferentialTopology.CompactMotionVelocity

/-! # Ambient transport of a retained curve circle to a radial graph

An analytic curve embedded and immersed on its punctured parameter disk
carries the explicit radial motion to a native Euclidean ambient diffeotopy.
The initial circle is not assumed to lie on a target norm sphere.
-/

@[expose] public noncomputable section

open Set Metric Function Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

set_option backward.isDefEq.respectTransparency false in
/-- Explicit radial interpolation of the same analytic curve has a native
ambient diffeotopy, with both endpoint parametrizations retained. -/
theorem exists_curve_radialGraph_diffeotopy {F : ℂ → E} {R : ℝ} (hR : 0 < R)
    (ha : AnalyticOnNhd ℂ F (closedBall 0 R))
    (hi : InjOn F (closedBall 0 R))
    (hd : ∀ z ∈ closedBall 0 R, z ≠ 0 → Injective (fderiv ℂ F z))
    (ρ : Circle → ℝ) (hρ : ∀ u, 0 < ρ u ∧ ρ u ≤ R)
    (hs : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ) :
    ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, E) ∞ E,
      (∀ t : unitInterval, ∀ u : Circle,
        Φ (t, F (R • (u : ℂ))) = F (radialGraphMotion R ρ (t, u))) ∧
      (∀ u : Circle, Φ.final (F (R • (u : ℂ))) = F (ρ u • (u : ℂ))) ∧
      (∀ u : Circle, Φ.final (F (R • ((u⁻¹ : Circle) : ℂ))) =
        F (ρ u⁻¹ • ((u⁻¹ : Circle) : ℂ))) := by
  let q := radialGraphMotion R ρ
  let G : ℝ × Circle → E := fun p => F (q p)
  have hq := radialGraphMotion_contMDiff R hs
  have hqmem (p : ℝ × Circle) : q p ∈ closedBall 0 R := by
    rw [mem_closedBall_zero_iff, radialGraphMotion_norm hR (fun u => (hρ u).1)]
    exact radialGraphMotionRadius_le (fun u => (hρ u).2) p
  have hqne (p : ℝ × Circle) : q p ≠ 0 := norm_pos_iff.mp (by
    rw [radialGraphMotion_norm hR (fun u => (hρ u).1)]
    exact radialGraphMotionRadius_pos hR (fun u => (hρ u).1) p)
  have hG : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞ G := by
    intro p
    exact ((ha (q p) (hqmem p)).restrictScalars.contDiffAt.contMDiffAt).comp p hq.contMDiffAt
  have hGi (t : ℝ) : Injective (fun u => G (t, u)) := by
    intro u v huv
    exact radialGraphMotion_injective hR (fun u => (hρ u).1) t
      (hi (hqmem (t, u)) (hqmem (t, v)) huv)
  have hGd (t : ℝ) (u : Circle) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => G (t, v)) u) := by
    have hF := (ha (q (t, u)) (hqmem (t, u))).differentiableAt
    have hqs : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v => q (t, v)) :=
      hq.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (F ∘ fun v => q (t, v)) u)
    rw [mfderiv_comp u (hF.restrictScalars ℝ).mdifferentiableAt
      (hqs.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
      hF.fderiv_restrictScalars ℝ]
    exact (hd _ (hqmem (t, u)) (hqne (t, u))).comp
      (radialGraphMotion_mfderiv_injective hR (fun v => (hρ v).1) hs t u)
  have hGa (t : ℝ) (ht : t ≤ 0) (u : Circle) : G (t, u) = G (0, u) := by
    simp only [G, q, radialGraphMotion_of_nonpos R ρ ht,
      radialGraphMotion_of_nonpos R ρ le_rfl]
  have hGb (t : ℝ) (ht : 1 ≤ t) (u : Circle) : G (t, u) = G (1, u) := by
    simp only [G, q, radialGraphMotion_of_one_le R ρ ht,
      radialGraphMotion_of_one_le R ρ le_rfl]
  obtain ⟨X, hX, hcX, hderiv⟩ := exists_compact_motion_velocity hG hGi hGd hGa hGb
  obtain ⟨K, hK⟩ := exists_lipschitz_timeDependentSuspension
    (contDiff_infty.mp hX 1) hcX
  let Φ := timeDependentEvolutionDiffeotopy X hK hX
  have hfollow (t : unitInterval) (u : Circle) : Φ (t, G (0, u)) = G (t, u) := by
    exact (TauCeti.eq_timeDependentFlow X hK (fun s => hderiv s u) 0 t).symm
  have hfinal (u : Circle) : Φ.final (F (R • (u : ℂ))) = F (ρ u • (u : ℂ)) := by
    have h := hfollow 1 u
    change Φ (1, F (radialGraphMotion R ρ (0, u))) =
      F (radialGraphMotion R ρ (1, u)) at h
    rw [TauCeti.Diffeotopy.final_apply]
    simpa only [radialGraphMotion_of_nonpos R ρ le_rfl,
      radialGraphMotion_of_one_le R ρ le_rfl] using h
  refine ⟨Φ, ?_, hfinal, fun u => hfinal u⁻¹⟩
  intro t u
  simpa only [G, q, radialGraphMotion_of_nonpos R ρ le_rfl] using hfollow t u

end OnLeConjecture.Analytic
