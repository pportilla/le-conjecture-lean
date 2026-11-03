/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetBoundary
public import OnLeConjecture.Analytic.CurveLocalImageShrink

/-! # Confinement of target cuts of an assembled section

Compact unique-fibre image shrinking, together with the proved injectivity
of the assembled map, confines every sufficiently small Euclidean target cut
to a strictly smaller open source ball. The same chosen map, source radii,
target radius and nearby level retain the target-boundary submersivity.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

/-- The existing compact-fibre image comparison confines every preimage
because the map is injective on the fixed closed source ball. -/
theorem exists_euclidean_target_cut_confinement
    (H : Source 2 → Source 3) (hH0 : H 0 = 0)
    {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hH : ContinuousOn H (closedBall (0 : Source 2) R))
    (hinj : InjOn H (closedBall (0 : Source 2) R)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ x ∈ closedBall (0 : Source 2) R,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε₀ →
        x ∈ ball (0 : Source 2) r := by
  let Q : Source 2 → EuclideanSpace ℂ (Fin 3) :=
    fun x => (EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)
  have hQ : ContinuousOn Q (closedBall (0 : Source 2) R) :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn hH
  have hQinj : InjOn Q (closedBall (0 : Source 2) R) := by
    intro x hx y hy hxy
    exact hinj hx hy ((EuclideanSpace.equiv (Fin 3) ℂ).symm.injective hxy)
  have hQ0 : Q 0 = 0 := by simp only [Q, hH0, map_zero]
  have hsmall := eventually_mem_image_iff_of_compact_unique_fibre
    (isCompact_closedBall (0 : Source 2) R) hQ (ball_mem_nhds _ hr)
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le))
    (fun x hx hzero => hQinj hx (mem_closedBall_self (hr.le.trans hrR.le))
      (hzero.trans hQ0.symm))
  obtain ⟨ε, hε, hεsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro x hx hxε
  have hQx : Q x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) ε :=
    mem_ball_zero_iff.mpr (hxε.trans_lt (half_lt_self hε))
  obtain ⟨y, hy, hyx⟩ := (hεsmall hQx).mpr ⟨x, hx, rfl⟩
  have hyR : y ∈ closedBall (0 : Source 2) R :=
    ball_subset_closedBall (ball_subset_ball hrR.le hy)
  exact hQinj hyR hx hyx ▸ hy

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- One fixed closed source ball and a strictly smaller open ball contain
all sufficiently small target cuts. The same actual nearby level has a
submersive boundary at each chosen target radius. -/
theorem exists_confined_target_boundary_levels (A : ResolutionSectionAssembly g hd hi) :
    ∃ R r ε₀ : ℝ, 0 < r ∧ r < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
      InjOn A.H (closedBall (0 : Source 2) R) ∧
      (∀ x ∈ closedBall (0 : Source 2) R,
        ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε₀ →
          x ∈ ball (0 : Source 2) r) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ L : ResolutionSectionLevel A, L.radius = R ∧ ‖L.parameter‖ < ε ∧
          (∀ x ∈ L.sourceLevel,
            ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε →
              x ∈ ball (0 : Source 2) r) ∧
          (∀ x ∈ L.sourceLevel,
            ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ = ε →
              Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x)) := by
  obtain ⟨B, hB, hBA, haB, hboundary⟩ := A.exists_target_boundary_submersion
  let R : ℝ := B / 2
  let r : ℝ := R / 2
  have hR : 0 < R := half_pos hB
  have hr : 0 < r := half_pos hR
  have hRB : R < B := half_lt_self hB
  have hrR : r < R := half_lt_self hR
  have hRA : R < A.radius := hRB.trans_le hBA
  have ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) :=
    haB.mono (closedBall_subset_closedBall hRB.le)
  obtain ⟨L₀, hL₀⟩ := A.exists_level_at_radius A.radius A.radius_pos le_rfl
  have hinjA : InjOn A.H (ball (0 : Source 2) A.radius) := by
    simpa only [hL₀] using L₀.injective
  have hinj : InjOn A.H (closedBall (0 : Source 2) R) :=
    hinjA.mono (closedBall_subset_ball hRA)
  obtain ⟨ε₀, hε₀, hconfine⟩ :=
    exists_euclidean_target_cut_confinement A.H A.H_zero hr hrR ha.continuousOn hinj
  refine ⟨R, r, ε₀, hr, hrR, hRA, hε₀, ha, hinj, hconfine, ?_⟩
  intro ε hε hεε₀
  obtain ⟨δ, hδ, hsub⟩ := hboundary ε hε
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < min δ ε := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hδ hε)] with s hs
    exact mem_ball_zero_iff.mp hs
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := self_mem_nhdsWithin
  obtain ⟨s, ⟨hlevel, hsmall⟩, hs0⟩ :=
    (((A.levels R hR hRA.le).and hsmall).filter_mono nhdsWithin_le_nhds |>.and hne).exists
  obtain ⟨Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩ := hlevel hs0
  let L : ResolutionSectionLevel A :=
    ⟨R, hR, hRA.le, s, hs0, Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩
  refine ⟨L, rfl, hsmall.trans_le (min_le_right _ _), ?_, ?_⟩
  · intro x hx hxe
    exact hconfine x hx.1 (hxe.trans hεε₀)
  · intro x hx hxe
    exact hsub s (hsmall.trans_le (min_le_left _ _)) x
      (closedBall_subset_closedBall hRB.le hx.1) hx.2 hxe

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
