/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskBranchImmersion
public import OnLeConjecture.Analytic.CurveRadialGraphDiffeotopy
public import OnLeConjecture.Analytic.CurveSphereRadialOrientation

/-! # The retained hole circle and the same local equation sphere link

The Euclidean ambient diffeotopy follows radial graphs of the retained
centered parametrization. Its clockwise endpoint is explicitly the reversed
positive analytic sphere parametrization and has negative angular tangent.
No identification of the original coordinate circle with a norm sphere,
or isotopy confined to the exterior surface, is asserted.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

set_option backward.isDefEq.respectTransparency false in
/-- The same coordinate circle is transported to the literal local equation
sphere link. Inverting the source direction at both endpoints retains the
incoming orientation, with its strict negative tangent sign proved. -/
theorem exists_diskBranch_sphere_diffeotopy (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius)
    (j : L.points) (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hWgerm : localSectionEquation A.H j = ofFunction W hW) :
    let B := L.diskBranch D j
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ρ : Circle → ℝ,
        (∀ u, 0 < ρ u ∧ ρ u < (D j).radius) ∧
        ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ ∧
        (∀ u, ‖B (ρ u • (u : ℂ))‖ = ε) ∧
        range (fun u => B (ρ u • (u : ℂ))) =
          sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0} ∧
        range (fun u : Circle => B (ρ u⁻¹ • ((u⁻¹ : Circle) : ℂ))) =
          sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0} ∧
        (∀ θ : ℝ, 0 < (inner ℂ
          (B (ρ (Circle.exp θ) • (Circle.exp θ : ℂ)))
          (deriv (fun t : ℝ => B (ρ (Circle.exp t) • (Circle.exp t : ℂ))) θ)).im) ∧
        (∀ θ : ℝ, (inner ℂ
          (B (ρ ((Circle.exp θ)⁻¹) • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))
          (deriv (fun t : ℝ => B (ρ ((Circle.exp t)⁻¹) •
            (((Circle.exp t)⁻¹ : Circle) : ℂ))) θ)).im < 0) ∧
        ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, CollarPlane) ∞ CollarPlane,
          (∀ t : unitInterval, ∀ u : Circle,
            Φ (t, B ((D j).radius • (u : ℂ))) =
              B (radialGraphMotion (D j).radius ρ (t, u))) ∧
          (∀ u : Circle, Φ.final (B ((D j).radius • (u : ℂ))) =
            B (ρ u • (u : ℂ))) ∧
          (∀ u : Circle, Φ.final (B ((D j).radius • ((u⁻¹ : Circle) : ℂ))) =
            B (ρ u⁻¹ • ((u⁻¹ : Circle) : ℂ))) := by
  let B := L.diskBranch D j
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hBa := L.diskBranch_analytic D ha hD j
  have hBi := L.diskBranch_injOn D hD j
  have hB0 : B 0 = 0 := L.diskBranch_zero D j
  have hB : AnalyticAt ℂ B 0 := hBa 0 (mem_closedBall_self (D j).radius_pos.le)
  have hpoint := (L.points_iff j).mp j.property
  have hA := ha j (ball_subset_closedBall hpoint.1)
  let G : Source 1 → Source 2 := fun t => e (B (curveParameterEquiv t))
  have hG : AnalyticAt ℂ G 0 := L.diskBranch_at_center D j hA
  have hG0 : G 0 = 0 := by simp only [G, map_zero, hB0]
  have hg : L.diskBranchGerm D j hA = PointedMapGerm.ofFunction G hG hG0 :=
    L.diskBranchGerm_eq_ofFunction D j hA
  have hiG : (PointedMapGerm.ofFunction G hG hG0).HasInjectiveRepresentative :=
    hg ▸ L.diskBranchGerm_hasInjectiveRepresentative D j hA
  have hnG := PointedMapGerm.exists_nonzero_coordinate_pullback_of_injective_curve
    (PointedMapGerm.ofFunction G hG hG0) hiG
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), B z = 0 := by
    intro hz
    have hcomponent : ∃ i, (PointedMapGerm.ofFunction G hG hG0).1.component i ≠ 0 := by
      simpa only [PointedMapGerm.pullback_coordinate] using hnG
    apply curve_representative_not_eventually_zero G hG hG0 hcomponent
    filter_upwards [hz] with z hz
    simp only [G, ContinuousLinearEquiv.apply_symm_apply, hz, map_zero]
  obtain ⟨r, hr, hrD, har, hir, _, himage⟩ :=
    L.exists_diskBranch_equation_coverage D ha hD j W hW hWgerm
  obtain ⟨ε₀, hε₀, hgraphs⟩ := exists_small_sphere_radialGraph hB hB0 hne hr
    har.continuousOn hir (fun y => W (e y)) himage
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨ρ, hρ, hs, hp, hn, hrange⟩ := hgraphs ε hε hεsmall
  have hρD (u : Circle) : 0 < ρ u ∧ ρ u < (D j).radius :=
    ⟨(hρ u).1, (hρ u).2.trans hrD⟩
  have hqmem (u : Circle) : ρ u • (u : ℂ) ∈ closedBall 0 (D j).radius := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hρ u).1, Circle.norm_coe, mul_one]
    exact (hρD u).2.le
  obtain ⟨hpositive, hincoming⟩ := sphere_radialGraph_orientation (fun u => (hρ u).1) hs
    (fun u => (hBa _ (hqmem u)).differentiableAt) hp hn
  obtain ⟨Φ, hfollow, hfinal, hreverse⟩ := exists_curve_radialGraph_diffeotopy
    (D j).radius_pos hBa hBi (fun z hz hne => L.diskBranch_fderiv_injective D ha hdisj hD j hz hne)
    ρ (fun u => ⟨(hρD u).1, (hρD u).2.le⟩) hs
  have hrangeRev : range (fun u : Circle => B (ρ u⁻¹ • ((u⁻¹ : Circle) : ℂ))) =
      range (fun u : Circle => B (ρ u • (u : ℂ))) :=
    inv_surjective.range_comp (fun u : Circle => B (ρ u • (u : ℂ)))
  exact ⟨ρ, hρD, hs, hn, hrange, hrangeRev.trans hrange, hpositive, hincoming,
    Φ, hfollow, hfinal, hreverse⟩

end ResolutionSectionLevel
end OnLeConjecture.Analytic
