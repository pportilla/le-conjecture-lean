/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskExterior

/-! # Coordinate-disk removal on the same nearby target cut

The nearby section, target cutoff, rational homology and outer boundary
charts are chosen together. The complete critical list lies in pairwise
disjoint source coordinate disks, whose removal leaves a compact immersed
exterior. These statements do not identify the boundary components with
knots or identify the numerical genus expression with a surface genus.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The common nearby target cut admits disjoint source coordinate disks
around its complete critical list, and a compact exterior with an injective
level tangent. All choices refer to the same assembly, section and radius. -/
theorem exists_targetSectionCriticalExterior (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
      InjOn A.H (closedBall (0 : Source 2) R) ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A,
        L.radius = R ∧ ‖L.parameter‖ < ε / 2 ∧
        HasCurveRatHomology ↥(targetSectionCut A.H R ε L.parameter)
          (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) : ℤ)) ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 0) = 1 ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 1) =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) ∧
        IsCompact (targetSectionCut A.H R ε L.parameter) ∧
        IsPathConnected (targetSectionCut A.H R ε L.parameter) ∧
        (∃ γ : ℕ, 2 * γ + irreducibleBranchCount A.sourceEquation =
            Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 1) + 1 ∧
          γ + irreducibleBranchCount A.sourceEquation = deltaInvariant A.sourceEquation + 1) ∧
        (∀ x ∈ closedBall (0 : Source 2) R,
          ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε → x ∈ ball 0 (R / 2)) ∧
        (∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = L.parameter →
          ε / 2 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ →
          Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x)) ∧
        (∀ z ∈ targetSectionBoundary A.H R ε L.parameter,
          Nonempty (SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
            (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
            ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z)) ∧
        ∃ D : (j : L.points) → L.PointCoordinateDisk j,
          Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk) ∧
          (∀ j, ∀ z ∈ (D j).closedDisk,
            (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 R ∧
            ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
              (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z))‖ < ε / 2) ∧
          IsCompact (L.diskExterior D ε) ∧
          Topology.IsClosedEmbedding
            ((L.diskExterior D ε).domRestrict (euclideanSectionMap A.H)) ∧
          targetSectionBoundary A.H R ε L.parameter ⊆ L.diskExterior D ε ∧
          (∀ j, L.diskExterior D ε ∩ (D j).closedDisk = (D j).boundaryCircle) ∧
          ∀ z ∈ L.diskExterior D ε,
            let x := (EuclideanSpace.equiv (Fin 2) ℂ) z
            x ∉ L.points ∧ AnalyticAt ℂ A.sectionMap x ∧
              fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
              Injective (L.sectionTangentMap x) ∧
              Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 := by
  obtain ⟨R, ε₀, hR, hRA, hε₀, ha, hinj, hlevel⟩ := A.exists_common_targetSectionLevel
  refine ⟨R, ε₀, hR, hRA, hε₀, ha, hinj, ?_⟩
  intro ε hε hεsmall
  obtain ⟨L, hLR, hs, hh, hzero, hone, hc, hp, hγ, hconf, hsub, hcharts, hpoints⟩ :=
    hlevel ε hε hεsmall
  have haL : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius) := hLR.symm ▸ ha
  obtain ⟨D, hdisj, hD⟩ := L.exists_disjoint_pointCoordinateDisks haL hpoints
  have hDc : ∀ j, (D j).closedDisk ⊆ targetSectionCut A.H L.radius ε L.parameter := by
    intro j z hz
    apply (mem_targetSectionCut_iff hε.le).mpr
    exact ⟨⟨ball_subset_closedBall (hD j z hz).1, (D j).closedDisk_subset_level hz⟩,
      ((hD j z hz).2.trans (half_lt_self hε)).le⟩
  have hcL : IsCompact (targetSectionCut A.H L.radius ε L.parameter) := hLR.symm ▸ hc
  have hinside : ∀ z ∈ targetSectionCut A.H L.radius ε L.parameter,
      (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius := by
    intro z hz
    have hz' := (mem_targetSectionCut_iff hε.le).mp hz
    rw [hLR] at hz' ⊢
    exact ball_subset_ball (half_lt_self hR).le (hconf _ hz'.1.1 hz'.2)
  refine ⟨L, hLR, hs, hh, hzero, hone, hc, hp, hγ, hconf, hsub, hcharts,
    D, hdisj, ?_, L.isCompact_diskExterior D hcL,
    L.diskExterior_closedEmbedding D haL hcL, ?_,
    L.diskExterior_inter_closedDisk D hdisj hDc, ?_⟩
  · intro j z hz
    simpa only [hLR] using hD j z hz
  · rw [← hLR]
    exact L.targetSectionBoundary_subset_diskExterior D hε.le (half_lt_self hε).le
      (fun j z hz => (hD j z hz).2)
  · intro z hz
    exact ⟨L.not_mem_points_of_mem_diskExterior D hz,
      L.diskExterior_tangent_properties D haL hinside hz⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
