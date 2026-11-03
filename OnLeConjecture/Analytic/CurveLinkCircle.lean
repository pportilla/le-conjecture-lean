/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveLevelEmbedding
public import OnLeConjecture.Analytic.CurveAnalyticRadialLevels

/-!
# Embedded small-sphere circles of injective analytic curves

For every injective pointed curve germ, this module constructs an actual
representative whose image meets each sufficiently small Euclidean sphere
in an embedded circle. The range equality specifies the precise sphere
intersection. Smoothness and independence of the radius remain separate
requirements for the knot-theoretic argument.
-/

public noncomputable section

open scoped Topology

namespace OnLeConjecture.Analytic

/-- An injective analytic curve germ has actual embedded small-sphere
circles, with range equal to the sphere intersection of its disc image. -/
theorem PointedMapGerm.exists_euclidean_embedded_norm_level_circles
    {n : ℕ} (g : PointedMapGerm 1 n) (hi : g.HasInjectiveRepresentative) :
    ∃ G : Source 1 → Source n, ∃ hG : AnalyticAt ℂ G 0, ∃ hG0 : G 0 = 0,
      g = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
        let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
          (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
        AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
        Set.InjOn F (Metric.closedBall 0 R) ∧
        ∀ c : ℝ, 0 < c → c < δ →
          ∃ L : Metric.sphere (0 : ℂ) 1 →
              Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (Real.sqrt c),
            Topology.IsClosedEmbedding L ∧
            Set.range (fun u => (L u : EuclideanSpace ℂ (Fin n))) =
              Metric.sphere 0 (Real.sqrt c) ∩ F '' Metric.closedBall 0 R := by
  obtain ⟨G, hG, hG0, hg, R, δ, hR, hδ, ha, hinj, hlevels⟩ :=
    g.exists_injective_euclidean_norm_level_homeomorphs hi
  refine ⟨G, hG, hG0, hg, R, δ, hR, hδ, ha, hinj, ?_⟩
  intro c hc hcδ
  obtain ⟨e⟩ := hlevels c hc hcδ
  exact ⟨curveNormLevelCircle _ R c e,
    curveNormLevelCircle_isClosedEmbedding e ha.continuousOn hinj,
    curveNormLevelCircle_range_eq_sphere_inter_image hc.le e⟩

end OnLeConjecture.Analytic
