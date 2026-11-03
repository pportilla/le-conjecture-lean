/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchSmoothLinkCircle
public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.FiniteDimensional

/-!
# Smooth embeddings parametrizing plane branch links

The sphere zero sets of an irreducible analytic plane equation are
parametrized by smooth embeddings in the ambient Euclidean space. The
embedding predicate includes the immersion normal form in charts.
-/

public noncomputable section

open Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic.Germ

/-- The entire intersection of an irreducible plane branch with any
sufficiently small sphere is the range of a smooth embedding of the circle. -/
theorem exists_smoothEmbedding_sphere_zero_set_of_irreducible
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hirr : Irreducible (ofFunction H hH)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ L : Metric.sphere (0 : ℂ) 1 → EuclideanSpace ℂ (Fin 2),
        IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ L ∧
        Set.range L = Metric.sphere 0 ε ∩
          {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0} := by
  obtain ⟨ε₀, hε₀, hlevels⟩ := exists_smooth_sphere_zero_set_circle_of_irreducible H hH hirr
  refine ⟨ε₀, hε₀, fun ε hε hεsmall => ?_⟩
  obtain ⟨L, hL, hs, hd, hrange⟩ := hlevels ε hε hεsmall
  refine ⟨fun u => (L u : EuclideanSpace ℂ (Fin 2)), ?_, hrange⟩
  exact hs.isSmoothEmbedding_of_injective_mfderiv (by simp) hd
    (Topology.IsEmbedding.subtypeVal.comp hL.isEmbedding)

end OnLeConjecture.Analytic.Germ
