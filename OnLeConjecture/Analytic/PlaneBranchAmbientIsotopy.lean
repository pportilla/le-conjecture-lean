/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchNormalizedLinkFamily
public import OnLeConjecture.Analytic.UnitSphereFamilyAmbientIsotopy

/-!
# Ambient isotopy of normalized small-sphere plane branch links

The zero-set links of an irreducible analytic plane equation, scaled to
the unit three-sphere, admit compatible smooth embeddings of the circle.
The constructed compact velocity extension and global flow give an ambient
isotopy of the entire unit sphere carrying one link to any other sufficiently
small link.
-/

public noncomputable section

open Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance planeBranchAmbientIsotopyRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeBranchAmbientIsotopyRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic.Germ

/-- All sufficiently small normalized zero-set links of an irreducible
analytic plane equation are ambient isotopic in the unit three-sphere.
The parametrizations and ambient isotopies are constructed
from the equation alone. -/
theorem exists_ambientIsotopic_unit_sphere_links_of_irreducible
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hirr : Irreducible (ofFunction H hH)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ K : Ioo 0 δ → TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞
          (Metric.sphere (0 : ℂ) 1) (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ c, Set.range (fun u => (K c u : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c.1)⁻¹ • y) ''
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c.1) ∩
              {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})) ∧
        ∀ c₀ c₁, ∃ Φ : TauCeti.AmbientIsotopy (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (K c₀ u) = K c₁ u := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_normalized_smooth_zero_set_family_of_irreducible H hH hirr
  let hn := fun c hc => (hC c hc).1
  let hs := fun c hc => (hC c hc).2.1
  let hd := fun c hc => (hC c hc).2.2.2.1
  let he := fun c hc => (hC c hc).2.2.1.isEmbedding
  refine ⟨δ, hδ, fun c => unitSphereFamilySlice (n := 3) C hn hs hd he c.1 c.2, ?_, ?_⟩
  · intro c
    simpa only [unitSphereFamilySlice_coe_apply] using (hC c.1 c.2).2.2.2.2
  · intro c₀ c₁
    exact exists_unitSphereFamilyAmbientIsotopy (n := 3) C hn hs hd he c₀.1 c₁.1 c₀.2 c₁.2

/-- All sufficiently small normalized zero-set links of an irreducible
analytic plane equation are smoothly ambient isotopic in the unit three-sphere.
The parametrizations and ambient diffeotopies are constructed
from the equation alone. -/
theorem exists_smoothAmbientIsotopic_unit_sphere_links_of_irreducible
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hirr : Irreducible (ofFunction H hH)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ K : Ioo 0 δ → TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞
          (Metric.sphere (0 : ℂ) 1) (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ c, Set.range (fun u => (K c u : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c.1)⁻¹ • y) ''
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c.1) ∩
              {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})) ∧
        ∀ c₀ c₁, ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (K c₀ u) = K c₁ u := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_normalized_smooth_zero_set_family_of_irreducible H hH hirr
  let hn := fun c hc => (hC c hc).1
  let hs := fun c hc => (hC c hc).2.1
  let hd := fun c hc => (hC c hc).2.2.2.1
  let he := fun c hc => (hC c hc).2.2.1.isEmbedding
  refine ⟨δ, hδ, fun c => unitSphereFamilySlice (n := 3) C hn hs hd he c.1 c.2, ?_, ?_⟩
  · intro c
    simpa only [unitSphereFamilySlice_coe_apply] using (hC c.1 c.2).2.2.2.2
  · intro c₀ c₁
    exact exists_unitSphereFamilyDiffeotopy (n := 3) C hn hs hd he c₀.1 c₁.1 c₀.2 c₁.2

end OnLeConjecture.Analytic.Germ
