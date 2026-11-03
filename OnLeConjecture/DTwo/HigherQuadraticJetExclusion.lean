/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.HigherQuadraticJetPreparation
public import OnLeConjecture.DTwo.CommonLinearGenericReductionExclusion
public import OnLeConjecture.DTwo.QuadraticResolutionReductionData

/-!
# Higher-rank quadratic exclusion from geometric reduction data

The rank-three and basepoint-free cases are excluded analytically. The
remaining higher-rank pencil is normalized and a node member is selected
inside the same open set on which the imported reduction conclusions hold.
Existence of the geometric reduction data is kept explicit.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem common_linear_false_of_quadraticResolutionReductionData
    (g : PointedMapGerm 2 3) (D : QuadraticResolutionReductionData g)
    (hf0 : g.1.component 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hf1 : g.1.component 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (hf2 : g.1.component 2 ∈ maximalIdeal 2 ^ 3) : False := by
  have hgenerators : D.weakData.generators D.pointBasis.root = g.1.component := by
    funext i
    exact D.root_generators i
  apply common_linear_excluded_of_open_general_member_reduction D.weakData
    D.root_charts D.complete D.root_multiplicity
    (by simpa only [D.root_generators] using hf0)
    (by simpa only [D.root_generators] using hf1)
    (by simpa only [D.root_generators] using hf2)
    D.coefficientOpen D.coefficientOpen_isOpen D.coefficientOpen_nonempty
  intro q hq
  obtain ⟨R⟩ := D.generalMemberReduction q hq
  refine ⟨R.critical, R.exponent, R.critical_mem, R.totalMultiplicity_le, ?_, ?_⟩
  · simpa only [D.root_generators] using R.common_minors 0 1
  · have hfinite : PlaneCurve.HasFiniteIntersection R.critical
        (germLinearCombination (D.weakData.generators D.pointBasis.root) q) := by
      simpa only [hgenerators] using R.critical_finite
    refine ⟨hfinite, ?_⟩
    simpa only [hgenerators] using R.polar

/-- Higher quadratic rank is excluded from the explicit geometric reduction
package along the right-left equivalence class. The imported input asserts
resolution and general-member data, not either classification exclusion. -/
theorem quadraticJetHigherRankExcluded_of_resolution_reduction
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (QuadraticResolutionReductionData f)) :
    QuadraticJetHigherRankExcluded g := by
  obtain ⟨D⟩ := hresolution g g.rightLeftEquivalent_refl
  obtain ⟨c, hc, hdiv⟩ := D.exists_common_minor_divisor
  rw [quadraticJetHigherRankExcluded_iff]
  intro P hP htail _hnonzero hhigher
  obtain ⟨f, _, hequivalent, _, hf0, hf1, hf2, _⟩ :=
    exists_common_linear_normalization_of_injective_higher_quadratic_jet
      g P hP htail c hc hdiv hinjective hhigher
  obtain ⟨D'⟩ := hresolution f hequivalent
  exact common_linear_false_of_quadraticResolutionReductionData f D' hf0 hf1 hf2

end OnLeConjecture.DTwo
