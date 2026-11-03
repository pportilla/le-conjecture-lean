/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectivityFactor
public import OnLeConjecture.DThree.PairRepresentativeComponents
public import OnLeConjecture.DThree.WeightedOrderContradiction
public import OnLeConjecture.DThree.WeightedQuarticInitialForm

/-!
# Noninjectivity of the prepared E and H pairs

An analytic plane pair with either normalized weighted initial pair has
collisions in every neighborhood of the origin. Adjoining the second source
coordinate reduces this assertion to the existing transverse monomial
collision and its analytic persistence. No condition on the pair Jacobian
or on an additional component is required.

Consequently, an analytic map factoring through either pair cannot have an
injective representative.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic
open scoped Topology

/-- Adjoining the second source coordinate preserves local injectivity
and retains the two original scalar components. -/
theorem exists_injective_coordinate_augmentation
    (g : PointedMapGerm 2 2) (hg : g.HasInjectiveRepresentative) :
    ∃ h : PointedMapGerm 2 3, h.HasInjectiveRepresentative ∧
      h.1.component 0 = g.1.component 0 ∧
      h.1.component 1 = g.1.component 1 ∧
      h.1.component 2 = Germ.coordinate (1 : Fin 2) := by
  obtain ⟨f, hf, hfzero, hfgerm, s, hs, hinjective⟩ := hg
  let F : Source 2 → Source 3 := fun z ↦ ![f z 0, f z 1, z 1]
  have hF : AnalyticAt ℂ F 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_pi_iff.mp hf 0
    · exact analyticAt_pi_iff.mp hf 1
    · exact (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  have hFzero : F 0 = 0 := by simp [F, hfzero]
  refine ⟨PointedMapGerm.ofFunction F hF hFzero, ?_, ?_, ?_, ?_⟩
  · refine ⟨F, hF, hFzero, rfl, s, hs, ?_⟩
    intro x hx y hy hxy
    apply hinjective hx hy
    funext i
    fin_cases i
    · exact congrFun hxy 0
    · exact congrFun hxy 1
  · rw [hfgerm]
    apply Subtype.ext
    simp only [PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
    rfl
  · rw [hfgerm]
    apply Subtype.ext
    simp only [PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
    rfl
  · apply Subtype.ext
    simp only [PointedMapGerm.ofFunction, MapGerm.component_ofFunction,
      Germ.coe_coordinate]
    rfl

/-- The normalized weighted E pair has no injective analytic
representative, for arbitrary higher weighted order corrections. -/
theorem eWeightedPair_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 2) (a : ℕ) (ha : 0 < a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 0 3) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 0 4 0) ∈
        Germ.weightedOrderIdeal a (4 * a + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨h, hInjective, hfirst, hsecond, hthird⟩ :=
    exists_injective_coordinate_augmentation g hg
  obtain ⟨representative, hanalytic, hzero, hh, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components h
  have hnot := eWeightedOrderTails_not_hasInjectiveRepresentative
    a 1 1 ha (by omega) one_ne_zero representative hanalytic hzero
  apply hnot
  · intro i
    rw [hcomponents i]
    fin_cases i
    · simpa [hfirst, eResiduePolynomialMap, residueWeightedDegrees,
        weightedCubicPolynomial] using htailZero
    · have hpolynomial : eResiduePolynomialMap a 1 1 1 =
          weightedQuarticPolynomial a 1 0 0 4 0 := by
        simp [eResiduePolynomialMap, weightedQuarticPolynomial]
        ring
      simpa [hsecond, hpolynomial, residueWeightedDegrees] using htailOne
    · simp [hthird, eResiduePolynomialMap, residueWeightedDegrees]
  · rwa [← hh]

/-- The normalized weighted H pair has no injective analytic
representative, for arbitrary higher weighted order corrections. -/
theorem hWeightedPair_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 2) (a : ℕ) (ha : 0 < a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 3 0) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 4 0 2) ∈
        Germ.weightedOrderIdeal a (4 * a + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨h, hInjective, hfirst, hsecond, hthird⟩ :=
    exists_injective_coordinate_augmentation g hg
  obtain ⟨representative, hanalytic, hzero, hh, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components h
  have hnot := hWeightedOrderTails_not_hasInjectiveRepresentative
    a 1 1 ha (by omega) one_ne_zero representative hanalytic hzero
  apply hnot
  · intro i
    rw [hcomponents i]
    fin_cases i
    · have hpolynomial : hResiduePolynomialMap a 1 1 0 =
          weightedCubicPolynomial a 3 0 := by
        simp [hResiduePolynomialMap, weightedCubicPolynomial]
        ring
      simpa [hfirst, hpolynomial, residueWeightedDegrees] using htailZero
    · have hpolynomial : hResiduePolynomialMap a 1 1 1 =
          weightedQuarticPolynomial a 1 0 4 0 2 := by
        simp [hResiduePolynomialMap, weightedQuarticPolynomial]
        ring
      simpa [hsecond, hpolynomial, residueWeightedDegrees] using htailOne
    · simp [hthird, hResiduePolynomialMap, residueWeightedDegrees]
  · rwa [← hh]

/-- Every analytic map factoring through a normalized weighted E pair is
noninjective near the origin. -/
theorem eWeightedPair_comp_not_hasInjectiveRepresentative
    {m : ℕ} (f : PointedMapGerm 2 m) (g : PointedMapGerm 2 2)
    (a : ℕ) (ha : 0 < a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 0 3) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 0 4 0) ∈
        Germ.weightedOrderIdeal a (4 * a + 1)) :
    ¬ (f.comp g).HasInjectiveRepresentative := by
  intro hfg
  exact eWeightedPair_not_hasInjectiveRepresentative g a ha htailZero htailOne
    (PointedMapGerm.hasInjectiveRepresentative_of_comp f g hfg)

/-- Every analytic map factoring through a normalized weighted H pair is
noninjective near the origin. -/
theorem hWeightedPair_comp_not_hasInjectiveRepresentative
    {m : ℕ} (f : PointedMapGerm 2 m) (g : PointedMapGerm 2 2)
    (a : ℕ) (ha : 0 < a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 3 0) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 4 0 2) ∈
        Germ.weightedOrderIdeal a (4 * a + 1)) :
    ¬ (f.comp g).HasInjectiveRepresentative := by
  intro hfg
  exact hWeightedPair_not_hasInjectiveRepresentative g a ha htailZero htailOne
    (PointedMapGerm.hasInjectiveRepresentative_of_comp f g hfg)

end OnLeConjecture.DThree
