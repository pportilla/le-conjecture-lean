/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.WeightedPairElimination
public import OnLeConjecture.Analytic.MonicTriangularFinite
public import OnLeConjecture.DThree.PreparedComponentsDegree
public import OnLeConjecture.DThree.PreparedPairNoninjectivity
import all OnLeConjecture.DThree.NormalizedBaseExclusion

/-!
# Analytic elimination of the third component in the E and H cases

Injectivity excludes membership of the third component in the analytic
image ring of the first pair. Finite analytic elimination then supplies a
third initial form outside the polynomial algebra of the two initial
forms. The analytic correction vanishes at the origin, so subtracting it
is a pointed invertible target change. The common Jacobian divisor is
preserved, and the previously proved collision exclusions apply.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- If the third component is an analytic expression in the first pair,
the entire map factors through that pair. -/
theorem exists_factor_firstTwo_of_third_mem_imageRing
    (g : PointedMapGerm 2 3)
    (hmem : g.1.component 2 ∈ g.firstTwo.ImageRing) :
    ∃ f : PointedMapGerm 2 3, g = f.comp g.firstTwo := by
  obtain ⟨q, hq⟩ := hmem
  have hqzero : Germ.valueRingHom 2 q = 0 := by
    rw [← valueRingHom_pullback g.firstTwo q, hq,
      MapGerm.valueRingHom_component, g.2]
    rfl
  have hgraph : ∃ f : PointedMapGerm 2 3,
      f.1.component 0 = Germ.coordinate 0 ∧
      f.1.component 1 = Germ.coordinate 1 ∧
      f.1.component 2 = q := by
    rcases q with ⟨q, hqanalytic⟩
    induction q using Filter.Germ.inductionOn with
    | _ q =>
        rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hqanalytic
        change q 0 = 0 at hqzero
        let F : Source 2 → Source 3 := fun z ↦ ![z 0, z 1, q z]
        have hF : AnalyticAt ℂ F 0 := by
          apply AnalyticAt.pi
          intro i
          fin_cases i
          · exact (ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
          · exact (ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
          · exact hqanalytic
        have hFzero : F 0 = 0 := by simp [F, hqzero]
        refine ⟨ofFunction F hF hFzero, ?_, ?_, ?_⟩
        all_goals apply Subtype.ext; rfl
  obtain ⟨f, hfzero, hfone, hftwo⟩ := hgraph
  refine ⟨f, ?_⟩
  apply ext_components
  intro i
  fin_cases i
  · change g.1.component 0 = (f.comp g.firstTwo).1.component 0
    rw [component_comp_eq_pullback, hfzero, pullback_coordinate]
    simp
  · change g.1.component 1 = (f.comp g.firstTwo).1.component 1
    rw [component_comp_eq_pullback, hfone, pullback_coordinate]
    simp
  · change g.1.component 2 = (f.comp g.firstTwo).1.component 2
    rw [component_comp_eq_pullback, hftwo, hq]

/-- An injective triple with a noninjective first pair has its third
component outside the analytic image ring of that pair. -/
theorem third_not_mem_imageRing_firstTwo_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (hpair : ¬ g.firstTwo.HasInjectiveRepresentative) :
    g.1.component 2 ∉ g.firstTwo.ImageRing := by
  intro hmem
  obtain ⟨f, hf⟩ := g.exists_factor_firstTwo_of_third_mem_imageRing hmem
  apply hpair
  apply hasInjectiveRepresentative_of_comp f g.firstTwo
  rwa [← hf]

end OnLeConjecture.Analytic.PointedMapGerm

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

private theorem positive_degree_of_not_mem_pair_algebra
    (a D : ℕ) (ha : 0 < a) (G : Fin 2 → Form ℂ) (R : Form ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hnotbase : R ∉ Set.range (MvPolynomial.aeval G : Form ℂ →ₐ[ℂ] Form ℂ)) :
    0 < D := by
  by_contra hD
  have hDzero : D = 0 := by omega
  subst D
  have hweights : ∀ i : Fin 2, ![a, 1] i ≠ 0 := by
    intro i
    fin_cases i
    · exact ha.ne'
    · exact one_ne_zero
  have hconstant : R = MvPolynomial.C (MvPolynomial.coeff 0 R) := by
    calc
      R = MvPolynomial.weightedHomogeneousComponent ![a, 1] 0 R :=
        (MvPolynomial.weightedHomogeneousComponent_eq_self hR).symm
      _ = MvPolynomial.C (MvPolynomial.coeff 0 R) :=
        MvPolynomial.weightedHomogeneousComponent_zero R hweights
  apply hnotbase
  exact ⟨MvPolynomial.C (MvPolynomial.coeff 0 R), by simpa using hconstant.symm⟩

private theorem elimination_correction_mem_maximalIdeal
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a) (hD : 0 < D)
    (q : Germ 2)
    (horder : g.1.component 2 - g.firstTwo.pullbackRingHom q ∈
      Germ.weightedOrderIdeal a D) :
    q ∈ Germ.maximalIdeal 2 := by
  have horderOne := Germ.weightedOrderIdeal_antitone a 1 D ha hD horder
  rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal a ha,
    Germ.mem_maximalIdeal_iff, map_sub, MapGerm.valueRingHom_component,
    g.2, PointedMapGerm.valueRingHom_pullback] at horderOne
  simpa [Germ.mem_maximalIdeal_iff] using horderOne

/-- A finite classified pair with no injective representative excludes
injectivity of a triple satisfying the common analytic Jacobian divisor. -/
theorem classifiedWeightedAnalyticTriple_of_pair_noninjective
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (hpair : ¬ g.firstTwo.HasInjectiveRepresentative)
    (htailZero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a A B) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  let P := weightedCubicPolynomial a A B
  let Q := weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀
  let G : Fin 2 → Form ℂ := ![P, Q]
  have hG : ∀ i, (G i).IsWeightedHomogeneous ![a, 1] (![3 * a, 4 * a] i) := by
    intro i
    fin_cases i
    · exact weightedCubicPolynomial_isWeightedHomogeneous a A B
    · exact weightedQuarticPolynomial_isWeightedHomogeneous a c₄ c₃ c₂ c₁ c₀
  have htail : ∀ i, g.firstTwo.1.component i - Germ.coordinatePolynomialAlgHom 2 (G i) ∈
      Germ.weightedOrderIdeal a (![3 * a, 4 * a] i + 1) := by
    intro i
    fin_cases i
    · simpa [G, P] using htailZero
    · simpa [G, Q] using htailOne
  obtain ⟨D, q, R, hRzero, hR, horder, hRtail, hnotbase⟩ :=
    g.firstTwo.exists_initial_form_outside_pair_algebra hfinite a ha
      ![3 * a, 4 * a] G hG htail (g.1.component 2)
      (g.third_not_mem_imageRing_firstTwo_of_injective hg hpair)
  have hD := positive_degree_of_not_mem_pair_algebra a D ha G R hR hnotbase
  have hq := elimination_correction_mem_maximalIdeal g a D ha hD q horder
  obtain ⟨h, hequivalent, hzero, hone, htwo⟩ := g.exists_target_subtraction q hq
  have hbaseMap : (MvPolynomial.aeval G : Form ℂ →ₐ[ℂ] Form ℂ) =
      pairBaseToForm P Q := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [G, pairBaseToForm]
  rw [hbaseMap] at hnotbase
  have hdivPair : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.coordinateJacobian g.firstTwo := by
    simpa [Germ.coordinateJacobian_eq, Germ.jacobian_eq] using hdivZeroOne
  have hdivs := Germ.dvd_jacobian_sub_compPointed g.firstTwo
    (g.1.component 2) q (Germ.coordinate (1 : Fin 2) ^ (6 * a - 1))
    hdivPair (by simpa using hdivZeroTwo) (by simpa using hdivOneTwo)
  apply classifiedWeightedThreeForms_not_hasInjectiveRepresentative_all_degrees
    h a D ha R hR hRzero A B c₄ c₃ c₂ c₁ c₀ hAB hquartic hnotbase
  · simpa [hzero] using htailZero
  · simpa [hone] using htailOne
  · simpa [htwo] using hRtail
  · simpa [hzero, hone] using hdivZeroOne
  · simpa [hzero, htwo] using hdivs.1
  · simpa [hone, htwo] using hdivs.2
  · exact hequivalent.hasInjectiveRepresentative hg

/-- A finite normalized E pair and the three analytic Jacobian divisors
exclude injectivity without an assumption on the third initial form. -/
theorem eWeightedAnalyticTriple_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a)
    (htailZero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 0 3) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 0 4 0) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  have hquartic : weightedQuarticPolynomial a 1 0 0 4 0 ≠ 0 := by
    intro hzero
    have heval := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℂ)) hzero
    simp [weightedQuarticPolynomial, zero_pow (by omega : 3 * a ≠ 0)] at heval
  exact classifiedWeightedAnalyticTriple_of_pair_noninjective g hfinite a ha 0 3 1 0 0 4 0
    (Or.inr (by norm_num)) hquartic
    (eWeightedPair_not_hasInjectiveRepresentative g.firstTwo a ha
      (by simpa using htailZero) (by simpa using htailOne))
    htailZero htailOne hdivZeroOne hdivZeroTwo hdivOneTwo

/-- A finite normalized H pair and the three analytic Jacobian divisors
exclude injectivity without an assumption on the third initial form. -/
theorem hWeightedAnalyticTriple_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a)
    (htailZero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 3 0) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 4 0 2) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  have hquartic : weightedQuarticPolynomial a 1 0 4 0 2 ≠ 0 := by
    intro hzero
    have heval := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℂ)) hzero
    simp [weightedQuarticPolynomial, zero_pow (by omega : 2 * a ≠ 0),
      zero_pow (by omega : 4 * a ≠ 0)] at heval
  exact classifiedWeightedAnalyticTriple_of_pair_noninjective g hfinite a ha 3 0 1 0 4 0 2
    (Or.inl (by norm_num)) hquartic
    (hWeightedPair_not_hasInjectiveRepresentative g.firstTwo a ha
      (by simpa using htailZero) (by simpa using htailOne))
    htailZero htailOne hdivZeroOne hdivZeroTwo hdivOneTwo

end OnLeConjecture.DThree
