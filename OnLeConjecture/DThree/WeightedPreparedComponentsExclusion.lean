/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.MonicTargetRescaling
public import OnLeConjecture.DThree.WeightedQuarticInitialForm

/-!
# Exclusion from prepared weighted components

Exact orders of the two coefficients of a prepared cubic component and exact
weighted order of the second component produce the monic cubic and quartic
initial forms. The target rescaling preserves the third initial form, the
algebra exclusion, the strict tails, and the divisibility of all three
analytic Jacobians. The classified weighted exclusion then rules out an
injective representative.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Every pair of weighted polynomial initial forms of the first two
components excludes the prescribed third initial form from its generated
algebra. -/
@[expose]
def HasWeightedInitialPairBaseExclusion
    (g : PointedMapGerm 2 3) (a : ℕ) (R : Form ℂ) : Prop :=
  ∀ P Q : Form ℂ,
    P.IsWeightedHomogeneous ![a, 1] (3 * a) →
    Q.IsWeightedHomogeneous ![a, 1] (4 * a) →
    g.1.component 0 - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (3 * a + 1) →
    g.1.component 1 - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (4 * a + 1) →
    R ∉ Set.range (pairBaseToForm P Q)

/-- The prepared coefficient and order hypotheses produce monic weighted
initial forms while transporting the third form and all three analytic
Jacobian divisibilities. -/
theorem PointedMapGerm.exists_monicWeightedThreeInitialForms_of_preparedComponents
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈
      Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉
      Germ.weightedOrderIdeal a (4 * a + 1))
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hnotbase : HasWeightedInitialPairBaseExclusion g a R)
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ∃ h : PointedMapGerm 2 3, ∃ A B c₄ c₃ c₂ c₁ c₀ : ℂ,
      g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      (A ≠ 0 ∨ B ≠ 0) ∧
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      R.IsWeightedHomogeneous ![a, 1] D ∧
      R ≠ 0 ∧
      R ∉ Set.range
        (pairBaseToForm
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)) ∧
      h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) ∧
      h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) ∧
      h.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) ∧
      Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
        Germ.jacobian (h.1.component 0) (h.1.component 1) ∧
      Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
        Germ.jacobian (h.1.component 0) (h.1.component 2) ∧
      Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
        Germ.jacobian (h.1.component 1) (h.1.component 2) := by
  obtain ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hr, hQzero,
      htailZeroRaw, htailOneRaw⟩ :=
    PointedMapGerm.exists_weightedCubicAndQuarticInitialForms_of_preparedComponents
      g a ha a₁ a₀ u hfirst hu ha₁ ha₀ hcubicExact
        hquartic hquarticExact
  let r := Germ.valueRingHom 2 u
  let P := weightedCubicPolynomial a A B
  let Q := weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀
  let Praw := MvPolynomial.C r * P
  let h := monicFirstTargetRescaledMap g r hr
  have hP : P.IsWeightedHomogeneous ![a, 1] (3 * a) :=
    weightedCubicPolynomial_isWeightedHomogeneous a A B
  have hQ : Q.IsWeightedHomogeneous ![a, 1] (4 * a) :=
    weightedQuarticPolynomial_isWeightedHomogeneous
      a c₄ c₃ c₂ c₁ c₀
  have hPraw : Praw.IsWeightedHomogeneous ![a, 1] (3 * a) :=
    hP.C_mul r
  have hnotbaseRaw : R ∉ Set.range (pairBaseToForm Praw Q) := by
    apply hnotbase Praw Q hPraw hQ
    · exact htailZeroRaw
    · exact htailOneRaw
  have hnotbaseMonic : R ∉ Set.range (pairBaseToForm P Q) := by
    exact not_mem_pairBase_of_not_mem_C_mul_pairBase
      P Q R r hr hnotbaseRaw
  have hcubicEvaluation :
      Germ.coordinatePolynomialAlgHom 2 Praw =
        Germ.constRingHom 2 r * Germ.coordinatePolynomialAlgHom 2 P := by
    dsimp only [Praw]
    rw [map_mul, Germ.coordinatePolynomialAlgHom_C]
  have hconstantProduct :
      Germ.constRingHom 2 r⁻¹ * Germ.constRingHom 2 r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have htailZero :
      h.1.component 0 - Germ.coordinatePolynomialAlgHom 2 P ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
    have hequality :
        h.1.component 0 - Germ.coordinatePolynomialAlgHom 2 P =
          Germ.constRingHom 2 r⁻¹ *
            (g.1.component 0 - Germ.coordinatePolynomialAlgHom 2 Praw) := by
      rw [monicFirstTargetRescaledMap_component_zero,
        hcubicEvaluation]
      calc
        Germ.constRingHom 2 r⁻¹ * g.1.component 0 -
            Germ.coordinatePolynomialAlgHom 2 P =
          Germ.constRingHom 2 r⁻¹ * g.1.component 0 -
            (Germ.constRingHom 2 r⁻¹ * Germ.constRingHom 2 r) *
              Germ.coordinatePolynomialAlgHom 2 P := by
                rw [hconstantProduct, one_mul]
        _ = _ := by ring
    rw [hequality]
    exact Ideal.mul_mem_left _ _ htailZeroRaw
  have htailOne :
      h.1.component 1 - Germ.coordinatePolynomialAlgHom 2 Q ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
    rw [monicFirstTargetRescaledMap_component_one]
    exact htailOneRaw
  have htailTwoH :
      h.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    rw [monicFirstTargetRescaledMap_component_two]
    exact htailTwo
  have hdivZeroOneH :=
    coordinate_pow_dvd_jacobian_monicFirstTarget_zero_one
      g r hr (6 * a - 1) hdivZeroOne
  have hdivZeroTwoH :=
    coordinate_pow_dvd_jacobian_monicFirstTarget_zero_two
      g r hr (6 * a - 1) hdivZeroTwo
  have hdivOneTwoH :=
    coordinate_pow_dvd_jacobian_monicFirstTarget_one_two
      g r hr (6 * a - 1) hdivOneTwo
  have hequivalent : g.RightLeftEquivalent h :=
    rightLeftEquivalent_monicFirstTargetRescaledMap g r hr
  have hinjective := hequivalent.hasInjectiveRepresentative_iff
  refine ⟨h, A, B, c₄, c₃, c₂, c₁, c₀,
    hequivalent, hinjective, hAB, hQzero, hR, hRzero,
    hnotbaseMonic, htailZero, htailOne, htailTwoH,
    hdivZeroOneH, hdivZeroTwoH, hdivOneTwoH⟩

/-- Prepared first and second components, a third weighted initial form, the
pair algebra exclusion, and the three analytic Jacobian divisibilities rule
out an injective representative. -/
theorem PointedMapGerm.preparedWeightedThreeComponents_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (hdegreeFive : 5 ≤ D / a)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈
      Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉
      Germ.weightedOrderIdeal a (4 * a + 1))
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hnotbase : HasWeightedInitialPairBaseExclusion g a R)
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨h, A, B, c₄, c₃, c₂, c₁, c₀,
      hequivalent, hinjective, hAB, hQzero, hR, hRzero,
      hnotbase, htailZero, htailOne, htailTwo,
      hdivZeroOne, hdivZeroTwo, hdivOneTwo⟩ :=
    PointedMapGerm.exists_monicWeightedThreeInitialForms_of_preparedComponents
      g a D ha a₁ a₀ u hfirst hu ha₁ ha₀ hcubicExact
        hquartic hquarticExact R hR hRzero htailTwo hnotbase
        hdivZeroOne hdivZeroTwo hdivOneTwo
  have hnotinjective : ¬ h.HasInjectiveRepresentative :=
    classifiedWeightedThreeForms_not_hasInjectiveRepresentative
      h a D ha hdegreeFive R hR hRzero
        A B c₄ c₃ c₂ c₁ c₀ hAB hQzero hnotbase
        htailZero htailOne htailTwo
        hdivZeroOne hdivZeroTwo hdivOneTwo
  intro hg
  exact hnotinjective (hinjective.mpr hg)

end OnLeConjecture.DThree
