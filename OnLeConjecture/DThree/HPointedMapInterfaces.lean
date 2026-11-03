/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddHomogeneous
public import OnLeConjecture.DThree.HInvariantAnalyticInterface
public import OnLeConjecture.DThree.HReflectionLineNoninjectivity
public import OnLeConjecture.DThree.OrdinaryOrderExpansion
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# Analytic interfaces for normalized H pointed map germs

Reflection invariant third forms descend through the quadratic substitution.
At ordinary source weight one, the descended polynomial map is the normalized
H polynomial map. The invariant collision theorem and the reflection line
collision theorem therefore apply to pointed map germs with the
corresponding component jet congruences.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- At source weight one, quadratic power substitution is quadratic
substitution. -/
theorem hWeightedQuadraticSubstitutionForm_one
    (R : MvPolynomial (Fin 2) ℂ) :
    hWeightedQuadraticSubstitutionForm 1 R =
      hQuadraticSubstitutionForm R := by
  have hequality : hWeightedQuadraticSubstitutionForm 1 =
      hQuadraticSubstitutionForm := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    all_goals
      simp [hWeightedQuadraticSubstitutionForm,
        hQuadraticSubstitutionForm]
  exact AlgHom.congr_fun hequality R

/-- Quadratic descent at source weight one recovers the ordinary normalized
H polynomial map. -/
theorem hQuadraticWeightedPolynomialMap_one_eq_hOrdinaryPolynomialMap
    (Rzero : MvPolynomial (Fin 2) ℂ) (R : Form ℂ)
    (hsubstitution : hQuadraticSubstitutionForm Rzero = R) :
    hQuadraticWeightedPolynomialMap 1 Rzero =
      hOrdinaryPolynomialMap R := by
  funext i
  fin_cases i
  · simp [hQuadraticWeightedPolynomialMap, hOrdinaryPolynomialMap,
      cubicForm, formX, formT]
    ring
  · simp [hQuadraticWeightedPolynomialMap, hOrdinaryPolynomialMap,
      quarticForm, formX, formT]
    ring
  · change hWeightedQuadraticSubstitutionForm 1 Rzero = R
    rw [hWeightedQuadraticSubstitutionForm_one, hsubstitution]

/-- The weighted degrees at source weight one are the ordinary degrees of
the normalized H map. -/
theorem hQuadraticWeightedDegrees_one_eq_hOrdinaryDegrees (N : ℕ) :
    hQuadraticWeightedDegrees 1 N = hOrdinaryDegrees N := by
  funext i
  fin_cases i
  all_goals
    simp [hQuadraticWeightedDegrees, hOrdinaryDegrees]

/-- A reflection invariant normalized H pointed map germ cannot have an
injective representative under the two Jacobian divisibilities and the base
exclusion hypothesis. -/
theorem hInvariantNormalizedPointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (R : Form ℂ) (N : ℕ)
    (hN : 5 ≤ N)
    (hR : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm (-1) R)
    (hnotbase : ∀ Rzero : MvPolynomial (Fin 2) ℂ,
      hQuadraticSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 3 0) R)
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) R)
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  have homega : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨Rzero, hsubstitution⟩ :=
    exists_h_weighted_descent_of_reflectionInvariant R homega hinvariant
  have hsubstitutionHomogeneous :
      (hQuadraticSubstitutionForm Rzero).IsHomogeneous N := by
    rw [hsubstitution]
    exact hR
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    isWeightedHomogeneous_of_hQuadraticSubstitutionForm_isHomogeneous
      hsubstitutionHomogeneous
  have hmap :=
    hQuadraticWeightedPolynomialMap_one_eq_hOrdinaryPolynomialMap
      Rzero R hsubstitution
  have hdegrees := hQuadraticWeightedDegrees_one_eq_hOrdinaryDegrees N
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    1 N (by norm_num) hN Rzero hRzero (hnotbase Rzero hsubstitution)
  · rw [hsubstitution]
    exact hPdiv
  · rw [hsubstitution]
    exact hQdiv
  · intro i
    rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
    rw [hdegrees, hmap, hcomponents i]
    exact htail i

/-- A normalized H pointed map germ with a reflection line collision cannot
have an injective representative. -/
theorem hReflectionLinePointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N)
    (data : HReflectionLineCollisionCertificate R)
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hReflectionLineMaximalIdealTails_not_hasInjectiveRepresentative
    hR data representative hanalytic hzero
  intro i
  rw [hcomponents i]
  exact htail i

end OnLeConjecture.DThree
