/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedBaseRescaling
public import OnLeConjecture.DThree.WeightedJacobianTransport
public import OnLeConjecture.DThree.WeightedPositiveResidueExclusion
public import OnLeConjecture.DThree.WeightedZeroResidueExclusion

/-!
# Exclusion for all residues after weighted normalization

The normalized E and H pairs exclude injectivity for every residue of the
third weighted degree. Retaining the source scalar and both target scalars
in the classified rescaling transports the generated pair exclusion, the
polynomial Jacobian divisibilities, and all three weighted tails.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A normalized weighted E map is incompatible with an injective
representative for every residue of the third weighted degree. -/
theorem eWeightedNormalizedAllResidues_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (hdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedCubicPolynomial a 0 3) R)
    (hnotbase : ∀ S : ESourceRing ℂ,
      S ∈ Set.range (eBaseToSource ℂ) →
        weightedPowerSubstitutionForm a
          (eSourceCubeSubstitutionForm S) ≠ R)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 0 3) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 0 4 0) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  by_cases hresidue : D % a = 0
  · exact eWeightedZeroResiduePointedMap_not_hasInjectiveRepresentative
      g a D ha R hR hresidue hdiv hnotbase
        htailZero htailOne htailTwo
  · have hpositive : 0 < D % a := Nat.pos_of_ne_zero hresidue
    exact ePositiveResiduePointedMap_not_hasInjectiveRepresentative
      g a D ha R hR hRzero hpositive
        htailZero htailOne htailTwo

/-- A normalized weighted H map is incompatible with an injective
representative for every residue of the third weighted degree. -/
theorem hWeightedNormalizedAllResidues_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (hdegreeFive : 5 ≤ D / a)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (hPdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedCubicPolynomial a 3 0) R)
    (hQdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedQuarticPolynomial a 1 0 4 0 2) R)
    (hnotbase : ∀ S : Form ℂ,
      S ∈ Set.range (hBaseToWeightedForm ℂ) →
        weightedPowerSubstitutionForm a
          (hQuadraticSubstitutionForm S) ≠ R)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 3 0) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 4 0 2) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  by_cases hresidue : D % a = 0
  · exact hWeightedZeroResiduePointedMap_not_hasInjectiveRepresentative
      g a D ha hdegreeFive R hR hresidue hPdiv hQdiv hnotbase
        htailZero htailOne htailTwo
  · have hpositive : 0 < D % a := Nat.pos_of_ne_zero hresidue
    exact hPositiveResiduePointedMap_not_hasInjectiveRepresentative
      g a D ha R hR hRzero hpositive
        htailZero htailOne htailTwo

/-- The normalized weighted E data used in the residue split. -/
@[expose]
def IsWeightedNormalizedECase
    (g : PointedMapGerm 2 3) (a D : ℕ) (R : Form ℂ) : Prop :=
  R.IsWeightedHomogeneous ![a, 1] D ∧
  R ≠ 0 ∧
  formT ^ (6 * a - 1) ∣
    OnLeConjecture.Polynomial.jacobian
      (weightedCubicPolynomial a 0 3) R ∧
  (∀ S : ESourceRing ℂ,
    S ∈ Set.range (eBaseToSource ℂ) →
      weightedPowerSubstitutionForm a
        (eSourceCubeSubstitutionForm S) ≠ R) ∧
  g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 0 3) ∈
    Germ.weightedOrderIdeal a (3 * a + 1) ∧
  g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 0 4 0) ∈
    Germ.weightedOrderIdeal a (4 * a + 1) ∧
  g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
    Germ.weightedOrderIdeal a (D + 1)

/-- The normalized weighted H data used in the residue split. -/
@[expose]
def IsWeightedNormalizedHCase
    (g : PointedMapGerm 2 3) (a D : ℕ) (R : Form ℂ) : Prop :=
  R.IsWeightedHomogeneous ![a, 1] D ∧
  R ≠ 0 ∧
  formT ^ (6 * a - 1) ∣
    OnLeConjecture.Polynomial.jacobian
      (weightedCubicPolynomial a 3 0) R ∧
  formT ^ (6 * a - 1) ∣
    OnLeConjecture.Polynomial.jacobian
      (weightedQuarticPolynomial a 1 0 4 0 2) R ∧
  (∀ S : Form ℂ,
    S ∈ Set.range (hBaseToWeightedForm ℂ) →
      weightedPowerSubstitutionForm a
        (hQuadraticSubstitutionForm S) ≠ R) ∧
  g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 3 0) ∈
    Germ.weightedOrderIdeal a (3 * a + 1) ∧
  g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 4 0 2) ∈
    Germ.weightedOrderIdeal a (4 * a + 1) ∧
  g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
    Germ.weightedOrderIdeal a (D + 1)

/-- The normalized weighted E data excludes an injective representative. -/
theorem IsWeightedNormalizedECase.not_hasInjectiveRepresentative
    {g : PointedMapGerm 2 3} {a D : ℕ} {R : Form ℂ}
    (data : IsWeightedNormalizedECase g a D R) (ha : 0 < a) :
    ¬ g.HasInjectiveRepresentative := by
  rcases data with ⟨hR, hRzero, hdiv, hnotbase,
    htailZero, htailOne, htailTwo⟩
  exact eWeightedNormalizedAllResidues_not_hasInjectiveRepresentative
    g a D ha R hR hRzero hdiv hnotbase
      htailZero htailOne htailTwo

/-- The normalized weighted H data excludes an injective representative. -/
theorem IsWeightedNormalizedHCase.not_hasInjectiveRepresentative
    {g : PointedMapGerm 2 3} {a D : ℕ} {R : Form ℂ}
    (data : IsWeightedNormalizedHCase g a D R)
    (ha : 0 < a) (hdegreeFive : 5 ≤ D / a) :
    ¬ g.HasInjectiveRepresentative := by
  rcases data with ⟨hR, hRzero, hPdiv, hQdiv, hnotbase,
    htailZero, htailOne, htailTwo⟩
  exact hWeightedNormalizedAllResidues_not_hasInjectiveRepresentative
    g a D ha hdegreeFive R hR hRzero hPdiv hQdiv hnotbase
      htailZero htailOne htailTwo

/-- Either normalized weighted pair excludes an injective representative. -/
theorem weightedNormalizedE_or_H_not_hasInjectiveRepresentative
    {g : PointedMapGerm 2 3} {a D : ℕ} {R : Form ℂ}
    (ha : 0 < a)
    (data : IsWeightedNormalizedECase g a D R ∨
      (5 ≤ D / a ∧ IsWeightedNormalizedHCase g a D R)) :
    ¬ g.HasInjectiveRepresentative := by
  rcases data with hE | hH
  · exact hE.not_hasInjectiveRepresentative ha
  · exact hH.2.not_hasInjectiveRepresentative ha hH.1

/-- The analytic classification retains all three rescaling scalars and
produces the complete normalized weighted E or H data. -/
theorem
    exists_rightLeft_weightedRescaling_isWeightedNormalizedECase_or_HCase
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a) (haD : a ≤ D)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (hnotbase : R ∉ Set.range
      (pairBaseToForm
        (weightedCubicPolynomial a A B)
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)))
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ∃ s u v : ℂ, ∃ h : PointedMapGerm 2 3,
      s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      (IsWeightedNormalizedECase h a D (rescaleForm s 1 R) ∨
        IsWeightedNormalizedHCase h a D (rescaleForm s 1 R)) := by
  let P := weightedCubicPolynomial a A B
  let Q := weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀
  have hP : P.IsWeightedHomogeneous ![a, 1] (3 * a) :=
    weightedCubicPolynomial_isWeightedHomogeneous a A B
  have hQ : Q.IsWeightedHomogeneous ![a, 1] (4 * a) :=
    weightedQuarticPolynomial_isWeightedHomogeneous
      a c₄ c₃ c₂ c₁ c₀
  have hPdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian P R := by
    apply formT_pow_dvd_polynomial_jacobian_of_analytic_divisibility
      a (3 * a) D (6 * a - 1) ha (by omega) haD
        P R hP hR (g.1.component 0) (g.1.component 2)
    · exact htailZero
    · exact htailTwo
    · exact hdivZeroTwo
  have hQdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian Q R := by
    apply formT_pow_dvd_polynomial_jacobian_of_analytic_divisibility
      a (4 * a) D (6 * a - 1) ha (by omega) haD
        Q R hQ hR (g.1.component 1) (g.1.component 2)
    · exact htailOne
    · exact htailTwo
    · exact hdivOneTwo
  have hJacobian := jacobian_weightedCubic_weightedQuartic_ne_zero
    a ha A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
  obtain ⟨c, hc, hODE⟩ :=
    exists_ode_of_analytic_weighted_initial_forms
      a ha A B c₄ c₃ c₂ c₁ c₀
      (g.1.component 0) (g.1.component 1)
      htailZero htailOne hdivZeroOne hJacobian
  obtain ⟨s, u, v, hs, hu, hv, hE | hH⟩ :=
    exists_weightedRescaling_to_E_or_H
      a A B c₄ c₃ c₂ c₁ c₀ c hc hODE
  all_goals
    let h := rescaledPointedMap g s u v 1 hs hu hv one_ne_zero
    have hequivalent : g.RightLeftEquivalent h :=
      rightLeftEquivalent_rescaledPointedMap
        g s u v 1 hs hu hv one_ne_zero
    have hinjective := hequivalent.hasInjectiveRepresentative_iff
    have hRscaled :
        (rescaleForm s 1 R).IsWeightedHomogeneous ![a, 1] D :=
      rescaleForm_isWeightedHomogeneous hR s 1
    have hRscaledZero : rescaleForm s 1 R ≠ 0 :=
      rescaleForm_ne_zero_of_ne_zero s 1 hs one_ne_zero hRzero
    refine ⟨s, u, v, h, hs, hu, hv, hequivalent, hinjective, ?_⟩
  · apply Or.inl
    rcases hE with ⟨hzeroForm, honeForm⟩
    refine ⟨hRscaled, hRscaledZero, ?_, ?_, ?_, ?_, ?_⟩
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s u 1 P R (6 * a - 1) hPdiv
      rw [hzeroForm] at hdiv
      exact hdiv
    · apply eWeightedBaseExclusion_of_not_mem_pairBase a
      exact rescaleForm_not_mem_ePairBase_of_not_mem_pairBase
        P Q R
        (weightedCubicPolynomial a 0 3)
        (weightedQuarticPolynomial a 1 0 0 4 0)
        s u v hs hzeroForm honeForm hnotbase
    · have htail := rescaledPointedMap_component_weightedTail
          g a (3 * a + 1) s u v 1 hs hu hv one_ne_zero 0 P htailZero
      simpa [h, P, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (4 * a + 1) s u v 1 hs hu hv one_ne_zero 1 Q htailOne
      simpa [h, Q, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (D + 1) s u v 1 hs hu hv one_ne_zero 2 R htailTwo
      simpa [h, targetRescaleVector] using htail
  · apply Or.inr
    rcases hH with ⟨hzeroForm, honeForm⟩
    refine ⟨hRscaled, hRscaledZero, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s u 1 P R (6 * a - 1) hPdiv
      rw [hzeroForm] at hdiv
      exact hdiv
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s v 1 Q R (6 * a - 1) hQdiv
      rw [honeForm] at hdiv
      exact hdiv
    · apply hWeightedBaseExclusion_of_not_mem_pairBase a
      exact rescaleForm_not_mem_hPairBase_of_not_mem_pairBase
        P Q R
        (weightedCubicPolynomial a 3 0)
        (weightedQuarticPolynomial a 1 0 4 0 2)
        s u v hs hzeroForm honeForm hnotbase
    · have htail := rescaledPointedMap_component_weightedTail
          g a (3 * a + 1) s u v 1 hs hu hv one_ne_zero 0 P htailZero
      simpa [h, P, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (4 * a + 1) s u v 1 hs hu hv one_ne_zero 1 Q htailOne
      simpa [h, Q, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (D + 1) s u v 1 hs hu hv one_ne_zero 2 R htailTwo
      simpa [h, targetRescaleVector] using htail

/-- Classified weighted cubic, quartic, and third initial forms exclude an
injective representative when all three analytic Jacobians have the required
second coordinate divisor. -/
theorem classifiedWeightedThreeForms_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (hdegreeFive : 5 ≤ D / a)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (hnotbase : R ∉ Set.range
      (pairBaseToForm
        (weightedCubicPolynomial a A B)
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)))
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  have hquotientPositive : 0 < D / a := by omega
  have haD : a ≤ D := by
    calc
      a ≤ a * (D / a) := Nat.le_mul_of_pos_right a hquotientPositive
      _ ≤ D := by
        have hdegree := weightedDegree_eq_residue_add_mul_quotient a D
        omega
  obtain ⟨s, u, v, h, hs, hu, hv, hequivalent, hinjective, hcase⟩ :=
    exists_rightLeft_weightedRescaling_isWeightedNormalizedECase_or_HCase
      g a D ha haD R hR hRzero A B c₄ c₃ c₂ c₁ c₀
        hAB hquartic hnotbase htailZero htailOne htailTwo
        hdivZeroOne hdivZeroTwo hdivOneTwo
  have hnormalized : ¬ h.HasInjectiveRepresentative :=
    weightedNormalizedE_or_H_not_hasInjectiveRepresentative
      ha (hcase.elim Or.inl (fun hH ↦ Or.inr ⟨hdegreeFive, hH⟩))
  intro hg
  exact hnormalized (hinjective.mpr hg)

end OnLeConjecture.DThree
