/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HInvariantAnalyticInterface
public import OnLeConjecture.DThree.HPointedMapInterfaces
public import OnLeConjecture.DThree.WeightedResidueDecomposition

/-!
# The invariant H branch with zero weighted residue

A form with zero residue is obtained by replacing the second variable of an
ordinary homogeneous form by `y^a`. If the ordinary form is invariant under
reflection, its quadratic descent converts this power substitution into the
weighted polynomial map used by the complete invariant `H` exclusion.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Apply the power substitution to every coordinate of the ordinary
normalized `H` polynomial map. -/
@[expose]
noncomputable def hResidueZeroPolynomialMap
    (a : ℕ) (R : Form ℂ) : Fin 3 → Form ℂ :=
  fun i ↦ weightedPowerSubstitutionForm a (hOrdinaryPolynomialMap R i)

/-- The power substitution applied after quadratic substitution is the
quadratic weighted substitution. -/
theorem weightedPowerSubstitutionForm_comp_hQuadraticSubstitutionForm
    (a : ℕ) :
    (weightedPowerSubstitutionForm a).comp hQuadraticSubstitutionForm =
      hWeightedQuadraticSubstitutionForm a := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [weightedPowerSubstitutionForm, hQuadraticSubstitutionForm,
      hWeightedQuadraticSubstitutionForm, formX, formT]
  · simp [weightedPowerSubstitutionForm, hQuadraticSubstitutionForm,
      hWeightedQuadraticSubstitutionForm, formX, formT, pow_mul]
    ring

/-- Quadratic descent identifies the zero residue polynomial map with the
quadratic weighted polynomial map. -/
theorem hResidueZeroPolynomialMap_eq_hQuadraticWeightedPolynomialMap
    (a : ℕ) (Rzero R : Form ℂ)
    (hsubstitution : hQuadraticSubstitutionForm Rzero = R) :
    hResidueZeroPolynomialMap a R =
      hQuadraticWeightedPolynomialMap a Rzero := by
  funext i
  fin_cases i
  · simp [hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, hQuadraticWeightedPolynomialMap,
      cubicForm, formX, formT]
    ring
  · simp [hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, hQuadraticWeightedPolynomialMap,
      quarticForm, formX, formT]
    ring
  · change weightedPowerSubstitutionForm a R =
      hWeightedQuadraticSubstitutionForm a Rzero
    rw [← hsubstitution]
    exact AlgHom.congr_fun
      (weightedPowerSubstitutionForm_comp_hQuadraticSubstitutionForm a)
        Rzero

/-- The degrees obtained from the ordinary normalized map agree with the
quadratic weighted degrees. -/
theorem hResidueZeroDegrees_eq_hQuadraticWeightedDegrees
    (a N : ℕ) :
    (fun i ↦ a * hOrdinaryDegrees N i) =
      hQuadraticWeightedDegrees a N := by
  funext i
  fin_cases i
  · simpa [hOrdinaryDegrees, hQuadraticWeightedDegrees] using
      Nat.mul_comm a 3
  · simpa [hOrdinaryDegrees, hQuadraticWeightedDegrees] using
      Nat.mul_comm a 4
  · simpa [hOrdinaryDegrees, hQuadraticWeightedDegrees] using
      Nat.mul_comm a N

/-- The three coordinates of the zero residue polynomial map have the
prescribed weighted degrees. -/
theorem hResidueZeroPolynomialMap_isWeightedHomogeneous
    (a N : ℕ) (R : Form ℂ) (hR : R.IsHomogeneous N) (i : Fin 3) :
    (hResidueZeroPolynomialMap a R i).IsWeightedHomogeneous
      ![a, 1] (hQuadraticWeightedDegrees a N i) := by
  have hhomogeneous :
      (hOrdinaryPolynomialMap R i).IsHomogeneous
        (hOrdinaryDegrees N i) := by
    have hweights : (![1, 1] : Fin 2 → ℕ) = 1 := by
      funext j
      fin_cases j
      · rfl
      · rfl
    change (hOrdinaryPolynomialMap R i).IsWeightedHomogeneous 1
      (hOrdinaryDegrees N i)
    rw [← hweights]
    exact hOrdinaryPolynomialMap_isWeightedHomogeneous R N hR i
  have hsubstitution := weightedPowerSubstitutionForm_isWeightedHomogeneous
    a (hOrdinaryDegrees N i) (hOrdinaryPolynomialMap R i) hhomogeneous
  change (weightedPowerSubstitutionForm a (hOrdinaryPolynomialMap R i))
    |>.IsWeightedHomogeneous ![a, 1]
      (hQuadraticWeightedDegrees a N i)
  rw [← congrFun (hResidueZeroDegrees_eq_hQuadraticWeightedDegrees a N) i]
  exact hsubstitution

/-- Zero residue in the weighted decomposition removes the power of the
second variable. -/
theorem exists_weightedPowerSubstitutionForm_of_residue_eq_zero
    (a D : ℕ) (ha : 0 < a) (P : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hresidue : D % a = 0) :
    ∃ R : Form ℂ, R.IsHomogeneous (D / a) ∧
      P = weightedPowerSubstitutionForm a R := by
  obtain ⟨R, hR, hdecomposition⟩ :=
    exists_weightedResidueDecomposition a D ha P hP
  refine ⟨R, hR, ?_⟩
  simpa only [hresidue, pow_zero, one_mul] using hdecomposition

/-- An invariant zero residue `H` form excludes injectivity for every
positive source weight. -/
theorem hInvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : Form ℂ) (hR : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm (-1) R)
    (hnotbase : ∀ Rzero : Form ℂ,
      hQuadraticSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 3 0) R)
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  have homega : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨Rzero, hsubstitution⟩ :=
    exists_h_weighted_descent_of_reflectionInvariant R homega hinvariant
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    isWeightedHomogeneous_of_hQuadraticSubstitutionForm_isHomogeneous (by
      rw [hsubstitution]
      exact hR)
  have hmap :=
    hResidueZeroPolynomialMap_eq_hQuadraticWeightedPolynomialMap
      a Rzero R hsubstitution
  apply hInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha hN Rzero hRzero (hnotbase Rzero hsubstitution)
  · rw [hsubstitution]
    exact hPdiv
  · rw [hsubstitution]
    exact hQdiv
  · intro i
    rw [← hmap]
    exact htail i

/-- The invariant zero residue exclusion for a pointed map germ. -/
theorem hInvariantResidueZeroPointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : Form ℂ) (hR : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm (-1) R)
    (hnotbase : ∀ Rzero : Form ℂ,
      hQuadraticSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 3 0) R)
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) R)
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hInvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha hN R hR hinvariant hnotbase hPdiv hQdiv representative
      hanalytic hzero
  intro i
  rw [hcomponents i]
  exact htail i

end OnLeConjecture.DThree
