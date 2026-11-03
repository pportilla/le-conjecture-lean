/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PrimitiveCharacterComparison
public import OnLeConjecture.Analytic.Injectivity

/-!
# Noninjectivity from the primitive residual comparison

An exponent not divisible by the primitive order gives the required
nontrivial character, without an upper bound on that exponent. The
bivariate model and component comparison then construct the prepared
analytic data, whose collision excludes injectivity. The endpoint permits
the coordinate changes used in the manuscript. Its comparison identity and
analytic correction conditions remain hypotheses.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The selected primitive root of a positive order. -/
@[expose]
noncomputable def residualPrimitiveRoot (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / k)

/-- The selected root has primitive order `k` when `k` is positive. -/
theorem residualPrimitiveRoot_isPrimitiveRoot
    {k : ℕ} (hk : 0 < k) :
    IsPrimitiveRoot (residualPrimitiveRoot k) k := by
  exact Complex.isPrimitiveRoot_exp k (by omega)

namespace ResidualPreparedAnalyticData

/-- An exponent not divisible by the primitive order supplies the
nontrivial character hypothesis in the primitive comparison constructor. -/
theorem ofBivariateModelAndPrimitiveComparison_of_not_dvd
    {a k j L N : ℕ} {zeta c T comparisonConstant : ℂ}
    {Psi : PreparedOddFamily N}
    {representative : ℂ × ℂ → Fin 3 → ℂ}
    (model : Psi.BivariateModel)
    (two_le_a : 2 ≤ a)
    (k_eq_two_mul_a : k = 2 * a)
    (L_eq_k_add_j : L = k + j)
    (primitive_root : IsPrimitiveRoot zeta k)
    (j_not_dvd : ¬ k ∣ j)
    (three_le_N : 3 ≤ N)
    (comparison_identity : PreparedPrimitiveComponentIdentity N (zeta ^ j)
      comparisonConstant (preparedCoefficient N model.polynomial))
    (c_ne_zero : c ≠ 0)
    (T_ne_zero : T ≠ 0)
    (representative_analytic : AnalyticAt ℂ representative 0)
    (representative_zero : representative 0 = 0)
    (correction_coefficient_divisibility : ∀ i,
      Germ.TwoWeightCoefficientDivisibility L 2
        (residualWeightedDegrees k L N i + 1)
        (pairRepresentativeComponentGerm representative
            representative_analytic i -
          Germ.coordinatePolynomialAlgHom 2
            (residualPreparedInitialPolynomials k L N c T
              (preparedCoefficient N model.polynomial) i))) :
    ResidualPreparedAnalyticData a k j L N zeta c T Psi
      (preparedCoefficient N model.polynomial) representative := by
  have hcharacter : zeta ^ j ≠ 1 :=
    (primitive_root.pow_eq_one_iff_dvd j).not.mpr j_not_dvd
  exact ofBivariateModelAndPrimitiveComparison model two_le_a
    k_eq_two_mul_a L_eq_k_add_j primitive_root hcharacter three_le_N
      comparison_identity c_ne_zero T_ne_zero representative_analytic
        representative_zero correction_coefficient_divisibility

end ResidualPreparedAnalyticData

namespace PointedMapGerm

/-- A pointed map identified with a prepared primitive comparison has no
injective representative. The coefficient formula, primitive character,
subgroup divisibility, collision certificate, and order ideal membership are
derived by the residual interface. -/
theorem not_hasInjectiveRepresentative_of_residualPrimitiveComparison
    (F : PointedMapGerm 2 3)
    {a k j L N : ℕ} {zeta c T comparisonConstant : ℂ}
    {Psi : PreparedOddFamily N}
    {representative : ℂ × ℂ → Fin 3 → ℂ}
    (model : Psi.BivariateModel)
    (two_le_a : 2 ≤ a)
    (k_eq_two_mul_a : k = 2 * a)
    (L_eq_k_add_j : L = k + j)
    (primitive_root : IsPrimitiveRoot zeta k)
    (j_not_dvd : ¬ k ∣ j)
    (three_le_N : 3 ≤ N)
    (comparison_identity : PreparedPrimitiveComponentIdentity N (zeta ^ j)
      comparisonConstant (preparedCoefficient N model.polynomial))
    (c_ne_zero : c ≠ 0)
    (T_ne_zero : T ≠ 0)
    (representative_analytic : AnalyticAt ℂ representative 0)
    (representative_zero : representative 0 = 0)
    (representative_eq : F = PointedMapGerm.ofPairFunction representative
      representative_analytic representative_zero)
    (correction_coefficient_divisibility : ∀ i,
      Germ.TwoWeightCoefficientDivisibility L 2
        (residualWeightedDegrees k L N i + 1)
        (pairRepresentativeComponentGerm representative
            representative_analytic i -
          Germ.coordinatePolynomialAlgHom 2
            (residualPreparedInitialPolynomials k L N c T
              (preparedCoefficient N model.polynomial) i))) :
    ¬ F.HasInjectiveRepresentative := by
  have hcharacter : zeta ^ j ≠ 1 :=
    (primitive_root.pow_eq_one_iff_dvd j).not.mpr j_not_dvd
  let data :=
    ResidualPreparedAnalyticData.ofBivariateModelAndPrimitiveComparison
      model two_le_a k_eq_two_mul_a L_eq_k_add_j primitive_root hcharacter
        three_le_N comparison_identity c_ne_zero T_ne_zero
          representative_analytic representative_zero
            correction_coefficient_divisibility
  rw [representative_eq]
  exact data.not_hasInjectiveRepresentative

/-- The canonical primitive root removes the root selection from the
prepared residual comparison. -/
theorem not_hasInjectiveRepresentative_of_residualCanonicalComparison
    (F : PointedMapGerm 2 3)
    {a k j L N : ℕ} {c T comparisonConstant : ℂ}
    {Psi : PreparedOddFamily N}
    {representative : ℂ × ℂ → Fin 3 → ℂ}
    (model : Psi.BivariateModel)
    (two_le_a : 2 ≤ a)
    (k_eq_two_mul_a : k = 2 * a)
    (L_eq_k_add_j : L = k + j)
    (j_not_dvd : ¬ k ∣ j)
    (three_le_N : 3 ≤ N)
    (comparison_identity : PreparedPrimitiveComponentIdentity N
      (residualPrimitiveRoot k ^ j) comparisonConstant
        (preparedCoefficient N model.polynomial))
    (c_ne_zero : c ≠ 0)
    (T_ne_zero : T ≠ 0)
    (representative_analytic : AnalyticAt ℂ representative 0)
    (representative_zero : representative 0 = 0)
    (representative_eq : F = PointedMapGerm.ofPairFunction representative
      representative_analytic representative_zero)
    (correction_coefficient_divisibility : ∀ i,
      Germ.TwoWeightCoefficientDivisibility L 2
        (residualWeightedDegrees k L N i + 1)
        (pairRepresentativeComponentGerm representative
            representative_analytic i -
          Germ.coordinatePolynomialAlgHom 2
            (residualPreparedInitialPolynomials k L N c T
              (preparedCoefficient N model.polynomial) i))) :
    ¬ F.HasInjectiveRepresentative := by
  have hk : 0 < k := by omega
  exact not_hasInjectiveRepresentative_of_residualPrimitiveComparison F
    model two_le_a k_eq_two_mul_a L_eq_k_add_j
      (residualPrimitiveRoot_isPrimitiveRoot hk) j_not_dvd three_le_N
        comparison_identity c_ne_zero T_ne_zero representative_analytic
          representative_zero representative_eq
            correction_coefficient_divisibility

end PointedMapGerm

/-- The inputs that attach the primitive residual endpoint to a pointed
map after coordinate changes. The component comparison and correction
conditions are required inputs, not conclusions of this structure. -/
structure ResidualCanonicalComparisonEndpoint
    (F : PointedMapGerm 2 3) where
  a : ℕ
  k : ℕ
  j : ℕ
  L : ℕ
  N : ℕ
  c : ℂ
  T : ℂ
  comparison_constant : ℂ
  Psi : PreparedOddFamily N
  representative : ℂ × ℂ → Fin 3 → ℂ
  model : Psi.BivariateModel
  two_le_a : 2 ≤ a
  k_eq_two_mul_a : k = 2 * a
  L_eq_k_add_j : L = k + j
  j_not_dvd : ¬ k ∣ j
  three_le_N : 3 ≤ N
  comparison_identity : PreparedPrimitiveComponentIdentity N
    (residualPrimitiveRoot k ^ j) comparison_constant
      (preparedCoefficient N model.polynomial)
  c_ne_zero : c ≠ 0
  T_ne_zero : T ≠ 0
  representative_analytic : AnalyticAt ℂ representative 0
  representative_zero : representative 0 = 0
  representative_equivalent : F.RightLeftEquivalent
    (PointedMapGerm.ofPairFunction representative
      representative_analytic representative_zero)
  correction_coefficient_divisibility : ∀ i,
    Germ.TwoWeightCoefficientDivisibility L 2
      (residualWeightedDegrees k L N i + 1)
      (pairRepresentativeComponentGerm representative
          representative_analytic i -
        Germ.coordinatePolynomialAlgHom 2
          (residualPreparedInitialPolynomials k L N c T
            (preparedCoefficient N model.polynomial) i))

namespace ResidualCanonicalComparisonEndpoint

/-- A pointed map with a primitive residual endpoint has no injective
representative. -/
theorem not_hasInjectiveRepresentative
    {F : PointedMapGerm 2 3}
    (data : ResidualCanonicalComparisonEndpoint F) :
    ¬ F.HasInjectiveRepresentative := by
  have hprepared :=
    PointedMapGerm.not_hasInjectiveRepresentative_of_residualCanonicalComparison
      (PointedMapGerm.ofPairFunction data.representative
        data.representative_analytic data.representative_zero)
      data.model data.two_le_a data.k_eq_two_mul_a data.L_eq_k_add_j
        data.j_not_dvd data.three_le_N data.comparison_identity
          data.c_ne_zero data.T_ne_zero data.representative_analytic
            data.representative_zero rfl
              data.correction_coefficient_divisibility
  intro hinjective
  exact hprepared
    (data.representative_equivalent.hasInjectiveRepresentative hinjective)

end ResidualCanonicalComparisonEndpoint

end OnLeConjecture.DTwo
