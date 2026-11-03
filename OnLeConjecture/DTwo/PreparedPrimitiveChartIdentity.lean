/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicInitialComponentIdentity
public import OnLeConjecture.DTwo.PreparedPrimitiveLeadingCoefficient

/-!
# The prepared primitive quotient identity from its affine chart

For a polynomial in the normalized variables `(x,T)` of weights `(1,2)`,
an affine primitive comparison implies the existing component quotient
identity. The polynomial's coefficients are extracted by the proved
weighted coefficient formula. Normalization of the leading coefficient
remains explicit when constructing a prepared odd family.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open scoped BigOperators

private theorem component_algebraMap_complex (χ c : ℂ) :
    algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C (C c)) =
      algebraMap ℂ (EqualizerComponentRing χ) c := by
  exact (IsScalarTower.algebraMap_apply ℂ EqualizerBaseRing (EqualizerComponentRing χ) c).symm

private theorem preparedComponent_source_aeval (N : ℕ) (χ : ℂ) (α : ℕ → ℂ) :
    MvPolynomial.aeval
        ![algebraMap EqualizerBaseRing (EqualizerComponentRing χ) X,
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X)]
        (preparedOddBivariatePolynomial N α) =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
        (preparedComponentPolynomial N α) := by
  simp only [preparedOddBivariatePolynomial, preparedComponentPolynomial,
    map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, component_algebraMap_complex]
  apply Finset.sum_congr rfl
  intro h hh
  ring

private theorem preparedComponent_rotated_aeval (N : ℕ) (χ : ℂ) (α : ℕ → ℂ) :
    MvPolynomial.aeval
        ![AdjoinRoot.root (componentPolynomial χ),
          algebraMap ℂ (EqualizerComponentRing χ) χ *
            algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X)]
        (preparedOddBivariatePolynomial N α) =
      componentSectorValue χ (preparedComponentPolynomial N α) := by
  simp only [preparedOddBivariatePolynomial, preparedComponentPolynomial,
    componentSectorValue_eq, map_sum, map_mul, map_pow,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, scaleEqualizerParameter_apply,
    Polynomial.C_comp, Polynomial.X_comp,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change ∑ h ∈ Finset.range (N / 2 + 1),
      algebraMap ℂ (EqualizerComponentRing χ) (α h) *
        AdjoinRoot.root (componentPolynomial χ) ^ (N - 2 * h) *
        (algebraMap ℂ (EqualizerComponentRing χ) χ *
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X)) ^ h =
    ∑ h ∈ Finset.range (N / 2 + 1),
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C (C (α h))) *
        (algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C (C χ)) *
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X)) ^ h *
        AdjoinRoot.root (componentPolynomial χ) ^ (N - 2 * h)
  simp only [component_algebraMap_complex]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The affine comparison of a prepared polynomial gives its existing
primitive component identity. -/
theorem preparedPrimitiveComponentIdentity_of_chart
    (N : ℕ) (χ cD : ℂ) (hχ : χ ≠ 1) (α : ℕ → ℂ)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] (preparedOddBivariatePolynomial N α) -
        MvPolynomial.eval ![S, χ] (preparedOddBivariatePolynomial N α) =
          cD * (s - S) ^ N) :
    PreparedPrimitiveComponentIdentity N χ cD α := by
  have hpoint : AdjoinRoot.root (componentPolynomial χ) ^ 2 =
      (algebraMap EqualizerBaseRing (EqualizerComponentRing χ) X) ^ 2 +
        algebraMap ℂ (EqualizerComponentRing χ) (1 - χ) *
          (algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X)) ^ 1 := by
    rw [componentRoot_sq, componentSquare_eq]
    simp only [map_add, map_mul, map_pow, component_algebraMap_complex, pow_one]
  have h := cyclicInitial_primitive_identity_of_chart 1 N (1 - χ) χ cD
    (sub_ne_zero.mpr (Ne.symm hχ)) (preparedOddBivariatePolynomial N α)
    (by simpa using preparedOddBivariatePolynomial_isWeightedHomogeneous N α)
    hchart _ _ _ hpoint
  rw [preparedComponent_source_aeval, preparedComponent_rotated_aeval] at h
  exact (preparedPrimitiveComponentIdentity_iff N χ cD α).mpr h

/-- An arbitrary homogeneous polynomial in normalized variables supplies
the complete prepared coefficient tuple and the primitive quotient identity. -/
theorem preparedPrimitiveComponentIdentity_of_homogeneous_chart
    (N : ℕ) (χ cD : ℂ) (hχ : χ ≠ 1) (H : MvPolynomial (Fin 2) ℂ)
    (hH : H.IsWeightedHomogeneous ![1, 2] N)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] H - MvPolynomial.eval ![S, χ] H = cD * (s - S) ^ N) :
    H = preparedOddBivariatePolynomial N (preparedCoefficient N H) ∧
      PreparedPrimitiveComponentIdentity N χ cD (preparedCoefficient N H) := by
  have hformula := eq_preparedOddBivariatePolynomial_of_isWeightedHomogeneous hH
  refine ⟨hformula, preparedPrimitiveComponentIdentity_of_chart N χ cD hχ _ ?_⟩
  simpa only [← hformula] using hchart

/-- Normalization and the affine primitive comparison construct a
prepared odd family and its bivariate model. The next coefficient and
the character `χ=-1` are conclusions, not assumptions. -/
theorem exists_preparedOddFamily_model_of_homogeneous_chart
    (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N) (χ cD : ℂ) (hχ : χ ≠ 1)
    (H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 2] N)
    (hzero : preparedCoefficient N H 0 = 1)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] H - MvPolynomial.eval ![S, χ] H = cD * (s - S) ^ N) :
    preparedCoefficient N H 1 = (N : ℂ) / 2 ∧ χ = -1 ∧
      ∃ Ψ : PreparedOddFamily N, ∃ model : Ψ.BivariateModel, model.polynomial = H := by
  obtain ⟨hformula, hidentity⟩ :=
    preparedPrimitiveComponentIdentity_of_homogeneous_chart N χ cD hχ H hH hchart
  refine ⟨preparedCoefficient_one_of_primitiveComponentIdentity hN hχ hzero hidentity,
    primitiveCharacter_eq_neg_one_of_normalizedComponentIdentity hN hodd hχ hzero hidentity,
    PreparedOddFamily.ofPrimitiveComponentIdentity hN hodd hχ hzero hidentity,
    PreparedOddFamily.BivariateModel.ofPrimitiveComponentIdentity hN hodd hχ hzero hidentity, ?_⟩
  exact hformula.symm

end OnLeConjecture.DTwo
