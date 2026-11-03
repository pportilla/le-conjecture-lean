/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryInitialGeneration
public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm
public import OnLeConjecture.Analytic.JacobianLinearSpan
public import OnLeConjecture.DTwo.FullQuadraticLinearSpan
import Mathlib.Tactic

/-!
# The Jacobian ideal of a full quadratic jet

For the quadratic jet `(x²,xy,y²)`, the three Jacobian minors generate the
square of the analytic maximal ideal. Consequently they admit no common
factor vanishing at the origin. Higher analytic terms are unrestricted.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

private theorem quadratic_jacobian_tail
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![1, 1] 2)
    (hQ : Q.IsWeightedHomogeneous ![1, 1] 2)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈ Germ.maximalIdeal 2 ^ 3)
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈ Germ.maximalIdeal 2 ^ 3) :
    Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2
      (OnLeConjecture.Polynomial.jacobian P Q) ∈ Germ.maximalIdeal 2 ^ 3 := by
  simpa only [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow] using
    Germ.jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
      1 2 2 (by omega) (by omega) (by omega) P Q hP hQ f g
      (by simpa only [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf)
      (by simpa only [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow] using hg)

/-- Scalar normalization of an initial monomial preserves its strict
ordinary tail. -/
private theorem normalized_scalar_tail
    (a : ℂ) (ha : a ≠ 0) (f g : Germ 2)
    (h : f - Germ.constRingHom 2 a * g ∈ Germ.maximalIdeal 2 ^ 3) :
    Germ.constRingHom 2 a⁻¹ * f - g ∈ Germ.maximalIdeal 2 ^ 3 := by
  have h' := (Germ.maximalIdeal 2 ^ 3).mul_mem_left (Germ.constRingHom 2 a⁻¹) h
  have hone : Germ.constRingHom 2 a⁻¹ * Germ.constRingHom 2 a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  simpa only [mul_sub, ← mul_assoc, hone, one_mul] using h'

/-- The three normalized minors have initial forms `y²`, `xy`, and `x²`.
The order of this list is the order of the ordinary monomial generators. -/
theorem normalized_quadratic_jacobian_initial_generators
    (f g h : Germ 2)
    (hf : f - Germ.coordinate (0 : Fin 2) ^ 2 ∈ Germ.maximalIdeal 2 ^ 3)
    (hg : g - Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hh : h - Germ.coordinate (1 : Fin 2) ^ 2 ∈ Germ.maximalIdeal 2 ^ 3) :
    ∀ i : Fin 3,
      ![Germ.constRingHom 2 ((2 : ℂ)⁻¹) * Germ.jacobian g h,
        Germ.constRingHom 2 ((4 : ℂ)⁻¹) * Germ.jacobian f h,
        Germ.constRingHom 2 ((2 : ℂ)⁻¹) * Germ.jacobian f g] i -
      Germ.weightedOrderGenerator 1 2 i ∈ Germ.maximalIdeal 2 ^ 3 := by
  let X : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0
  let Y : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1
  have hX : X.IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [X] using MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0
  have hY : Y.IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [Y] using MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 1
  have hf' : f - Germ.coordinatePolynomialAlgHom 2 (X ^ 2) ∈ Germ.maximalIdeal 2 ^ 3 := by
    simpa [X] using hf
  have hg' : g - Germ.coordinatePolynomialAlgHom 2 (X * Y) ∈ Germ.maximalIdeal 2 ^ 3 := by
    simpa [X, Y] using hg
  have hh' : h - Germ.coordinatePolynomialAlgHom 2 (Y ^ 2) ∈ Germ.maximalIdeal 2 ^ 3 := by
    simpa [Y] using hh
  have hgh := quadratic_jacobian_tail (X * Y) (Y ^ 2) (hX.mul hY) (hY.pow 2)
    g h hg' hh'
  have hfh := quadratic_jacobian_tail (X ^ 2) (Y ^ 2) (hX.pow 2) (hY.pow 2)
    f h hf' hh'
  have hfg := quadratic_jacobian_tail (X ^ 2) (X * Y) (hX.pow 2) (hX.mul hY)
    f g hf' hg'
  have hpolygh : OnLeConjecture.Polynomial.jacobian (X * Y) (Y ^ 2) =
      MvPolynomial.C 2 * Y ^ 2 := by
    rw [show (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat _ 2]
    norm_num [OnLeConjecture.Polynomial.jacobian, X, Y]
    ring
  have hpolyfh : OnLeConjecture.Polynomial.jacobian (X ^ 2) (Y ^ 2) =
      MvPolynomial.C 4 * (X * Y) := by
    rw [show (MvPolynomial.C (4 : ℂ) : MvPolynomial (Fin 2) ℂ) = 4 from map_ofNat _ 4]
    norm_num [OnLeConjecture.Polynomial.jacobian, X, Y]
    ring
  have hpolyfg : OnLeConjecture.Polynomial.jacobian (X ^ 2) (X * Y) =
      MvPolynomial.C 2 * X ^ 2 := by
    rw [show (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat _ 2]
    norm_num [OnLeConjecture.Polynomial.jacobian, X, Y]
    ring
  rw [hpolygh] at hgh
  rw [hpolyfh] at hfh
  rw [hpolyfg] at hfg
  simp only [map_mul, map_pow, Germ.coordinatePolynomialAlgHom_C,
    Germ.coordinatePolynomialAlgHom_X, X, Y] at hgh hfh hfg
  have h0 := normalized_scalar_tail 2 (by norm_num) _ _ hgh
  have h1 := normalized_scalar_tail 4 (by norm_num) _ _ hfh
  have h2 := normalized_scalar_tail 2 (by norm_num) _ _ hfg
  intro i
  fin_cases i
  · simpa [Germ.weightedOrderGenerator] using h0
  · simpa [Germ.weightedOrderGenerator] using h1
  · simpa [Germ.weightedOrderGenerator] using h2

/-- A full normalized quadratic jet is incompatible with any common
critical-curve equation dividing the three Jacobian minors. -/
theorem no_common_jacobian_divisor_of_full_quadratic_jet
    (f g h : Germ 2)
    (hf : f - Germ.coordinate (0 : Fin 2) ^ 2 ∈ Germ.maximalIdeal 2 ^ 3)
    (hg : g - Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hh : h - Germ.coordinate (1 : Fin 2) ^ 2 ∈ Germ.maximalIdeal 2 ^ 3)
    (c : Germ 2) (hc : c ∈ Germ.maximalIdeal 2)
    (hfg : c ∣ Germ.jacobian f g) (hfh : c ∣ Germ.jacobian f h)
    (hgh : c ∣ Germ.jacobian g h) : False := by
  apply Germ.no_common_nonunit_divisor_of_monomial_initial_generators 2 _
    (normalized_quadratic_jacobian_initial_generators f g h hf hg hh) c hc
  intro i
  fin_cases i
  · exact dvd_mul_of_dvd_right hgh _
  · exact dvd_mul_of_dvd_right hfh _
  · exact dvd_mul_of_dvd_right hfg _

/-- The rank-three obstruction does not require chosen target
coordinates. It suffices that the quadratic initial forms span all three
binary quadratic monomials. -/
theorem no_common_jacobian_divisor_of_spanning_quadratic_jets
    {ι : Type*} (f : ι → Germ 2) (P : ι → MvPolynomial (Fin 2) ℂ)
    (htail : ∀ i, f i - Germ.coordinatePolynomialAlgHom 2 (P i) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hx : MvPolynomial.X (0 : Fin 2) ^ 2 ∈ Submodule.span ℂ (Set.range P))
    (hxy : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
      Submodule.span ℂ (Set.range P))
    (hy : MvPolynomial.X (1 : Fin 2) ^ 2 ∈ Submodule.span ℂ (Set.range P))
    (c : Germ 2) (hc : c ∈ Germ.maximalIdeal 2)
    (hdiv : ∀ i j, c ∣ Germ.jacobian (f i) (f j)) : False := by
  obtain ⟨F, hF, hFt⟩ := Germ.exists_linear_span_lift_of_initial_form f P 3 htail hx
  obtain ⟨G, hG, hGt⟩ := Germ.exists_linear_span_lift_of_initial_form f P 3 htail hxy
  obtain ⟨H, hH, hHt⟩ := Germ.exists_linear_span_lift_of_initial_form f P 3 htail hy
  apply no_common_jacobian_divisor_of_full_quadratic_jet F G H
    (by simpa using hFt) (by simpa using hGt) (by simpa using hHt) c hc
  · exact Germ.dvd_jacobian_of_mem_linear_span f c hdiv hF hG
  · exact Germ.dvd_jacobian_of_mem_linear_span f c hdiv hF hH
  · exact Germ.dvd_jacobian_of_mem_linear_span f c hdiv hG hH

/-- Three linearly independent quadratic initial forms contradict a
common Jacobian divisor vanishing at the origin. This is the full
rank-three quadratic-jet exclusion, before any target normalization. -/
theorem not_linearIndependent_quadratic_jets_of_common_jacobian_divisor
    (f : Fin 3 → Germ 2) (P : Fin 3 → OrbitSourceForm)
    (hP : ∀ i, (P i).IsHomogeneous 2)
    (htail : ∀ i, f i - Germ.coordinatePolynomialAlgHom 2 (P i) ∈
      Germ.maximalIdeal 2 ^ 3)
    (c : Germ 2) (hc : c ∈ Germ.maximalIdeal 2)
    (hdiv : ∀ i j, c ∣ Germ.jacobian (f i) (f j)) :
    ¬ LinearIndependent ℂ P := by
  intro hind
  have hspan := span_quadratics_eq_monomial_span_of_linearIndependent P hP hind
  have hmon (i : Fin 3) : quadraticMonomials i ∈ Submodule.span ℂ (Set.range P) := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact no_common_jacobian_divisor_of_spanning_quadratic_jets f P htail
    (by simpa [quadraticMonomials] using hmon 0)
    (by simpa [quadraticMonomials] using hmon 1)
    (by simpa [quadraticMonomials] using hmon 2) c hc hdiv

end OnLeConjecture.DTwo
