/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.CubicDividedCoefficientAlternatives
public import OnLeConjecture.Analytic.OrdinaryCuspBlowup
public import OnLeConjecture.Analytic.SwappedNodeBlowup
import Mathlib.Tactic

/-!
# Analytic terminal germs of a divided depressed cubic

The coefficient assumptions give exact convergent expressions for the
smooth, cusp, and node alternatives. They are used only after being
derived from the original weighted coefficient orders.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem polynomialEvaluation_depressed_cubic
    (Q : Polynomial (Germ 1)) (hQ : Q.Monic) (hdegree : Q.natDegree = 3)
    (hdepressed : Q.coeff 2 = 0) :
    firstCoordinatePolynomialEvaluation Q = coordinate (0 : Fin 2) ^ 3 +
      hyperplaneExtension 1 (Q.coeff 1) * coordinate (0 : Fin 2) +
      hyperplaneExtension 1 (Q.coeff 0) := by
  have htop : Q.coeff 3 = 1 := by rw [← hdegree, coeff_natDegree, hQ]
  rw [firstCoordinatePolynomialEvaluation, eval₂_eq_sum_range, hdegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    htop, hdepressed, map_one, map_zero, zero_mul, zero_add, add_zero, pow_zero, pow_one,
    one_mul, mul_one]
  ring

theorem depressed_cubic_residue_eq_X_cube
    (Q : Polynomial (Germ 1)) (hQ : Q.Monic) (hdegree : Q.natDegree = 3)
    (hdepressed : Q.coeff 2 = 0)
    (h₁ : Q.coeff 1 ∈ maximalIdeal 1) (h₀ : Q.coeff 0 ∈ maximalIdeal 1) :
    Q.map (valueRingHom 1) = X ^ 3 := by
  have h := DThree.eq_cubic_of_monic_degree_three (Q.map (valueRingHom 1)) (hQ.map _)
    ((hQ.natDegree_map _).trans hdegree) (by rw [coeff_map, hdepressed, map_zero])
  simpa only [DThree.cubic, coeff_map, mem_maximalIdeal_iff.mp h₁,
    mem_maximalIdeal_iff.mp h₀, map_zero, zero_mul, add_zero] using h

theorem depressed_cubic_mem_cube_of_coefficient_orders
    (Q : Polynomial (Germ 1)) (hdepressed : Q.coeff 2 = 0)
    (h₁ : Q.coeff 1 ∈ maximalIdeal 1 ^ 2) (h₀ : Q.coeff 0 ∈ maximalIdeal 1 ^ 3) :
    firstCoordinatePolynomialEvaluation Q ∈ maximalIdeal 2 ^ 3 := by
  apply (mem_weightedOrderIdeal_one_iff 3 _).mp
  apply firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal 1 3 (by decide)
  intro j
  by_cases hj : j < 3
  · interval_cases j
    · simpa only [mul_zero, Nat.sub_zero] using h₀
    · simpa only [mul_one, Nat.reduceSub] using h₁
    · simp only [hdepressed, Ideal.zero_mem]
  · simp [Nat.sub_eq_zero_of_le (by omega : 3 ≤ j)]

theorem polynomialEvaluation_not_mem_square_of_constant_order_one
    (Q : Polynomial (Germ 1)) (B : Germ 1) (hB : IsUnit B)
    (hconstant : Q.coeff 0 = coordinate (0 : Fin 1) * B) :
    firstCoordinatePolynomialEvaluation Q ∉ maximalIdeal 2 ^ 2 := by
  intro hmem
  have hdiv := coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_maximalIdeal_pow
    2 (firstCoordinatePolynomialEvaluation Q) hmem 0
  rw [firstCoordinateTaylorCoefficient_polynomialEvaluation, Nat.sub_zero] at hdiv
  have hcoeff : Q.coeff 0 ∈ maximalIdeal 1 ^ 2 := by
    rwa [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton]
  have horder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hB
    (by simpa only [pow_one] using hconstant : Q.coeff 0 = coordinate (0 : Fin 1) ^ 1 * B)
  have hbound := mem_maximalIdeal_one_pow_iff.mp hcoeff
  rw [horder] at hbound
  norm_num at hbound

/-- A divided cubic with constant coefficient of order two and linear
coefficient of order at least two has the required cusp expression. -/
theorem exists_depressed_cubic_cusp_expression
    (Q : Polynomial (Germ 1)) (hQ : Q.Monic) (hdegree : Q.natDegree = 3)
    (hdepressed : Q.coeff 2 = 0) (B : Germ 1) (hB : IsUnit B)
    (hconstant : Q.coeff 0 = coordinate (0 : Fin 1) ^ 2 * B)
    (hlinear : Q.coeff 1 ∈ maximalIdeal 1 ^ 2) :
    ∃ C : Germ 2, IsUnit C ∧ firstCoordinatePolynomialEvaluation Q =
      coordinate (0 : Fin 2) ^ 3 + coordinate (1 : Fin 2) ^ 2 * C := by
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hlinear
  obtain ⟨D, hD⟩ := hlinear
  let C := hyperplaneExtension 1 D * coordinate (0 : Fin 2) + hyperplaneExtension 1 B
  have hC : IsUnit C := by
    apply isUnit_iff_valueRingHom_ne_zero.mpr
    simpa only [C, map_add, map_mul, valueRingHom_coordinate, mul_zero, zero_add] using
      valueRingHom_ne_zero_of_isUnit (hB.map (hyperplaneExtension 1))
  refine ⟨C, hC, ?_⟩
  rw [polynomialEvaluation_depressed_cubic Q hQ hdegree hdepressed, hconstant, hD,
    map_mul, map_mul, map_pow, hyperplaneExtension_coordinate_plane]
  dsimp only [C]
  ring

/-- A linear coefficient of order one and constant coefficient of order
at least two give a node with its coordinate tangent equal to `y=0`. -/
theorem exists_depressed_cubic_node_initial
    (Q : Polynomial (Germ 1)) (hQ : Q.Monic) (hdegree : Q.natDegree = 3)
    (hdepressed : Q.coeff 2 = 0) (B : Germ 1) (hB : IsUnit B)
    (hlinear : Q.coeff 1 = coordinate (0 : Fin 1) * B)
    (hconstant : Q.coeff 0 ∈ maximalIdeal 1 ^ 2) :
    ∃ α β : ℂ, β ≠ 0 ∧ firstCoordinatePolynomialEvaluation Q -
      coordinate (1 : Fin 2) * (constRingHom 2 α * coordinate (1 : Fin 2) +
        constRingHom 2 β * coordinate (0 : Fin 2)) ∈ maximalIdeal 2 ^ 3 := by
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hconstant
  obtain ⟨D, hD⟩ := hconstant
  let α := valueRingHom 1 D
  let β := valueRingHom 1 B
  have hBtail : hyperplaneExtension 1 B - constRingHom 2 β ∈ maximalIdeal 2 := by
    simp only [mem_maximalIdeal_iff, map_sub, valueRingHom_hyperplaneExtension,
      valueRingHom_const, β, sub_self]
  have hDtail : hyperplaneExtension 1 D - constRingHom 2 α ∈ maximalIdeal 2 := by
    simp only [mem_maximalIdeal_iff, map_sub, valueRingHom_hyperplaneExtension,
      valueRingHom_const, α, sub_self]
  have hxy : coordinate (1 : Fin 2) * coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul (coordinate_mem_maximalIdeal 1)
      (coordinate_mem_maximalIdeal 0)
  have hBterm : coordinate (1 : Fin 2) * coordinate (0 : Fin 2) *
      (hyperplaneExtension 1 B - constRingHom 2 β) ∈ maximalIdeal 2 ^ 3 := by
    simpa only [pow_succ] using Ideal.mul_mem_mul hxy hBtail
  have hDterm : coordinate (1 : Fin 2) ^ 2 *
      (hyperplaneExtension 1 D - constRingHom 2 α) ∈ maximalIdeal 2 ^ 3 := by
    simpa only [pow_succ] using Ideal.mul_mem_mul
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) 2) hDtail
  refine ⟨α, β, valueRingHom_ne_zero_of_isUnit hB, ?_⟩
  have hsum := (maximalIdeal 2 ^ 3).add_mem
    ((maximalIdeal 2 ^ 3).add_mem (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 3) hBterm)
    hDterm
  convert hsum using 1
  rw [polynomialEvaluation_depressed_cubic Q hQ hdegree hdepressed, hlinear, hD,
    map_mul, map_mul, map_pow, hyperplaneExtension_coordinate_plane]
  ring

end OnLeConjecture.Analytic.Germ
