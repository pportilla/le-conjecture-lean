/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MonicWeierstrassInitialForm
public import OnLeConjecture.Analytic.RamifiedIntersection
public import OnLeConjecture.Analytic.FreeChainCoefficientOrder
public import OnLeConjecture.DFour.QuarticTransformMultiplicity
import Mathlib.Tactic

/-!
# Quartic transforms derived from the square Newton initial polynomial

The ramified weighted initial chart is assumed to be the actual square
`(X²+η)²`. Its coefficients determine the residues of analytically divided
Weierstrass coefficients. Exact coefficient orders and the subsequent
analytic chart expressions are derived from this initial-form identity.
No coverage statement about a resolution graph is asserted here.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- Scaling the ramified polynomial constructs coefficient quotients with
the residues prescribed by the actual square initial chart. -/
theorem exists_coefficients_of_quartic_square_initial
    (s r : ℕ) (hs : 0 < s) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (horder : ∀ i < 4,
      ((r * (4 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * 4))
    (htail : firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
      coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * 4 + 1))
    (η : ℂ) (hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ =
      (X ^ 2 + C η) ^ 2) :
    ∃ q₂ q₁ q₀ : Germ 1,
      (oneVariablePowerMapGerm s hs).pullbackRingHom (P.coeff 2) =
        coordinate (0 : Fin 1) ^ (2 * r) * q₂ ∧ valueRingHom 1 q₂ = 2 * η ∧
      (oneVariablePowerMapGerm s hs).pullbackRingHom (P.coeff 1) =
        coordinate (0 : Fin 1) ^ (3 * r) * q₁ ∧ valueRingHom 1 q₁ = 0 ∧
      (oneVariablePowerMapGerm s hs).pullbackRingHom (P.coeff 0) =
        coordinate (0 : Fin 1) ^ (4 * r) * q₀ ∧ valueRingHom 1 q₀ = η ^ 2 := by
  let B := P.map (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hB : B.Monic := hmonic.map _
  have hBm : B.natDegree = 4 := (hmonic.natDegree_map _).trans hdegree
  have hcoeff : ∀ i, B.coeff i ∈ maximalIdeal 1 ^ (r * (4 - i)) := by
    intro i
    by_cases hi : i < 4
    · exact coefficient_mem_maximalIdeal_pow_after_ramification s r 4 hs P horder i hi
    · simp [Nat.sub_eq_zero_of_le (by omega : 4 ≤ i)]
  obtain ⟨Q, _hQ, hQm, hscale, hfactor⟩ :=
    exists_monic_weighted_polynomial_scaling B 4 r hB hBm hcoeff
  have hresidue := weighted_initial_chart_eq_scaled_residue r 4 hr B Q hQm
    hscale P₀ hP₀ htail
  have heq : Q.map (valueRingHom 1) = (X ^ 2 + C η) ^ 2 := hresidue.symm.trans hchart
  have htwo := congrArg (fun T : ℂ[X] ↦ T.coeff 2) heq
  have hone := congrArg (fun T : ℂ[X] ↦ T.coeff 1) heq
  have hzero := congrArg (fun T : ℂ[X] ↦ T.coeff 0) heq
  have hexp : (X ^ 2 + C η) ^ 2 = X ^ 4 + C (2 * η) * X ^ 2 + C (η ^ 2) := by
    simp only [map_mul, map_ofNat, map_pow]
    ring
  rw [hexp] at htwo hone hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_map, Polynomial.coeff_C] at htwo hone hzero
  norm_num at htwo hone hzero
  refine ⟨Q.coeff 2, Q.coeff 1, Q.coeff 0, ?_, htwo, ?_, hone, ?_, hzero⟩
  · simpa only [B, Polynomial.coeff_map, Nat.reduceSub, Nat.mul_comm r 2] using hfactor 2
  · simpa only [B, Polynomial.coeff_map, Nat.reduceSub, Nat.mul_comm r 3] using hfactor 1
  · simpa only [B, Polynomial.coeff_map, Nat.sub_zero, Nat.mul_comm r 4] using hfactor 0

/-- A nonzero divided residue detects the exact order before ramification. -/
theorem ramified_order_eq_of_divided_value_ne_zero
    (s d : ℕ) (hs : 0 < s) (b q : Germ 1)
    (hfactor : (oneVariablePowerMapGerm s hs).pullbackRingHom b =
      coordinate (0 : Fin 1) ^ d * q) (hq : valueRingHom 1 q ≠ 0) :
    s • vanishingOrder b = (d : ℕ∞) := by
  rw [← vanishingOrder_oneVariablePowerMapGerm_pullback s hs]
  exact vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
    (isUnit_of_valueRingHom_ne_zero hq) hfactor

/-- A zero divided residue forces strict inequality, including when the
original coefficient is zero and its order is infinite. -/
theorem ramified_order_gt_of_divided_value_zero
    (s d : ℕ) (hs : 0 < s) (b q : Germ 1)
    (hfactor : (oneVariablePowerMapGerm s hs).pullbackRingHom b =
      coordinate (0 : Fin 1) ^ d * q) (hq : valueRingHom 1 q = 0) :
    (d : ℕ∞) < s • vanishingOrder b := by
  have hmem : (oneVariablePowerMapGerm s hs).pullbackRingHom b ∈
      maximalIdeal 1 ^ (d + 1) := by
    rw [hfactor, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) d)
      (mem_maximalIdeal_iff.mpr hq)
  have hbound := mem_maximalIdeal_one_pow_iff.mp hmem
  rw [vanishingOrder_oneVariablePowerMapGerm_pullback] at hbound
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d) hbound

/-- The square initial chart forces the two exact even-coefficient orders
and the strict odd-coefficient inequality. In particular `2*r/s` is an
integer, expressed without division by `∃ n, s*n=2*r`. -/
theorem quartic_square_initial_orders
    (s r : ℕ) (hs : 0 < s) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (horder : ∀ i < 4,
      ((r * (4 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * 4))
    (htail : firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
      coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * 4 + 1))
    (η : ℂ) (hη : η ≠ 0)
    (hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ = (X ^ 2 + C η) ^ 2) :
    s • vanishingOrder (P.coeff 2) = ((2 * r : ℕ) : ℕ∞) ∧
    s • vanishingOrder (P.coeff 0) = ((4 * r : ℕ) : ℕ∞) ∧
    ((3 * r : ℕ) : ℕ∞) < s • vanishingOrder (P.coeff 1) ∧
    ∃ n : ℕ, s * n = 2 * r := by
  obtain ⟨q₂, q₁, q₀, hf₂, hv₂, hf₁, hv₁, hf₀, hv₀⟩ :=
    exists_coefficients_of_quartic_square_initial s r hs hr P hmonic hdegree
      horder P₀ hP₀ htail η hchart
  have hq₂ : valueRingHom 1 q₂ ≠ 0 := by rw [hv₂]; exact mul_ne_zero (by norm_num) hη
  have hq₀ : valueRingHom 1 q₀ ≠ 0 := by rw [hv₀]; exact pow_ne_zero 2 hη
  have htwo := ramified_order_eq_of_divided_value_ne_zero s (2 * r) hs _ q₂ hf₂ hq₂
  refine ⟨htwo, ramified_order_eq_of_divided_value_ne_zero s (4 * r) hs _ q₀ hf₀ hq₀,
    ramified_order_gt_of_divided_value_zero s (3 * r) hs _ q₁ hf₁ hv₁, ?_⟩
  have hb : P.coeff 2 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hf₂
    exact (mul_ne_zero (pow_ne_zero _ coordinate_zero_ne_zero)
      (isUnit_of_valueRingHom_ne_zero hq₂).ne_zero) hf₂.symm
  have hfinite := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hb)
  refine ⟨(vanishingOrder (P.coeff 2)).toNat, ?_⟩
  rw [← hfinite, nsmul_eq_mul] at htwo
  exact_mod_cast htwo

/-- Recover an analytic coefficient expansion before ramification, with
its specified nonzero leading scalar. The original quotient is constructed
by analytic coordinate division and its value is recovered by cancellation. -/
theorem exists_coefficient_expansion_of_ramified_factor
    (s d : ℕ) (hs : 0 < s) (b q : Germ 1) (γ : ℂ) (hγ : γ ≠ 0)
    (hfactor : (oneVariablePowerMapGerm s hs).pullbackRingHom b =
      coordinate (0 : Fin 1) ^ (s * d) * q) (hq : valueRingHom 1 q = γ) :
    ∃ a : Germ 1, b = coordinate (0 : Fin 1) ^ d *
      (constRingHom 1 γ + coordinate (0 : Fin 1) * a) := by
  have hqne : valueRingHom 1 q ≠ 0 := by rwa [hq]
  have hord := ramified_order_eq_of_divided_value_ne_zero s (s * d) hs b q hfactor hqne
  have hb : b ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfactor
    exact (mul_ne_zero (pow_ne_zero _ coordinate_zero_ne_zero)
      (isUnit_of_valueRingHom_ne_zero hqne).ne_zero) hfactor.symm
  have hfinite := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hb)
  have hn : (vanishingOrder b).toNat = d := by
    rw [← hfinite, nsmul_eq_mul] at hord
    have heq : s * (vanishingOrder b).toNat = s * d := by exact_mod_cast hord
    nlinarith
  have hmem : b ∈ maximalIdeal 1 ^ d := by
    rw [mem_maximalIdeal_one_pow_iff, ← hfinite, hn]
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨u, hu⟩ := hmem
  have hpull := congrArg (oneVariablePowerMapGerm s hs).pullbackRingHom hu
  rw [map_mul, map_pow, oneVariablePowerMapGerm_pullback_coordinate, ← pow_mul] at hpull
  have huq : (oneVariablePowerMapGerm s hs).pullbackRingHom u = q :=
    mul_left_cancel₀ (pow_ne_zero _ coordinate_zero_ne_zero) (hpull.symm.trans hfactor)
  have huvalue : valueRingHom 1 u = γ := by
    rw [← PointedMapGerm.valueRingHom_pullback (oneVariablePowerMapGerm s hs) u, huq, hq]
  have hrem : u - constRingHom 1 γ ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, map_sub, valueRingHom_const, huvalue, sub_self]
  rw [maximalIdeal_one_eq_span_coordinate, Ideal.mem_span_singleton] at hrem
  obtain ⟨a, ha⟩ := hrem
  refine ⟨a, ?_⟩
  rw [hu]
  congr 1
  rw [← ha]
  ring

/-- A strict ramified order bound forces the next integral order before
ramification. Zero coefficients are included. -/
theorem mem_pow_succ_of_strict_ramified_order
    (s B : ℕ) (_hs : 0 < s) (b : Germ 1)
    (horder : ((s * B : ℕ) : ℕ∞) < s • vanishingOrder b) :
    b ∈ maximalIdeal 1 ^ (B + 1) := by
  by_cases hb : b = 0
  · simp [hb]
  have hfinite := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hb)
  rw [← hfinite, nsmul_eq_mul] at horder
  have hnat : s * B < s * (vanishingOrder b).toNat := by exact_mod_cast horder
  have hbound : B + 1 ≤ (vanishingOrder b).toNat := by nlinarith
  rw [mem_maximalIdeal_one_pow_iff, ← hfinite]
  exact_mod_cast hbound

/-- Polynomial evaluation of a depressed monic quartic has precisely its
three lower coefficient terms. -/
theorem polynomialEvaluation_depressed_quartic
    (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0) :
    firstCoordinatePolynomialEvaluation P = coordinate (0 : Fin 2) ^ 4 +
      hyperplaneExtension 1 (P.coeff 2) * coordinate (0 : Fin 2) ^ 2 +
      hyperplaneExtension 1 (P.coeff 1) * coordinate (0 : Fin 2) +
      hyperplaneExtension 1 (P.coeff 0) := by
  have htop : P.coeff 4 = 1 := by rw [← hdegree, Polynomial.coeff_natDegree, hmonic]
  rw [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_eq_sum_range, hdegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    htop, hdepressed, map_one, map_zero, zero_mul, zero_add, add_zero, pow_zero, pow_one,
    mul_one, one_mul]
  ring

/-- A translated exceptional chart still fixes every analytic coefficient
depending only on the second coordinate. -/
theorem pointBlowupChart_pullback_hyperplaneExtension (ζ : ℂ) (f : Germ 1) :
    (pointBlowupChartGerm ζ).pullbackRingHom (hyperplaneExtension 1 f) =
      hyperplaneExtension 1 f := by
  obtain ⟨F, hF, rfl⟩ := Germ.exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF) (hyperplaneTailGerm 1))
    (pointBlowupChartGerm ζ) = compPointed (ofFunction F hF) (hyperplaneTailGerm 1)
  simp only [pointBlowupChartGerm, hyperplaneTailGerm, compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change F (hyperplaneTail 1 (pointBlowupChart ζ z)) = F (hyperplaneTail 1 z)
  congr 1
  ext i
  fin_cases i
  rfl

/-- After `A-1` zero charts, use the exceptional chart centered at `ζ`.
For positive `A`, its coordinate expression is `(y^A*(x+ζ),y)`. -/
@[expose] noncomputable def centeredFreeChainChart (A : ℕ) (ζ : ℂ) : PointedMapGerm 2 2 :=
  (freeChainChartGerm (A - 1)).comp (pointBlowupChartGerm ζ)

theorem centeredFreeChainChart_pullback_zero (A : ℕ) (hA : 0 < A) (ζ : ℂ) :
    (centeredFreeChainChart A ζ).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) ^ A * (coordinate (0 : Fin 2) + constRingHom 2 ζ) := by
  rw [centeredFreeChainChart, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    freeChainChartGerm_pullback_zero, map_mul, map_pow, pointBlowupChartGerm_pullback_one,
    pointBlowupChartGerm_pullback_zero, ← mul_assoc, ← pow_succ,
    Nat.sub_add_cancel hA]

theorem centeredFreeChainChart_pullback_hyperplaneExtension
    (A : ℕ) (ζ : ℂ) (f : Germ 1) :
    (centeredFreeChainChart A ζ).pullbackRingHom (hyperplaneExtension 1 f) =
      hyperplaneExtension 1 f := by
  rw [centeredFreeChainChart, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    freeChainChartGerm_pullback_hyperplaneExtension,
    pointBlowupChart_pullback_hyperplaneExtension]

private theorem hyperplaneExtension_const (γ : ℂ) :
    hyperplaneExtension 1 (constRingHom 1 γ) = constRingHom 2 γ :=
  PointedMapGerm.pullback_constRingHom (hyperplaneTailGerm 1) γ

/-- The original coefficient expansions give the actual analytic integral
quartic transform at every exceptional coordinate `ζ`. -/
theorem integral_quartic_transform_of_coefficient_expansions
    (A : ℕ) (hA : 0 < A) (P : Polynomial (Germ 1))
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (η ζ : ℂ) (a₂ a₁ a₀ : Germ 1)
    (hc₂ : P.coeff 2 = coordinate (0 : Fin 1) ^ (2 * A) *
      (constRingHom 1 (2 * η) + coordinate (0 : Fin 1) * a₂))
    (hc₁ : P.coeff 1 = coordinate (0 : Fin 1) ^ (3 * A + 1) * a₁)
    (hc₀ : P.coeff 0 = coordinate (0 : Fin 1) ^ (4 * A) *
      (constRingHom 1 (η ^ 2) + coordinate (0 : Fin 1) * a₀)) :
    (centeredFreeChainChart A ζ).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      coordinate (1 : Fin 2) ^ (4 * A) * integralQuarticTransform η ζ
        (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) := by
  rw [polynomialEvaluation_depressed_quartic P hmonic hdegree hdepressed]
  simp only [map_add, map_mul, map_pow, centeredFreeChainChart_pullback_zero A hA,
    centeredFreeChainChart_pullback_hyperplaneExtension]
  rw [hc₂, hc₁, hc₀]
  simp only [map_add, map_mul, map_pow, hyperplaneExtension_coordinate_plane,
    hyperplaneExtension_const, map_ofNat, integralQuarticTransform]
  exact integral_quartic_chart_identity A (coordinate 0 + constRingHom 2 ζ)
    (coordinate 1) (constRingHom 2 η)
    (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀)

/-- The half-integral coefficient expansions give the actual analytic
quartic transform after `A` zero-center charts. -/
theorem half_integral_quartic_transform_of_coefficient_expansions
    (A : ℕ) (P : Polynomial (Germ 1))
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (η : ℂ) (a₂ a₁ a₀ : Germ 1)
    (hc₂ : P.coeff 2 = coordinate (0 : Fin 1) ^ (2 * A + 1) *
      (constRingHom 1 (2 * η) + coordinate (0 : Fin 1) * a₂))
    (hc₁ : P.coeff 1 = coordinate (0 : Fin 1) ^ (3 * A + 2) * a₁)
    (hc₀ : P.coeff 0 = coordinate (0 : Fin 1) ^ (4 * A + 2) *
      (constRingHom 1 (η ^ 2) + coordinate (0 : Fin 1) * a₀)) :
    (freeChainChartGerm A).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      coordinate (1 : Fin 2) ^ (4 * A) * halfIntegralQuarticTransform η
        (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) := by
  rw [polynomialEvaluation_depressed_quartic P hmonic hdegree hdepressed]
  simp only [map_add, map_mul, map_pow, freeChainChartGerm_pullback_zero,
    freeChainChartGerm_pullback_hyperplaneExtension]
  rw [hc₂, hc₁, hc₀]
  simp only [map_add, map_mul, map_pow, hyperplaneExtension_coordinate_plane,
    hyperplaneExtension_const, map_ofNat, halfIntegralQuarticTransform]
  exact half_integral_quartic_chart_identity A (coordinate 0)
    (coordinate 1) (constRingHom 2 η)
    (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀)

/-- The integral Newton case constructs the actual quartic transform at
each root of its exceptional polynomial, with multiplicity at most two.
The coefficient expansions are derived from the ramified initial form. -/
theorem exists_integral_quartic_transform_of_square_initial
    (s r A : ℕ) (hs : 0 < s) (hr : 0 < r) (hα : r = s * A)
    (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0)
    (horder : ∀ i < 4,
      ((r * (4 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * 4))
    (htail : firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
      coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * 4 + 1))
    (η ζ : ℂ) (hη : η ≠ 0) (hroot : ζ ^ 2 + η = 0)
    (hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ = (X ^ 2 + C η) ^ 2) :
    ∃ a₂ a₁ a₀ : Germ 1,
      (centeredFreeChainChart A ζ).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
        coordinate (1 : Fin 2) ^ (4 * A) * integralQuarticTransform η ζ
          (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) ∧
      integralQuarticTransform η ζ (hyperplaneExtension 1 a₂)
        (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) ∉ maximalIdeal 2 ^ 3 := by
  obtain ⟨q₂, q₁, q₀, hf₂, hv₂, hf₁, hv₁, hf₀, hv₀⟩ :=
    exists_coefficients_of_quartic_square_initial s r hs hr P hmonic hdegree
      horder P₀ hP₀ htail η hchart
  have he₂ : s * (2 * A) = 2 * r := by rw [hα]; ring
  have he₀ : s * (4 * A) = 4 * r := by rw [hα]; ring
  obtain ⟨a₂, ha₂⟩ := exists_coefficient_expansion_of_ramified_factor s (2 * A) hs
    (P.coeff 2) q₂ (2 * η) (mul_ne_zero (by norm_num) hη) (by simpa only [he₂] using hf₂) hv₂
  obtain ⟨a₀, ha₀⟩ := exists_coefficient_expansion_of_ramified_factor s (4 * A) hs
    (P.coeff 0) q₀ (η ^ 2) (pow_ne_zero 2 hη) (by simpa only [he₀] using hf₀) hv₀
  have hstrict := ramified_order_gt_of_divided_value_zero s (3 * r) hs (P.coeff 1) q₁ hf₁ hv₁
  have he₁ : s * (3 * A) = 3 * r := by rw [hα]; ring
  have hmem := mem_pow_succ_of_strict_ramified_order s (3 * A) hs (P.coeff 1)
    (by simpa only [he₁] using hstrict)
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨a₁, ha₁⟩ := hmem
  have hA : 0 < A := by nlinarith
  refine ⟨a₂, a₁, a₀,
    integral_quartic_transform_of_coefficient_expansions A hA P hmonic hdegree
      hdepressed η ζ a₂ a₁ a₀ ha₂ ha₁ ha₀, ?_⟩
  exact (integralQuarticTransform_at_root η ζ hη hroot _ _ _).2

/-- The half-integral Newton case constructs the actual quartic transform
after `A` zero-center charts. Its nonzero quadratic parameter coefficient
gives multiplicity exactly two. -/
theorem exists_half_integral_quartic_transform_of_square_initial
    (s r A : ℕ) (hs : 0 < s) (hr : 0 < r) (hα : 2 * r = s * (2 * A + 1))
    (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0)
    (horder : ∀ i < 4,
      ((r * (4 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * 4))
    (htail : firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
      coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * 4 + 1))
    (η : ℂ) (hη : η ≠ 0)
    (hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ = (X ^ 2 + C η) ^ 2) :
    ∃ a₂ a₁ a₀ : Germ 1,
      (freeChainChartGerm A).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
        coordinate (1 : Fin 2) ^ (4 * A) * halfIntegralQuarticTransform η
          (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) ∧
      halfIntegralQuarticTransform η (hyperplaneExtension 1 a₂)
        (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) ∈ maximalIdeal 2 ^ 2 ∧
      halfIntegralQuarticTransform η (hyperplaneExtension 1 a₂)
        (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) ∉ maximalIdeal 2 ^ 3 := by
  obtain ⟨q₂, q₁, q₀, hf₂, hv₂, hf₁, hv₁, hf₀, hv₀⟩ :=
    exists_coefficients_of_quartic_square_initial s r hs hr P hmonic hdegree
      horder P₀ hP₀ htail η hchart
  have he₀ : s * (4 * A + 2) = 4 * r := by nlinarith [hα]
  obtain ⟨a₂, ha₂⟩ := exists_coefficient_expansion_of_ramified_factor s (2 * A + 1) hs
    (P.coeff 2) q₂ (2 * η) (mul_ne_zero (by norm_num) hη)
      (by simpa only [← hα] using hf₂) hv₂
  obtain ⟨a₀, ha₀⟩ := exists_coefficient_expansion_of_ramified_factor s (4 * A + 2) hs
    (P.coeff 0) q₀ (η ^ 2) (pow_ne_zero 2 hη) (by simpa only [he₀] using hf₀) hv₀
  have hstrict := ramified_order_gt_of_divided_value_zero s (3 * r) hs (P.coeff 1) q₁ hf₁ hv₁
  have he₁ : s * (3 * A + 1) < 3 * r := by nlinarith [hα]
  have hmem := mem_pow_succ_of_strict_ramified_order s (3 * A + 1) hs (P.coeff 1)
    (lt_trans (by exact_mod_cast he₁) hstrict)
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨a₁, ha₁⟩ := hmem
  refine ⟨a₂, a₁, a₀,
    half_integral_quartic_transform_of_coefficient_expansions A P hmonic hdegree
      hdepressed η a₂ a₁ a₀ ha₂ (by simpa only [Nat.add_assoc] using ha₁) ha₀,
    halfIntegralQuarticTransform_mem_square η _ _ _,
    halfIntegralQuarticTransform_not_mem_cube η hη _ _ _⟩

/-- The integral value of twice the Newton slope leaves only the integral
and half-integral cases used by the two transform constructions. -/
theorem integral_or_half_integral_of_double_weight_integral
    (s r : ℕ) (h : ∃ n : ℕ, s * n = 2 * r) :
    ∃ A : ℕ, r = s * A ∨ 2 * r = s * (2 * A + 1) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n / 2, ?_⟩
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have heq : n = 2 * (n / 2) := by omega
    rw [heq] at hn
    left
    nlinarith
  · have heq : n = 2 * (n / 2) + 1 := by omega
    rw [heq] at hn
    exact Or.inr hn.symm

/-- The multiplicity bound transfers from a polynomial transform to the
transform of an analytic unit multiple. Both factorizations are actual
germ identities, and cancellation identifies the latter quotient. -/
theorem unit_multiple_transform_not_mem_cube
    (B : PointedMapGerm 2 2) (D : ℕ) (f u T g : Germ 2) (hu : IsUnit u)
    (hpolynomial : B.pullbackRingHom f = coordinate (1 : Fin 2) ^ D * T)
    (hactual : B.pullbackRingHom (f * u) = coordinate (1 : Fin 2) ^ D * g)
    (hT : T ∉ maximalIdeal 2 ^ 3) : g ∉ maximalIdeal 2 ^ 3 := by
  have heq : g = T * B.pullbackRingHom u := by
    apply mul_left_cancel₀ (pow_ne_zero D (coordinate_ne_zero (1 : Fin 2)))
    rw [← hactual, map_mul, hpolynomial, mul_assoc]
  obtain ⟨v, hv⟩ := (hu.map B.pullbackRingHom).exists_right_inv
  intro hg
  have hmul := Ideal.mul_mem_right v (maximalIdeal 2 ^ 3) hg
  rw [heq, mul_assoc, hv, mul_one] at hmul
  exact hT hmul

end OnLeConjecture.DFour
