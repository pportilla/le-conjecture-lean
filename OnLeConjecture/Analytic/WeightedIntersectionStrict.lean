/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionBound
public import OnLeConjecture.Analytic.WeightedOrderCancellation

/-!
# Strict weighted intersection bounds from analytic initial forms

At a common root of the weighted initial forms, restriction to the
corresponding weighted analytic line raises the order of both germs.
Weighted order cancellation controls the analytic division quotient and
transfers this root to the residual scaled polynomials.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Weighted coefficient orders imply weighted order of the evaluated
analytic polynomial. -/
theorem firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal
    (r L : ℕ) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hcoeff : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (L - r * i)) :
    firstCoordinatePolynomialEvaluation P ∈ weightedOrderIdeal r L := by
  classical
  rw [← P.sum_monomial_eq, Polynomial.sum_def, firstCoordinatePolynomialEvaluation,
    Polynomial.eval₂_finsetSum]
  apply Ideal.sum_mem
  intro i hi
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton.mp
    (show P.coeff i ∈ Ideal.span {coordinate (0 : Fin 1) ^ (L - r * i)} by
      rw [← maximalIdeal_one_pow_eq_span_coordinate_pow]
      exact hcoeff i))
  rw [Polynomial.eval₂_monomial, hc, map_mul, map_pow,
    hyperplaneExtension_coordinate_plane]
  have hmon := monomial_mem_weightedOrderIdeal_of_threshold r L i (L - r * i) hr
    (by omega)
  convert (weightedOrderIdeal r L).mul_mem_left (hyperplaneExtension 1 c) hmon using 1
  ring

/-- A weighted line with second coordinate `t` leaves analytic coefficient
germs unchanged. -/
theorem weightedLineMapGerm_pullback_hyperplaneExtension
    (r : ℕ) (hr : 0 < r) (z : ℂ) (f : Germ 1) :
    (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (hyperplaneExtension 1 f) = f := by
  rcases f with ⟨f, hf⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro t
    change f (hyperplaneTail 1 (weightedLineMap r ![z, 1] t)) = f t
    congr 1
    ext i
    fin_cases i
    simp [hyperplaneTail, weightedLineMap]

/-- Evaluating an analytic polynomial along a weighted line substitutes
`t^r z` in its polynomial variable. -/
theorem weightedLineMapGerm_pullback_polynomial
    (r : ℕ) (hr : 0 < r) (z : ℂ) (P : Polynomial (Germ 1)) :
    (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
        (firstCoordinatePolynomialEvaluation P) =
      P.eval (coordinate (0 : Fin 1) ^ r * constRingHom 1 z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_add,
      map_add, Polynomial.eval_add] at hP hQ ⊢
    rw [hP, hQ]
  | monomial n c =>
    simp only [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_monomial,
      map_mul, map_pow, weightedLineMapGerm_pullback_hyperplaneExtension,
      weightedLineMapGerm_pullback_coordinate, Polynomial.eval_monomial,
      Matrix.cons_val_zero]

/-- A specified weighted polynomial scaling becomes an exact coordinate
power times the evaluated scaled polynomial on a weighted line. -/
theorem weightedLineMapGerm_pullback_scaled_polynomial
    (r L : ℕ) (hr : 0 < r) (z : ℂ) (P Q : Polynomial (Germ 1))
    (hL : r * Q.natDegree ≤ L)
    (hscale : P = C (coordinate (0 : Fin 1) ^ (L - r * Q.natDegree)) *
      Q.scaleRoots (coordinate (0 : Fin 1) ^ r)) :
    (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
        (firstCoordinatePolynomialEvaluation P) =
      coordinate (0 : Fin 1) ^ L * Q.eval (constRingHom 1 z) := by
  rw [weightedLineMapGerm_pullback_polynomial, hscale, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.scaleRoots_eval_mul, ← pow_mul,
    ← mul_assoc, ← pow_add, Nat.sub_add_cancel hL]

/-- Vanishing of a specified initial form at a weighted direction raises
the order of restriction to that direction. -/
theorem weightedLineMapGerm_pullback_mem_succ_of_initial_root
    (r D : ℕ) (hr : 0 < r) (z : ℂ) (f : Germ 2)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F.IsWeightedHomogeneous ![r, 1] D)
    (hf : f - coordinatePolynomialAlgHom 2 F ∈ weightedOrderIdeal r (D + 1))
    (hroot : MvPolynomial.eval ![z, 1] F = 0) :
    (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom f ∈ maximalIdeal 1 ^ (D + 1) := by
  have htail := weightedLineMapGerm_pullback_mem_maximalIdeal_pow r (D + 1) hr ![z, 1] hf
  simpa [map_sub, weightedLineMapGerm_pullback_coordinatePolynomial r D hr _ hF,
    hroot] using htail

/-- The scalar residue of a scaled polynomial vanishes if its weighted
line evaluation has order greater than the extracted coordinate power. -/
theorem scaled_polynomial_residue_isRoot_of_line_order
    (D : ℕ) (z : ℂ) (Q : Polynomial (Germ 1))
    (horder : coordinate (0 : Fin 1) ^ D * Q.eval (constRingHom 1 z) ∈
      maximalIdeal 1 ^ (D + 1)) :
    (Q.map (valueRingHom 1)).IsRoot z := by
  have hvalue := value_divided_coefficient_eq_of_initial_congruence
    (coordinate (0 : Fin 1) ^ D * Q.eval (constRingHom 1 z))
    (Q.eval (constRingHom 1 z)) D 0 rfl (by simpa using horder)
  change (Q.map (valueRingHom 1)).eval z = 0
  simpa using (Polynomial.eval_map_apply (p := Q) (valueRingHom 1)
    (constRingHom 1 z)).trans hvalue

/-- A shared root of the original weighted initial forms is a shared root
of the residual polynomials of any actual weighted Weierstrass scaling. -/
theorem WeightedWeierstrassScaling.residual_common_root_of_initial_common_root
    {P : Polynomial (Germ 1)} {H : Germ 2} {r L m : ℕ}
    (data : WeightedWeierstrassScaling P H r L m)
    (hr : 0 < r) (hL : r * m ≤ L)
    (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (z : ℂ) (hProot : MvPolynomial.eval ![z, 1] P₀ = 0)
    (hHroot : MvPolynomial.eval ![z, 1] H₀ = 0) :
    (data.firstScaled.map (valueRingHom 1)).IsRoot z ∧
      (data.secondScaled.map (valueRingHom 1)).IsRoot z := by
  have hH : H ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hHtail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hH₀)
    simpa only [sub_add_cancel] using hsum
  have hR : firstCoordinatePolynomialEvaluation data.remainder ∈ weightedOrderIdeal r L := by
    apply firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal r L hr
    intro i
    rw [data.second_coeff]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 1)) (L - r * i))
  have hproduct : firstCoordinatePolynomialEvaluation P * data.quotient ∈
      weightedOrderIdeal r (r * m + (L - r * m)) := by
    rw [Nat.add_sub_of_le hL]
    have hdifference := (weightedOrderIdeal r L).sub_mem hH hR
    simpa only [data.division, add_sub_cancel_right] using hdifference
  have hq := mem_weightedOrderIdeal_of_mul_mem r (r * m) (L - r * m) hr
    P₀ hP₀ hP₀ne (firstCoordinatePolynomialEvaluation P) data.quotient hPtail hproduct
  have hPline := weightedLineMapGerm_pullback_mem_succ_of_initial_root
    r (r * m) hr z (firstCoordinatePolynomialEvaluation P) P₀ hP₀ hPtail hProot
  have hHline := weightedLineMapGerm_pullback_mem_succ_of_initial_root
    r L hr z H H₀ hH₀ hHtail hHroot
  have hqline := weightedLineMapGerm_pullback_mem_maximalIdeal_pow
    r (L - r * m) hr ![z, 1] hq
  have hproductLine := Ideal.mul_mem_mul hPline hqline
  have hsum : r * m + 1 + (L - r * m) = L + 1 := by omega
  rw [← pow_add, hsum] at hproductLine
  have hRline : (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (firstCoordinatePolynomialEvaluation data.remainder) ∈ maximalIdeal 1 ^ (L + 1) := by
    have hsub := (maximalIdeal 1 ^ (L + 1)).sub_mem hHline hproductLine
    simpa only [data.division, map_add, map_mul, add_sub_cancel_left] using hsub
  constructor
  · apply scaled_polynomial_residue_isRoot_of_line_order (r * m) z
    rw [weightedLineMapGerm_pullback_polynomial, data.first_scaling,
      Polynomial.scaleRoots_eval_mul, ← pow_mul, data.first_degree] at hPline
    exact hPline
  · apply scaled_polynomial_residue_isRoot_of_line_order L z
    rwa [weightedLineMapGerm_pullback_scaled_polynomial
      r L hr z data.remainder data.secondScaled data.second_weight data.second_scaling] at hRline

/-- A common complex root in the chart `y = 1` of the original analytic
weighted initial forms forces strictness of the weighted intersection bound.
The division remainder and its scaled residual polynomials are constructed,
not assumed. -/
theorem weighted_intersection_strict_lower_bound_of_initial_common_root
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m) (hL : r * m ≤ L)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H)
    (z : ℂ) (hProot : MvPolynomial.eval ![z, 1] P₀ = 0)
    (hHroot : MvPolynomial.eval ![z, 1] H₀ = 0) :
    m * L < PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite := by
  have hH : H ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hHtail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hH₀)
    simpa only [sub_add_cancel] using hsum
  obtain ⟨data⟩ := exists_weightedWeierstrassScaling r L m hr hm hL P hP hPm hcoeff H hH
  obtain ⟨hfirstRoot, hsecondRoot⟩ := data.residual_common_root_of_initial_common_root
    hr hL P₀ H₀ hP₀ hP₀ne hH₀ hPtail hHtail z hProot hHroot
  exact data.strict_intersection_lower_bound hr hm hcoeff hfinite z hfirstRoot hsecondRoot

end OnLeConjecture.Analytic.Germ
