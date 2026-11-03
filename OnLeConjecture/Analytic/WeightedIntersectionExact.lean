/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MonicWeierstrassInitialForm
public import OnLeConjecture.Analytic.UnitIntersection

/-!
# Exact weighted intersection from coprime initial charts

When the original weighted initial charts have no common root, the
residual scaled Weierstrass polynomials also have no common root. Their
resultant is an analytic unit. Exact resultant scaling then determines the
intersection number and proves finiteness of the original analytic pair.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A specified initial form vanishes in a direction whenever restriction
to its weighted line has order greater than the initial degree. -/
theorem initial_root_of_weighted_line_order_succ
    (r D : ℕ) (hr : 0 < r) (z : ℂ) (f : Germ 2)
    (F : MvPolynomial (Fin 2) ℂ) (hF : F.IsWeightedHomogeneous ![r, 1] D)
    (htail : f - coordinatePolynomialAlgHom 2 F ∈ weightedOrderIdeal r (D + 1))
    (hline : (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom f ∈
      maximalIdeal 1 ^ (D + 1)) :
    MvPolynomial.eval ![z, 1] F = 0 := by
  have htailLine := weightedLineMapGerm_pullback_mem_maximalIdeal_pow r (D + 1) hr ![z, 1] htail
  have hpolyLine : (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (coordinatePolynomialAlgHom 2 F) ∈ maximalIdeal 1 ^ (D + 1) := by
    have hsub := (maximalIdeal 1 ^ (D + 1)).sub_mem hline htailLine
    simpa only [map_sub, sub_sub_cancel] using hsub
  rw [weightedLineMapGerm_pullback_coordinatePolynomial r D hr _ hF] at hpolyLine
  have hvalue := value_divided_coefficient_eq_of_initial_congruence
    (coordinate (0 : Fin 1) ^ D * constRingHom 1 (MvPolynomial.eval ![z, 1] F))
    (constRingHom 1 (MvPolynomial.eval ![z, 1] F)) D 0 rfl (by simpa using hpolyLine)
  simpa only [valueRingHom_const] using hvalue

/-- The actual analytic division quotient has the expected weighted
order when the first initial form is nonzero. -/
theorem WeightedWeierstrassScaling.quotient_mem_weightedOrderIdeal
    {P : Polynomial (Germ 1)} {H : Germ 2} {r L m : ℕ}
    (data : WeightedWeierstrassScaling P H r L m) (hr : 0 < r) (hL : r * m ≤ L)
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hH : H ∈ weightedOrderIdeal r L) :
    data.quotient ∈ weightedOrderIdeal r (L - r * m) := by
  have hR : firstCoordinatePolynomialEvaluation data.remainder ∈ weightedOrderIdeal r L := by
    apply firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal r L hr
    intro j
    rw [data.second_coeff]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 1)) (L - r * j))
  have hproduct : firstCoordinatePolynomialEvaluation P * data.quotient ∈
      weightedOrderIdeal r (r * m + (L - r * m)) := by
    rw [Nat.add_sub_of_le hL]
    have hsub := (weightedOrderIdeal r L).sub_mem hH hR
    simpa only [data.division, add_sub_cancel_right] using hsub
  exact mem_weightedOrderIdeal_of_mul_mem r (r * m) (L - r * m) hr P₀ hP₀ hP₀ne
    (firstCoordinatePolynomialEvaluation P) data.quotient hPtail hproduct

/-- A common root of the residual scaled polynomials is a common root
of the original analytic weighted initial forms. -/
theorem WeightedWeierstrassScaling.initial_common_root_of_residual_common_root
    {P : Polynomial (Germ 1)} {H : Germ 2} {r L m : ℕ}
    (data : WeightedWeierstrassScaling P H r L m) (hr : 0 < r) (hL : r * m ≤ L)
    (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (z : ℂ) (hAroot : (data.firstScaled.map (valueRingHom 1)).IsRoot z)
    (hBroot : (data.secondScaled.map (valueRingHom 1)).IsRoot z) :
    MvPolynomial.eval ![z, 1] P₀ = 0 ∧ MvPolynomial.eval ![z, 1] H₀ = 0 := by
  have hchart := weighted_initial_chart_eq_scaled_residue r m hr P data.firstScaled
    data.first_degree data.first_scaling P₀ hP₀ hPtail
  have hProot : MvPolynomial.eval ![z, 1] P₀ = 0 := by
    rw [← OnLeConjecture.Polynomial.eval_weighted_chart P₀ z, hchart]
    exact hAroot
  refine ⟨hProot, ?_⟩
  have hH : H ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hHtail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hH₀)
    simpa only [sub_add_cancel] using hsum
  have hq := data.quotient_mem_weightedOrderIdeal hr hL P₀ hP₀ hP₀ne hPtail hH
  have hPline := weightedLineMapGerm_pullback_mem_succ_of_initial_root
    r (r * m) hr z (firstCoordinatePolynomialEvaluation P) P₀ hP₀ hPtail hProot
  have hqline := weightedLineMapGerm_pullback_mem_maximalIdeal_pow
    r (L - r * m) hr ![z, 1] hq
  have hproductLine := Ideal.mul_mem_mul hPline hqline
  rw [← pow_add, show r * m + 1 + (L - r * m) = L + 1 by omega] at hproductLine
  have hBvalue : valueRingHom 1 (data.secondScaled.eval (constRingHom 1 z)) = 0 := by
    have heval := Polynomial.eval_map_apply (p := data.secondScaled)
      (valueRingHom 1) (constRingHom 1 z)
    simpa only [valueRingHom_const] using heval.symm.trans hBroot
  have hRline : (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (firstCoordinatePolynomialEvaluation data.remainder) ∈ maximalIdeal 1 ^ (L + 1) := by
    rw [weightedLineMapGerm_pullback_scaled_polynomial
      r L hr z data.remainder data.secondScaled data.second_weight data.second_scaling, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) L)
      (mem_maximalIdeal_iff.mpr hBvalue)
  apply initial_root_of_weighted_line_order_succ r L hr z H H₀ hH₀ hHtail
  rw [data.division, map_add, map_mul]
  exact (maximalIdeal 1 ^ (L + 1)).add_mem hproductLine hRline

/-- For a monic first polynomial, absence of a common root of the
residual polynomials makes the analytic resultant a unit, even when
specialization lowers the second polynomial's degree. -/
theorem resultant_isUnit_of_residual_no_common_root
    (A B : Polynomial (Germ 1)) (hA : A.Monic)
    (hno : ∀ z : ℂ, ¬ ((A.map (valueRingHom 1)).IsRoot z ∧
      (B.map (valueRingHom 1)).IsRoot z)) :
    IsUnit (A.resultant B) := by
  let A₀ := A.map (valueRingHom 1)
  let B₀ := B.map (valueRingHom 1)
  have hA₀ : A₀.Monic := hA.map (valueRingHom 1)
  have hcoprime : IsCoprime A₀ B₀ := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ A₀ B₀).mpr
    intro z
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
      Polynomial.IsRoot.def, A₀, B₀] using
      not_and_or.mp (hno z)
  have hdegreeA : A₀.natDegree = A.natDegree := hA.natDegree_map (valueRingHom 1)
  have hdegreeB : B₀.natDegree ≤ B.natDegree := Polynomial.natDegree_map_le
  have hfixed : A₀.resultant B₀ A₀.natDegree B.natDegree = A₀.resultant B₀ := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hdegreeB
    conv_lhs => rw [hk]
    rw [Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl,
      hA₀.coeff_natDegree, one_pow, one_mul]
  have hmap : valueRingHom 1 (A.resultant B) = A₀.resultant B₀ := by
    rw [← Polynomial.resultant_map_map, ← hdegreeA]
    exact hfixed
  apply isUnit_of_valueRingHom_ne_zero
  rw [hmap]
  exact Polynomial.resultant_ne_zero A₀ B₀ hcoprime

/-- Coprime original initial charts give finite intersection and the
exact weighted intersection number. This version permits the direct
coefficient scaling of the analytic division remainder. -/
theorem weighted_intersection_eq_of_no_common_initial_root
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m) (hL : r * m ≤ L)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (r * (m - j)))
    (H : Germ 2) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] H₀ = 0)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H,
      PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) H hfinite =
        m * L := by
  have hH : H ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hHtail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hH₀)
    simpa only [sub_add_cancel] using hsum
  obtain ⟨data⟩ := exists_weightedWeierstrassScaling r L m hr hm hL P hP hPm hcoeff H hH
  have hunit : IsUnit (data.firstScaled.resultant data.secondScaled) := by
    apply resultant_isUnit_of_residual_no_common_root _ _ data.first_monic
    intro z hz
    exact hno z (data.initial_common_root_of_residual_common_root
      hr hL P₀ H₀ hP₀ hP₀ne hH₀ hPtail hHtail z hz.1 hz.2)
  have hscale := PolynomialResultant.resultant_weighted_scaleRoots
    data.firstScaled data.secondScaled (coordinate (0 : Fin 1)) coordinate_zero_ne_zero
    r L data.second_weight
  rw [← data.first_scaling, ← data.second_scaling] at hscale
  have hresNe : P.resultant data.remainder ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (pow_ne_zero _ coordinate_zero_ne_zero) hunit.ne_zero
  have hdist := coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff
  have hfiniteR := hasFiniteIntersection_of_resultant_ne_zero (m - 1) P data.remainder
    hP (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hPm)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hdist) hresNe
  have hideal := PlaneCurve.pairIdeal_eq_of_remainder (firstCoordinatePolynomialEvaluation P) H
    (firstCoordinatePolynomialEvaluation data.remainder) data.quotient data.division
  have hfinite := hfiniteR.of_pairIdeal_eq hideal.symm
  refine ⟨hfinite, ?_⟩
  have hcast := data.intersectionMultiplicity_cast_eq hr hm hcoeff hfinite
  rw [vanishingOrder_eq_zero_iff_isUnit.mpr hunit, add_zero] at hcast
  exact_mod_cast hcast

private theorem finite_intersection_of_second_mul
    (f H c : Germ 2) (hfinite : PlaneCurve.HasFiniteIntersection f (c * H)) :
    PlaneCurve.HasFiniteIntersection f H := by
  obtain ⟨N, hN⟩ := (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f (c * H)).mp
    hfinite
  apply (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f H).mpr
  refine ⟨N, hN.trans ?_⟩
  rw [PlaneCurve.pairIdeal_eq_span, Ideal.span_le]
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact Ideal.subset_span (by simp)
  · rw [Set.mem_singleton_iff] at hv
    subst v
    exact Ideal.mul_mem_left _ c (Ideal.subset_span (by simp))

/-- The exact weighted intersection formula at every second degree,
with finiteness deduced from the original initial charts. -/
theorem weighted_intersection_eq_any_order_of_no_common_initial_root
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (r * (m - j)))
    (H : Germ 2) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] H₀ = 0)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H,
      PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) H hfinite =
        m * L := by
  let K := r * m
  have hY : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![r, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![r, 1] 1
  have hYK : (MvPolynomial.X (1 : Fin 2) ^ K : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![r, 1] K := by simpa using hY.pow K
  have hcoordinate : coordinate (1 : Fin 2) ^ K ∈ weightedOrderIdeal r K := by
    simpa only [map_pow, coordinatePolynomialAlgHom_X] using
      coordinatePolynomial_mem_weightedOrderIdeal r K hr hYK
  have htail : coordinate (1 : Fin 2) ^ K * H -
      coordinatePolynomialAlgHom 2 (MvPolynomial.X (1 : Fin 2) ^ K * H₀) ∈
      weightedOrderIdeal r (K + L + 1) := by
    have hproduct := weightedOrderIdeal_mul_mem r K (L + 1) hr hcoordinate hHtail
    simpa only [map_mul, map_pow, coordinatePolynomialAlgHom_X, mul_sub,
      Nat.add_assoc] using hproduct
  have hno' : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] (MvPolynomial.X (1 : Fin 2) ^ K * H₀) = 0) := by
    simpa using hno
  obtain ⟨hfiniteK, hinterK⟩ := weighted_intersection_eq_of_no_common_initial_root
    r (K + L) m hr hm (by dsimp only [K]; omega) P hP hPm hcoeff
      (coordinate (1 : Fin 2) ^ K * H) P₀ (MvPolynomial.X (1 : Fin 2) ^ K * H₀)
      hP₀ hP₀ne (hYK.mul hH₀) hPtail htail hno'
  have hfinite := finite_intersection_of_second_mul (firstCoordinatePolynomialEvaluation P) H
    (coordinate (1 : Fin 2) ^ K) hfiniteK
  obtain ⟨hfiniteK', hinterMul⟩ := exists_finite_intersection_second_power_mul_eq m K hm P hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff) H hfinite
  refine ⟨hfinite, ?_⟩
  rw [hinterK, Nat.mul_add] at hinterMul
  omega

/-- The exact intersection formula retains an arbitrary preparation
unit and uses initial forms of the actual first germ. Finiteness follows
from the absence of a common initial root. -/
theorem weighted_intersection_unit_eq_any_order_of_no_common_initial_root
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (r * (m - j)))
    (U H : Germ 2) (hU : IsUnit U) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : U * firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] H₀ = 0)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) H,
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) H hfinite =
        m * L := by
  obtain ⟨v, rfl⟩ := hU
  let V : Germ 2 := ↑v⁻¹
  let c : ℂ := valueRingHom 2 V
  have hc : c ≠ 0 := valueRingHom_ne_zero_of_isUnit (Units.isUnit v⁻¹)
  have hbareTail := mul_weighted_initial_tail r (r * m) hr V
    ((v : Germ 2) * firstCoordinatePolynomialEvaluation P) P₀ hP₀ hPtail
  have hcancel : V * ((v : Germ 2) * firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation P := by
    dsimp only [V]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcancel] at hbareTail
  have hbareNe : MvPolynomial.C c * P₀ ≠ 0 :=
    mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc) hP₀ne
  have hno' : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] (MvPolynomial.C c * P₀) = 0 ∧
      MvPolynomial.eval ![z, 1] H₀ = 0) := by
    intro z hz
    apply hno z
    refine ⟨?_, hz.2⟩
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_eq_zero,
      hc, false_or] using hz.1
  obtain ⟨hfiniteBare, hinterBare⟩ := weighted_intersection_eq_any_order_of_no_common_initial_root
    r L m hr hm P hP hPm hcoeff H (MvPolynomial.C c * P₀) H₀ (hP₀.C_mul c) hbareNe
    hH₀ hbareTail hHtail hno'
  have hfinite := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff
    (v : Germ 2) (firstCoordinatePolynomialEvaluation P) H v.isUnit).mpr hfiniteBare
  refine ⟨hfinite, ?_⟩
  rw [PlaneCurve.intersectionMultiplicity_unit_mul_left
    (v : Germ 2) (firstCoordinatePolynomialEvaluation P) H v.isUnit hfinite hfiniteBare]
  exact hinterBare

end OnLeConjecture.Analytic.Germ
