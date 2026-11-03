/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalPreparedBareInitialForm

/-!
# Exact coefficient orders detected by a rational initial form

A nonzero coefficient of the initial chart forces equality in its
original ramified coefficient-order bound. Its weight is consequently
divisible by the ramification denominator.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem RationalPreparedWeightedPair.coefficient_order_of_chart_ne_zero
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = m) (hU : IsUnit U)
    (horder : ∀ i, i < m →
      ((r * (m - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (j : ℕ)
    (hj : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial).coeff j ≠ 0) :
    s • vanishingOrder (P.coeff j) = ((r * (m - j) : ℕ) : ℕ∞) ∧
      s ∣ r * (m - j) := by
  let PR := P.map (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hPR : PR.Monic := hP.map _
  have hPRm : PR.natDegree = m := (hP.natDegree_map _).trans hPm
  have hcoeff : ∀ i, PR.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)) := by
    intro i
    by_cases hi : i < m
    · exact coefficient_mem_maximalIdeal_pow_after_ramification s r m hs P horder i hi
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ i)]
  obtain ⟨A, _hA, hAm, hscale, hfactor⟩ := exists_monic_weighted_polynomial_scaling
    PR m r hPR hPRm hcoeff
  have hchart := weighted_initial_chart_eq_scaled_residue r m hr PR A hAm hscale
    data.firstInitial data.first_homogeneous (data.bare_first_tail hr hU)
  rw [hchart, coeff_map] at hj
  have hunit : IsUnit (A.coeff j) := isUnit_iff_valueRingHom_ne_zero.mpr hj
  have hvalue := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hunit (hfactor j)
  change vanishingOrder ((P.map (oneVariablePowerMapGerm s hs).pullbackRingHom).coeff j) = _
    at hvalue
  rw [coeff_map, vanishingOrder_oneVariablePowerMapGerm_pullback] at hvalue
  refine ⟨hvalue, ?_⟩
  have hnat := congrArg ENat.toNat hvalue
  simp only [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast] at hnat
  exact ⟨(vanishingOrder (P.coeff j)).toNat, hnat.symm⟩

/-- Once the rational weight is integral, the original unramified
polynomial admits the corresponding root scaling. Its residue is the
same first chart that was constructed after ramification. -/
theorem RationalPreparedWeightedPair.exists_unramified_scaled_polynomial
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = m) (hU : IsUnit U)
    (horder : ∀ i, i < m →
      ((r * (m - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (hdiv : s ∣ r) :
    ∃ a : ℕ, 0 < a ∧ r = s * a ∧ ∃ A : Polynomial (Germ 1),
      A.Monic ∧ A.natDegree = m ∧ P = A.scaleRoots (coordinate (0 : Fin 1) ^ a) ∧
      A.map (valueRingHom 1) = MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial ∧
      ∀ i, P.coeff i = coordinate (0 : Fin 1) ^ (a * (m - i)) * A.coeff i := by
  obtain ⟨a, hra⟩ := hdiv
  have ha : 0 < a := by nlinarith
  have hsne : (s : ℕ∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hs
  have hcoeff : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (a * (m - i)) := by
    intro i
    by_cases hi : i < m
    · apply mem_maximalIdeal_one_pow_iff.mpr
      apply (ENat.mul_le_mul_left_iff hsne (ENat.natCast_ne_top s)).mp
      simpa only [hra, Nat.mul_assoc, Nat.cast_mul, nsmul_eq_mul] using horder i hi
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ i)]
  obtain ⟨A, hA, hAm, hscale, hfactor⟩ :=
    exists_monic_weighted_polynomial_scaling P m a hP hPm hcoeff
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hscaleR : P.map ψ = (A.map ψ).scaleRoots (coordinate (0 : Fin 1) ^ r) := by
    rw [hscale, Polynomial.map_scaleRoots A _ ψ (by rw [hA, map_one]; exact one_ne_zero),
      map_pow, oneVariablePowerMapGerm_pullback_coordinate, ← pow_mul, hra]
  have hAmR : (A.map ψ).natDegree = m := (hA.natDegree_map ψ).trans hAm
  have hchart := weighted_initial_chart_eq_scaled_residue r m hr (P.map ψ) (A.map ψ)
    hAmR hscaleR data.firstInitial data.first_homogeneous (data.bare_first_tail hr hU)
  have hres : (A.map ψ).map (valueRingHom 1) = A.map (valueRingHom 1) := by
    rw [Polynomial.map_map]
    congr 1
    ext b
    exact PointedMapGerm.valueRingHom_pullback (oneVariablePowerMapGerm s hs) b
  exact ⟨a, ha, hra, A, hA, hAm, hscale, (hchart.trans hres).symm, hfactor⟩

end OnLeConjecture.Analytic.Germ
