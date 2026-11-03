/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalPreparedBareInitialForm
public import OnLeConjecture.DFour.QuarticClassification
public import OnLeConjecture.DFour.QuarticSlopeFromCompleteness
import Mathlib.Tactic

/-!
# Classification of the constructed rational quartic initial pair

The first and second forms are the outputs of the analytic rational
prepared-pair construction. Attainment excludes a pure fourth power,
and chart injectivity transfers the proved normalization condition to
the chart polynomials. A vanishing weighted Jacobian therefore gives
the square quartic and an odd power of its quadratic factor.
-/

public section

namespace OnLeConjecture.DFour

open _root_.Polynomial

/-- A monic depressed quartic that is a fourth power is `X^4`. -/
theorem depressed_quartic_ne_fourth_power
    (p : ℂ[X]) (hp : p.Monic) (hdegree : p.natDegree = 4)
    (hdepressed : p.coeff 3 = 0) (hnontrivial : p ≠ X ^ 4) :
    ∀ Q : ℂ[X], p ≠ Q ^ 4 := by
  intro Q hpower
  have hQdegree : Q.natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hpower
    rw [hdegree, Polynomial.natDegree_pow] at h
    omega
  obtain ⟨a, ha, b, hQ⟩ := Polynomial.natDegree_eq_one.mp hQdegree
  have hexp : (C a * X + C b) ^ 4 =
      C (a ^ 4) * X ^ 4 + C (4 * a ^ 3 * b) * X ^ 3 +
      C (6 * a ^ 2 * b ^ 2) * X ^ 2 + C (4 * a * b ^ 3) * X + C (b ^ 4) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  have hthree := congrArg (fun f : ℂ[X] ↦ f.coeff 3) hpower
  rw [← hQ, hexp] at hthree
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, hdepressed] at hthree
  norm_num at hthree
  have hb : b = 0 := by
    exact hthree.resolve_left ha
  have hform : p = C (a ^ 4) * X ^ 4 := by
    rw [hpower, ← hQ, hb, map_zero, add_zero, mul_pow, ← map_pow]
  have hfour := hp.coeff_natDegree
  rw [hdegree, hform, coeff_C_mul] at hfour
  norm_num at hfour
  exact hnontrivial (by rw [hform, hfour, map_one, one_mul])

end OnLeConjecture.DFour

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A power relation between chart polynomials lifts to the actual
homogeneous forms when their weighted degrees match. -/
theorem RationalPreparedWeightedPair.chart_normalized_of_weight_relation
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hweight : data.degree = r *
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree) :
    ∀ (a : ℕ) (γ : ℂ), 0 < a → γ ≠ 0 →
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial ≠
        C γ * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial) ^ a := by
  intro a γ ha hγ heq
  have hdegree := congrArg Polynomial.natDegree heq
  rw [natDegree_C_mul hγ, data.first_chart_monic.natDegree_pow, data.first_chart_degree]
    at hdegree
  apply data.normalized a γ ha hγ
  apply OnLeConjecture.Polynomial.eq_of_weighted_chart_eq r data.degree
    data.secondInitial (MvPolynomial.C γ * data.firstInitial ^ a) data.second_homogeneous
  · have hhom := (data.first_homogeneous.pow a).C_mul γ
    have hdeg : a • (r * m) = data.degree := by rw [hweight, hdegree]; simp [smul_eq_mul]; ring
    simpa only [hdeg] using hhom
  · simpa only [map_mul, map_pow, MvPolynomial.aeval_C, algebraMap_eq] using heq

/-- The ordinary order of the corrected original second germ bounds
the degree of its ramified chart whenever its weighted degree is `r*k`. -/
theorem RationalPreparedWeightedPair.chart_degree_ge_original_order
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite) (hr : 0 < r)
    (hweight : data.degree = r *
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree) :
    m ≤ (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree := by
  apply maximalIdeal_order_le_weighted_chart_degree r m _ hr
    ((secondCoordinatePowerGerm s hs).pullbackRingHom
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) data.correction))
    (PointedMapGerm.pullback_mem_maximalIdeal_pow _ data.original_order)
    data.secondInitial (by simpa only [hweight] using data.second_homogeneous)
    data.second_ne rfl
  simpa only [hweight] using data.second_tail

/-- Vanishing Omega for the attained depressed quartic gives the precise
square/quadratic-power classification, including the lower bound on the
odd exponent. All normalization and order hypotheses come from the
constructed rational prepared pair. -/
theorem RationalPreparedWeightedPair.quartic_zero_omega_classification
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 4 t hs P U u hfinite)
    (hr : 0 < r) (hdepressed : P.coeff 3 = 0)
    (hattained : ∃ j, j < 4 ∧
      ((r * (4 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (hOmega : OnLeConjecture.Polynomial.weightedPairOmega 4 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) = 0) :
    ∃ (e : ℕ) (η μ : ℂ), 3 ≤ e ∧ Odd e ∧ η ≠ 0 ∧ μ ≠ 0 ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 2 * e ∧
      data.degree = r * (2 * e) ∧
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial = (X ^ 2 + C η) ^ 2 ∧
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial =
        C μ * (X ^ 2 + C η) ^ e ∧
      8 * e * r < s * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) u hfinite := by
  obtain ⟨hweight, ⟨κ, hκ, hpower⟩, hstrict⟩ := data.zero_omega hOmega
  have hkLower := data.chart_degree_ge_original_order hr hweight
  obtain ⟨e, η, μ, _hmod, hdegree, heodd, hημ, hp, hq⟩ :=
    DFour.quartic_power_identity_classification data.first_chart_monic data.first_chart_degree
      (data.first_zero_coefficient 3 hdepressed)
      (DFour.depressed_quartic_ne_fourth_power _ data.first_chart_monic data.first_chart_degree
        (data.first_zero_coefficient 3 hdepressed) (data.first_chart_ne_X_pow hattained))
      (by omega) hκ hpower (data.chart_normalized_of_weight_relation hweight)
  have he : 3 ≤ e := by
    have hodd := Nat.odd_iff.mp heodd
    omega
  refine ⟨e, η, μ, he, heodd, (mul_ne_zero_iff.mp hημ).1, (mul_ne_zero_iff.mp hημ).2,
    hdegree, hweight.trans (congrArg (r * ·) hdegree), hp, hq, ?_⟩
  rw [hweight, hdegree] at hstrict
  nlinarith

end OnLeConjecture.Analytic.Germ
