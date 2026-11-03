/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NormalizedWeightedInitialPair
public import OnLeConjecture.Analytic.MonicWeierstrassInitialForm

/-!
# The weighted initial-pair lemma from coefficient-prepared analytic data

The first initial form is constructed from the Weierstrass coefficient
bounds. Constant rescaling normalizes the preparation unit at the origin.
Finite target normalization then constructs the second initial form and
proves the weighted dichotomy. Both initial forms and the target correction
are outputs of the theorem.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Multiplication of the first germ by a constant rescales its Jacobian
by the same constant. -/
theorem jacobian_const_mul_left (c : ℂ) (f g : Germ 2) :
    jacobian (constRingHom 2 c * f) g = constRingHom 2 c * jacobian f g := by
  rw [jacobian_mul_left, jacobian_const_left]
  ring

/-- The integral-weight initial-pair lemma from an analytic Weierstrass
polynomial, its preparation unit, and an arbitrary second germ. Constant
rescaling and finite target normalization preserve the original
intersection number. No initial form is an input. -/
theorem exists_prepared_weighted_initial_pair_dichotomy
    (r m M t : ℕ) (hr : 0 < r) (hm : 3 ≤ m) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (U u : Germ 2) (hU : IsUnit U) (huOrdinary : u ∈ maximalIdeal 2 ^ m)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ (c : ℂ) (V : Germ 2) (p : ℂ[X]) (L : ℕ) (P₀ Q₀ : MvPolynomial (Fin 2) ℂ),
      let f := U * firstCoordinatePolynomialEvaluation P
      let F := V * firstCoordinatePolynomialEvaluation P
      let g := u - Polynomial.aeval F p
      let p₀ := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
      let q₀ := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
      let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p₀ q₀
      let i := PlaneCurve.intersectionMultiplicity f u hfinite
      c = (valueRingHom 2 U)⁻¹ ∧ c ≠ 0 ∧ V = constRingHom 2 c * U ∧
        IsUnit V ∧ valueRingHom 2 V = 1 ∧
        P₀ ≠ 0 ∧ P₀.IsWeightedHomogeneous ![r, 1] (r * m) ∧ p₀.Monic ∧
        p₀.natDegree = m ∧
        firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
          weightedOrderIdeal r (r * m + 1) ∧
        F - coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * m + 1) ∧
        (∀ j, P.coeff j = 0 → p₀.coeff j = 0) ∧
        (∀ j, vanishingOrder (P.coeff j) = ((r * (m - j) : ℕ) : ℕ∞) → p₀.coeff j ≠ 0) ∧
        p.coeff 0 = 0 ∧ 0 < L ∧ Q₀ ≠ 0 ∧ Q₀.IsWeightedHomogeneous ![r, 1] L ∧
        g ∈ maximalIdeal 2 ^ m ∧ g ∈ weightedOrderIdeal r L ∧
        g ∉ weightedOrderIdeal r (L + 1) ∧
        g - coordinatePolynomialAlgHom 2 Q₀ ∈ weightedOrderIdeal r (L + 1) ∧
        (∀ (s : ℕ) (b : ℂ), 0 < s → b ≠ 0 → Q₀ ≠ MvPolynomial.C b * P₀ ^ s) ∧
        PlaneCurve.pairIdeal f g = PlaneCurve.pairIdeal f u ∧
        PlaneCurve.pairIdeal F g = PlaneCurve.pairIdeal f u ∧
        jacobian f g = jacobian f u ∧
        jacobian F g = constRingHom 2 c * jacobian f u ∧
        (∃ hfinite' : PlaneCurve.HasFiniteIntersection f g,
          PlaneCurve.intersectionMultiplicity f g hfinite' = i) ∧
        m * L ≤ i ∧
        (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
          t ≤ L + r * (m - 1 - Ω.natDegree) ∧
          L = r * q₀.natDegree ∧ m + 1 ≤ q₀.natDegree) ∧
        (Ω = 0 → L = r * q₀.natDegree ∧
          (∃ b : ℂ, b ≠ 0 ∧ q₀ ^ m = C b * p₀ ^ q₀.natDegree) ∧ m * L < i) := by
  let f := U * firstCoordinatePolynomialEvaluation P
  let c := (valueRingHom 2 U)⁻¹
  let V := constRingHom 2 c * U
  let F := V * firstCoordinatePolynomialEvaluation P
  have hvalueU : valueRingHom 2 U ≠ 0 := valueRingHom_ne_zero_of_isUnit hU
  have hc : c ≠ 0 := inv_ne_zero hvalueU
  have hcUnit : IsUnit (constRingHom 2 c) := isUnit_of_valueRingHom_ne_zero (by simpa using hc)
  have hV : IsUnit V := hcUnit.mul hU
  have hVvalue : valueRingHom 2 V = 1 := by
    simp only [V, map_mul, valueRingHom_const, c, inv_mul_cancel₀ hvalueU]
  have hF : F = constRingHom 2 c * f := by dsimp only [F, V, f]; ring
  have hpair (v : Germ 2) : PlaneCurve.pairIdeal F v = PlaneCurve.pairIdeal f v := by
    rw [hF]
    exact PlaneCurve.pairIdeal_unit_mul_left _ _ _ hcUnit
  have hfiniteF : PlaneCurve.HasFiniteIntersection F u := by
    rw [hF]
    exact (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hcUnit).mpr hfinite
  have hinterF : PlaneCurve.intersectionMultiplicity F u hfiniteF =
      PlaneCurve.intersectionMultiplicity f u hfinite := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [hpair]
  have hnumberF : PlaneCurve.intersectionMultiplicity F u hfiniteF + M ≤ 3 * t := by
    rw [hinterF]
    exact hnumber
  have hJacF (v : Germ 2) : jacobian F v = constRingHom 2 c * jacobian f v := by
    rw [hF, jacobian_const_mul_left]
  have hdivF : coordinate (1 : Fin 2) ^ (t - 1) ∣ jacobian F u := by
    rw [hJacF]
    exact dvd_mul_of_dvd_right hdiv _
  obtain ⟨P₀, hP₀ne, hP₀, hbareTail, hPchart, hPdegree, hzero, hexact⟩ :=
    exists_monic_weierstrass_initial_form r m hr P hP hPm hcoeff
  have hFTail : F - coordinatePolynomialAlgHom 2 P₀ ∈ weightedOrderIdeal r (r * m + 1) := by
    have htail := mul_weighted_initial_tail r (r * m) hr V
      (firstCoordinatePolynomialEvaluation P) P₀ hP₀ hbareTail
    simpa only [hVvalue, map_one, one_mul] using htail
  obtain ⟨p, L, Q₀, hp, hL, hQ₀ne, hQ₀, hgOrdinary, hgWeighted, hgNext,
      hgTail, hnormalized, hideal, hJac, _hfiniteG, hdichotomy⟩ :=
    exists_normalized_weighted_initial_pair_dichotomy r m M t hr hm hM P hP hPm hcoeff
      V u hV huOrdinary P₀ hP₀ hPchart hPdegree hFTail hfiniteF hnumberF hdivF
  let g := u - Polynomial.aeval F p
  have hidealOriginal : PlaneCurve.pairIdeal f g = PlaneCurve.pairIdeal f u := by
    rw [← hpair g, ← hpair u]
    exact hideal
  have hidealMixed : PlaneCurve.pairIdeal F g = PlaneCurve.pairIdeal f u :=
    hideal.trans (hpair u)
  have hJacOriginal : jacobian f g = jacobian f u := by
    have hconstNe : constRingHom 2 c ≠ 0 := hcUnit.ne_zero
    apply mul_left_cancel₀ hconstNe
    rw [← hJacF, ← hJacF]
    exact hJac
  have hJacMixed : jacobian F g = constRingHom 2 c * jacobian f u := by
    rw [hJacF, hJacOriginal]
  have hfiniteOriginal : PlaneCurve.HasFiniteIntersection f g :=
    hfinite.of_pairIdeal_eq hidealOriginal.symm
  have hinterOriginal : PlaneCurve.intersectionMultiplicity f g hfiniteOriginal =
      PlaneCurve.intersectionMultiplicity f u hfinite :=
    PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq
      hfiniteOriginal hfinite hidealOriginal
  rw [hinterF] at hdichotomy
  exact ⟨c, V, p, L, P₀, Q₀, rfl, hc, rfl, hV, hVvalue, hP₀ne, hP₀, hPchart,
    hPdegree, hbareTail, hFTail, hzero, hexact, hp, hL, hQ₀ne, hQ₀, hgOrdinary,
    hgWeighted, hgNext, hgTail, hnormalized, hidealOriginal, hidealMixed, hJacOriginal,
    hJacMixed, ⟨hfiniteOriginal, hinterOriginal⟩, hdichotomy⟩

end OnLeConjecture.Analytic.Germ
