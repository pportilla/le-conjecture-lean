/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialPairTheorem
public import OnLeConjecture.Analytic.WeightedPowerNormalization

/-!
# Finite normalization and the weighted initial-pair dichotomy

Finite intersection produces a polynomial correction in the first germ
whose remainder has a normalized nonzero weighted initial form. The
correction preserves ordinary order, the pair ideal, the Jacobian, and the
intersection multiplicity. The integral-weight dichotomy then applies to
this constructed remainder.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Finite target normalization and both alternatives of the integral
weighted initial-pair lemma, with an analytic preparation unit retained.
Only the prepared first initial form is an input. The correction and the
normalized second initial form are outputs. -/
theorem exists_normalized_weighted_initial_pair_dichotomy
    (r m M t : ℕ) (hr : 0 < r) (hm : 3 ≤ m) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (U u : Germ 2) (hU : IsUnit U) (huOrdinary : u ∈ maximalIdeal 2 ^ m)
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m))
    (hPchart : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic)
    (hPchartDegree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m)
    (hPtail : U * firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ (p : ℂ[X]) (L : ℕ) (Q₀ : MvPolynomial (Fin 2) ℂ),
      let f := U * firstCoordinatePolynomialEvaluation P
      let g := u - Polynomial.aeval f p
      let p₀ := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
      let q₀ := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
      let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p₀ q₀
      let i := PlaneCurve.intersectionMultiplicity f u hfinite
      p.coeff 0 = 0 ∧ 0 < L ∧ Q₀ ≠ 0 ∧ Q₀.IsWeightedHomogeneous ![r, 1] L ∧
        g ∈ maximalIdeal 2 ^ m ∧ g ∈ weightedOrderIdeal r L ∧
        g ∉ weightedOrderIdeal r (L + 1) ∧
        g - coordinatePolynomialAlgHom 2 Q₀ ∈ weightedOrderIdeal r (L + 1) ∧
        (∀ (s : ℕ) (c : ℂ), 0 < s → c ≠ 0 → Q₀ ≠ MvPolynomial.C c * P₀ ^ s) ∧
        PlaneCurve.pairIdeal f g = PlaneCurve.pairIdeal f u ∧ jacobian f g = jacobian f u ∧
        (∃ hfinite' : PlaneCurve.HasFiniteIntersection f g,
          PlaneCurve.intersectionMultiplicity f g hfinite' = i) ∧
        m * L ≤ i ∧
        (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
          t ≤ L + r * (m - 1 - Ω.natDegree) ∧
          L = r * q₀.natDegree ∧ m + 1 ≤ q₀.natDegree) ∧
        (Ω = 0 → L = r * q₀.natDegree ∧
          (∃ c : ℂ, c ≠ 0 ∧ q₀ ^ m = C c * p₀ ^ q₀.natDegree) ∧ m * L < i) := by
  let f := U * firstCoordinatePolynomialEvaluation P
  have hP₀ne : P₀ ≠ 0 := by
    intro hzero
    apply hPchart.ne_zero
    simp [hzero]
  have hfWeighted : f ∈ weightedOrderIdeal r (r * m) := by
    have hsum := (weightedOrderIdeal r (r * m)).add_mem
      (weightedOrderIdeal_antitone r (r * m) (r * m + 1) hr (by omega) hPtail)
      (coordinatePolynomial_mem_weightedOrderIdeal r (r * m) hr hP₀)
    simpa only [sub_add_cancel] using hsum
  have hfOrdinary : f ∈ maximalIdeal 2 ^ m :=
    weightedOrderIdeal_mul_le_maximalIdeal_pow r m hr hfWeighted
  have huWeighted : u ∈ weightedOrderIdeal r 1 := by
    rw [weightedOrderIdeal_one_eq_maximalIdeal r hr]
    exact Ideal.pow_le_self (by omega : m ≠ 0) huOrdinary
  have hcolength : ∃ N : ℕ, maximalIdeal 2 ^ N ≤ Ideal.span {f, u} :=
    (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f u).mp hfinite
  obtain ⟨L, Q₀, p, hL, hp, hQ₀ne, hQ₀, hgWeighted, hgNext, hgTail,
      hideal, hJac, hnormalized⟩ :=
    exists_weighted_initial_form_avoiding_powers r (r * m) 1 hr
      (by positivity) P₀ hP₀ne hP₀ f u hPtail huWeighted hcolength
  let g := u - Polynomial.aeval f p
  have hpOrdinary : Polynomial.aeval f p ∈ maximalIdeal 2 ^ m := by
    apply (show Ideal.span {f} ≤ maximalIdeal 2 ^ m from
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfOrdinary))
    exact polynomial_aeval_mem_span_singleton f p hp
  have hgOrdinary : g ∈ maximalIdeal 2 ^ m :=
    (maximalIdeal 2 ^ m).sub_mem huOrdinary hpOrdinary
  have hideal' : PlaneCurve.pairIdeal f g = PlaneCurve.pairIdeal f u := hideal
  have hfinite' : PlaneCurve.HasFiniteIntersection f g :=
    hfinite.of_pairIdeal_eq hideal'.symm
  have hinter : PlaneCurve.intersectionMultiplicity f g hfinite' =
      PlaneCurve.intersectionMultiplicity f u hfinite :=
    PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfinite' hfinite hideal'
  have hnumber' : PlaneCurve.intersectionMultiplicity f g hfinite' + M ≤ 3 * t := by
    rw [hinter]
    exact hnumber
  have hdiv' : coordinate (1 : Fin 2) ^ (t - 1) ∣ jacobian f g := by
    rw [hJac]
    exact hdiv
  have hdichotomy := weighted_initial_pair_unit_dichotomy
    r L m M t hr (by omega) hm hM P hP hPm hcoeff U g hU hgOrdinary
    P₀ Q₀ hP₀ hQ₀ hQ₀ne hPchart hPchartDegree hPtail hgTail hfinite'
    hnormalized hnumber' hdiv'
  dsimp only at hdichotomy
  rw [hinter] at hdichotomy
  exact ⟨p, L, Q₀, hp, by omega, hQ₀ne, hQ₀, hgOrdinary, hgWeighted, hgNext,
    hgTail, hnormalized, hideal', hJac, ⟨hfinite', hinter⟩, hdichotomy⟩

end OnLeConjecture.Analytic.Germ
