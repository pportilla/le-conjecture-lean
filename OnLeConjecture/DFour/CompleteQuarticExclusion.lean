/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DFour.RationalQuarticInitialPair
import Mathlib.Tactic.Linarith

/-!
# The prepared quartic contradiction from complete proximity data

The two weighted-Jacobian branches are applied to the rational initial
pair constructed from the analytic preparation. The square initial form,
the odd exponent, the slope alternatives, and the absence of entries
three are derived. The resolution, its specified coordinate compatibility
and completeness, the Noether intersection equality, and the reduction's
numerical and Jacobian-divisibility inputs remain explicit hypotheses.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- Denominator-cleared arithmetic for the nonzero weighted-Jacobian
branch. -/
theorem quartic_nonzero_omega_estimates_impossible
    (s r A M i t k : ℕ) (hr : 0 < r) (hAr : s * A ≤ r) (hk : 5 ≤ k)
    (hpoint : i ≤ 3 * M + 4 * A) (hlower : 4 * (r * k) ≤ s * i)
    (hglobal : i + M ≤ 3 * t) (hpolar : s * t ≤ r * k + 3 * r) : False := by
  have hpoint' := Nat.mul_le_mul_left s hpoint
  have hglobal' := Nat.mul_le_mul_left s hglobal
  have hk' := Nat.mul_le_mul_left r hk
  nlinarith

/-- Denominator-cleared strict terminal estimate. The use of `t-1`
is justified by the global estimate, which forces `t>0`. -/
theorem quartic_strict_terminal_estimates_impossible
    (s r A M i t b e : ℕ) (_hs : 0 < s) (hA : 0 < A) (hb : 0 < b)
    (he : 3 ≤ e) (hAr : s * A ≤ r) (hstrict : 8 * e * r < s * i)
    (hpoint : i ≤ 2 * M + 8 * A) (hglobal : i + M ≤ 3 * t)
    (hpolar : 4 * (t - 1) + M + b ≤ 2 * i) : False := by
  have her := Nat.mul_le_mul_right r he
  have hi : 24 * A < i := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left s (show i ≤ 24 * A by omega)
    nlinarith
  have ht : 0 < t := by omega
  have htadd : t - 1 + 1 = t := Nat.sub_add_cancel ht
  omega

end OnLeConjecture.DFour

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- The global and point-basis estimates force Omega to vanish for the
constructed rational quartic pair. -/
theorem RationalPreparedWeightedPair.quartic_omega_eq_zero_of_point_bounds
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 4 t hs P U u hfinite)
    (hr : 0 < r) (A M : ℕ) (hAr : s * A ≤ r)
    (hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 3 * M + 4 * A)
    (hglobal : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t) :
    OnLeConjecture.Polynomial.weightedPairOmega 4 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) = 0 := by
  by_contra hne
  obtain ⟨_, ht, hweight, hk⟩ := data.nonzero_omega hne
  have hpolar : s * t ≤ r *
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree + 3 * r := by
    have hm := Nat.mul_le_mul_left r (show 4 - 1 -
        (OnLeConjecture.Polynomial.weightedPairOmega 4 (data.degree : ℂ) (r : ℂ)
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial)).natDegree ≤ 3 by omega)
    have hbound : s * t ≤ data.degree + 3 * r := by nlinarith
    simpa only [hweight] using hbound
  exact DFour.quartic_nonzero_omega_estimates_impossible s r A M _ t _ hr hAr hk hpoint
    (by simpa only [hweight] using data.lower_bound) hglobal hpolar

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- The constructed rational initial pair is incompatible with complete
quartic proximity data and the refined reduction estimates. -/
theorem rational_quartic_pair_excluded_of_terminal_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * U)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (t b : ℕ) (hb : 0 < b)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hglobal : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : 4 * (t - 1) + Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
      2 * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite)
    (s r : ℕ) (hs : 0 < s) (hr : 0 < r) (hAr : s * d.topOrderChain.length ≤ r)
    (horder : ∀ j, j < 4 → ((r * (4 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hattained : ∃ j, j < 4 ∧
      ((r * (4 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (data : RationalPreparedWeightedPair s r 4 t hs P U u hfinite) : False := by
  have hcount : Numerical.MultiplicityCounts.valueCount c.multiplicity 4 =
      d.topOrderChain.length := by
    simpa only [hroot] using d.topOrderChain.valueCount_eq_length
  have hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤
        3 * Numerical.MultiplicityCounts.sum c.multiplicity + 4 * d.topOrderChain.length := by
    rw [hintersection, ← hcount]
    exact Numerical.MultiplicityCounts.squareSum_le_three_sum_add_four_valueCount
      c.multiplicity (fun q ↦ (c.multiplicity_le_root q).trans_eq hroot)
  have hOmega := data.quartic_omega_eq_zero_of_point_bounds hr
    d.topOrderChain.length (Numerical.MultiplicityCounts.sum c.multiplicity) hAr hpoint hglobal
  obtain ⟨e, η, μ, he, _heodd, hη, _hμ, _hdegree, _hweight, hp, _hq, hstrict⟩ :=
    data.quartic_zero_omega_classification hr hdepressed hattained hOmega
  let w : SquareQuarticNewtonData P η := {
    s := s, r := r, s_pos := hs, r_pos := hr, monic := hmonic, degree := hdegree
    depressed := hdepressed, parameter_ne_zero := hη, order := horder
    initial := data.firstInitial, homogeneous := data.first_homogeneous
    tail := data.bare_first_tail hr hU, chart := hp }
  have hterminal := (square_initial_point_basis_bounds_of_terminal_complete_proximity
    d hcoordinates hcomplete hroot w U hU hprepared).2.2
  rw [← hintersection] at hterminal
  exact quartic_strict_terminal_estimates_impossible s r d.topOrderChain.length
    (Numerical.MultiplicityCounts.sum c.multiplicity) _ t b e hs d.topOrderChain.length_pos
    hb he hAr hstrict hterminal hglobal hpolar

/-- The weight, the normalized rational initial pair, and both weighted
Jacobian branches are constructed from the prepared analytic germs. -/
theorem prepared_quartic_excluded_of_terminal_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * U)
    (hsquarefree : Squarefree (U * firstCoordinatePolynomialEvaluation P))
    (huOrdinary : u ∈ maximalIdeal 2 ^ 4)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (t b : ℕ) (hb : 0 < b)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hglobal : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : 4 * (t - 1) + Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
      2 * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) : False := by
  have hcoeff : ∀ j, j < 4 → P.coeff j ∈ maximalIdeal 1 ^
      (d.topOrderChain.length * (4 - j)) := by
    intro j hj
    have h := d.topOrderChain.coefficient_mem_pow_of_straightened_preparation d
      hcoordinates.free_coordinates P U hU hprepared j (by omega)
    rw [d.topOrderChain.valueCount_eq_length, hroot] at h
    exact h
  have hM : 0 < Numerical.MultiplicityCounts.sum c.multiplicity := by
    have h := Finset.single_le_sum (fun q (_hq : q ∈ Finset.univ) ↦ Nat.zero_le (c.multiplicity q))
      (Finset.mem_univ c.root)
    exact lt_of_lt_of_le (c.multiplicity_pos c.root) h
  obtain ⟨s, r, hs, _hsEq, hr, hAr, horder, ⟨j, hj, _hjNe, hjOrder⟩, ⟨data⟩⟩ :=
    exists_newton_prepared_weighted_pair_of_squarefree 4 d.topOrderChain.length
      (Numerical.MultiplicityCounts.sum c.multiplicity) t (by decide)
      d.topOrderChain.length_pos hM P hmonic hdegree hcoeff U u hU hsquarefree
      huOrdinary hfinite hglobal hdiv
  exact rational_quartic_pair_excluded_of_terminal_complete_proximity d hcoordinates hcomplete hroot
    hmonic hdegree hdepressed U u hU hprepared hfinite t b hb hintersection hglobal hpolar
    s r hs hr hAr horder ⟨j, hj, hjOrder⟩ data

/-- Compatibility wrapper using global finite-chart completeness. -/
theorem rational_quartic_pair_excluded_of_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : FiniteSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    {P : Polynomial (Germ 1)} (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * U)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (t b : ℕ) (hb : 0 < b)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hglobal : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : 4 * (t - 1) + Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
      2 * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite)
    (s r : ℕ) (hs : 0 < s) (hr : 0 < r) (hAr : s * d.topOrderChain.length ≤ r)
    (horder : ∀ j, j < 4 → ((r * (4 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hattained : ∃ j, j < 4 ∧
      ((r * (4 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (data : RationalPreparedWeightedPair s r 4 t hs P U u hfinite) : False := by
  exact rational_quartic_pair_excluded_of_terminal_complete_proximity
    d hcoordinates hcomplete.terminal hroot hmonic hdegree hdepressed U u hU hprepared
    hfinite t b hb hintersection hglobal hpolar s r hs hr hAr horder hattained data

/-- Compatibility wrapper using global finite-chart completeness. -/
theorem prepared_quartic_excluded_of_complete_proximity
    {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d) (hcomplete : FiniteSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hdepressed : P.coeff 3 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hprepared : (freeChainStraighteningEquiv d.topOrderChain.chartCenters
      (d.topOrderChain.length - 1)).forward.pullbackRingHom (c.germ c.root) =
        firstCoordinatePolynomialEvaluation P * U)
    (hsquarefree : Squarefree (U * firstCoordinatePolynomialEvaluation P))
    (huOrdinary : u ∈ maximalIdeal 2 ^ 4)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (t b : ℕ) (hb : 0 < b)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hglobal : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : 4 * (t - 1) + Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
      2 * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) : False := by
  exact prepared_quartic_excluded_of_terminal_complete_proximity
    d hcoordinates hcomplete.terminal hroot P hmonic hdegree hdepressed U u hU hprepared
    hsquarefree huOrdinary hfinite t b hb hintersection hglobal hpolar hdiv

end OnLeConjecture.DFour
