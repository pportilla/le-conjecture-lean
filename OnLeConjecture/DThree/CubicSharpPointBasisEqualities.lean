/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.CubicTerminalPointCounts
import Mathlib.Tactic

/-!
# Integral Newton weight and sharp cubic point-basis equalities

The E/H coefficient equations, actual terminal transforms, and matched
point counts exclude every positive fractional excess. The weak weighted
intersection estimate and analytic Jacobian divisor then force the
sharp equalities. No Milnor invariant or global polar identity is used.
-/

public section

namespace OnLeConjecture.Numerical.MultiplicityCounts

open scoped BigOperators

theorem cubic_squareSum_eq_sum_add_counts
    {ι : Type*} [Fintype ι] (v : ι → ℕ) (hbound : ∀ p, v p ≤ 3) :
    squareSum v = sum v + 6 * valueCount v 3 + 2 * valueCount v 2 := by
  classical
  have hpoint (p : ι) : v p ^ 2 =
      v p + (if v p = 3 then 6 else 0) + (if v p = 2 then 2 else 0) := by
    have hp := hbound p
    interval_cases h : v p <;> norm_num
  calc
    squareSum v = ∑ p, (v p + (if v p = 3 then 6 else 0) +
      (if v p = 2 then 2 else 0)) := Finset.sum_congr rfl fun p _ ↦ hpoint p
    _ = sum v + 6 * valueCount v 3 + 2 * valueCount v 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_filter, ← Finset.sum_filter]
      simp [sum, valueCount, mul_comm]

end OnLeConjecture.Numerical.MultiplicityCounts

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem mem_pow_of_coordinate_power_factor
    (n k : ℕ) (hk : k ≤ n) (b u : Germ 1)
    (hfactor : b = coordinate (0 : Fin 1) ^ n * u) : b ∈ maximalIdeal 1 ^ k := by
  rw [hfactor]
  exact (maximalIdeal 1 ^ k).mul_mem_right u
    (Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) n))

set_option maxHeartbeats 1200000 in
-- The finite coefficient alternatives instantiate several dependent analytic constructions.
/-- The Newton weight equals the number of order-three entries. The
point basis has no order-two entries, and all numerical bounds are
equalities. Initial forms and coefficient orders are those constructed
by the rational prepared-pair theorem. -/
theorem RationalPreparedWeightedPair.cubic_sharp_equalities_of_matched_point_basis
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = 3) (hU : IsUnit U)
    (horder : ∀ j, j < 3 →
      ((r * (3 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hdepressed : P.coeff 2 = 0)
    (hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 3)
    (hprepared : d.topOrderChain.straightenedGerm 0 = firstCoordinatePolynomialEvaluation P * U)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hweight : s * d.topOrderChain.length ≤ r) :
    r = s * d.topOrderChain.length ∧ (∀ q, c.multiplicity q ≠ 2) ∧
      Numerical.MultiplicityCounts.sum c.multiplicity = 6 * d.topOrderChain.length ∧
      t = 6 * d.topOrderChain.length ∧
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        12 * d.topOrderChain.length := by
  let S := d.topOrderChain
  let M := Numerical.MultiplicityCounts.sum c.multiplicity
  let B₂ := Numerical.MultiplicityCounts.valueCount c.multiplicity 2
  let i := PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite
  change s * S.length ≤ r at hweight
  have hcount : Numerical.MultiplicityCounts.valueCount c.multiplicity 3 = S.length := by
    simpa only [hroot] using S.valueCount_eq_length
  have hbounded (q : Fin N) : c.multiplicity q ≤ 3 := by
    simpa only [hroot] using c.multiplicity_le_root q
  have hpoint : i ≤ 2 * M + 3 * S.length := by
    dsimp only [i, M]
    rw [hintersection, ← hcount]
    exact Numerical.MultiplicityCounts.cubic_squareSum_le_two_sum_add_three_count _ hbounded
  obtain ⟨hne, hconstant, _hdegrees, hdegree, _hnoCommon, hsquare⟩ :=
    data.cubic_initial_constraints hr hdepressed hattained M S.length hnumber hpoint hweight
  have hfour := data.cubic_initial_degree_eq_four_of_matched_point_basis hr hP hPm hU horder
    hdepressed hattained c d hcoordinates hroot hprepared hintersection hnumber hweight
  rw [hfour] at hdegree
  have hlower := data.lower_bound
  rw [hdegree] at hlower
  change 3 * (r * 4) ≤ s * i at hlower
  have ht := (data.nonzero_omega hne).2.1
  rw [hconstant, hdegree] at ht
  change s * t ≤ r * 4 + r * 2 at ht
  have hi : i = M + 6 * S.length + 2 * B₂ := by
    dsimp only [i, M, B₂]
    rw [hintersection, Numerical.MultiplicityCounts.cubic_squareSum_eq_sum_add_counts _ hbounded,
      hcount]
  have hnumberS := Nat.mul_le_mul_left s hnumber
  change s * (i + M) ≤ s * (3 * t) at hnumberS
  have hiS := congrArg (fun n : ℕ ↦ s * n) hi
  have hmain : 6 * r ≤ 6 * s * S.length + 2 * s * B₂ := by
    nlinarith only [hlower, ht, hnumberS, hiS]
  have hcoeff : ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (S.length * (3 - j)) := by
    intro j
    by_cases hj : j < 3
    · have h := S.coefficient_mem_pow_of_straightened_preparation d hcoordinates.free_coordinates
        P U hU (S.straightenedGerm_root.symm.trans hprepared) j (by omega)
      simpa only [hroot, hcount] using h
    · simp [Nat.sub_eq_zero_of_le (by omega : 3 ≤ j)]
  obtain ⟨Q, hQ, hQm, hscale, hfactor⟩ := exists_monic_weighted_polynomial_scaling
    P 3 S.length hP hPm hcoeff
  have hQdepressed : Q.coeff 2 = 0 := by
    have h := hfactor 2
    rw [hdepressed] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ coordinate_zero_ne_zero)
  have hQprepared : S.straightenedGerm 0 = firstCoordinatePolynomialEvaluation
      (Q.scaleRoots (coordinate (0 : Fin 1) ^ S.length)) * U := by rwa [← hscale]
  have hf₁ : P.coeff 1 = coordinate (0 : Fin 1) ^ (2 * S.length) * Q.coeff 1 := by
    simpa only [Nat.reduceSub, Nat.mul_comm] using hfactor 1
  have hf₀ : P.coeff 0 = coordinate (0 : Fin 1) ^ (3 * S.length) * Q.coeff 0 := by
    simpa only [Nat.sub_zero, Nat.mul_comm] using hfactor 0
  have hintegral : r = s * S.length := by
    by_contra hnot
    have hgap : s * S.length < r := by omega
    rcases data.quartic_coefficient_order_alternatives hr hP hPm hU horder hdepressed
      hfour hne hconstant with ⟨hexact, hstrict, _hdiv⟩ | ⟨hexact, hstrict, _hdiv⟩
    · obtain ⟨n, B, hB, hBfactor, hn, hlinear, hlinear₂⟩ := cubic_E_divided_coefficient_orders
        s r S.length hs hweight _ _ _ _ hf₁ hf₀ hexact hstrict
      have hnpos : 0 < n := by nlinarith only [hn, hgap]
      have hconstant₁ : Q.coeff 0 ∈ maximalIdeal 1 := by
        simpa only [pow_one] using mem_pow_of_coordinate_power_factor n 1 hnpos _ B hBfactor
      have hres := depressed_cubic_residue_eq_X_cube Q hQ hQm hQdepressed hlinear hconstant₁
      by_cases hnOne : n = 1
      · have hzero : B₂ = 0 := S.valueCount_two_eq_zero_of_divided_constant_order_one
          d hcoordinates hroot Q hQ hQm hres U hU hQprepared B hB
            (by simpa only [hnOne, pow_one] using hBfactor)
        rw [hzero] at hmain
        nlinarith only [hmain, hgap]
      by_cases hnTwo : n = 2
      · have hcount₂ : B₂ ≤ 1 := S.valueCount_two_le_one_of_divided_cusp d hcoordinates hroot
          Q hQ hQm hres U hU hQprepared hQdepressed B hB
            (by simpa only [hnTwo] using hBfactor) (hlinear₂ (by omega))
        rw [hnTwo] at hn
        have hc := Nat.mul_le_mul_left s hcount₂
        nlinarith only [hmain, hn, hs, hc]
      · have hconstant₃ := mem_pow_of_coordinate_power_factor n 3 (by omega) _ B hBfactor
        have hzero : B₂ = 0 := S.valueCount_two_eq_zero_of_divided_cubic_mem_cube
          d hcoordinates hroot Q hQ hQm hres U hU hQprepared
            (depressed_cubic_mem_cube_of_coefficient_orders Q hQdepressed
              (hlinear₂ (by omega)) hconstant₃)
        rw [hzero] at hmain
        nlinarith only [hmain, hgap]
    · obtain ⟨n, B, hB, hBfactor, hn, hconstant₂, hconstant₃⟩ := cubic_H_divided_coefficient_orders
        s r S.length hs _ _ _ _ hf₁ hf₀ hexact hstrict
      have hnpos : 0 < n := by nlinarith only [hn, hgap]
      have hlinear₁ : Q.coeff 1 ∈ maximalIdeal 1 := by
        simpa only [pow_one] using mem_pow_of_coordinate_power_factor n 1 hnpos _ B hBfactor
      have hconstant₁ : Q.coeff 0 ∈ maximalIdeal 1 := by
        simpa only [pow_one] using Ideal.pow_le_pow_right (by decide : 1 ≤ 2) (hconstant₂ hnpos)
      have hres := depressed_cubic_residue_eq_X_cube Q hQ hQm hQdepressed hlinear₁ hconstant₁
      by_cases hnOne : n = 1
      · have hcount₂ : B₂ ≤ 1 := S.valueCount_two_le_one_of_divided_node d hcoordinates hroot
          Q hQ hQm hres U hU hQprepared hQdepressed B hB
            (by simpa only [hnOne, pow_one] using hBfactor) (hconstant₂ hnpos)
        rw [hnOne] at hn
        have hc := Nat.mul_le_mul_left s hcount₂
        nlinarith only [hmain, hn, hs, hc]
      · have hlinear₂ := mem_pow_of_coordinate_power_factor n 2 (by omega) _ B hBfactor
        have hzero : B₂ = 0 := S.valueCount_two_eq_zero_of_divided_cubic_mem_cube
          d hcoordinates hroot Q hQ hQm hres U hU hQprepared
            (depressed_cubic_mem_cube_of_coefficient_orders Q hQdepressed
              hlinear₂ (hconstant₃ (by omega)))
        rw [hzero] at hmain
        nlinarith only [hmain, hgap]
  obtain ⟨a, _ha, hra, R, hR, hRm, hRscale, hRresidue, _hRcoeff⟩ :=
    data.exists_unramified_scaled_polynomial hr hP hPm hU horder ⟨S.length, hintegral⟩
  have ha : a = S.length := by nlinarith
  subst a
  have hoff : ∀ q, c.multiplicity q ≤ 1 ∨ c.multiplicity q = 3 := by
    intro q
    by_cases hq : c.multiplicity q = 3
    · exact Or.inr hq
    · left
      apply S.off_top_chain_multiplicity_le_one_of_squarefree_scaled_residue d hcoordinates hroot
        R hR hRm (le_refl S.length) U hU
      · simpa only [← hRscale] using hprepared
      · rwa [hRresidue]
      · exact hq
  have hiExact : i = M + 6 * S.length := by
    dsimp only [i, M]
    rw [hintersection, Numerical.MultiplicityCounts.cubic_squareSum_eq_sum_add_six_count _ hoff,
      hcount]
  have hnoTwo : ∀ q, c.multiplicity q ≠ 2 := by
    intro q hq
    rcases hoff q with h | h <;> omega
  rw [hintegral] at ht hlower
  have htl : t ≤ 6 * S.length := by nlinarith
  have hil : 12 * S.length ≤ i := by nlinarith
  have hM : M = 6 * S.length := by change i + M ≤ 3 * t at hnumber; omega
  have htEq : t = 6 * S.length := by change i + M ≤ 3 * t at hnumber; omega
  have hiEq : i = 12 * S.length := by omega
  exact ⟨hintegral, hnoTwo, hM, htEq, hiEq⟩

end OnLeConjecture.Analytic.Germ
