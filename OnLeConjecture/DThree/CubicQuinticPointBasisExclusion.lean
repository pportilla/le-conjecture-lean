/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.RationalQuinticInitialPair
public import OnLeConjecture.Analytic.SquarefreeScaledResolution
import Mathlib.Tactic

/-!
# Excluding the quintic alternative from a matched analytic point basis

The cubic-quintic equation makes the Newton weight integral. Its
squarefree initial cubic then excludes every order-two entry in the
matched point basis. The square sum minus the sum is six times the
number of order-three entries. The weighted intersection and Jacobian
bounds contradict the quintic alternative. No Milnor or global polar
identity enters this argument.
-/

public section

namespace OnLeConjecture.Numerical.MultiplicityCounts

open scoped BigOperators

theorem cubic_squareSum_le_two_sum_add_three_count
    {ι : Type*} [Fintype ι] (v : ι → ℕ) (hbound : ∀ p, v p ≤ 3) :
    squareSum v ≤ 2 * sum v + 3 * valueCount v 3 := by
  classical
  have hpoint (p : ι) : v p ^ 2 ≤ 2 * v p + (if v p = 3 then 3 else 0) := by
    split_ifs with hp
    · norm_num [hp]
    · have hle : v p ≤ 2 := by have := hbound p; omega
      nlinarith
  calc
    squareSum v ≤ ∑ p, (2 * v p + if v p = 3 then 3 else 0) :=
      Finset.sum_le_sum fun p _ ↦ hpoint p
    _ = 2 * sum v + 3 * valueCount v 3 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
      simp [sum, valueCount, mul_comm]

theorem cubic_squareSum_eq_sum_add_six_count
    {ι : Type*} [Fintype ι] (v : ι → ℕ) (hbound : ∀ p, v p ≤ 1 ∨ v p = 3) :
    squareSum v = sum v + 6 * valueCount v 3 := by
  classical
  have hpoint (p : ι) : v p ^ 2 = v p + (if v p = 3 then 6 else 0) := by
    rcases hbound p with hp | hp
    · have hn : v p ≠ 3 := by omega
      rw [if_neg hn]
      interval_cases hv : v p <;> norm_num
    · norm_num [hp]
  calc
    squareSum v = ∑ p, (v p + if v p = 3 then 6 else 0) :=
      Finset.sum_congr rfl fun p _ ↦ hpoint p
    _ = sum v + 6 * valueCount v 3 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [sum, valueCount, mul_comm]

end OnLeConjecture.Numerical.MultiplicityCounts

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- The normalized second initial chart has degree four. The initial
forms are those already constructed from analytic weighted elimination.
All point-basis information is supplied by genuine matched germs,
proximity data, and the intersection square-sum identification. -/
theorem RationalPreparedWeightedPair.cubic_initial_degree_eq_four_of_matched_point_basis
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
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 4 := by
  let S := d.topOrderChain
  let M := Numerical.MultiplicityCounts.sum c.multiplicity
  let i := PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite
  have hcount : Numerical.MultiplicityCounts.valueCount c.multiplicity 3 = S.length := by
    simpa only [hroot] using S.valueCount_eq_length
  have hpoint : i ≤ 2 * M + 3 * S.length := by
    dsimp only [i, M]
    rw [hintersection, ← hcount]
    exact Numerical.MultiplicityCounts.cubic_squareSum_le_two_sum_add_three_count
      c.multiplicity (fun q ↦ by simpa only [hroot] using c.multiplicity_le_root q)
  obtain ⟨hne, hconstant, hdegrees, hdegree, _hnoCommon, hsquare⟩ :=
    data.cubic_initial_constraints hr hdepressed hattained M S.length hnumber hpoint hweight
  rcases hdegrees with hfour | hquintic
  · exact hfour
  exfalso
  obtain ⟨_, _, _, _, _, hdiv⟩ :=
    data.quintic_weight_integral hr hP hPm hU horder hdepressed hquintic hne hconstant
  obtain ⟨a, ha, hra, A, hA, hAm, hscale, hresidue, _hcoeff⟩ :=
    data.exists_unramified_scaled_polynomial hr hP hPm hU horder hdiv
  have hchainBound : S.length ≤ a := by dsimp only [S]; nlinarith
  have hoff : ∀ q, c.multiplicity q ≤ 1 ∨ c.multiplicity q = 3 := by
    intro q
    by_cases hq : c.multiplicity q = 3
    · exact Or.inr hq
    · left
      apply S.off_top_chain_multiplicity_le_one_of_squarefree_scaled_residue d hcoordinates hroot
        A hA hAm hchainBound U hU
      · simpa only [← hscale] using hprepared
      · rwa [hresidue]
      · exact hq
  have hi : i = M + 6 * S.length := by
    dsimp only [i, M]
    rw [hintersection, Numerical.MultiplicityCounts.cubic_squareSum_eq_sum_add_six_count
      c.multiplicity hoff, hcount]
  have hlower := data.lower_bound
  have ht := (data.nonzero_omega hne).2.1
  rw [hquintic] at hdegree
  rw [hdegree] at hlower
  rw [hconstant, hdegree] at ht
  change 3 * (r * 5) ≤ s * i at hlower
  change s * t ≤ r * 5 + r * 2 at ht
  have hnumberS := Nat.mul_le_mul_left s hnumber
  change s * (i + M) ≤ s * (3 * t) at hnumberS
  nlinarith

/-- Matched analytic and proximity data, an order-three preparation in
the constructed straightening coordinates, and the two original
intersection conditions construct a cubic-quartic initial pair. The
coefficient bounds, Newton slope, target correction, and second chart
degree are conclusions. -/
theorem exists_rational_cubic_quartic_initial_pair_of_matched_point_basis
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 3)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = 3)
    (hdepressed : P.coeff 2 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hprepared : d.topOrderChain.straightenedGerm 0 = firstCoordinatePolynomialEvaluation P * U)
    (hsquarefree : Squarefree (U * firstCoordinatePolynomialEvaluation P))
    (huOrdinary : u ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hintersection : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (t : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ s r : ℕ, ∃ hs : 0 < s, s = 6 ∧ 0 < r ∧ s * d.topOrderChain.length ≤ r ∧
      ∃ data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite,
        RationalCubicInitialProperties data ∧
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 4 := by
  let S := d.topOrderChain
  let M := Numerical.MultiplicityCounts.sum c.multiplicity
  have hcount : Numerical.MultiplicityCounts.valueCount c.multiplicity 3 = S.length := by
    simpa only [hroot] using S.valueCount_eq_length
  have hM : 0 < M := by
    have hle : c.multiplicity c.root ≤ ∑ p, c.multiplicity p :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c.root)
    change c.multiplicity c.root ≤ M at hle
    rw [hroot] at hle
    omega
  have hcoeff : ∀ j, j < 3 → P.coeff j ∈ maximalIdeal 1 ^ (S.length * (3 - j)) := by
    intro j hj
    have h := S.coefficient_mem_pow_of_straightened_preparation d hcoordinates.free_coordinates
      P U hU (S.straightenedGerm_root.symm.trans hprepared) j (by omega)
    simpa only [hroot, hcount] using h
  obtain ⟨s, r, hs, hsEq, hr, hAr, horder, hsharp, ⟨data⟩⟩ :=
    exists_newton_prepared_weighted_pair_of_squarefree 3 S.length M t (by decide)
      S.length_pos hM P hP hPm hcoeff U u hU hsquarefree huOrdinary hfinite hnumber hdiv
  obtain ⟨j, hj, _hne, hjsharp⟩ := hsharp
  have hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j) := ⟨j, hj, hjsharp⟩
  have hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 2 * M + 3 * S.length := by
    dsimp only [M]
    rw [hintersection, ← hcount]
    exact Numerical.MultiplicityCounts.cubic_squareSum_le_two_sum_add_three_count
      c.multiplicity (fun q ↦ by simpa only [hroot] using c.multiplicity_le_root q)
  refine ⟨s, r, hs, by simpa only [show Nat.factorial 3 = 6 by decide] using hsEq,
    hr, hAr, data, ?_, ?_⟩
  · exact data.cubic_properties hr hP hPm
      (coeff_mem_maximalIdeal_of_weighted_bounds S.length 3 S.length_pos P hcoeff)
      horder hU hdepressed hattained M S.length hnumber hpoint hAr
  · exact data.cubic_initial_degree_eq_four_of_matched_point_basis hr hP hPm hU horder
      hdepressed hattained c d hcoordinates hroot hprepared hintersection hnumber hAr

end OnLeConjecture.Analytic.Germ
