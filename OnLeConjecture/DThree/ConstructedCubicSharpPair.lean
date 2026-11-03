/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.CubicSharpPointBasisEqualities
import Mathlib.Tactic

/-!
# Construction of the integral cubic-quartic prepared pair

The rational construction and the matched point basis force integral
weight. Running analytic normalization at this proved integral weight
then gives an unramified polynomial target correction with exact quartic
order. No reflection theorem for ramified initial forms is needed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

@[simp] theorem secondCoordinatePowerGerm_one (h : 0 < (1 : ℕ)) :
    secondCoordinatePowerGerm 1 h = PointedMapGerm.identity 2 := by
  have hf : (fun z : Source 2 ↦ ![z 0, z 1 ^ 1]) = id := by
    funext z
    ext i
    fin_cases i <;> simp
  simp only [secondCoordinatePowerGerm, hf, PointedMapGerm.identity]

/-- An original prepared cubic and a matched point basis construct the
polynomial target correction, its exact quartic order, the sharp cubic
coefficient, and all cubic point-basis equalities. -/
theorem exists_cubic_sharp_correction_of_matched_point_basis
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
    let A := d.topOrderChain.length
    let f := U * firstCoordinatePolynomialEvaluation P
    (∀ q, c.multiplicity q ≠ 2) ∧ Numerical.MultiplicityCounts.sum c.multiplicity = 6 * A ∧
      t = 6 * A ∧ PlaneCurve.intersectionMultiplicity f u hfinite = 12 * A ∧
      P.coeff 1 ∈ maximalIdeal 1 ^ (2 * A) ∧ P.coeff 0 ∈ maximalIdeal 1 ^ (3 * A) ∧
      (P.coeff 1 ∉ maximalIdeal 1 ^ (2 * A + 1) ∨
        P.coeff 0 ∉ maximalIdeal 1 ^ (3 * A + 1)) ∧
      ∃ p : ℂ[X], p.coeff 0 = 0 ∧
        u - Polynomial.aeval f p ∈ weightedOrderIdeal A (4 * A) ∧
        u - Polynomial.aeval f p ∉ weightedOrderIdeal A (4 * A + 1) ∧
        PlaneCurve.pairIdeal f (u - Polynomial.aeval f p) = PlaneCurve.pairIdeal f u ∧
        jacobian f (u - Polynomial.aeval f p) = jacobian f u := by
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
  obtain ⟨s, r, hs, _hsEq, hr, hAr, horder, hsharp, ⟨data⟩⟩ :=
    exists_newton_prepared_weighted_pair_of_squarefree 3 S.length M t (by decide)
      S.length_pos hM P hP hPm hcoeff U u hU hsquarefree huOrdinary hfinite hnumber hdiv
  obtain ⟨j, hj, _hne, hjsharp⟩ := hsharp
  have hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j) := ⟨j, hj, hjsharp⟩
  obtain ⟨hrA, hnoTwo, hMsharp, htsharp, hisharp⟩ :=
    data.cubic_sharp_equalities_of_matched_point_basis hr hP hPm hU horder hdepressed
      hattained c d hcoordinates hroot hprepared hintersection hnumber hAr
  have hjorder : vanishingOrder (P.coeff j) = ((S.length * (3 - j) : ℕ) : ℕ∞) := by
    apply order_eq_of_ramified_order_eq s _ hs
    simpa only [hrA, Nat.mul_assoc] using hjsharp.symm
  have hcubicExact : P.coeff 1 ∉ maximalIdeal 1 ^ (2 * S.length + 1) ∨
      P.coeff 0 ∉ maximalIdeal 1 ^ (3 * S.length + 1) := by
    interval_cases j
    · right
      apply not_mem_pow_succ_of_order_eq_nat
      simpa only [Nat.sub_zero, Nat.mul_comm] using hjorder
    · left
      apply not_mem_pow_succ_of_order_eq_nat
      simpa only [Nat.reduceSub, Nat.mul_comm] using hjorder
    · rw [hdepressed, vanishingOrder_zero] at hjorder
      exact (ENat.natCast_ne_top (S.length * (3 - 2)) hjorder.symm).elim
  have horderOne : ∀ k, k < 3 → ((S.length * (3 - k) : ℕ) : ℕ∞) ≤
      1 • vanishingOrder (P.coeff k) := by
    intro k hk
    simpa only [one_nsmul] using mem_maximalIdeal_one_pow_iff.mp (hcoeff k hk)
  have hfOrdinary : U * firstCoordinatePolynomialEvaluation P ∈ maximalIdeal 2 ^ 3 := by
    have h := (S.straightenedGerm_exact_order 0 S.length_pos).1
    rw [hroot, hprepared, mul_comm] at h
    exact h
  obtain ⟨integerData⟩ := exists_rational_prepared_weighted_pair 1 S.length 3 M t
    (by decide) S.length_pos (by decide) hM P hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds S.length 3 S.length_pos P hcoeff) horderOne
    U u hU hfOrdinary huOrdinary hfinite hnumber hdiv
  have hattainedOne : ∃ k, k < 3 ∧ ((S.length * (3 - k) : ℕ) : ℕ∞) =
      1 • vanishingOrder (P.coeff k) :=
    ⟨j, hj, by simpa only [one_nsmul] using hjorder.symm⟩
  have hfour := integerData.cubic_initial_degree_eq_four_of_matched_point_basis
    S.length_pos hP hPm hU horderOne hdepressed hattainedOne
    c d hcoordinates hroot hprepared hintersection hnumber
    (by change 1 * S.length ≤ S.length; simp only [one_mul, le_refl])
  have hne := integerData.cubic_omega_ne_zero S.length_pos hdepressed hattainedOne
  have hdegree := (integerData.nonzero_omega hne).2.2.1
  rw [hfour, Nat.mul_comm S.length 4] at hdegree
  refine ⟨hnoTwo, hMsharp, htsharp, hisharp, ?_, ?_, hcubicExact,
    integerData.correction, integerData.correction_zero, ?_, ?_,
    integerData.original_ideal, integerData.original_jacobian⟩
  · simpa only [Nat.reduceSub, Nat.mul_comm] using hcoeff 1 (by decide)
  · simpa only [Nat.sub_zero, Nat.mul_comm] using hcoeff 0 (by decide)
  · simpa only [secondCoordinatePowerGerm_one, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply, hdegree] using integerData.second_order
  · simpa only [secondCoordinatePowerGerm_one, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply, hdegree] using integerData.second_not_next

end OnLeConjecture.Analytic.Germ
