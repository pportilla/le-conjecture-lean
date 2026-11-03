/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedWeierstrassRemainder
public import OnLeConjecture.Analytic.WeightedPolynomialScaling
public import OnLeConjecture.Analytic.ScaledResultantOrder
public import OnLeConjecture.Analytic.IntersectionResultant
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# Weighted lower bounds for analytic intersection multiplicity

Analytic Weierstrass division supplies a polynomial remainder with the
required weighted coefficient orders. Coefficientwise division constructs
the two scaled polynomials, and the resultant formula then proves the
intersection lower bound for the original analytic germs.

The strict bound is proved when the residual polynomials of the constructed
scaling have a common root. Identifying that condition with a particular
weighted initial form of the original second germ is not assumed here.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- Replacing a germ by a remainder modulo the first generator preserves
the intersection ideal. -/
theorem pairIdeal_eq_of_remainder
    (g H R q : Germ 2) (hdivision : H = g * q + R) :
    pairIdeal g H = pairIdeal g R := by
  have hrem : H - g * q = R := by rw [hdivision]; ring
  rw [← hrem]
  exact (pairIdeal_sub_mul_right g H q).symm

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Analytic division and coefficientwise scaling data, including the
identities linking every polynomial to the original analytic germs. -/
structure WeightedWeierstrassScaling
    (P : Polynomial (Germ 1)) (H : Germ 2) (r L m : ℕ) where
  quotient : Germ 2
  remainder : Polynomial (Germ 1)
  firstScaled : Polynomial (Germ 1)
  secondScaled : Polynomial (Germ 1)
  division : H = firstCoordinatePolynomialEvaluation P * quotient +
    firstCoordinatePolynomialEvaluation remainder
  remainder_degree : remainder.degree < (m : ℕ)
  first_monic : firstScaled.Monic
  first_degree : firstScaled.natDegree = m
  second_degree : secondScaled.natDegree = remainder.natDegree
  second_weight : r * secondScaled.natDegree ≤ L
  first_scaling : P = firstScaled.scaleRoots (coordinate (0 : Fin 1) ^ r)
  second_scaling : remainder =
    C (coordinate (0 : Fin 1) ^ (L - r * secondScaled.natDegree)) *
      secondScaled.scaleRoots (coordinate (0 : Fin 1) ^ r)
  first_coeff : ∀ i, P.coeff i =
    coordinate (0 : Fin 1) ^ (r * (m - i)) * firstScaled.coeff i
  second_coeff : ∀ i, remainder.coeff i =
    coordinate (0 : Fin 1) ^ (L - r * i) * secondScaled.coeff i

/-- Weighted analytic membership constructs the remainder and both scaled
polynomials. No analytic remainder or scaling identity is an input. -/
theorem exists_weightedWeierstrassScaling
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m) (hL : r * m ≤ L)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (hH : H ∈ weightedOrderIdeal r L) :
    Nonempty (WeightedWeierstrassScaling P H r L m) := by
  obtain ⟨q, R, hdivision, hRdegree, hRcoeff⟩ :=
    exists_weightedWeierstrassRemainder r L m hr hm P hP hPm hcoeff H hH
  have hRnat : R.natDegree < m := by
    by_cases hzero : R = 0
    · simpa [hzero] using hm
    · exact (natDegree_lt_iff_degree_lt hzero).mpr hRdegree
  have hcoeffAll : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)) := by
    intro i
    by_cases hi : i < m
    · exact hcoeff i hi
    · simp [Nat.sub_eq_zero_of_le (show m ≤ i by omega)]
  obtain ⟨A, hAmonic, hAm, hAscale, hAcoeff⟩ :=
    exists_monic_weighted_polynomial_scaling P m r hP hPm hcoeffAll
  have hRweight : r * R.natDegree ≤ L :=
    (Nat.mul_le_mul_left r (Nat.le_of_lt hRnat)).trans hL
  obtain ⟨B, hBdegree, hBscale, hBcoeff⟩ :=
    exists_weighted_polynomial_scaling R r L hRweight hRcoeff
  exact ⟨{
    quotient := q
    remainder := R
    firstScaled := A
    secondScaled := B
    division := hdivision
    remainder_degree := hRdegree
    first_monic := hAmonic
    first_degree := hAm
    second_degree := hBdegree
    second_weight := by simpa [hBdegree] using hRweight
    first_scaling := hAscale
    second_scaling := hBscale
    first_coeff := hAcoeff
    second_coeff := hBcoeff }⟩

/-- Analytic division identifies the intersection multiplicity with the
order of the actual remainder resultant, which is nonzero. -/
theorem intersectionMultiplicity_eq_remainder_resultant_order
    (m : ℕ) (hm : 0 < m) (P R : Polynomial (Germ 1))
    (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1)
    (H q : Germ 2)
    (hdivision : H = firstCoordinatePolynomialEvaluation P * q +
      firstCoordinatePolynomialEvaluation R)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) H hfinite =
      (vanishingOrder (P.resultant R)).toNat ∧ P.resultant R ≠ 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hideal := PlaneCurve.pairIdeal_eq_of_remainder
    (firstCoordinatePolynomialEvaluation P) H (firstCoordinatePolynomialEvaluation R) q hdivision
  have hfiniteR := hfinite.of_pairIdeal_eq hideal
  refine ⟨?_, resultant_ne_zero_of_hasFiniteIntersection d P R hP hPm hdist hfiniteR⟩
  rw [PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfinite hfiniteR hideal]
  exact intersectionMultiplicity_eq_resultant_order d P R hP hPm hdist hfiniteR

/-- The constructed weighted scaling gives an exact formula in extended
natural numbers for the original analytic intersection multiplicity. -/
theorem WeightedWeierstrassScaling.intersectionMultiplicity_cast_eq
    {P : Polynomial (Germ 1)} {H : Germ 2} {r L m : ℕ}
    (data : WeightedWeierstrassScaling P H r L m)
    (hr : 0 < r) (hm : 0 < m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    (PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite : ℕ∞) =
        ((m * L : ℕ) : ℕ∞) + vanishingOrder (data.firstScaled.resultant data.secondScaled) := by
  have hP : P.Monic := by
    rw [data.first_scaling]
    exact (monic_scaleRoots_iff _).mpr data.first_monic
  have hPm : P.natDegree = m := by
    rw [data.first_scaling, natDegree_scaleRoots, data.first_degree]
  obtain ⟨hinter, hnonzero⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    m hm P data.remainder hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff)
    H data.quotient data.division hfinite
  rw [hinter, ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hnonzero)]
  have hscale := vanishingOrder_resultant_weighted_scaleRoots
    data.firstScaled data.secondScaled r L data.second_weight
  rw [← data.first_scaling, ← data.second_scaling] at hscale
  have hmult : L * data.firstScaled.natDegree = m * L := by
    rw [data.first_degree, Nat.mul_comm]
  rwa [hmult] at hscale

/-- Weighted order of an arbitrary analytic second germ gives the weak
intersection bound with a distinguished monic first polynomial. -/
theorem weighted_intersection_lower_bound
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m) (hL : r * m ≤ L)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (hH : H ∈ weightedOrderIdeal r L)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    m * L ≤ PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite := by
  obtain ⟨data⟩ := exists_weightedWeierstrassScaling r L m hr hm hL P hP hPm hcoeff H hH
  have hcast := data.intersectionMultiplicity_cast_eq hr hm hcoeff hfinite
  have hbound : ((m * L : ℕ) : ℕ∞) ≤
      (PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation P) H hfinite : ℕ∞) := by
    rw [hcast]
    exact le_self_add
  exact_mod_cast hbound

/-- A common root of the residual polynomials of an actual weighted
Weierstrass scaling forces the strict analytic intersection bound. -/
theorem WeightedWeierstrassScaling.strict_intersection_lower_bound
    {P : Polynomial (Germ 1)} {H : Germ 2} {r L m : ℕ}
    (data : WeightedWeierstrassScaling P H r L m)
    (hr : 0 < r) (hm : 0 < m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H)
    (z : ℂ)
    (hfirstRoot : (data.firstScaled.map (valueRingHom 1)).IsRoot z)
    (hsecondRoot : (data.secondScaled.map (valueRingHom 1)).IsRoot z) :
    m * L < PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite := by
  have hstrict := mul_lt_vanishingOrder_resultant_weighted_scaleRoots
    data.firstScaled data.secondScaled r L data.second_weight data.first_monic z
    hfirstRoot hsecondRoot
  rw [vanishingOrder_resultant_weighted_scaleRoots _ _ _ _ data.second_weight] at hstrict
  have hmult : L * data.firstScaled.natDegree = m * L := by
    rw [data.first_degree, Nat.mul_comm]
  rw [hmult] at hstrict
  have hcast := data.intersectionMultiplicity_cast_eq hr hm hcoeff hfinite
  have hbound : ((m * L : ℕ) : ℕ∞) <
      (PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation P) H hfinite : ℕ∞) := by
    rw [hcast]
    exact hstrict
  exact_mod_cast hbound

end OnLeConjecture.Analytic.Germ
