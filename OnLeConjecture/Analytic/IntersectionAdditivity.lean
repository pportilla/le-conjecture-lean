/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionBound
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.Analytic.AllOrdersPreparation
public import OnLeConjecture.Analytic.WeightedPrincipalClosure

/-!
# Additivity of analytic local intersection multiplicity

Finite intersection with a product is equivalent to finite intersection
with each factor. For a distinguished monic prepared curve, analytic
division and multiplication of resultants prove additivity of the local
intersection number for arbitrary analytic factors. Linear coordinates
and analytic Weierstrass preparation then remove the preparation
assumption. The zero and unit germs are treated separately.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- Enlarging the pair ideal preserves finiteness of the local algebra. -/
theorem HasFiniteIntersection.of_pairIdeal_le
    {f g h k : Germ 2} (hfinite : HasFiniteIntersection f g)
    (hle : pairIdeal f g ≤ pairIdeal h k) : HasFiniteIntersection h k := by
  obtain ⟨N, hN⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f g).mp hfinite
  exact (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le h k).mpr ⟨N, hN.trans hle⟩

/-- The product of the two pair ideals is contained in the ideal of the
product, with the other generator fixed. -/
theorem pairIdeal_mul_pairIdeal_le (h f g : Germ 2) :
    pairIdeal h f * pairIdeal h g ≤ pairIdeal h (f * g) := by
  rw [pairIdeal, pairIdeal, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  have hh : h ∈ pairIdeal h (f * g) := Ideal.subset_span (by simp)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Ideal.mul_mem_left _ _ hh
  · exact Ideal.mul_mem_right _ _ hh
  · exact Ideal.mul_mem_left _ _ hh
  · exact Ideal.subset_span (by simp)

/-- The finiteness equivalence follows directly from powers of the maximal
ideal. It needs no assumption about a nonzerodivisor in a quotient. -/
theorem hasFiniteIntersection_mul_right_iff (h f g : Germ 2) :
    HasFiniteIntersection h (f * g) ↔ HasFiniteIntersection h f ∧ HasFiniteIntersection h g := by
  constructor
  · intro hfinite
    have hhf : h ∈ pairIdeal h f := Ideal.subset_span (by simp)
    have hff : f ∈ pairIdeal h f := Ideal.subset_span (by simp)
    have hhg : h ∈ pairIdeal h g := Ideal.subset_span (by simp)
    have hgg : g ∈ pairIdeal h g := Ideal.subset_span (by simp)
    constructor
    · apply hfinite.of_pairIdeal_le
      rw [pairIdeal, Ideal.span_le]
      intro q hq
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq :
        q = h ∨ q = f * g) with rfl | rfl
      · exact hhf
      · exact Ideal.mul_mem_right _ _ hff
    · apply hfinite.of_pairIdeal_le
      rw [pairIdeal, Ideal.span_le]
      intro q hq
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq :
        q = h ∨ q = f * g) with rfl | rfl
      · exact hhg
      · exact Ideal.mul_mem_left _ _ hgg
  · rintro ⟨hf, hg⟩
    obtain ⟨N, hN⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le h f).mp hf
    obtain ⟨M, hM⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le h g).mp hg
    apply (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le h (f * g)).mpr
    refine ⟨N + M, ?_⟩
    rw [pow_add]
    exact (mul_le_mul' hN hM).trans (pairIdeal_mul_pairIdeal_le h f g)

/-- The same finiteness equivalence with the product in the first
generator. -/
theorem hasFiniteIntersection_mul_left_iff (f g h : Germ 2) :
    HasFiniteIntersection (f * g) h ↔ HasFiniteIntersection f h ∧ HasFiniteIntersection g h := by
  simpa only [hasFiniteIntersection_comm (f * g) h, hasFiniteIntersection_comm f h,
    hasFiniteIntersection_comm g h] using hasFiniteIntersection_mul_right_iff h f g

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Monicity removes the extra degree padding in the product formula for
resultants, including a zero polynomial factor. -/
theorem resultant_mul_right_of_monic (P R S : Polynomial (Germ 1)) (hP : P.Monic) :
    P.resultant (R * S) = P.resultant R * P.resultant S := by
  have hdeg : (R * S).natDegree ≤ R.natDegree + S.natDegree := natDegree_mul_le
  have hpadding := resultant_add_right_deg P (R * S) P.natDegree (R * S).natDegree
    (R.natDegree + S.natDegree - (R * S).natDegree) le_rfl
  simp only [Nat.add_sub_of_le hdeg, hP.coeff_natDegree, one_pow, one_mul] at hpadding
  exact hpadding.symm.trans (resultant_mul_right P R S P.natDegree le_rfl)

private theorem exists_analytic_polynomial_remainder
    (d : ℕ) (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = d + 1)
    (hdist : ∀ j, j < d + 1 → P.coeff j ∈ maximalIdeal 1) (f : Germ 2) :
    ∃ R : Polynomial (Germ 1), ∃ q : Germ 2,
      f = firstCoordinatePolynomialEvaluation P * q + firstCoordinatePolynomialEvaluation R := by
  obtain ⟨R, hR⟩ := exists_polynomial_mod_distinguished d P hP hPm hdist f
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hR
  exact ⟨R, q, by rw [← hq]; ring⟩

/-- Analytic intersection with a positive-degree distinguished monic
Weierstrass polynomial is additive in arbitrary analytic factors. -/
theorem intersectionMultiplicity_prepared_mul_right
    (d : ℕ) (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = d + 1)
    (hdist : ∀ j, j < d + 1 → P.coeff j ∈ maximalIdeal 1) (f g : Germ 2)
    (hf : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) f)
    (hg : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) g)
    (hfg : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) (f * g)) :
    PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) (f * g) hfg =
      PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) f hf +
        PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) g hg := by
  obtain ⟨R, q, hR⟩ := exists_analytic_polynomial_remainder d P hP hPm hdist f
  obtain ⟨S, v, hS⟩ := exists_analytic_polynomial_remainder d P hP hPm hdist g
  have hproduct : f * g = firstCoordinatePolynomialEvaluation P *
      (firstCoordinatePolynomialEvaluation P * q * v +
        q * firstCoordinatePolynomialEvaluation S + firstCoordinatePolynomialEvaluation R * v) +
          firstCoordinatePolynomialEvaluation (R * S) := by
    rw [hR, hS]
    simp only [firstCoordinatePolynomialEvaluation, eval₂_mul]
    ring
  obtain ⟨hfEq, hfRes⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    (d + 1) (by omega) P R hP hPm hdist f q hR hf
  obtain ⟨hgEq, hgRes⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    (d + 1) (by omega) P S hP hPm hdist g v hS hg
  obtain ⟨hfgEq, _⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    (d + 1) (by omega) P (R * S) hP hPm hdist (f * g) _ hproduct hfg
  rw [hfEq, hgEq, hfgEq, resultant_mul_right_of_monic P R S hP, vanishingOrder_mul,
    ENat.toNat_add (vanishingOrder_eq_top_iff.not.mpr hfRes)
      (vanishingOrder_eq_top_iff.not.mpr hgRes)]

/-- The preparation unit remains in the curve germ in the additivity
formula. -/
theorem intersectionMultiplicity_unit_prepared_mul_right
    (d : ℕ) (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = d + 1)
    (hdist : ∀ j, j < d + 1 → P.coeff j ∈ maximalIdeal 1) (U f g : Germ 2) (hU : IsUnit U)
    (hf : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) f)
    (hg : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) g)
    (hfg : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) (f * g)) :
    PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) (f * g) hfg =
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) f hf +
        PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) g hg := by
  have hf' := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hU).mp hf
  have hg' := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hU).mp hg
  have hfg' := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hU).mp hfg
  rw [PlaneCurve.intersectionMultiplicity_unit_mul_left _ _ _ hU hfg hfg',
    PlaneCurve.intersectionMultiplicity_unit_mul_left _ _ _ hU hf hf',
    PlaneCurve.intersectionMultiplicity_unit_mul_left _ _ _ hU hg hg']
  exact intersectionMultiplicity_prepared_mul_right d P hP hPm hdist f g hf' hg' hfg'

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- A unit generator makes the local intersection algebra zero. -/
theorem intersectionMultiplicity_eq_zero_of_isUnit_left
    (h f : Germ 2) (hh : IsUnit h) (hfinite : HasFiniteIntersection h f) :
    intersectionMultiplicity h f hfinite = 0 := by
  have htop : pairIdeal h f = ⊤ :=
    (pairIdeal h f).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) hh
  change Module.finrank ℂ _ = 0
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

/-- A finite intersection with the zero germ forces the other germ to be
a unit. The principal ideal theorem in the two-dimensional analytic local
ring supplies the needed exclusion. -/
theorem isUnit_of_hasFiniteIntersection_zero_right
    (f : Germ 2) (hfinite : HasFiniteIntersection f 0) : IsUnit f := by
  by_contra hunit
  have hf : f ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    by_contra hvalue
    exact hunit (Germ.isUnit_of_valueRingHom_ne_zero hvalue)
  have hexclusion := Germ.not_mem_span_singleton_of_pair_finite_colength f 0 hf
    ((hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f 0).mp hfinite)
  exact hexclusion (Ideal.zero_mem _)

/-- Analytic coordinate preparation reduces additivity for a nonzero
curve germ to the proved resultant formula. -/
theorem intersectionMultiplicity_mul_right_of_ne_zero
    (h f g : Germ 2) (hh : h ≠ 0)
    (hf : HasFiniteIntersection h f) (hg : HasFiniteIntersection h g)
    (hfg : HasFiniteIntersection h (f * g)) :
    intersectionMultiplicity h (f * g) hfg =
      intersectionMultiplicity h f hf + intersectionMultiplicity h g hg := by
  by_cases hunit : IsUnit h
  · rw [intersectionMultiplicity_eq_zero_of_isUnit_left h _ hunit hfg,
      intersectionMultiplicity_eq_zero_of_isUnit_left h _ hunit hf,
      intersectionMultiplicity_eq_zero_of_isUnit_left h _ hunit hg]
  obtain ⟨e, n, hregular⟩ := Germ.exists_linear_equiv_regularInFirstCoordinate hh
  have hn : 0 < n := by
    by_contra hn
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hunitTransformed : IsUnit (e.forward.pullbackRingHom h) := by
      simpa using Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
    exact hunit ((MulEquiv.isUnit_map e.pullbackRingEquiv.toMulEquiv).mp hunitTransformed)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨P, U, hP, hPm, hdist, hU, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hregular
  have hfactor' : e.pullbackAlgEquiv h = U * Germ.firstCoordinatePolynomialEvaluation P := by
    simpa only [PointedEquivGerm.pullbackAlgEquiv_apply,
      PointedEquivGerm.pullbackRingEquiv_apply, mul_comm] using hfactor
  have hf' : HasFiniteIntersection (U * Germ.firstCoordinatePolynomialEvaluation P)
      (e.pullbackAlgEquiv f) := by
    simpa only [hfactor'] using hf.pullback e
  have hg' : HasFiniteIntersection (U * Germ.firstCoordinatePolynomialEvaluation P)
      (e.pullbackAlgEquiv g) := by
    simpa only [hfactor'] using hg.pullback e
  have hfg' : HasFiniteIntersection (U * Germ.firstCoordinatePolynomialEvaluation P)
      (e.pullbackAlgEquiv f * e.pullbackAlgEquiv g) := by
    simpa only [hfactor', map_mul] using hfg.pullback e
  have hformula := Germ.intersectionMultiplicity_unit_prepared_mul_right
    d P hP hPm hdist U (e.pullbackAlgEquiv f) (e.pullbackAlgEquiv g) hU hf' hg' hfg'
  rw [intersectionMultiplicity_pullback e hf, intersectionMultiplicity_pullback e hg,
    intersectionMultiplicity_pullback e hfg]
  simpa only [hfactor', map_mul] using hformula

/-- Local intersection multiplicity is additive in a product of arbitrary
plane analytic germs. All finite proofs may be supplied independently. -/
theorem intersectionMultiplicity_mul_right
    (h f g : Germ 2)
    (hf : HasFiniteIntersection h f) (hg : HasFiniteIntersection h g)
    (hfg : HasFiniteIntersection h (f * g)) :
    intersectionMultiplicity h (f * g) hfg =
      intersectionMultiplicity h f hf + intersectionMultiplicity h g hg := by
  by_cases hh : h = 0
  · subst h
    have hfu := isUnit_of_hasFiniteIntersection_zero_right f
      ((hasFiniteIntersection_comm 0 f).mp hf)
    have hgu := isUnit_of_hasFiniteIntersection_zero_right g
      ((hasFiniteIntersection_comm 0 g).mp hg)
    rw [intersectionMultiplicity_comm 0 _ hfg,
      intersectionMultiplicity_comm 0 _ hf, intersectionMultiplicity_comm 0 _ hg,
      intersectionMultiplicity_eq_zero_of_isUnit_left _ _ (hfu.mul hgu),
      intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hfu,
      intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hgu]
  · exact intersectionMultiplicity_mul_right_of_ne_zero h f g hh hf hg hfg

/-- Additivity with the product in the first generator. -/
theorem intersectionMultiplicity_mul_left
    (f g h : Germ 2)
    (hf : HasFiniteIntersection f h) (hg : HasFiniteIntersection g h)
    (hfg : HasFiniteIntersection (f * g) h) :
    intersectionMultiplicity (f * g) h hfg =
      intersectionMultiplicity f h hf + intersectionMultiplicity g h hg := by
  rw [intersectionMultiplicity_comm _ _ hfg, intersectionMultiplicity_comm _ _ hf,
    intersectionMultiplicity_comm _ _ hg]
  exact intersectionMultiplicity_mul_right h f g _ _ _

end OnLeConjecture.PlaneCurve
