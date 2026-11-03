/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolynomial
public import OnLeConjecture.Analytic.WeightedParameterTranslation
public import OnLeConjecture.Analytic.StrictBlowupFiniteIntersection
public import OnLeConjecture.Analytic.IntersectionAdditivity

/-!
# The first blowup recurrence for a finite analytic intersection

Root scaling of the two prepared polynomials extracts the product of the
ordinary orders from their resultant. Analytic factorization over all
residue roots identifies the remaining order with local intersections of
the actual chart transforms. Preparation units remain in the equations.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic

theorem pairIdeal_unit_mul_both (U V f g : Germ 2) (hU : IsUnit U) (hV : IsUnit V) :
    pairIdeal (U * f) (V * g) = pairIdeal f g := by
  rw [pairIdeal_unit_mul_left U f _ hU, pairIdeal_comm f (V * g),
    pairIdeal_unit_mul_left V g f hV, pairIdeal_comm g f]

theorem intersectionMultiplicity_eq_zero_of_isUnit_right
    (f g : Germ 2) (hg : IsUnit g) (hfinite : HasFiniteIntersection f g) :
    intersectionMultiplicity f g hfinite = 0 := by
  rw [intersectionMultiplicity_comm]
  exact intersectionMultiplicity_eq_zero_of_isUnit_left g f hg _

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- The general prepared-pair recurrence. All residue factors and local
finite intersections are constructed from the original finite pair. -/
theorem exists_prepared_pointBlowup_intersection_recurrence
    (m n : ℕ) (hm : 0 < m) (P Q : Polynomial (Germ 1))
    (hP : P.Monic) (hQ : Q.Monic) (hPm : P.natDegree = m) (hQn : Q.natDegree = n)
    (hPcoeff : ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (m - j))
    (hQcoeff : ∀ j, Q.coeff j ∈ maximalIdeal 1 ^ (n - j))
    (U V : Germ 2) (hU : IsUnit U) (hV : IsUnit V)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q)) :
    ∃ A B : Polynomial (Germ 1),
      A.Monic ∧ A.natDegree = m ∧ B.Monic ∧ B.natDegree = n ∧
      P = A.scaleRoots (coordinate (0 : Fin 1)) ∧
      Q = B.scaleRoots (coordinate (0 : Fin 1)) ∧
      (∀ c : ℂ, (pointBlowupChartGerm c).pullbackRingHom
          (U * firstCoordinatePolynomialEvaluation P) = coordinate (1 : Fin 2) ^ m *
        ((pointBlowupChartGerm c).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A c))) ∧
      (∀ c : ℂ, (pointBlowupChartGerm c).pullbackRingHom
          (V * firstCoordinatePolynomialEvaluation Q) = coordinate (1 : Fin 2) ^ n *
        ((pointBlowupChartGerm c).pullbackRingHom V *
          firstCoordinatePolynomialEvaluation (rootTranslation B c))) ∧
      ∃ hf : ∀ c : (A.map (valueRingHom 1)).roots.toFinset,
        PlaneCurve.HasFiniteIntersection
          ((pointBlowupChartGerm c).pullbackRingHom U *
            firstCoordinatePolynomialEvaluation (rootTranslation A c))
          ((pointBlowupChartGerm c).pullbackRingHom V *
            firstCoordinatePolynomialEvaluation (rootTranslation B c)),
        PlaneCurve.intersectionMultiplicity
          (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q)
          hfinite = m * n + ∑ c : (A.map (valueRingHom 1)).roots.toFinset,
            PlaneCurve.intersectionMultiplicity
              ((pointBlowupChartGerm c).pullbackRingHom U *
                firstCoordinatePolynomialEvaluation (rootTranslation A c))
              ((pointBlowupChartGerm c).pullbackRingHom V *
                firstCoordinatePolynomialEvaluation (rootTranslation B c)) (hf c) := by
  obtain ⟨A, hA, hAm, hscaleP, _⟩ := exists_monic_weighted_polynomial_scaling P m 1
    hP hPm (by simpa only [one_mul] using hPcoeff)
  obtain ⟨B, hB, hBn, hscaleQ, _⟩ := exists_monic_weighted_polynomial_scaling Q n 1
    hQ hQn (by simpa only [one_mul] using hQcoeff)
  simp only [pow_one] at hscaleP hscaleQ
  have hdist : ∀ j, j < (m - 1) + 1 → P.coeff j ∈ maximalIdeal 1 := by
    simpa only [Nat.sub_add_cancel hm] using
      coeff_mem_maximalIdeal_of_weighted_bounds 1 m (by decide) P
        (fun j _ ↦ by simpa only [one_mul] using hPcoeff j)
  have hdegree : P.natDegree = (m - 1) + 1 := by
    rw [hPm, Nat.sub_add_cancel hm]
  have hideal := PlaneCurve.pairIdeal_unit_mul_both U V
    (firstCoordinatePolynomialEvaluation P) (firstCoordinatePolynomialEvaluation Q) hU hV
  have hfPQ : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q) := by
    unfold PlaneCurve.HasFiniteIntersection
    rw [← hideal]
    exact hfinite
  have hPQresultant := resultant_ne_zero_of_hasFiniteIntersection (m - 1) P Q
    hP hdegree hdist hfPQ
  have hresultant : P.resultant Q =
      coordinate (0 : Fin 1) ^ (m * n) * A.resultant B := by
    rw [hscaleP, hscaleQ, resultant_scaleRoots, hAm, hBn]
  have hABresultant : A.resultant B ≠ 0 :=
    (mul_ne_zero_iff.mp (hresultant ▸ hPQresultant)).2
  have hinter : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q)
      hfinite = m * n + (vanishingOrder (A.resultant B)).toNat := by
    have hpair : PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q)
        hfinite = PlaneCurve.intersectionMultiplicity
          (firstCoordinatePolynomialEvaluation P) (firstCoordinatePolynomialEvaluation Q) hfPQ := by
      change Module.finrank ℂ _ = Module.finrank ℂ _
      rw [hideal]
    rw [hpair, intersectionMultiplicity_eq_resultant_order (m - 1) P Q hP hdegree hdist hfPQ,
      hresultant, vanishingOrder_mul, vanishingOrder_coordinate_pow,
      ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hABresultant),
      ENat.toNat_natCast]
  have htransformP (c : ℂ) : (pointBlowupChartGerm c).pullbackRingHom
      (U * firstCoordinatePolynomialEvaluation P) = coordinate (1 : Fin 2) ^ m *
        ((pointBlowupChartGerm c).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A c)) := by
    rw [map_mul, hscaleP, pointBlowupChart_pullback_scaled_polynomial, hAm]
    ring
  have htransformQ (c : ℂ) : (pointBlowupChartGerm c).pullbackRingHom
      (V * firstCoordinatePolynomialEvaluation Q) = coordinate (1 : Fin 2) ^ n *
        ((pointBlowupChartGerm c).pullbackRingHom V *
          firstCoordinatePolynomialEvaluation (rootTranslation B c)) := by
    rw [map_mul, hscaleQ, pointBlowupChart_pullback_scaled_polynomial, hBn]
    ring
  obtain ⟨hfAB, hiAB⟩ := exists_resultant_order_eq_sum_translated_intersections A B hA hABresultant
  have hlocalIdeal (c : ℂ) : PlaneCurve.pairIdeal
      ((pointBlowupChartGerm c).pullbackRingHom U *
        firstCoordinatePolynomialEvaluation (rootTranslation A c))
      ((pointBlowupChartGerm c).pullbackRingHom V *
        firstCoordinatePolynomialEvaluation (rootTranslation B c)) =
      PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation A c))
        (firstCoordinatePolynomialEvaluation (rootTranslation B c)) :=
    PlaneCurve.pairIdeal_unit_mul_both _ _ _ _ (hU.map _) (hV.map _)
  have hf (c : (A.map (valueRingHom 1)).roots.toFinset) : PlaneCurve.HasFiniteIntersection
      ((pointBlowupChartGerm c).pullbackRingHom U *
        firstCoordinatePolynomialEvaluation (rootTranslation A c))
      ((pointBlowupChartGerm c).pullbackRingHom V *
        firstCoordinatePolynomialEvaluation (rootTranslation B c)) := by
    unfold PlaneCurve.HasFiniteIntersection
    rw [hlocalIdeal]
    exact hfAB c
  refine ⟨A, B, hA, hAm, hB, hBn, hscaleP, hscaleQ, htransformP, htransformQ, hf, ?_⟩
  rw [hinter, hiAB]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [hlocalIdeal]

/-- The first-blowup intersection recurrence for original analytic
equations whose first-axis orders equal their ordinary orders. No
preparation, residue polynomial, factorization, or local finiteness
hypothesis is required in addition to the original finite intersection. -/
theorem exists_pointBlowup_intersection_recurrence_of_regular
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfregular : IsRegularInFirstCoordinateOfOrder f m)
    (hgregular : IsRegularInFirstCoordinateOfOrder g n)
    (hfinite : PlaneCurve.HasFiniteIntersection f g) :
    ∃ s : Finset ℂ,
      (∀ c, c ∈ s ↔ ¬ IsUnit (pointBlowupTransform c m f hf)) ∧
      ∃ hlocal : ∀ c : ℂ, PlaneCurve.HasFiniteIntersection
        (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg),
        PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ c : s,
          PlaneCurve.intersectionMultiplicity
            (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg) (hlocal c) ∧
        IsUnit (pointBlowupTransform 0 m
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow hf)) := by
  classical
  obtain ⟨P, U, hP, hPm, hU, hfEq, hPcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm f hfregular
      (by simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf)
  obtain ⟨Q, V, hQ, hQn, hV, hgEq, hQcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 n hn g hgregular
      (by simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hg)
  rw [mul_comm] at hfEq hgEq
  have hfPQ : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q) := by
    rwa [← hfEq, ← hgEq]
  obtain ⟨A, B, hA, _hAm, _hB, _hBn, _hscaleP, _hscaleQ, htransP, htransQ, hlocalAB, hi⟩ :=
    exists_prepared_pointBlowup_intersection_recurrence m n hm P Q hP hQ hPm hQn
      (by simpa only [one_mul] using hPcoeff) (by simpa only [one_mul] using hQcoeff)
      U V hU hV hfPQ
  let s : Finset ℂ := (A.map (valueRingHom 1)).roots.toFinset
  have hlocalF (c : ℂ) : pointBlowupTransform c m f hf =
      (pointBlowupChartGerm c).pullbackRingHom U *
        firstCoordinatePolynomialEvaluation (rootTranslation A c) := by
    apply pointBlowupTransform_unique c m f _ _ (pointBlowupTransform_factor _ _ _ _)
    simpa only [← hfEq] using htransP c
  have hlocalG (c : ℂ) : pointBlowupTransform c n g hg =
      (pointBlowupChartGerm c).pullbackRingHom V *
        firstCoordinatePolynomialEvaluation (rootTranslation B c) := by
    apply pointBlowupTransform_unique c n g _ _ (pointBlowupTransform_factor _ _ _ _)
    simpa only [← hgEq] using htransQ c
  have hlocal (c : ℂ) : PlaneCurve.HasFiniteIntersection
      (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg) :=
    hasFiniteIntersection_pointBlowupTransforms c m n f g hf hg
      (not_mem_succ_maximalIdeal_pow_of_first_regular m f hfregular) hfinite
  refine ⟨s, ?_, hlocal, ?_, ?_⟩
  · intro c
    rw [hlocalF, IsUnit.mul_iff]
    have hu : IsUnit ((pointBlowupChartGerm c).pullbackRingHom U) := hU.map _
    simp only [hu, true_and, isUnit_iff_valueRingHom_ne_zero,
      value_firstCoordinatePolynomialEvaluation_rootTranslation, not_not]
    exact (Multiset.mem_toFinset.trans (mem_roots (hA.map (valueRingHom 1)).ne_zero))
  · calc
      PlaneCurve.intersectionMultiplicity f g hfinite =
          PlaneCurve.intersectionMultiplicity
            (U * firstCoordinatePolynomialEvaluation P) (V * firstCoordinatePolynomialEvaluation Q)
            hfPQ := by
              change Module.finrank ℂ _ = Module.finrank ℂ _
              rw [hfEq, hgEq]
      _ = m * n + ∑ c : s, PlaneCurve.intersectionMultiplicity
            ((pointBlowupChartGerm c).pullbackRingHom U *
              firstCoordinatePolynomialEvaluation (rootTranslation A c))
            ((pointBlowupChartGerm c).pullbackRingHom V *
              firstCoordinatePolynomialEvaluation (rootTranslation B c)) (hlocalAB c) := hi
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        change Module.finrank ℂ _ = Module.finrank ℂ _
        rw [hlocalF, hlocalG]
  · exact complementaryBlowupTransform_isUnit_of_regular m f _ hfregular
      (pointBlowupTransform_factor _ _ _ _)

/-- The intersection recurrence may be indexed by any finite set covering
the common nonunit strict transforms. A center at which either equation
is a unit has zero local intersection and need not be recorded. -/
theorem pointBlowup_intersection_recurrence_of_common_zero_cover
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfregular : IsRegularInFirstCoordinateOfOrder f m)
    (hgregular : IsRegularInFirstCoordinateOfOrder g n)
    (hfinite : PlaneCurve.HasFiniteIntersection f g) (s : Finset ℂ)
    (hcover : ∀ c, ¬ IsUnit (pointBlowupTransform c m f hf) →
      ¬ IsUnit (pointBlowupTransform c n g hg) → c ∈ s) :
    ∃ hlocal : ∀ c : ℂ, PlaneCurve.HasFiniteIntersection
      (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg),
      PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ c ∈ s,
        PlaneCurve.intersectionMultiplicity
          (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg) (hlocal c) := by
  classical
  obtain ⟨t, ht, hlocal, hi, _⟩ :=
    exists_pointBlowup_intersection_recurrence_of_regular
      m n hm hn f g hf hg hfregular hgregular hfinite
  let I : ℂ → ℕ := fun c ↦ PlaneCurve.intersectionMultiplicity
    (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg) (hlocal c)
  have hzeroT (c : ℂ) (hc : c ∉ t) : I c = 0 := by
    have hunit : IsUnit (pointBlowupTransform c m f hf) := by
      by_contra hnot
      exact hc ((ht c).mpr hnot)
    exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hunit _
  have hzeroS (c : ℂ) (hc : c ∉ s) : I c = 0 := by
    by_cases hunit : IsUnit (pointBlowupTransform c m f hf)
    · exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hunit _
    · have hgunit : IsUnit (pointBlowupTransform c n g hg) := by
        by_contra hnot
        exact hc (hcover c hunit hnot)
      exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_right _ _ hgunit _
  have hsumT : (∑ c ∈ t, I c) = ∑ c ∈ t ∪ s, I c :=
    Finset.sum_subset Finset.subset_union_left (fun c _ hc ↦ hzeroT c hc)
  have hsumS : (∑ c ∈ s, I c) = ∑ c ∈ t ∪ s, I c :=
    Finset.sum_subset Finset.subset_union_right (fun c _ hc ↦ hzeroS c hc)
  refine ⟨hlocal, ?_⟩
  change PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ c ∈ s, I c
  change PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ c : t, I c at hi
  rw [Finset.sum_coe_sort t I] at hi
  rw [hi, hsumT, hsumS]

/-- A separated finite list covering the simultaneous weak zeros indexes
the intersection recurrence. -/
theorem pointBlowup_intersection_recurrence_of_indexed_common_zero_cover
    {κ : Type*} (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfregular : IsRegularInFirstCoordinateOfOrder f m)
    (hgregular : IsRegularInFirstCoordinateOfOrder g n)
    (hfinite : PlaneCurve.HasFiniteIntersection f g) (s : Finset κ)
    (center : κ → ℂ) (hinj : Set.InjOn center s)
    (hcover : ∀ c, ¬ IsUnit (pointBlowupTransform c m f hf) →
      ¬ IsUnit (pointBlowupTransform c n g hg) → ∃ i ∈ s, center i = c) :
    ∃ hlocal : ∀ c : ℂ, PlaneCurve.HasFiniteIntersection
      (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg),
      PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ i ∈ s,
        PlaneCurve.intersectionMultiplicity
          (pointBlowupTransform (center i) m f hf) (pointBlowupTransform (center i) n g hg)
          (hlocal (center i)) := by
  classical
  obtain ⟨hlocal, hi⟩ := pointBlowup_intersection_recurrence_of_common_zero_cover
    m n hm hn f g hf hg hfregular hgregular hfinite (s.image center)
      (fun c hc hd ↦ Finset.mem_image.mpr (hcover c hc hd))
  refine ⟨hlocal, ?_⟩
  rw [hi, Finset.sum_image hinj]

end OnLeConjecture.Analytic.Germ
