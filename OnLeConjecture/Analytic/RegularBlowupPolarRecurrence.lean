/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveReducedBlowupBranchCount
public import OnLeConjecture.Analytic.PlaneFiniteColengthCriterion
public import OnLeConjecture.Analytic.PointBlowupPolarIntersection

/-!
# Polar conservation for a reduced transverse equation

Squarefreeness and transverse regularity imply finiteness of the first
partial polar. Analytic preparation then gives the polar intersection
recurrence for the strict transforms of the original equation.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- A reduced equation whose first-axis order equals its ordinary order
has finite intersection with its first partial derivative. -/
theorem finite_first_partial_polar_of_squarefree_regular
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f) :
    PlaneCurve.HasFiniteIntersection f (partialDerivative (0 : Fin 2) f) := by
  have hnext := not_mem_succ_maximalIdeal_pow_of_first_regular m f hregular
  have hfne : f ≠ 0 := by
    intro hz
    exact hnext (hz ▸ (maximalIdeal 2 ^ (m + 1)).zero_mem)
  apply PlaneCurve.hasFiniteIntersection_of_no_common_prime_divisor f _ hfne
  rintro p hp ⟨hpf, hpd⟩
  obtain ⟨k, hpk, hpkregular⟩ :=
    exists_exact_regular_order_of_dvd m f p hf hregular hp.ne_zero hpf
  obtain ⟨q, hq⟩ := hpf
  have hpq : ¬ p ∣ q := by
    rintro ⟨r, hr⟩
    apply hp.irreducible.not_isUnit
    apply hsq p
    refine ⟨r, ?_⟩
    rw [hq, hr]
    ring
  have hpdq : p ∣ partialDerivative (0 : Fin 2) p * q := by
    have h := dvd_sub hpd (dvd_mul_right p (partialDerivative (0 : Fin 2) q))
    rw [hq, partialDerivative_mul] at h
    simpa only [add_sub_cancel_right] using h
  have hpp : p ∣ partialDerivative (0 : Fin 2) p :=
    (hp.dvd_mul.mp hpdq).resolve_right hpq
  apply not_dvd_partialDerivative_zero_of_regular p _ k hpkregular hpp
  rw [mem_maximalIdeal_iff]
  by_contra hvalue
  exact hp.irreducible.not_isUnit (isUnit_of_valueRingHom_ne_zero hvalue)

/-- The first partial polar satisfies the blowup recurrence at the exact
finite set of nonunit strict transforms of a reduced transverse equation. -/
theorem exists_pointBlowup_polar_recurrence_of_squarefree_regular
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f) :
    ∃ (s : Finset ℂ)
      (hpolar : PlaneCurve.HasFiniteIntersection f (partialDerivative (0 : Fin 2) f)),
      (∀ c, c ∈ s ↔ ¬ IsUnit (pointBlowupTransform c m f hf)) ∧
      ∃ hlocal : ∀ c, PlaneCurve.HasFiniteIntersection (pointBlowupTransform c m f hf)
        (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)),
        PlaneCurve.intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar =
          m * (m - 1) + ∑ c ∈ s, PlaneCurve.intersectionMultiplicity
            (pointBlowupTransform c m f hf)
            (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)) (hlocal c) := by
  classical
  have hpolar := finite_first_partial_polar_of_squarefree_regular m f hf hregular hsq
  obtain ⟨P, U, hP, hPm, hU, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm f hregular
      (by simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf)
  have hmodel : f = U * firstCoordinatePolynomialEvaluation P := by
    rw [hfactor, mul_comm]
  have hmodelFinite : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative 0 (U * firstCoordinatePolynomialEvaluation P)) := by
    simpa only [← hmodel] using hpolar
  obtain ⟨A, hA, _hAm, _hscale, htransform, _hderivative, hfA, hiA⟩ :=
    exists_pointBlowup_polar_intersection_recurrence m hm P hP hPm
      (by simpa only [one_mul] using hcoeff) U hU hmodelFinite
  let s := (A.map (valueRingHom 1)).roots.toFinset
  have hT (c : ℂ) : pointBlowupTransform c m f hf =
      (pointBlowupChartGerm c).pullbackRingHom U *
        firstCoordinatePolynomialEvaluation (rootTranslation A c) := by
    apply pointBlowupTransform_unique c m f _ _ (pointBlowupTransform_factor c m f hf)
    rw [hmodel]
    exact htransform c
  have hs (c : ℂ) : c ∈ s ↔ ¬ IsUnit (pointBlowupTransform c m f hf) := by
    rw [hT, IsUnit.mul_iff]
    have hu : IsUnit ((pointBlowupChartGerm c).pullbackRingHom U) := hU.map _
    simp only [hu, true_and, isUnit_iff_valueRingHom_ne_zero,
      value_firstCoordinatePolynomialEvaluation_rootTranslation, not_not]
    exact Multiset.mem_toFinset.trans (mem_roots (hA.map (valueRingHom 1)).ne_zero)
  have hlocal (c : ℂ) : PlaneCurve.HasFiniteIntersection (pointBlowupTransform c m f hf)
      (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)) := by
    by_cases hc : c ∈ s
    · simpa only [hT] using hfA ⟨c, hc⟩
    · have hu : IsUnit (pointBlowupTransform c m f hf) := by
        by_contra hn
        exact hc ((hs c).mpr hn)
      have htop : PlaneCurve.pairIdeal (pointBlowupTransform c m f hf)
          (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu
      unfold PlaneCurve.HasFiniteIntersection
      rw [htop]
      infer_instance
  refine ⟨s, hpolar, hs, hlocal, ?_⟩
  have hcount : PlaneCurve.intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar =
      m * (m - 1) + ∑ c : s, PlaneCurve.intersectionMultiplicity
        (pointBlowupTransform c m f hf)
        (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)) (hlocal c) := by
    convert hiA using 1
    · simp only [hmodel]
    · congr 1
      apply Finset.sum_congr rfl
      intro c _
      simp only [hT]
  rwa [Finset.sum_coe_sort s (fun c ↦ PlaneCurve.intersectionMultiplicity
    (pointBlowupTransform c m f hf)
    (partialDerivative (0 : Fin 2) (pointBlowupTransform c m f hf)) (hlocal c))] at hcount

end OnLeConjecture.Analytic.Germ
