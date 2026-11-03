/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntersectionParametrization
public import OnLeConjecture.Analytic.InjectiveCurveParametrization

/-!
# Injective parametrizations computing intersection multiplicity

The smooth, source-coordinate, and blowdown constructions preserve local
injectivity and the intersection-order formula simultaneously. Induction
along a finite smooth-resolution chain therefore supplies a single
parametrization with both properties for every irreducible equation.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

/-- A smooth plane equation has an intersection parametrization obtained
from the analytic implicit function theorem, retaining local injectivity. -/
theorem exists_injective_intersectionParametrization_of_smooth
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    ∃ P : IntersectionParametrization f, P.map.HasInjectiveRepresentative := by
  obtain ⟨e, he⟩ := exists_equiv_pullback_eq_coordinate f hf
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).1
  refine ⟨{
    map := e.forward.comp (hyperplaneInclusionGerm 1)
    curve_eq_zero := ?_
    nonconstant := ?_
    intersection_order := ?_ },
      e.forward.comp_hasInjectiveRepresentative (hyperplaneInclusionGerm 1)
        e.forward_hasInjectiveRepresentative
        (hyperplaneInclusionGerm_hasInjectiveRepresentative 1)⟩
  · rw [PointedMapGerm.pullbackRingHom_comp]
    change hyperplaneRestriction 1 (e.pullbackAlgEquiv f) = 0
    rw [he, hyperplaneRestriction_coordinate_zero]
  · apply PointedMapGerm.exists_nonzero_coordinate_pullback_comp_equiv
    refine ⟨1, ?_⟩
    change hyperplaneRestriction 1 (coordinate (1 : Fin 2)) ≠ 0
    simpa only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
      hyperplaneRestriction_coordinate_succ] using coordinate_zero_ne_zero
  · intro g hfinite
    have hefinite := hfinite.pullback e
    rw [he] at hefinite
    have hne := restriction_ne_zero_of_hasFiniteIntersection_coordinate _ hefinite
    have hi := intersectionMultiplicity_pullback e hfinite
    change Module.finrank ℂ _ = Module.finrank ℂ _ at hi
    rw [he] at hi
    rw [PointedMapGerm.pullbackRingHom_comp]
    exact hi.trans (intersectionMultiplicity_coordinate_eq_restrictionOrder _ hne)

/-- Blowing down the unique strict-transform branch preserves the
intersection-parametrization property and local injectivity. -/
theorem exists_injective_intersectionParametrization_of_pointBlowup
    (m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hirr : Irreducible f) (c : ℂ)
    (P : IntersectionParametrization (pointBlowupTransform c m f hf))
    (hPi : P.map.HasInjectiveRepresentative) :
    ∃ Q : IntersectionParametrization f, Q.map.HasInjectiveRepresentative := by
  classical
  let F := pointBlowupTransform c m f hf
  have hFmem : F ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    have h := congrArg (valueRingHom 1) P.curve_eq_zero
    simpa only [PointedMapGerm.valueRingHom_pullback, map_zero] using h
  have hFunit : ¬ IsUnit (projectiveStrictTransform m f hf (some c)) := by
    rw [projectiveStrictTransform_some]
    intro hu
    exact (valueRingHom_ne_zero_of_isUnit hu) (mem_maximalIdeal_iff.mp hFmem)
  obtain ⟨_, hother⟩ := irreducible_projectiveStrictTransform_of_nonunit
    m hm f hf hnext hirr (some c) hFunit
  have haxis : HasFiniteIntersection F (coordinate (1 : Fin 2)) := by
    rw [hasFiniteIntersection_comm]
    exact finite_intersection_exceptional_pointBlowupTransform c m f hf hnext
  have hyne : P.map.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0 :=
    P.pullback_ne_zero _ haxis
  have hyorder : (vanishingOrder (P.map.pullbackRingHom (coordinate (1 : Fin 2)))).toNat = m := by
    rw [← P.intersection_order _ haxis, intersectionMultiplicity_comm,
      intersectionMultiplicity_secondCoordinate_eq_exceptionalRestrictionOrder]
    have ho := projectiveExceptionalIntersectionOrder_eq_of_irreducible m hm f hf hnext
      hirr (some c) hFunit
    simpa only [projectiveExceptionalIntersectionOrder, projectiveStrictTransform_some] using ho
  refine ⟨{
    map := (pointBlowupChartGerm c).comp P.map
    curve_eq_zero := ?_
    nonconstant := ?_
    intersection_order := ?_ }, hPi.pointBlowupChart_comp hyne c⟩
  · rw [PointedMapGerm.pullbackRingHom_comp]
    change P.map.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom f) = 0
    rw [pointBlowupTransform_factor c m f hf, map_mul, P.curve_eq_zero, mul_zero]
  · refine ⟨1, ?_⟩
    rw [PointedMapGerm.pullbackRingHom_comp]
    change P.map.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate 1)) ≠ 0
    rwa [pointBlowupChartGerm_pullback_one]
  · intro g hfinite
    by_cases hunit : IsUnit g
    · rw [intersectionMultiplicity_eq_zero_of_isUnit_right f g hunit hfinite,
        vanishingOrder_eq_zero_iff_isUnit.mpr (hunit.map _), ENat.toNat_zero]
    have hgne : g ≠ 0 := by
      intro hz
      exact hirr.not_isUnit (isUnit_of_hasFiniteIntersection_zero_right f (hz ▸ hfinite))
    obtain ⟨n, hg, hgn⟩ := exists_exact_maximalIdeal_order_of_ne_zero g hgne
    have hn : 0 < n := by
      by_contra h
      have hnzero : n = 0 := by omega
      rw [hnzero, zero_add, pow_one, mem_maximalIdeal_iff] at hgn
      exact hunit (isUnit_of_valueRingHom_ne_zero hgn)
    obtain ⟨hlocal, hi⟩ := projectiveBlowup_intersection_recurrence_of_common_zero_cover
      m n hm hn f g hf hg hnext hgn hfinite {some c} (by
        intro t ht _
        apply Finset.mem_singleton.mpr
        by_contra h
        exact ht (hother t h))
    have hchild : HasFiniteIntersection F (pointBlowupTransform c n g hg) := by
      simpa only [projectiveStrictTransform_some] using hlocal (some c)
    have hchildne := P.pullback_ne_zero _ hchild
    have histep : intersectionMultiplicity f g hfinite =
        m * n + intersectionMultiplicity F (pointBlowupTransform c n g hg) hchild := by
      simpa only [Finset.sum_singleton, projectiveStrictTransform_some] using hi
    rw [histep, P.intersection_order _ hchild, PointedMapGerm.pullbackRingHom_comp]
    change m * n + (vanishingOrder (P.map.pullbackRingHom
        (pointBlowupTransform c n g hg))).toNat =
      (vanishingOrder (P.map.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom g))).toNat
    rw [pointBlowupTransform_factor c n g hg, map_mul, map_pow, vanishingOrder_mul]
    rw [ENat.toNat_add
      (vanishingOrder_eq_top_iff.not.mpr (pow_ne_zero n hyne))
      (vanishingOrder_eq_top_iff.not.mpr hchildne)]
    rw [vanishingOrder_pow, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast, hyorder, Nat.mul_comm]

namespace Germ.HasFiniteSmoothBlowupChain

/-- A finite smooth-resolution chain constructs an intersection
parametrization with a locally injective representative. -/
theorem exists_injective_intersectionParametrization {f : Germ 2}
    (h : HasFiniteSmoothBlowupChain f) (hirr : Irreducible f) :
    ∃ P : IntersectionParametrization f, P.map.HasInjectiveRepresentative := by
  induction h with
  | smooth f hf hn => exact exists_injective_intersectionParametrization_of_smooth f hf hn
  | source f e _ ih =>
    obtain ⟨P, hPi⟩ := ih ((MulEquiv.irreducible_iff e.pullbackRingEquiv.toMulEquiv).mpr hirr)
    refine ⟨P.ofPullback f e, ?_⟩
    exact e.forward.comp_hasInjectiveRepresentative P.map e.forward_hasInjectiveRepresentative hPi
  | blowup f m hm hf hn c hchild ih =>
    have hnonunit : ¬ IsUnit (projectiveStrictTransform m f hf (some c)) := by
      rw [projectiveStrictTransform_some]
      intro hu
      exact (valueRingHom_ne_zero_of_isUnit hu) (mem_maximalIdeal_iff.mp hchild.mem_maximalIdeal)
    have hchildirr := (irreducible_projectiveStrictTransform_of_nonunit m (by omega) f hf hn
      hirr (some c) hnonunit).1
    rw [projectiveStrictTransform_some] at hchildirr
    obtain ⟨P, hPi⟩ := ih hchildirr
    exact exists_injective_intersectionParametrization_of_pointBlowup
      m (by omega) f hf hn hirr c P hPi

end Germ.HasFiniteSmoothBlowupChain

/-- Every irreducible plane equation has one locally injective
parametrization computing all its finite local intersection multiplicities. -/
theorem exists_injective_intersectionParametrization_of_irreducible
    (f : Germ 2) (hirr : Irreducible f) :
    ∃ P : IntersectionParametrization f, P.map.HasInjectiveRepresentative :=
  (hasFiniteSmoothBlowupChain_of_irreducible f hirr).exists_injective_intersectionParametrization
    hirr

end OnLeConjecture.Analytic
