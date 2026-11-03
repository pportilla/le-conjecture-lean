/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleSmoothResolutionChain
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.PlaneCurve.SmoothStraightening

/-!
# Nonconstant analytic parametrizations of irreducible plane curves

A finite smooth-resolution chain gives a convergent parametrization by
composing an implicit-function parametrization with its chart maps. The
exceptional restriction of each strict transform is nonzero, which proves
that no blowdown collapses the parametrizing curve to a point.

No primitivity or normalization degree is asserted for this parametrization.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

theorem pullback_eq_zero_of_coordinate_pullbacks_eq_zero {n m : ℕ}
    (γ : PointedMapGerm n m)
    (hγ : ∀ i : Fin m, γ.pullbackRingHom (coordinate i) = 0)
    (f : Germ m) (hf : f ∈ maximalIdeal m) : γ.pullbackRingHom f = 0 := by
  have hle : maximalIdeal m ≤ RingHom.ker γ.pullbackRingHom := by
    rw [← span_range_coordinate_eq_maximalIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hγ i
  exact hle hf

theorem exists_nonzero_coordinate_pullback_comp_equiv
    (γ : PointedMapGerm 1 2) (hγ : ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0)
    (e : PointedEquivGerm 2) :
    ∃ i : Fin 2, (e.forward.comp γ).pullbackRingHom (coordinate i) ≠ 0 := by
  by_contra h
  have hall : ∀ i : Fin 2, (e.forward.comp γ).pullbackRingHom (coordinate i) = 0 := by
    simpa using h
  obtain ⟨i, hi⟩ := hγ
  have hz := (e.forward.comp γ).pullback_eq_zero_of_coordinate_pullbacks_eq_zero hall
    (e.inverse.pullbackRingHom (coordinate i))
    (e.inverse.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i))
  rw [pullbackRingHom_comp] at hz
  change γ.pullbackRingHom (e.pullbackRingEquiv (e.pullbackRingEquiv.symm (coordinate i))) = 0 at hz
  rw [e.pullbackRingEquiv.apply_symm_apply] at hz
  exact hi hz

theorem coordinate_pullbacks_eq_zero_of_finite_pair
    (γ : PointedMapGerm 1 2) (f g : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection f g)
    (hf : γ.pullbackRingHom f = 0) (hg : γ.pullbackRingHom g = 0) :
    ∀ i : Fin 2, γ.pullbackRingHom (coordinate i) = 0 := by
  obtain ⟨N, hN⟩ :=
    (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f g).mp hfinite
  have hker : PlaneCurve.pairIdeal f g ≤ RingHom.ker γ.pullbackRingHom := by
    rw [PlaneCurve.pairIdeal, Ideal.span_le]
    intro z hz
    rcases (show z = f ∨ z = g by simpa using hz) with rfl | rfl
    · exact hf
    · exact hg
  intro i
  have hz : γ.pullbackRingHom (coordinate i ^ N) = 0 :=
    hker (hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal i) N))
  rw [map_pow] at hz
  by_contra h
  exact pow_ne_zero N h hz

end PointedMapGerm

namespace Germ

theorem constructed_pointBlowupTransform_exceptionalRestriction_ne_zero
    (c : ℂ) (m : ℕ) (f : Germ 2) (ho : f ∈ maximalIdeal 2 ^ m)
    (hn : f ∉ maximalIdeal 2 ^ (m + 1)) :
    pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f ho) ≠ 0 := by
  obtain ⟨g, P, T, hfactor, _hP, _hPhom, _htail, _hchart, hT, hdegree,
    hrestriction, _hgnext⟩ := exists_pointBlowupTransform_with_initial c m f ho hn
  have heq := pointBlowupTransform_unique c m f _ g
    (pointBlowupTransform_factor c m f ho) hfactor
  rw [heq, hrestriction]
  intro hzero
  exact oneVariablePolynomialEvaluation_not_mem_pow m T hT hdegree
    (hzero ▸ (maximalIdeal 1 ^ (m + 1)).zero_mem)

theorem finite_intersection_exceptional_pointBlowupTransform
    (c : ℂ) (m : ℕ) (f : Germ 2) (ho : f ∈ maximalIdeal 2 ^ m)
    (hn : f ∉ maximalIdeal 2 ^ (m + 1)) :
    PlaneCurve.HasFiniteIntersection (coordinate (1 : Fin 2)) (pointBlowupTransform c m f ho) := by
  have hy : Irreducible (coordinate (1 : Fin 2)) := by
    apply (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _ (coordinate_mem_maximalIdeal 1) _).2
    intro hmem
    have hd := (mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 hmem)).2
    have hv := congrArg (fun L : Source 2 →L[ℂ] ℂ => L (coordinateVector 1)) hd
    simp [coordinateVector] at hv
  apply PlaneCurve.hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors _ _ hy
  intro hdiv
  have hline := pointBlowupExceptionalLine.pullbackRingHom.map_dvd hdiv
  change pointBlowupExceptionalLine.pullbackRingHom (coordinate 1) ∣
    pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f ho) at hline
  rw [pointBlowupExceptionalLine_pullback_one, zero_dvd_iff] at hline
  exact constructed_pointBlowupTransform_exceptionalRestriction_ne_zero c m f ho hn hline

theorem exists_nonconstant_parametrization_of_smooth
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0 := by
  obtain ⟨e, he⟩ := PlaneCurve.exists_equiv_pullback_eq_coordinate f hf
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).1
  refine ⟨e.forward.comp (hyperplaneInclusionGerm 1), ?_, ?_⟩
  · rw [PointedMapGerm.pullbackRingHom_comp]
    change hyperplaneRestriction 1 (e.pullbackAlgEquiv f) = 0
    rw [he, hyperplaneRestriction_coordinate_zero]
  · apply PointedMapGerm.exists_nonzero_coordinate_pullback_comp_equiv
    refine ⟨1, ?_⟩
    change hyperplaneRestriction 1 (coordinate (1 : Fin 2)) ≠ 0
    simpa only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
      hyperplaneRestriction_coordinate_succ] using coordinate_zero_ne_zero

theorem HasFiniteSmoothBlowupChain.exists_nonconstant_parametrization
    {f : Germ 2} (h : HasFiniteSmoothBlowupChain f) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0 := by
  induction h with
  | smooth f hf hn => exact exists_nonconstant_parametrization_of_smooth f hf hn
  | source f e _ ih =>
      obtain ⟨γ, hγ, hnonconstant⟩ := ih
      refine ⟨e.forward.comp γ, ?_, γ.exists_nonzero_coordinate_pullback_comp_equiv hnonconstant e⟩
      rw [PointedMapGerm.pullbackRingHom_comp]
      exact hγ
  | blowup f m _ ho hn c _ ih =>
      obtain ⟨γ, hγ, hnonconstant⟩ := ih
      have hy : γ.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0 := by
        intro hz
        have hall := γ.coordinate_pullbacks_eq_zero_of_finite_pair _ _
          (finite_intersection_exceptional_pointBlowupTransform c m f ho hn) hz hγ
        obtain ⟨i, hi⟩ := hnonconstant
        exact hi (hall i)
      refine ⟨(pointBlowupChartGerm c).comp γ, ?_, 1, ?_⟩
      · rw [PointedMapGerm.pullbackRingHom_comp]
        change γ.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom f) = 0
        rw [pointBlowupTransform_factor c m f ho, map_mul, hγ, mul_zero]
      · rw [PointedMapGerm.pullbackRingHom_comp]
        change γ.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate 1)) ≠ 0
        rw [pointBlowupChartGerm_pullback_one]
        exact hy

/-- Every irreducible plane analytic equation admits a nonconstant
convergent pointed parametrization. Its normalization degree is not specified. -/
theorem exists_nonconstant_parametrization_of_irreducible
    (f : Germ 2) (hf : Irreducible f) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0 :=
  (hasFiniteSmoothBlowupChain_of_irreducible f hf).exists_nonconstant_parametrization

end Germ

end OnLeConjecture.Analytic
