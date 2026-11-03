/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectiveIntersectionParametrization
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection

/-!
# Equation multiplicity and the orders of a parametrization

For an intersection parametrization of an irreducible plane equation,
the minimum order of its two components equals the maximal-ideal order
of the equation. Coordinate-axis intersections give the lower bound.
A linear coordinate change achieving the exact equation order supplies
a smooth test function giving the upper bound. A component identically
zero is assigned infinite order throughout.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

/-- Finite intersection with either coordinate axis is at least the
maximal-ideal order of the plane equation. -/
theorem equation_order_le_coordinate_intersection
    (f : Germ 2) (m : ℕ) (hf : f ∈ maximalIdeal 2 ^ m) (i : Fin 2)
    (hfinite : HasFiniteIntersection (coordinate i) f) :
    m ≤ intersectionMultiplicity (coordinate i) f hfinite := by
  fin_cases i
  · change m ≤ intersectionMultiplicity (coordinate 0) f hfinite
    have hne := restriction_ne_zero_of_hasFiniteIntersection_coordinate f hfinite
    rw [intersectionMultiplicity_coordinate_eq_restrictionOrder f hne]
    have hbound := mem_maximalIdeal_one_pow_iff.mp
      ((hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow hf)
    change (m : ℕ∞) ≤ vanishingOrder (hyperplaneRestriction 1 f) at hbound
    simpa only [ENat.toNat_natCast] using
      ENat.toNat_le_toNat hbound (vanishingOrder_eq_top_iff.not.mpr hne)
  · change m ≤ intersectionMultiplicity (coordinate 1) f hfinite
    have hne : pointBlowupExceptionalLine.pullbackRingHom f ≠ 0 := by
      intro hzero
      have hall := pointBlowupExceptionalLine.coordinate_pullbacks_eq_zero_of_finite_pair
        (coordinate (1 : Fin 2)) f hfinite pointBlowupExceptionalLine_pullback_one hzero
      exact coordinate_zero_ne_zero (pointBlowupExceptionalLine_pullback_zero.symm.trans (hall 0))
    rw [intersectionMultiplicity_secondCoordinate_eq_exceptionalRestrictionOrder]
    have hbound := mem_maximalIdeal_one_pow_iff.mp
      (pointBlowupExceptionalLine.pullback_mem_maximalIdeal_pow hf)
    simpa only [ENat.toNat_natCast] using
      ENat.toNat_le_toNat hbound (vanishingOrder_eq_top_iff.not.mpr hne)

namespace IntersectionParametrization

/-- Every component order is bounded below by the equation order. -/
theorem equation_order_le_component_order {f : Germ 2}
    (P : IntersectionParametrization f) (hirr : Irreducible f)
    (m : ℕ) (hf : f ∈ maximalIdeal 2 ^ m) (i : Fin 2) :
    (m : ℕ∞) ≤ vanishingOrder (P.map.pullbackRingHom (coordinate i)) := by
  by_cases hzero : P.map.pullbackRingHom (coordinate i) = 0
  · rw [hzero, vanishingOrder_zero]
    exact le_top
  have hfinite : HasFiniteIntersection f (coordinate i) :=
    hasFiniteIntersection_of_irreducible_not_dvd f (coordinate i) hirr (by
      rintro ⟨q, hq⟩
      apply hzero
      rw [hq, map_mul, P.curve_eq_zero, zero_mul])
  have hbound := equation_order_le_coordinate_intersection f m hf i
    ((hasFiniteIntersection_comm _ _).mp hfinite)
  rw [intersectionMultiplicity_comm, P.intersection_order _ hfinite] at hbound
  exact (show (m : ℕ∞) ≤ ↑(vanishingOrder (P.map.pullbackRingHom (coordinate i))).toNat by
    exact_mod_cast hbound).trans (ENat.natCast_toNat_le_self _)

/-- The coordinate ideal of an intersection parametrization has exactly
the maximal-ideal order of its irreducible equation. -/
theorem coordinateIdeal_order {f : Germ 2}
    (P : IntersectionParametrization f) (hirr : Irreducible f)
    (m : ℕ) (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    P.map.1.coordinateIdeal ≤ maximalIdeal 1 ^ m ∧
      ¬ P.map.1.coordinateIdeal ≤ maximalIdeal 1 ^ (m + 1) := by
  refine ⟨?_, ?_⟩
  · rw [MapGerm.coordinateIdeal_le]
    intro i
    rw [← PointedMapGerm.pullback_coordinate, mem_maximalIdeal_one_pow_iff]
    exact P.equation_order_le_component_order hirr m hf i
  · obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hf hnext
    let l := e.inverse.pullbackRingHom (coordinate (1 : Fin 2))
    have hregfinite := hasFiniteIntersection_secondCoordinate_of_regular
      (e.forward.pullbackRingHom f) m he
    have hreginter := intersectionMultiplicity_secondCoordinate_of_regular
      (e.forward.pullbackRingHom f) m he hregfinite
    have hlf : HasFiniteIntersection l f := by
      have h := hregfinite.pullback e.symm
      change HasFiniteIntersection l (e.pullbackAlgEquiv.symm (e.pullbackAlgEquiv f)) at h
      simpa only [AlgEquiv.symm_apply_apply] using h
    have hli : intersectionMultiplicity l f hlf = m := by
      have h := intersectionMultiplicity_pullback e.symm hregfinite
      change intersectionMultiplicity (coordinate (1 : Fin 2))
        (e.forward.pullbackRingHom f) hregfinite =
          intersectionMultiplicity l (e.pullbackAlgEquiv.symm (e.pullbackAlgEquiv f)) _ at h
      simpa only [AlgEquiv.symm_apply_apply, hreginter] using h.symm
    have hlmem : l ∈ maximalIdeal 2 :=
      e.inverse.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 1)
    have hpullmem : P.map.pullbackRingHom l ∈ P.map.1.coordinateIdeal := by
      rw [← P.map.map_maximalIdeal_eq_coordinateIdeal]
      exact Ideal.mem_map_of_mem _ hlmem
    have hpullne := P.pullback_ne_zero l ((hasFiniteIntersection_comm _ _).mp hlf)
    have hpullorder : (vanishingOrder (P.map.pullbackRingHom l)).toNat = m := by
      rw [← P.intersection_order _ ((hasFiniteIntersection_comm _ _).mp hlf),
        intersectionMultiplicity_comm]
      exact hli
    intro hle
    have hbound := mem_maximalIdeal_one_pow_iff.mp (hle hpullmem)
    have hnat := ENat.toNat_le_toNat hbound (vanishingOrder_eq_top_iff.not.mpr hpullne)
    simp only [ENat.toNat_natCast, hpullorder] at hnat
    omega

/-- The multiplicity of the irreducible equation is the minimum of the
two component orders of any intersection parametrization. -/
theorem min_component_orders_eq_equation_order {f : Germ 2}
    (P : IntersectionParametrization f) (hirr : Irreducible f)
    (m : ℕ) (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    min (vanishingOrder (P.map.1.component 0)) (vanishingOrder (P.map.1.component 1)) = m := by
  obtain ⟨hI, hInext⟩ := P.coordinateIdeal_order hirr m hf hnext
  have hbound (i : Fin 2) : (m : ℕ∞) ≤ vanishingOrder (P.map.1.component i) :=
    mem_maximalIdeal_one_pow_iff.mp (hI (P.map.1.component_mem_coordinateIdeal i))
  apply le_antisymm
  · by_contra h
    have hlt : (m : ℕ∞) < min (vanishingOrder (P.map.1.component 0))
        (vanishingOrder (P.map.1.component 1)) := lt_of_not_ge h
    apply hInext
    rw [MapGerm.coordinateIdeal_le]
    intro i
    rw [mem_maximalIdeal_one_pow_iff]
    have hmi : (m : ℕ∞) < vanishingOrder (P.map.1.component i) := by
      fin_cases i
      · exact hlt.trans_le (min_le_left _ _)
      · exact hlt.trans_le (min_le_right _ _)
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hmi
  · exact le_min (hbound 0) (hbound 1)

end IntersectionParametrization

end OnLeConjecture.Analytic
