/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticBranchPullback
public import OnLeConjecture.DTwo.QuadraticRemainder
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# Intersection multiplicity after centering a quadratic decomposition

The centered quadratic decomposition differs from the original component by
an analytic multiple of `x² + yᵏ`. This file proves that the corresponding
pair ideal and intersection multiplicity are unchanged.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

namespace Germ

theorem secondCoordinateConstantExtension_mul (p q : Germ 1) :
    secondCoordinateConstantExtension (p * q) =
      secondCoordinateConstantExtension p *
        secondCoordinateConstantExtension q := by
  change planeCoordinateSwapEquiv.pullbackAlgEquiv
      (Germ.hyperplaneExtension 1 (p * q)) =
    planeCoordinateSwapEquiv.pullbackAlgEquiv
        (Germ.hyperplaneExtension 1 p) *
      planeCoordinateSwapEquiv.pullbackAlgEquiv
        (Germ.hyperplaneExtension 1 q)
  rw [map_mul, map_mul]

@[simp]
theorem secondCoordinateConstantExtension_coordinate :
    secondCoordinateConstantExtension
        (Germ.coordinate (0 : Fin 1)) =
      Germ.coordinate (0 : Fin 2) := by
  rw [secondCoordinateConstantExtension,
    Germ.hyperplaneExtension_coordinate]
  simpa only [show (Fin.succ 0 : Fin 2) = 1 by decide] using
    Germ.planeCoordinateSwapEquiv_pullback_one

/-- The term removed by centering is a multiple of the quadratic base
equation when the uncentered component vanishes at the origin. -/
theorem exists_centeredCorrection_eq_quadraticBaseEquation_mul
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hvalue : Germ.valueRingHom 2
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0) :
    ∃ q : Germ 2,
      quadraticBaseSubstitutionAlgHom k hk
          (secondCoordinateConstantExtension
            (secondCoordinateTaylorCoefficient 0 A)) =
        quadraticBaseEquation k * q := by
  have hvalueA : Germ.valueRingHom 2 A = 0 := by
    have h := hvalue
    rw [map_add, map_mul, Germ.valueRingHom_coordinate, zero_mul,
      add_zero] at h
    rw [quadraticBaseSubstitutionAlgHom_apply] at h
    change Germ.valueRingHom 2
      ((quadraticBaseMapGerm k hk).pullbackRingHom A) = 0 at h
    rwa [PointedMapGerm.valueRingHom_pullback] at h
  let c : Germ 1 := secondCoordinateTaylorCoefficient 0 A
  have hcValue : Germ.valueRingHom 1 c = 0 := by
    simpa only [c, value_secondCoordinateTaylorCoefficient_zero]
      using hvalueA
  have hcMax : c ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    exact hcValue
  obtain ⟨a, ha⟩ := Germ.exists_eq_sum_coordinate_mul hcMax
  let q := quadraticBaseSubstitutionAlgHom k hk
    (secondCoordinateConstantExtension (a 0))
  refine ⟨q, ?_⟩
  have hc : c = Germ.coordinate (0 : Fin 1) * a 0 := by
    simpa only [Fin.sum_univ_one] using ha
  rw [show secondCoordinateTaylorCoefficient 0 A = c by rfl, hc,
    secondCoordinateConstantExtension_mul,
    secondCoordinateConstantExtension_coordinate, map_mul,
    quadraticBaseSubstitution_coordinate_zero]

/-- Centering preserves the pair ideal generated with the quadratic base
equation. -/
theorem pairIdeal_quadraticBaseEquation_centered
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hvalue : Germ.valueRingHom 2
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0) :
    pairIdeal (quadraticBaseEquation k)
        (centeredQuadraticBaseDecomposition k hk A B) =
      pairIdeal (quadraticBaseEquation k)
        (quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk B) := by
  obtain ⟨q, hq⟩ :=
    exists_centeredCorrection_eq_quadraticBaseEquation_mul
      k hk A B hvalue
  rw [centeredQuadraticBaseDecomposition_eq, hq]
  exact pairIdeal_sub_mul_right _ _ _

/-- Finite intersection with the quadratic base equation is preserved by
centering. -/
theorem hasFiniteIntersection_centeredQuadraticBaseDecomposition
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hvalue : Germ.valueRingHom 2
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation k)
      (quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk B)) :
    HasFiniteIntersection (quadraticBaseEquation k)
      (centeredQuadraticBaseDecomposition k hk A B) := by
  exact hfinite.of_pairIdeal_eq
    (pairIdeal_quadraticBaseEquation_centered
      k hk A B hvalue).symm

/-- Centering preserves intersection multiplicity with the quadratic base
equation. -/
theorem intersectionMultiplicity_centeredQuadraticBaseDecomposition
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hvalue : Germ.valueRingHom 2
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation k)
      (quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk B)) :
    intersectionMultiplicity (quadraticBaseEquation k)
        (centeredQuadraticBaseDecomposition k hk A B)
        (hasFiniteIntersection_centeredQuadraticBaseDecomposition
          k hk A B hvalue hfinite) =
      intersectionMultiplicity (quadraticBaseEquation k)
        (quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk B) hfinite := by
  exact intersectionMultiplicity_eq_of_pairIdeal_eq
    (hasFiniteIntersection_centeredQuadraticBaseDecomposition
      k hk A B hvalue hfinite)
    hfinite
    (pairIdeal_quadraticBaseEquation_centered k hk A B hvalue)

end Germ

end OnLeConjecture.DTwo
