/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PreparedCyclicPair
public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Choosing a unit second coefficient

If at least one of the two coefficients is a unit, either no target
change is needed or adding the third component to the second suffices.
The first and third target components remain unchanged.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_target_add_third_to_second (g : PointedMapGerm 2 3) :
    ∃ g' : PointedMapGerm 2 3, g.RightLeftEquivalent g' ∧
      g'.1.component 0 = g.1.component 0 ∧
      g'.1.component 1 = g.1.component 1 + g.1.component 2 ∧
      g'.1.component 2 = g.1.component 2 := by
  let e : Source 3 ≃ₗ[ℂ] Source 3 :=
    { toFun := fun z => ![z 0, z 1 + z 2, z 2]
      invFun := fun z => ![z 0, z 1 - z 2, z 2]
      map_add' := by
        intro z w
        ext i
        fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c z
        ext i
        fin_cases i <;> simp [mul_add]
      left_inv := by
        intro z
        ext i
        fin_cases i <;> simp
      right_inv := by
        intro z
        ext i
        fin_cases i <;> simp }
  let E := pointedEquivGermOfContinuousLinearEquiv e.toContinuousLinearEquiv
  have hE0 : E.forward.1.component 0 = coordinate 0 := by apply Subtype.ext; rfl
  have hE1 : E.forward.1.component 1 = coordinate 1 + coordinate 2 := by apply Subtype.ext; rfl
  have hE2 : E.forward.1.component 2 = coordinate 2 := by apply Subtype.ext; rfl
  refine ⟨E.forward.comp g, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, E, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · rw [PointedMapGerm.component_comp_eq_pullback, hE0, PointedMapGerm.pullback_coordinate]
  · rw [PointedMapGerm.component_comp_eq_pullback, hE1, map_add,
      PointedMapGerm.pullback_coordinate, PointedMapGerm.pullback_coordinate]
  · rw [PointedMapGerm.component_comp_eq_pullback, hE2, PointedMapGerm.pullback_coordinate]

theorem exists_cyclic_unit_second_coefficient
    (g : PointedMapGerm 2 3) (k p : ℕ) (h₂ h₃ : Germ 2)
    (hunit : valueRingHom 2 h₂ ≠ 0 ∨ valueRingHom 2 h₃ ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p h₂)
    (hZ : g.1.component 2 = coordinate 1 ^ k * h₃) :
    ∃ g' : PointedMapGerm 2 3, ∃ β : Germ 2,
      g.RightLeftEquivalent g' ∧ valueRingHom 2 β ≠ 0 ∧
      g'.1.component 0 = cyclicFirst k ∧ g'.1.component 1 = cyclicSecond k p β ∧
      g'.1.component 2 = coordinate 1 ^ k * h₃ := by
  by_cases hh₂ : valueRingHom 2 h₂ = 0
  · have hh₃ : valueRingHom 2 h₃ ≠ 0 := hunit.resolve_left (not_not.mpr hh₂)
    obtain ⟨g', hequiv, hg'0, hg'1, hg'2⟩ := exists_target_add_third_to_second g
    refine ⟨g', h₂ + h₃, hequiv, ?_, hg'0.trans hP, ?_, hg'2.trans hZ⟩
    · simpa only [map_add, hh₂, zero_add] using hh₃
    · rw [hg'1, hQ, hZ]
      simp only [cyclicSecond]
      ring
  · exact ⟨g, h₂, g.rightLeftEquivalent_refl, hh₂, hP, hQ, hZ⟩

end OnLeConjecture.DTwo
