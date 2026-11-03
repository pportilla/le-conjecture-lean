/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicOneVariableCoefficientExclusion
public import OnLeConjecture.DTwo.CyclicSecondNormalization
public import OnLeConjecture.DTwo.CyclicUnitCoefficientSelection

/-!
# Exclusion of the cyclic normal form with two-variable coefficients

The unit second coefficient is chosen by a linear target change.
An actual analytic source equivalence normalizes that coefficient to
depend only on the second coordinate and preserves the third-coordinate
ideal. The complete odd preparation and weighted collision then apply.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclic_normal_form_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a k p : ℕ) (ha : 2 ≤ a) (hk : k = 2 * a) (hp : 3 ≤ p) (hodd : Odd p)
    (h₂ h₃ : Germ 2) (hunit : valueRingHom 2 h₂ ≠ 0 ∨ valueRingHom 2 h₃ ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p h₂)
    (hZ : g.1.component 2 = coordinate 1 ^ k * h₃) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨f, h, hequiv, hh, hf0, hf1, hf2⟩ :=
    exists_cyclic_unit_second_coefficient g k p h₂ h₃ hunit hP hQ hZ
  obtain ⟨e, β, hβ, he0, he1, hideal⟩ :=
    CyclicNormalization.exists_normalization_equiv k p (by omega) hp h hh
  let f' := f.comp e.forward
  have hequiv' : f.RightLeftEquivalent f' := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hf'0 : f'.1.component 0 = cyclicFirst k := by
    rw [PointedMapGerm.component_comp_eq_pullback, hf0]
    exact he0
  have hf'1 : f'.1.component 1 = cyclicSecond k p (hyperplaneExtension 1 β) := by
    rw [PointedMapGerm.component_comp_eq_pullback, hf1]
    exact he1
  have hf2ideal : f.1.component 2 ∈ Ideal.span {coordinate (1 : Fin 2) ^ k} := by
    rw [Ideal.mem_span_singleton, hf2]
    exact dvd_mul_right _ _
  have hf'2ideal : f'.1.component 2 ∈ Ideal.span {coordinate (1 : Fin 2) ^ k} := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← hideal]
    exact Ideal.mem_map_of_mem e.forward.pullbackRingHom hf2ideal
  rw [Ideal.mem_span_singleton] at hf'2ideal
  obtain ⟨h', hh'⟩ := hf'2ideal
  exact cyclic_oneVariable_coefficient_not_hasInjectiveRepresentative f' a k p
    ha hk hp hodd β (hβ ▸ hh) hf'0 hf'1 h' hh'
      ((hequiv.trans hequiv').hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
