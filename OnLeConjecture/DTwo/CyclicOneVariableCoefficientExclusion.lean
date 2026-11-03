/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparedNoninjectivity
public import OnLeConjecture.DTwo.CyclicNormalizedOddPreparation

/-!
# Exclusion of the cyclic map with a one-variable unit coefficient

The third component is an arbitrary analytic multiple of `y^k`.
Its normalized odd initial form and all subsequent weighted data are
constructed, not supplied as hypotheses.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclic_oneVariable_coefficient_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a k p : ℕ) (ha : 2 ≤ a) (hk : k = 2 * a) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 1) (hβ : valueRingHom 1 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p (hyperplaneExtension 1 β))
    (h : Germ 2) (hH : g.1.component 2 = coordinate 1 ^ k * h) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  have hk0 : 0 < k := by omega
  have hβext : valueRingHom 2 (hyperplaneExtension 1 β) ≠ 0 := by
    rw [hyperplaneExtension, PointedMapGerm.valueRingHom_pullback]
    exact hβ
  obtain ⟨q₀, g', hequiv, hg'0, hg'1, htail⟩ :=
    exists_cyclic_normalized_odd_preparation g hg k p hk0 hp hodd
      (hyperplaneExtension 1 β) hβext hP hQ h hH
  obtain ⟨B, hB, hBβ⟩ := exists_cyclicCoefficientGerm_representation β
  have hc : B 0 ≠ 0 := by
    have hvalue : valueRingHom 1 (cyclicCoefficientGerm B hB) = B 0 := rfl
    rw [← hvalue, hBβ]
    exact hβ
  have hNodd : Odd (p + 2 * q₀) := hodd.add_even (even_two_mul q₀)
  apply cyclic_prepared_not_hasInjectiveRepresentative g' a k p (p + 2 * q₀)
    ha hk hp hodd (by omega) hNodd B hB hc (hg'0.trans hP) _ htail
      (hequiv.hasInjectiveRepresentative hg)
  rw [hBβ]
  exact hg'1.trans hQ

end OnLeConjecture.DTwo
