/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicCriticalAxisExclusion
public import OnLeConjecture.Analytic.OneVariableLeadingTerm

/-!
# A smooth critical axis and independent quadratic jets

If both transverse coefficients vanish, the quadratic jets of the other
two components are scalar multiples of the first. Thus a second independent
quadratic jet supplies the unit coefficient needed for cyclic exclusion.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_scalar_quadratic_jet_of_axis_decomposition
    (k : ℕ) (hk : 2 ≤ k) (H : Germ 2) (A B : Germ 1) (C : Germ 2)
    (hA : A ∈ maximalIdeal 1) (hB : B ∈ maximalIdeal 1) (hC : C ∈ maximalIdeal 2)
    (hH : H = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom B + coordinate 1 ^ k * C) :
    ∃ c : ℂ, H - constRingHom 2 c * cyclicFirst k ∈ maximalIdeal 2 ^ 3 := by
  let σ := cyclicScalarMap k (by omega : 1 ≤ k)
  have hP : cyclicFirst k ∈ maximalIdeal 2 ^ 2 := by
    exact (maximalIdeal 2 ^ 2).add_mem
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
      (Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k))
  have hmap : Ideal.map σ.pullbackRingHom (maximalIdeal 1) ≤ maximalIdeal 2 ^ 2 := by
    rw [σ.map_maximalIdeal_eq_coordinateIdeal, MapGerm.coordinateIdeal_le]
    intro i
    rw [cyclicScalarMap_component]
    exact hP
  have hmapPow (r : ℕ) : Ideal.map σ.pullbackRingHom (maximalIdeal 1 ^ r) ≤
      maximalIdeal 2 ^ (2 * r) := by
    rw [Ideal.map_pow, pow_mul]
    exact pow_le_pow_left' hmap r
  obtain ⟨c, hc⟩ := exists_scalar_leadingTerm_of_mem_maximalIdeal_pow A 1
    (by simpa using hA)
  have hArest : σ.pullbackRingHom A - constRingHom 2 c * cyclicFirst k ∈
      maximalIdeal 2 ^ 3 := by
    have hh := hmapPow 2 (Ideal.mem_map_of_mem σ.pullbackRingHom hc)
    have hcoord : σ.pullbackRingHom (coordinate 0) = cyclicFirst k := by
      rw [PointedMapGerm.pullback_coordinate, cyclicScalarMap_component]
      rfl
    simp only [pow_one, map_sub, map_mul, hcoord,
      PointedMapGerm.pullback_constRingHom] at hh
    exact Ideal.pow_le_pow_right (by omega : 3 ≤ 2 * 2) hh
  have hBpull : σ.pullbackRingHom B ∈ maximalIdeal 2 ^ 2 :=
    hmap (Ideal.mem_map_of_mem σ.pullbackRingHom hB)
  have hodd : coordinate (0 : Fin 2) * σ.pullbackRingHom B ∈ maximalIdeal 2 ^ 3 := by
    simpa only [← pow_succ'] using Ideal.mul_mem_mul
      (coordinate_mem_maximalIdeal 0) hBpull
  have htransverse : coordinate (1 : Fin 2) ^ k * C ∈ maximalIdeal 2 ^ 3 := by
    have hh : coordinate (1 : Fin 2) ^ k * C ∈ maximalIdeal 2 ^ (k + 1) := by
      simpa only [pow_succ] using Ideal.mul_mem_mul
        (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k) hC
    exact Ideal.pow_le_pow_right (by omega) hh
  refine ⟨c, ?_⟩
  have heq : H - constRingHom 2 c * cyclicFirst k =
      (σ.pullbackRingHom A - constRingHom 2 c * cyclicFirst k) +
        coordinate 0 * σ.pullbackRingHom B + coordinate 1 ^ k * C := by
    rw [hH]
    change (σ.pullbackRingHom A + coordinate 0 * σ.pullbackRingHom B +
      coordinate 1 ^ k * C) - constRingHom 2 c * cyclicFirst k = _
    ring
  rw [heq]
  exact (maximalIdeal 2 ^ 3).add_mem ((maximalIdeal 2 ^ 3).add_mem hArest hodd) htransverse

/-- Independent quadratic jets and the indicated smooth critical factor
exclude injectivity. All analytic axis coefficients are constructed. -/
theorem critical_axis_independent_quadratic_jets_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQderivative : valueRingHom 2 (partialDerivative 0 (g.1.component 1)) = 0)
    (hZderivative : valueRingHom 2 (partialDerivative 0 (g.1.component 2)) = 0)
    (hJQ : coordinate (1 : Fin 2) ^ (k - 1) ∣ jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (k - 1) ∣ jacobian (g.1.component 0) (g.1.component 2))
    (hquadratic : ¬ ((∃ c : ℂ, g.1.component 1 - constRingHom 2 c * cyclicFirst k ∈
        maximalIdeal 2 ^ 3) ∧
      (∃ c : ℂ, g.1.component 2 - constRingHom 2 c * cyclicFirst k ∈ maximalIdeal 2 ^ 3))) :
    ¬ g.HasInjectiveRepresentative := by
  rw [hP] at hJQ hJZ
  obtain ⟨A, B, H₂, hQ⟩ := exists_cyclic_axis_decomposition k (by omega) (g.1.component 1) hJQ
  obtain ⟨C, D, H₃, hZ⟩ := exists_cyclic_axis_decomposition k (by omega) (g.1.component 2) hJZ
  have hcomponentzero (i : Fin 3) : valueRingHom 2 (g.1.component i) = 0 := by
    rw [← PointedMapGerm.pullback_coordinate, PointedMapGerm.valueRingHom_pullback,
      valueRingHom_coordinate]
  have hA : A ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, value_even_coefficient_of_cyclic_axis_decomposition
      k (by omega) _ A B H₂ hQ]
    exact hcomponentzero 1
  have hC : C ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, value_even_coefficient_of_cyclic_axis_decomposition
      k (by omega) _ C D H₃ hZ]
    exact hcomponentzero 2
  have hB : valueRingHom 1 B = 0 :=
    (value_odd_coefficient_of_cyclic_axis_decomposition k (by omega) _ A B H₂ hQ).trans hQderivative
  have hD : valueRingHom 1 D = 0 :=
    (value_odd_coefficient_of_cyclic_axis_decomposition k (by omega) _ C D H₃ hZ).trans hZderivative
  have hunit : valueRingHom 2 H₂ ≠ 0 ∨ valueRingHom 2 H₃ ≠ 0 := by
    by_contra hz
    push Not at hz
    apply hquadratic
    constructor
    · exact exists_scalar_quadratic_jet_of_axis_decomposition k hk _ A B H₂ hA
        (mem_maximalIdeal_iff.mpr hB) (mem_maximalIdeal_iff.mpr hz.1) hQ
    · exact exists_scalar_quadratic_jet_of_axis_decomposition k hk _ C D H₃ hC
        (mem_maximalIdeal_iff.mpr hD) (mem_maximalIdeal_iff.mpr hz.2) hZ
  exact not_hasInjectiveRepresentative_of_critical_axis_decompositions
    g k hk A B C D hA hC hB hD H₂ H₃ hunit hP hQ hZ

end OnLeConjecture.DTwo
