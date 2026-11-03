/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicAxisOddNormalization
public import OnLeConjecture.Analytic.InjectiveCompositionCancellation

/-!
# Exclusion from the critical-axis coefficients

Injectivity forces a nonzero odd axis coefficient. The valuation of
one-variable analytic germs chooses the coefficient of minimum order.
No distinguished nonzero coefficient or divisibility is assumed.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclic_axis_odd_coefficients_not_both_zero
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k : ℕ) (hk : 1 ≤ k) (A B C D : Germ 1) (H₂ H₃ : Germ 2)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = (cyclicScalarMap k hk).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ k * H₂)
    (hZ : g.1.component 2 = (cyclicScalarMap k hk).pullbackRingHom C +
      coordinate 0 * (cyclicScalarMap k hk).pullbackRingHom D + coordinate 1 ^ k * H₃) :
    B ≠ 0 ∨ D ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hB, hD⟩
  obtain ⟨a, ha⟩ := PointedMapGerm.exists_with_components
    (![coordinate (0 : Fin 1), 0] : Fin 2 → Germ 1)
    (by
      intro i
      fin_cases i
      · exact coordinate_mem_maximalIdeal 0
      · exact Ideal.zero_mem _)
  obtain ⟨b, hb⟩ := PointedMapGerm.exists_with_components
    (![-coordinate (0 : Fin 1), 0] : Fin 2 → Germ 1)
    (by
      intro i
      fin_cases i
      · exact (maximalIdeal 1).neg_mem (coordinate_mem_maximalIdeal 0)
      · exact Ideal.zero_mem _)
  have hσ : (cyclicScalarMap k hk).comp a = (cyclicScalarMap k hk).comp b := by
    apply PointedMapGerm.ext_components
    intro i
    simp only [PointedMapGerm.component_comp_eq_pullback, cyclicScalarMap_component,
      map_add, map_pow, PointedMapGerm.pullback_coordinate, ha, hb,
      Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq]
  have hscalar (q : Germ 1) :
      a.pullbackRingHom ((cyclicScalarMap k hk).pullbackRingHom q) =
        b.pullbackRingHom ((cyclicScalarMap k hk).pullbackRingHom q) := by
    have h := congrArg (fun f : PointedMapGerm 1 1 => f.pullbackRingHom q) hσ
    simpa only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] using h
  have hcomp : g.comp a = g.comp b := by
    apply PointedMapGerm.ext_components
    intro i
    rw [PointedMapGerm.component_comp_eq_pullback, PointedMapGerm.component_comp_eq_pullback]
    fin_cases i
    · change a.pullbackRingHom (g.1.component 0) = b.pullbackRingHom (g.1.component 0)
      rw [hP]
      simp only [cyclicFirst, map_add, map_pow, PointedMapGerm.pullback_coordinate,
        ha, hb, Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq]
    · change a.pullbackRingHom (g.1.component 1) = b.pullbackRingHom (g.1.component 1)
      rw [hQ, hB, map_zero, mul_zero, add_zero]
      simp only [map_add, map_mul, map_pow, PointedMapGerm.pullback_coordinate,
        ha, hb, Matrix.cons_val_one, Matrix.cons_val_zero,
        zero_pow (by omega : k ≠ 0), zero_mul, add_zero, hscalar]
    · change a.pullbackRingHom (g.1.component 2) = b.pullbackRingHom (g.1.component 2)
      rw [hZ, hD, map_zero, mul_zero, add_zero]
      simp only [map_add, map_mul, map_pow, PointedMapGerm.pullback_coordinate,
        ha, hb, Matrix.cons_val_one, Matrix.cons_val_zero,
        zero_pow (by omega : k ≠ 0), zero_mul, add_zero, hscalar]
  have hab := hg.comp_left_cancel hcomp
  have hcoord := congrArg (fun f : PointedMapGerm 1 2 => f.1.component 0) hab
  rw [ha, hb] at hcoord
  change coordinate (0 : Fin 1) = -coordinate 0 at hcoord
  apply coordinate_zero_ne_zero
  have htwo : (2 : Germ 1) ≠ 0 := by
    intro hz
    have hv := congrArg (valueRingHom 1) hz
    rw [map_ofNat, map_zero] at hv
    norm_num at hv
  exact (mul_eq_zero.mp (show (2 : Germ 1) * coordinate 0 = 0 by
    linear_combination hcoord)).resolve_left htwo

theorem exists_target_swap_last_two (g : PointedMapGerm 2 3) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      f.1.component 0 = g.1.component 0 ∧
      f.1.component 1 = g.1.component 2 ∧ f.1.component 2 = g.1.component 1 := by
  let L : Source 3 ≃ₗ[ℂ] Source 3 :=
    { toFun := fun z => ![z 0, z 2, z 1]
      invFun := fun z => ![z 0, z 2, z 1]
      map_add' := by intro z w; ext i; fin_cases i <;> rfl
      map_smul' := by intro c z; ext i; fin_cases i <;> rfl
      left_inv := by intro z; ext i; fin_cases i <;> rfl
      right_inv := by intro z; ext i; fin_cases i <;> rfl }
  let e := pointedEquivGermOfContinuousLinearEquiv L.toContinuousLinearEquiv
  have he (i : Fin 3) : e.forward.1.component i =
      (![coordinate 0, coordinate 2, coordinate 1] : Fin 3 → Germ 3) i := by
    apply Subtype.ext
    fin_cases i <;> rfl
  refine ⟨e.forward.comp g, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  all_goals
    rw [PointedMapGerm.component_comp_eq_pullback, he]
    exact PointedMapGerm.pullback_coordinate g _

theorem not_hasInjectiveRepresentative_of_critical_axis_decompositions
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (A B C D : Germ 1) (hA : A ∈ maximalIdeal 1) (hC : C ∈ maximalIdeal 1)
    (hBzero : valueRingHom 1 B = 0) (hDzero : valueRingHom 1 D = 0)
    (H₂ H₃ : Germ 2) (hunit : valueRingHom 2 H₂ ≠ 0 ∨ valueRingHom 2 H₃ ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom B + coordinate 1 ^ k * H₂)
    (hZ : g.1.component 2 = (cyclicScalarMap k (by omega)).pullbackRingHom C +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom D + coordinate 1 ^ k * H₃) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  have hnonzero := cyclic_axis_odd_coefficients_not_both_zero g hg k (by omega)
    A B C D H₂ H₃ hP hQ hZ
  rcases le_total (vanishingOrder B) (vanishingOrder D) with hBD | hDB
  · have hdiv : B ∣ D := vanishingOrder_le_iff_dvd.mp hBD
    have hB : B ≠ 0 := by
      intro hz
      have hD : D = 0 := by simpa [hz] using hdiv
      exact hnonzero.elim (fun h => h hz) (fun h => h hD)
    exact not_hasInjectiveRepresentative_of_axis_decompositions
      g k hk A B C D hA hC hB hBzero hdiv H₂ H₃ hunit hP hQ hZ hg
  · have hdiv : D ∣ B := vanishingOrder_le_iff_dvd.mp hDB
    have hD : D ≠ 0 := by
      intro hz
      have hB : B = 0 := by simpa [hz] using hdiv
      exact hnonzero.elim (fun h => h hB) (fun h => h hz)
    obtain ⟨f, hgf, hf0, hf1, hf2⟩ := exists_target_swap_last_two g
    exact not_hasInjectiveRepresentative_of_axis_decompositions
      f k hk C D A B hC hA hD hDzero hdiv H₃ H₂ hunit.symm
      (hf0.trans hP) (hf1.trans hZ) (hf2.trans hQ) (hgf.hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
