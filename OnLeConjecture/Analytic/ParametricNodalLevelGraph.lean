/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticCrossingSpecialization
public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.QuadraticCrossingPersistence

/-!
# Analytic level graphs for a deformation of a node

Two one-variable parametric Morse transformations produce an analytic
critical level. One of its two branches projects regularly to `Y+X`.
Reparametrizing that branch gives a graph with prescribed `Y+X` and
parameter coordinates. The branch projection is proved to be regular.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.ParametricNodalLevel

open OnLeConjecture.Analytic.Germ PointedMapGerm QuadraticCrossing

@[expose] noncomputable def swapPlane : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (fun z => ![z 1, z 0])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i <;> exact
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) _).analyticAt 0)
    (by ext i; fin_cases i <;> rfl)

@[simp] theorem swapPlane_component (i : Fin 2) :
    swapPlane.1.component i = ![coordinate 1, coordinate 0] i := by
  fin_cases i <;> apply Subtype.ext <;> rfl

@[simp] theorem swapPlane_pullback_coordinate (i : Fin 2) :
    swapPlane.pullbackRingHom (coordinate i) = ![coordinate 1, coordinate 0] i := by
  rw [pullback_coordinate, swapPlane_component]

private theorem exists_first_morse (g A : Germ 3)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A) :
    ∃ e : PointedEquivGerm 3, ∃ h : Germ 2,
      e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension 2 h ∧
      (∀ q : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 q) =
        hyperplaneExtension 2 q) ∧ h ∈ maximalIdeal 2 ∧
      hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2) ∧
      valueRingHom 3 (partialDerivative 2 (e.forward.1.component 0)) = 0 := by
  have hgmax : g ∈ maximalIdeal 3 := by rw [mem_maximalIdeal_iff, hg]; simp
  have hderivative : partialDerivative 0 g =
      (2 : Germ 3) * coordinate 0 + coordinate 1 * partialDerivative 0 A := by
    rw [hg, partialDerivative_add, partialDerivative_sub, partialDerivative_pow,
      partialDerivative_pow, partialDerivative_mul]
    simp [smul_eq_mul, nsmul_eq_mul]
  have hfirst : valueRingHom 3 (partialDerivative 0 g) = 0 := by
    rw [hderivative]
    simp
  have hsecond : valueRingHom 3 (partialDerivative 0 (partialDerivative 0 g)) ≠ 0 := by
    rw [hderivative, partialDerivative_add, partialDerivative_mul, partialDerivative_mul]
    simp only [Fin.isValue, partialDerivative_coordinate_same, mul_one, ne_eq,
      zero_ne_one, not_false_eq_true, partialDerivative_coordinate_ne, zero_mul,
      zero_add, map_add, map_mul, valueRingHom_coordinate, mul_zero, add_zero]
    rw [map_ofNat]
    exact two_ne_zero
  obtain ⟨e, h, hnormal, hfix, hh⟩ :=
    exists_finite_parametric_morse_normal_form g hgmax hfirst hsecond
  obtain ⟨hres, hsign⟩ := morse_specialization_eq_or_eq_neg g A e h hg hnormal hfix
  refine ⟨e, h, hnormal, hfix, hh, hres, ?_⟩
  have hchain : partialDerivative 1
      (specialGerm.pullbackRingHom (e.forward.1.component 0)) =
      specialGerm.pullbackRingHom (partialDerivative 2 (e.forward.1.component 0)) := by
    change partialDerivative 1 (compPointed _ specialGerm) = _
    rw [partialDerivative_compPointed_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
    simp [specialGerm_component]
  have hz : partialDerivative 1
      (specialGerm.pullbackRingHom (e.forward.1.component 0)) = 0 := by
    rcases hsign with hs | hs
    · rw [hs, partialDerivative_coordinate_ne (by decide : (1 : Fin 2) ≠ 0)]
    · rw [hs, partialDerivative_neg, partialDerivative_coordinate_ne
        (by decide : (1 : Fin 2) ≠ 0), neg_zero]
  rw [hchain] at hz
  have hv := congrArg (valueRingHom 2) hz
  simpa only [valueRingHom_pullback, map_zero] using hv

private theorem exists_second_morse (h : Germ 2)
    (hh : h ∈ maximalIdeal 2)
    (hres : hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2)) :
    ∃ d : PointedEquivGerm 2, ∃ b : Germ 1,
      (swapPlane.comp d.forward).pullbackRingHom h =
        -(coordinate (0 : Fin 2) ^ 2) + hyperplaneExtension 1 b ∧
      (∀ q : Germ 1, d.pullbackAlgEquiv (hyperplaneExtension 1 q) =
        hyperplaneExtension 1 q) ∧ b ∈ maximalIdeal 1 := by
  obtain ⟨a, ha⟩ := exists_eq_hyperplaneExtension_add_coordinate_mul h
  have hshape : h = -(coordinate (1 : Fin 2) ^ 2) + coordinate 0 * a := by
    rw [ha, hres, map_neg, map_pow, hyperplaneExtension_coordinate]
    rfl
  let f := -swapPlane.pullbackRingHom h
  have hf : f = coordinate (0 : Fin 2) ^ 2 -
      coordinate 1 * swapPlane.pullbackRingHom a := by
    dsimp only [f]
    rw [hshape, map_add, map_neg, map_pow, map_mul,
      swapPlane_pullback_coordinate, swapPlane_pullback_coordinate]
    change -(-coordinate (0 : Fin 2) ^ 2 + coordinate 1 * _) = _
    ring
  have hfmax : f ∈ maximalIdeal 2 :=
    (maximalIdeal 2).neg_mem (swapPlane.pullback_mem_maximalIdeal hh)
  have hderiv : partialDerivative 0 f =
      (2 : Germ 2) * coordinate 0 - coordinate 1 *
        partialDerivative 0 (swapPlane.pullbackRingHom a) := by
    rw [hf, partialDerivative_sub, partialDerivative_pow, partialDerivative_mul]
    simp [nsmul_eq_mul]
  have hfirst : valueRingHom 2 (partialDerivative 0 f) = 0 := by rw [hderiv]; simp
  have hsecond : valueRingHom 2 (partialDerivative 0 (partialDerivative 0 f)) ≠ 0 := by
    rw [hderiv, partialDerivative_sub, partialDerivative_mul, partialDerivative_mul]
    simp only [Fin.isValue, partialDerivative_coordinate_same, mul_one,
      partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1), zero_mul,
      zero_add, map_sub, map_add, map_mul, valueRingHom_coordinate, mul_zero, sub_zero]
    rw [map_ofNat]
    exact two_ne_zero
  obtain ⟨d, b, hnormal, hfix, hb⟩ :=
    exists_finite_parametric_morse_normal_form f hfmax hfirst hsecond
  refine ⟨d, -b, ?_, hfix, (maximalIdeal 1).neg_mem hb⟩
  change d.forward.pullbackRingHom f = _ at hnormal
  dsimp only [f] at hnormal
  rw [map_neg] at hnormal
  rw [pullbackRingHom_comp]
  change d.forward.pullbackRingHom (swapPlane.pullbackRingHom h) = _
  rw [map_neg]
  linear_combination -hnormal

/-- For a deformation of `Y²-X²`, a convergent critical-level branch
can be parametrized by `Y+X` and the unchanged deformation parameter. -/
theorem exists_level_graph (g A : Germ 3)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A) :
    ∃ b : Germ 1, ∃ s : PointedMapGerm 2 3,
      b ∈ maximalIdeal 1 ∧
      s.1.component 0 + s.1.component 2 = coordinate 0 ∧
      s.1.component 1 = coordinate 1 ∧
      s.pullbackRingHom g = hyperplaneExtension 1 b := by
  obtain ⟨e, h, hnormal, hefix, hh, hres, hederiv⟩ := exists_first_morse g A hg
  obtain ⟨d, b, hdnormal, hdfix, hb⟩ := exists_second_morse h hh hres
  have hecoord := equiv_fixes_tail_of_fixes_hyperplaneExtension e hefix
  have hdcoord := equiv_fixes_tail_of_fixes_hyperplaneExtension d hdfix
  have heone : e.forward.1.component 1 = coordinate 1 := hecoord 0
  have hetwo : e.forward.1.component 2 = coordinate 2 := hecoord 1
  have hdone : d.forward.1.component 1 = coordinate 1 := hdcoord 0
  have hdunit := first_partialDerivative_isUnit_of_equiv_fixes_tail d hdcoord
  have hdnonzero := valueRingHom_ne_zero_of_isUnit hdunit
  have hbranches (v : ℂ) (hv : v ^ 2 = 1) :
      ∃ s : PointedMapGerm 2 3,
        s.1.component 1 = coordinate 1 ∧ s.1.component 2 = d.forward.1.component 0 ∧
        s.pullbackRingHom g = hyperplaneExtension 1 b ∧
        valueRingHom 2 (partialDerivative 0 (s.1.component 0)) =
          v * valueRingHom 3 (partialDerivative 0 (e.forward.1.component 0)) := by
    obtain ⟨r, hr⟩ := exists_with_components
      (![constRingHom 2 v * coordinate 0, coordinate 1, d.forward.1.component 0] :
        Fin 3 → Germ 2)
      (by
        intro i
        fin_cases i
        · exact (maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 0)
        · exact coordinate_mem_maximalIdeal 1
        · rw [← pullback_coordinate]
          exact d.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 0))
    have htail : (hyperplaneTailGerm 2).comp r = swapPlane.comp d.forward := by
      apply ext_components
      intro i
      fin_cases i
      · rw [component_comp_eq_pullback, component_comp_eq_pullback, swapPlane_component]
        change r.pullbackRingHom (coordinate 1) = d.forward.pullbackRingHom (coordinate 1)
        rw [pullback_coordinate, pullback_coordinate, hr 1, hdone]
        rfl
      · rw [component_comp_eq_pullback, component_comp_eq_pullback, swapPlane_component]
        change r.pullbackRingHom (coordinate 2) = d.forward.pullbackRingHom (coordinate 0)
        rw [pullback_coordinate, pullback_coordinate, hr 2]
        rfl
    refine ⟨e.forward.comp r, ?_, ?_, ?_, ?_⟩
    · rw [component_comp_eq_pullback, heone, pullback_coordinate, hr 1]
      rfl
    · rw [component_comp_eq_pullback, hetwo, pullback_coordinate, hr 2]
      rfl
    · rw [pullbackRingHom_comp]
      change r.pullbackRingHom (e.pullbackAlgEquiv g) = _
      rw [hnormal, map_add, map_pow, pullback_coordinate, hr 0]
      have hH : r.pullbackRingHom (hyperplaneExtension 2 h) =
          (swapPlane.comp d.forward).pullbackRingHom h := by
        change (r.pullbackRingHom.comp (hyperplaneTailGerm 2).pullbackRingHom) h = _
        rw [← pullbackRingHom_comp, htail]
      rw [hH, hdnormal]
      change (constRingHom 2 v * coordinate 0) ^ 2 + _ = _
      rw [mul_pow, ← map_pow, hv, map_one, one_mul]
      ring
    · rw [component_comp_eq_pullback]
      change valueRingHom 2 (partialDerivative 0 (compPointed _ r)) = _
      rw [partialDerivative_compPointed_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
      change valueRingHom 2
        (r.pullbackRingHom (partialDerivative 0 (e.forward.1.component 0)) *
          partialDerivative 0 (r.1.component 0) +
          (r.pullbackRingHom (partialDerivative 1 (e.forward.1.component 0)) *
            partialDerivative 0 (r.1.component 1) +
          r.pullbackRingHom (partialDerivative 2 (e.forward.1.component 0)) *
            partialDerivative 0 (r.1.component 2))) = _
      rw [hr 0, hr 1, hr 2]
      change valueRingHom 2
        (r.pullbackRingHom (partialDerivative 0 (e.forward.1.component 0)) *
          partialDerivative 0 (constRingHom 2 v * coordinate 0) +
          (r.pullbackRingHom (partialDerivative 1 (e.forward.1.component 0)) *
            partialDerivative 0 (coordinate 1) +
          r.pullbackRingHom (partialDerivative 2 (e.forward.1.component 0)) *
            partialDerivative 0 (d.forward.1.component 0))) = _
      simp only [partialDerivative_mul, partialDerivative_const,
        partialDerivative_coordinate_same,
        partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1), zero_mul,
        mul_one, zero_add, mul_zero, map_add, map_mul, valueRingHom_pullback,
        valueRingHom_const, hederiv, add_zero]
      ring
  obtain ⟨splus, hpone, hptwo, hpnormal, hpderiv⟩ := hbranches 1 (by simp)
  obtain ⟨sminus, hmone, hmtwo, hmnormal, hmderiv⟩ := hbranches (-1) (by norm_num)
  have hregular : ∃ s : PointedMapGerm 2 3,
      s.1.component 1 = coordinate 1 ∧ s.pullbackRingHom g = hyperplaneExtension 1 b ∧
      valueRingHom 2 (partialDerivative 0 (s.1.component 0 + s.1.component 2)) ≠ 0 := by
    by_cases hp : valueRingHom 2
        (partialDerivative 0 (splus.1.component 0 + splus.1.component 2)) ≠ 0
    · exact ⟨splus, hpone, hpnormal, hp⟩
    · refine ⟨sminus, hmone, hmnormal, ?_⟩
      intro hm
      have hpzero := not_ne_iff.mp hp
      rw [partialDerivative_add, map_add, hptwo, hpderiv] at hpzero
      rw [partialDerivative_add, map_add, hmtwo, hmderiv] at hm
      apply hdnonzero
      linear_combination (hpzero + hm) / 2
  obtain ⟨s, hsone, hsnormal, hsregular⟩ := hregular
  let x := s.1.component 0 + s.1.component 2
  have hxmax : x ∈ maximalIdeal 2 := by
    apply (maximalIdeal 2).add_mem
    all_goals rw [← pullback_coordinate]
    all_goals exact s.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal _)
  have hxregular : differential x (firstCoordinateVector 1) ≠ 0 := by
    change differential x (coordinateVector 0) ≠ 0
    rw [← valueRingHom_partialDerivative]
    exact hsregular
  obtain ⟨c, hcx, hcfix⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension x hxmax hxregular
  refine ⟨b, s.comp c.inverse, hb, ?_, ?_, ?_⟩
  · rw [component_comp_eq_pullback, component_comp_eq_pullback, ← map_add]
    change c.pullbackAlgEquiv.symm x = coordinate 0
    rw [← hcx, c.pullbackAlgEquiv.symm_apply_apply]
  · rw [component_comp_eq_pullback, hsone]
    change c.symm.pullbackAlgEquiv (coordinate 1) = coordinate 1
    change c.symm.pullbackAlgEquiv (hyperplaneExtension 1 (coordinate 0)) =
      hyperplaneExtension 1 (coordinate 0)
    exact c.symm_pullback_hyperplaneExtension_eq hcfix _
  · rw [pullbackRingHom_comp]
    change c.inverse.pullbackRingHom (s.pullbackRingHom g) = _
    rw [hsnormal]
    exact c.symm_pullback_hyperplaneExtension_eq hcfix b

/-- The same graph theorem, with the original equation specified only
by its exact analytic restriction to the parameter-zero plane. -/
theorem exists_level_graph_of_special (g : Germ 3)
    (hspecial : specialGerm.pullbackRingHom g =
      coordinate (0 : Fin 2) ^ 2 - coordinate 1 ^ 2) :
    ∃ b : Germ 1, ∃ s : PointedMapGerm 2 3,
      b ∈ maximalIdeal 1 ∧
      s.1.component 0 + s.1.component 2 = coordinate 0 ∧
      s.1.component 1 = coordinate 1 ∧
      s.pullbackRingHom g = hyperplaneExtension 1 b := by
  obtain ⟨G, hG, hrep⟩ := exists_analyticRepresentative_allOrders g
  rw [hrep] at hspecial
  have hspec : ∀ᶠ z in nhds (0 : Source 2),
      G (specialFunction z) = z 0 ^ 2 - z 1 ^ 2 :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hspecial)
  obtain ⟨A, hA⟩ := exists_crossing_parameter_factor G hG hspec
  rw [← hrep] at hA
  exact exists_level_graph g A hA

end OnLeConjecture.Analytic.ParametricNodalLevel
