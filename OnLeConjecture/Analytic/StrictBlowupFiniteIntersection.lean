/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakBlowupFiniteColength
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Finite intersection after removing individual exceptional powers

The generators may have different orders. Their strict-transform ideal
contains the pulled-back ideal and therefore an exceptional-coordinate
power. An exact-order generator has a nonzero exceptional restriction.
These two facts prove finite colength without assuming that the strict
transforms have no common branch.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem not_mem_succ_maximalIdeal_pow_of_first_regular
    (m : ℕ) (f : Germ 2) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    f ∉ maximalIdeal 2 ^ (m + 1) := by
  intro h
  have hline := (lineGerm (firstCoordinateVector 1)).pullback_mem_maximalIdeal_pow h
  have ho := mem_maximalIdeal_one_pow_iff.mp hline
  change ((m + 1 : ℕ) : ℕ∞) ≤ vanishingOrder
    (lineRestriction (firstCoordinateVector 1) f) at ho
  rw [hregular] at ho
  have : m + 1 ≤ m := by exact_mod_cast ho
  omega

/-- Finite colength is preserved when each generator is divided by its
own exceptional power, provided one removed power is its exact order. -/
theorem strictIdeal_quotient_moduleFinite
    {ι : Type*} [Finite ι] (c : ℂ) (m : ι → ℕ) (F G : ι → Germ 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (hexact : ∃ i, F i ∈ maximalIdeal 2 ^ m i ∧
      F i ∉ maximalIdeal 2 ^ (m i + 1))
    (htransform : ∀ i, (pointBlowupChartGerm c).pullbackRingHom (F i) =
      coordinate (1 : Fin 2) ^ m i * G i) :
    Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range G)) := by
  obtain ⟨N, hN⟩ := exists_exceptional_power_mem_weakIdeal c 0 F
    (fun i ↦ (pointBlowupChartGerm c).pullbackRingHom (F i)) hfinite (by simp)
  have hle : Ideal.span (Set.range
      (fun i ↦ (pointBlowupChartGerm c).pullbackRingHom (F i))) ≤
      Ideal.span (Set.range G) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    rw [htransform]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  have hNJ := hle hN
  obtain ⟨i, hi, hinext⟩ := hexact
  have hrestriction := pointBlowupTransform_exceptionalRestriction_ne_zero
    c (m i) (F i) (G i) hi hinext (htransform i)
  have hline : lineRestriction (firstCoordinateVector 1) (G i) ≠ 0 := by
    change (lineGerm (firstCoordinateVector 1)).pullbackRingHom (G i) ≠ 0
    rwa [← pointBlowupExceptionalLine_eq_lineGerm]
  have htop : vanishingOrder (lineRestriction (firstCoordinateVector 1) (G i)) ≠ ⊤ :=
    vanishingOrder_eq_top_iff.not.mpr hline
  let k := (vanishingOrder (lineRestriction (firstCoordinateVector 1) (G i))).toNat
  have hregular : IsRegularInFirstCoordinateOfOrder (G i) k :=
    (ENat.natCast_toNat htop).symm
  cases hk : k with
  | zero =>
      rw [hk] at hregular
      obtain ⟨u, hu, hGu, _⟩ := exists_finite_expansion_of_regular hregular
      have hGu' : G i = u := by simpa using hGu
      have hGUnit : IsUnit (G i) := hGu' ▸ hu
      have hJ : Ideal.span (Set.range G) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self i)) hGUnit
      apply quotient_moduleFinite_of_maximalIdeal_pow_le (N := 0)
      rw [hJ]
      exact le_top
  | succ d =>
      rw [hk] at hregular
      apply quotient_moduleFinite_of_regular_mem_and_parameter_mem
        (Ideal.span (Set.range G)) hregular (Ideal.subset_span (Set.mem_range_self i))
        (pow_ne_zero N coordinate_zero_ne_zero)
      simpa only [map_pow, hyperplaneExtension_coordinate_plane] using hNJ

/-- Two finite-intersection equations retain finite intersection in every
finite blowup chart after removal of their possibly different powers. -/
theorem hasFiniteIntersection_pointBlowupTransforms
    (c : ℂ) (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g) :
    PlaneCurve.HasFiniteIntersection
      (pointBlowupTransform c m f hf) (pointBlowupTransform c n g hg) := by
  have hspan (a b : Germ 2) : Ideal.span (Set.range (![a, b] : Fin 2 → Germ 2)) =
      PlaneCurve.pairIdeal a b := by
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  apply (show Module.Finite ℂ (Germ 2 ⧸ PlaneCurve.pairIdeal _ _) from ?_)
  rw [← hspan]
  apply strictIdeal_quotient_moduleFinite c (![m, n] : Fin 2 → ℕ)
    (![f, g] : Fin 2 → Germ 2)
  · rw [hspan]
    exact hfinite
  · exact ⟨0, hf, hfnext⟩
  · intro i
    fin_cases i
    · exact pointBlowupTransform_factor c m f hf
    · exact pointBlowupTransform_factor c n g hg

end OnLeConjecture.Analytic.Germ
