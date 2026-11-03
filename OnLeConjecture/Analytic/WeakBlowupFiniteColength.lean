/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularBlowupCharts
public import OnLeConjecture.Analytic.PlaneElimination
import Mathlib.Tactic

/-!
# Finite colength of analytic weak transforms

After removal of the common exceptional power, a finite-colength ideal
still contains an exceptional-coordinate power. An exact-order generator
has a nonzero restriction to the exceptional line. Together these facts
prove finite colength at every point of a finite blowup chart. This does
not yet establish a decreasing invariant or termination of principalization.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

theorem pointBlowupTransform_exceptionalRestriction_ne_zero
    (c : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) :
    pointBlowupExceptionalLine.pullbackRingHom g ≠ 0 := by
  obtain ⟨g', P, T, hfactor, _, _, _, _, hT, hdegree, hrestriction, _⟩ :=
    exists_pointBlowupTransform_with_initial c m f hf hnext
  have hgg' := pointBlowupTransform_unique c m f g g' htransform hfactor
  rw [hgg', hrestriction]
  intro hz
  exact oneVariablePolynomialEvaluation_not_mem_pow m T hT hdegree
    (hz ▸ (maximalIdeal 1 ^ (m + 1)).zero_mem)

/-- A common exceptional factor can be cancelled in the representation
of a sufficiently large coordinate power by the original generators. -/
theorem exceptional_power_mem_weakIdeal
    {ι : Type*} [Finite ι] (c : ℂ) (m N : ℕ) (F G : ι → Germ 2)
    (hpower : coordinate (1 : Fin 2) ^ (m + N) ∈ Ideal.span (Set.range F))
    (htransform : ∀ i, (pointBlowupChartGerm c).pullbackRingHom (F i) =
      coordinate (1 : Fin 2) ^ m * G i) :
    coordinate (1 : Fin 2) ^ N ∈ Ideal.span (Set.range G) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hpower
  have hpull := congrArg (pointBlowupChartGerm c).pullbackRingHom ha
  simp only [map_sum, map_mul, htransform, map_pow,
    pointBlowupChartGerm_pullback_one, pow_add] at hpull
  have heq : ∑ i, (pointBlowupChartGerm c).pullbackRingHom (a i) * G i =
      coordinate (1 : Fin 2) ^ N := by
    apply mul_left_cancel₀ (pow_ne_zero m (coordinate_ne_zero (1 : Fin 2)))
    calc
      coordinate (1 : Fin 2) ^ m *
          (∑ i, (pointBlowupChartGerm c).pullbackRingHom (a i) * G i) =
        ∑ i, (pointBlowupChartGerm c).pullbackRingHom (a i) *
          (coordinate (1 : Fin 2) ^ m * G i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = coordinate (1 : Fin 2) ^ m * coordinate (1 : Fin 2) ^ N := hpull
  rw [← heq]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span (Set.mem_range_self i))

theorem exists_exceptional_power_mem_weakIdeal
    {ι : Type*} [Finite ι] (c : ℂ) (m : ℕ) (F G : ι → Germ 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (htransform : ∀ i, (pointBlowupChartGerm c).pullbackRingHom (F i) =
      coordinate (1 : Fin 2) ^ m * G i) :
    ∃ N : ℕ, coordinate (1 : Fin 2) ^ N ∈ Ideal.span (Set.range G) := by
  obtain ⟨N, hN⟩ :=
    (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le _).mp hfinite
  refine ⟨N, exceptional_power_mem_weakIdeal c m N F G ?_ htransform⟩
  rw [pow_add]
  exact Ideal.mul_mem_left _ _
    (hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (1 : Fin 2)) N))

/-- Every weak ideal in a finite blowup chart has finite colength, provided
the exceptional factor removed is exactly the order of the original ideal. -/
theorem weakIdeal_quotient_moduleFinite
    {ι : Type*} [Finite ι] (c : ℂ) (m : ℕ) (F G : ι → Germ 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (horder : ∀ i, F i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, F i ∉ maximalIdeal 2 ^ (m + 1))
    (htransform : ∀ i, (pointBlowupChartGerm c).pullbackRingHom (F i) =
      coordinate (1 : Fin 2) ^ m * G i) :
    Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range G)) := by
  obtain ⟨N, hN⟩ := exists_exceptional_power_mem_weakIdeal c m F G hfinite htransform
  obtain ⟨i, hi⟩ := hexact
  have hrestriction := pointBlowupTransform_exceptionalRestriction_ne_zero
    c m (F i) (G i) (horder i) hi (htransform i)
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
      simpa only [map_pow, hyperplaneExtension_coordinate_plane] using hN

end OnLeConjecture.Analytic.Germ
