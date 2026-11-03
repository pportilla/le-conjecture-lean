/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisMember
public import OnLeConjecture.Analytic.MatrixLinearCoordinates
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Completing a finite pair of target linear combinations

Finite intersection prevents the second coefficient row from being a scalar
multiple of the first. A third row is then constructed explicitly from a
nonzero two-by-two minor. The resulting analytic target change retains the
specified pair exactly.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

@[expose] def targetThreeRows (q r s : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ![q, r, s] i j

theorem exists_row_completion_of_not_scalar_multiple
    (q r : Fin 3 → ℂ) (hq : q ≠ 0) (hr : ¬ ∃ a : ℂ, r = a • q) :
    ∃ s : Fin 3 → ℂ, (targetThreeRows q r s).det ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have h0 : q 1 * r 2 - q 2 * r 1 = 0 := by
    have hzero := hn (Pi.single 0 1)
    rw [Matrix.det_fin_three] at hzero
    simpa [targetThreeRows, Pi.single_apply] using hzero
  have h1 : q 2 * r 0 - q 0 * r 2 = 0 := by
    have hzero := hn (Pi.single 1 1)
    rw [Matrix.det_fin_three] at hzero
    simpa [targetThreeRows, Pi.single_apply, sub_eq_add_neg, add_comm] using hzero
  have h2 : q 0 * r 1 - q 1 * r 0 = 0 := by
    have hzero := hn (Pi.single 2 1)
    rw [Matrix.det_fin_three] at hzero
    simpa [targetThreeRows, Pi.single_apply] using hzero
  apply hr
  by_cases hq0 : q 0 = 0
  · by_cases hq1 : q 1 = 0
    · have hq2 : q 2 ≠ 0 := by
        intro hz
        apply hq
        ext i
        fin_cases i <;> simp [hq0, hq1, hz]
      refine ⟨r 2 / q 2, ?_⟩
      ext i
      fin_cases i
      · change r 0 = r 2 / q 2 * q 0
        rw [hq0, mul_zero]
        apply (mul_eq_zero.mp ?_).resolve_right hq2
        simpa only [hq0, zero_mul, sub_zero, mul_comm] using h1
      · change r 1 = r 2 / q 2 * q 1
        rw [hq1, mul_zero]
        apply (mul_eq_zero.mp ?_).resolve_right hq2
        linear_combination -h0 + r 2 * hq1
      · change r 2 = r 2 / q 2 * q 2
        rw [div_mul_cancel₀ _ hq2]
    · refine ⟨r 1 / q 1, ?_⟩
      ext i
      fin_cases i
      · change r 0 = r 1 / q 1 * q 0
        rw [hq0, mul_zero]
        apply (mul_eq_zero.mp ?_).resolve_right hq1
        linear_combination -h2 + r 1 * hq0
      · change r 1 = r 1 / q 1 * q 1
        rw [div_mul_cancel₀ _ hq1]
      · change r 2 = r 1 / q 1 * q 2
        field_simp
        linear_combination h0
  · refine ⟨r 0 / q 0, ?_⟩
    ext i
    fin_cases i
    · change r 0 = r 0 / q 0 * q 0
      rw [div_mul_cancel₀ _ hq0]
    · change r 1 = r 0 / q 0 * q 1
      field_simp
      linear_combination h2
    · change r 2 = r 0 / q 0 * q 2
      field_simp
      linear_combination -h1

/-- Finite intersection of the two members permits an invertible completion
of their coefficient rows. -/
theorem exists_row_completion_of_finite_intersection
    (g : PointedMapGerm 2 3) (q r : Fin 3 → ℂ) (hq : q ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (germLinearCombination g.1.component q) (germLinearCombination g.1.component r)) :
    ∃ s : Fin 3 → ℂ, (targetThreeRows q r s).det ≠ 0 := by
  have hr : ¬ ∃ a : ℂ, r = a • q := by
    rintro ⟨a, rfl⟩
    have hmem : germLinearCombination g.1.component q ∈ maximalIdeal 2 :=
      germLinearCombination_mem g.1.component (maximalIdeal 2)
        (fun i => g.pullback_coordinate i ▸
          g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i)) q
    apply not_mem_span_singleton_of_pair_finite_colength
      (germLinearCombination g.1.component q) (germLinearCombination g.1.component (a • q))
      hmem ((PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mp hfinite)
    rw [map_smul]
    exact ((Ideal.span {germLinearCombination g.1.component q}).restrictScalars ℂ).smul_mem a
      (Ideal.subset_span (by simp))
  exact exists_row_completion_of_not_scalar_multiple q r hq hr

/-- The two prescribed coefficient rows are retained. The third row and
the invertible analytic target change are constructed from finite intersection. -/
theorem exists_target_pair_linearCombination_of_finite_intersection
    (g : PointedMapGerm 2 3) (q r : Fin 3 → ℂ) (hq : q ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (germLinearCombination g.1.component q) (germLinearCombination g.1.component r)) :
    ∃ s : Fin 3 → ℂ, ∃ f : PointedMapGerm 2 3,
      g.RightLeftEquivalent f ∧
      ∀ i : Fin 3, f.1.component i =
        germLinearCombination g.1.component (![q, r, s] i) := by
  obtain ⟨s, hs⟩ := exists_row_completion_of_finite_intersection g q r hq hfinite
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix (targetThreeRows q r s) hs
  refine ⟨s, T.forward.comp g, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · intro i
    rw [PointedMapGerm.component_comp_eq_pullback, ← T.forward.pullback_coordinate i,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, g.pullback_coordinate]
    rfl

/-- Finite intersection alone suffices: pointedness already makes both
linear combinations nonunits, and hence their coefficient rows nonzero. -/
theorem exists_target_pair_of_finite_intersection
    (g : PointedMapGerm 2 3) (q r : Fin 3 → ℂ)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (germLinearCombination g.1.component q) (germLinearCombination g.1.component r)) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      f.1.component 0 = germLinearCombination g.1.component q ∧
      f.1.component 1 = germLinearCombination g.1.component r ∧
      ∀ i, f.1.component i ∈ Submodule.span ℂ (Set.range g.1.component) := by
  have hq : q ≠ 0 := by
    intro hz
    have hfinite' : PlaneCurve.HasFiniteIntersection
        (germLinearCombination g.1.component r) 0 := by
      have hc := (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfinite
      simpa only [hz, map_zero] using hc
    have hmem : germLinearCombination g.1.component r ∈ maximalIdeal 2 :=
      germLinearCombination_mem g.1.component (maximalIdeal 2)
        (fun i => g.pullback_coordinate i ▸
          g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i)) r
    exact not_mem_span_singleton_of_pair_finite_colength
      (germLinearCombination g.1.component r) 0 hmem
      ((PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mp hfinite')
      (Ideal.zero_mem _)
  obtain ⟨s, f, hgf, hf⟩ :=
    exists_target_pair_linearCombination_of_finite_intersection g q r hq hfinite
  refine ⟨f, hgf, ?_, ?_, ?_⟩
  · simpa only [Matrix.cons_val_zero] using hf 0
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using hf 1
  · intro i
    rw [hf]
    change (∑ j, ![q, r, s] i j • g.1.component j) ∈ _
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))

end OnLeConjecture.Analytic
