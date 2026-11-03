/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteExceptionalBasepoints
public import OnLeConjecture.Analytic.PlaneElimination
import Mathlib.Tactic

/-!
# Weak ideals under a change of source coordinates

The analytic lift of a source equivalence identifies the weak ideals in
the corresponding projective charts. Every weak generator has the same
exceptional unit factor, so the generated ideals are equivalent. Properness
and every adic order bound are preserved. No completeness or principalization
is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem span_range_unit_mul {ι : Type*} (U : Germ 2) (hU : IsUnit U) (F : ι → Germ 2) :
    Ideal.span (Set.range (fun i => U * F i)) = Ideal.span (Set.range F) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ U (Ideal.subset_span (Set.mem_range_self i))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    apply (Ideal.unit_mul_mem_iff_mem _ hU).mp
    exact Ideal.subset_span (Set.mem_range_self i)

/-- Weak generators in one projective chart, defined by analytic division
of the source pullbacks by the common exceptional power. -/
@[expose] noncomputable def projectiveWeakGenerators
    {ι : Type*} (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) (t : Option ℂ) : ι → Germ 2 :=
  fun i => pointBlowupTransform (projectiveChartCenter t) m
    ((projectiveChartSource t).forward.pullbackRingHom (F i))
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow (hF i))

/-- Transport of all weak generators and their ideal through the same
constructed analytic lift. The old projective chart is an output. -/
theorem exists_twoChart_weakIdeal_equivalence
    {ι : Type*} (e : PointedEquivGerm 2) (ζ : ℂ) (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) :
    ∃ (t : Option ℂ) (E : PointedEquivGerm 2) (U : Germ 2), IsUnit U ∧
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (projectiveChartSource t).forward.comp
          ((pointBlowupChartGerm (projectiveChartCenter t)).comp E.forward) ∧
      (∀ i, pointBlowupTransform ζ m (e.forward.pullbackRingHom (F i))
          (e.forward.pullback_mem_maximalIdeal_pow (hF i)) =
        U ^ m * E.forward.pullbackRingHom (projectiveWeakGenerators m F hF t i)) ∧
      Ideal.map E.forward.pullbackRingHom
          (Ideal.span (Set.range (projectiveWeakGenerators m F hF t))) =
        Ideal.span (Set.range (fun i => pointBlowupTransform ζ m
          (e.forward.pullbackRingHom (F i))
          (e.forward.pullback_mem_maximalIdeal_pow (hF i)))) ∧
      ∀ k : ℕ,
        (∀ i, pointBlowupTransform ζ m (e.forward.pullbackRingHom (F i))
            (e.forward.pullback_mem_maximalIdeal_pow (hF i)) ∈ maximalIdeal 2 ^ k) ↔
          ∀ i, projectiveWeakGenerators m F hF t i ∈ maximalIdeal 2 ^ k := by
  obtain ⟨t, E, U, hU, hEy, hcomm⟩ := exists_twoChart_blowup_lift e ζ
  have hgenerators (i : ι) : pointBlowupTransform ζ m (e.forward.pullbackRingHom (F i))
      (e.forward.pullback_mem_maximalIdeal_pow (hF i)) =
      U ^ m * E.forward.pullbackRingHom (projectiveWeakGenerators m F hF t i) := by
    have h := congrArg (fun B : PointedMapGerm 2 2 => B.pullbackRingHom (F i)) hcomm
    simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
    rw [pointBlowupTransform_factor ζ m _ (e.forward.pullback_mem_maximalIdeal_pow (hF i)),
      pointBlowupTransform_factor (projectiveChartCenter t) m _
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow (hF i)),
      map_mul, map_pow, hEy, mul_pow, mul_assoc] at h
    exact mul_left_cancel₀ (pow_ne_zero m (coordinate_ne_zero (1 : Fin 2))) h
  refine ⟨t, E, U, hU, hEy, hcomm, hgenerators, ?_, ?_⟩
  · simp_rw [hgenerators]
    rw [span_range_unit_mul (U ^ m) (hU.pow m), Ideal.map_span, ← Set.range_comp]
    rfl
  · intro k
    simp_rw [hgenerators, Ideal.unit_mul_mem_iff_mem _ (hU.pow m),
      E.pullback_mem_maximalIdeal_pow_iff]

/-- The weak-ideal equivalence applies to either chart of the changed
coordinates, including its complementary projective point. -/
theorem exists_projective_weakIdeal_equivalence
    {ι : Type*} (e : PointedEquivGerm 2) (s : Option ℂ) (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) :
    ∃ (t : Option ℂ) (E : PointedEquivGerm 2),
      Ideal.map E.forward.pullbackRingHom
          (Ideal.span (Set.range (projectiveWeakGenerators m F hF t))) =
        Ideal.span (Set.range (projectiveWeakGenerators m
          (fun i => e.forward.pullbackRingHom (F i))
          (fun i => e.forward.pullback_mem_maximalIdeal_pow (hF i)) s)) ∧
      ∀ k : ℕ,
        (∀ i, projectiveWeakGenerators m (fun i => e.forward.pullbackRingHom (F i))
            (fun i => e.forward.pullback_mem_maximalIdeal_pow (hF i)) s i ∈
              maximalIdeal 2 ^ k) ↔
          ∀ i, projectiveWeakGenerators m F hF t i ∈ maximalIdeal 2 ^ k := by
  let e' := e.comp (projectiveChartSource s)
  obtain ⟨t, E, U, _hU, _hEy, _hcomm, _hgenerators, hideal, horder⟩ :=
    exists_twoChart_weakIdeal_equivalence e' (projectiveChartCenter s) m F hF
  have hpull (i : ι) : e'.forward.pullbackRingHom (F i) =
      (projectiveChartSource s).forward.pullbackRingHom
        (e.forward.pullbackRingHom (F i)) := by
    change (e.forward.comp (projectiveChartSource s).forward).pullbackRingHom (F i) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  have hweak (i : ι) : pointBlowupTransform (projectiveChartCenter s) m
      (e'.forward.pullbackRingHom (F i)) (e'.forward.pullback_mem_maximalIdeal_pow (hF i)) =
      projectiveWeakGenerators m (fun i => e.forward.pullbackRingHom (F i))
        (fun i => e.forward.pullback_mem_maximalIdeal_pow (hF i)) s i := by
    simp only [projectiveWeakGenerators, hpull]
  refine ⟨t, E, ?_, ?_⟩
  · simpa only [hweak] using hideal
  · intro k
    simpa only [hweak] using horder k

end OnLeConjecture.Analytic.Germ
