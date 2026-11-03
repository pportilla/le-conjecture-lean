/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolynomial
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism
public import OnLeConjecture.Analytic.DividedCoefficientOrders
public import OnLeConjecture.PlaneCurve.ParametricMorse

/-!
# Lifting analytic parameter translations through a point blowup

An analytic translation `x ↦ x+a(y)` with `a(0)=0` lifts through every
finite blowup chart. Division by `y` determines the translation of the
exceptional center and the pointed translation of the strict-transform
coordinates. All identities are identities of analytic map germs.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The analytic parameter translation, with its coordinate identities. -/
theorem exists_parameterTranslation
    (a : Germ 1) (ha : a ∈ maximalIdeal 1) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinate 0 + hyperplaneExtension 1 a ∧
      ∀ b : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 b) =
        hyperplaneExtension 1 b := by
  let x' := coordinate (0 : Fin 2) + hyperplaneExtension 1 a
  have hx' : x' ∈ maximalIdeal 2 := (maximalIdeal 2).add_mem
    (coordinate_mem_maximalIdeal 0) ((hyperplaneTailGerm 1).pullback_mem_maximalIdeal ha)
  have hd : differential x' (firstCoordinateVector 1) ≠ 0 := by
    rw [show x' = coordinate (0 : Fin 2) + hyperplaneExtension 1 a from rfl,
      differential_add]
    change differential (coordinate (0 : Fin 2)) (firstCoordinateVector 1) +
      differential (hyperplaneExtension 1 a) (firstCoordinateVector 1) ≠ 0
    rw [differential_coordinate_apply, differential_hyperplaneExtension_firstCoordinate]
    simp [firstCoordinateVector]
  obtain ⟨e, hx, hb⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension x' hx' hd
  exact ⟨e, hx, hb⟩

theorem parameterTranslation_preserves_y
    (e : PointedEquivGerm 2)
    (he : ∀ b : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 b) =
      hyperplaneExtension 1 b) :
    e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 := by
  simpa only [hyperplaneExtension_coordinate_plane] using he (coordinate (0 : Fin 1))

/-- Dividing the translation by the parameter gives the commuting
finite-chart square, including the shift of the exceptional center. -/
theorem parameterTranslation_blowup_identity
    (a b : Germ 1) (c ζ : ℂ)
    (hab : a = coordinate (0 : Fin 1) * (b + constRingHom 1 c))
    (e E : PointedEquivGerm 2)
    (hex : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 + hyperplaneExtension 1 a)
    (hea : ∀ q : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 q) =
      hyperplaneExtension 1 q)
    (hEx : E.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 + hyperplaneExtension 1 b)
    (hEa : ∀ q : Germ 1, E.forward.pullbackRingHom (hyperplaneExtension 1 q) =
      hyperplaneExtension 1 q) :
    e.forward.comp (pointBlowupChartGerm (ζ - c)) =
      (pointBlowupChartGerm ζ).comp E.forward := by
  have hey := parameterTranslation_preserves_y e hea
  have hEy := parameterTranslation_preserves_y E hEa
  apply PointedMapGerm.ext_components
  intro j
  have hcomponent (B : PointedMapGerm 2 2) : B.1.component j =
      B.pullbackRingHom (coordinate j) := (B.pullback_coordinate j).symm
  rw [hcomponent, hcomponent, PointedMapGerm.pullbackRingHom_comp,
    PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, RingHom.comp_apply]
  fin_cases j
  · change (pointBlowupChartGerm (ζ - c)).pullbackRingHom
      (e.forward.pullbackRingHom (coordinate (0 : Fin 2))) =
        E.forward.pullbackRingHom ((pointBlowupChartGerm ζ).pullbackRingHom (coordinate 0))
    rw [hex, map_add, pointBlowupChartGerm_pullback_zero,
      pointBlowupChart_pullback_hyperplaneExtension, pointBlowupChartGerm_pullback_zero,
      map_mul, map_add, hEx, hEy, PointedMapGerm.pullback_constRingHom,
      hab, map_mul, map_add, hyperplaneExtension_coordinate_plane]
    change _ + coordinate (1 : Fin 2) * (hyperplaneExtension 1 b +
      (hyperplaneTailGerm 1).pullbackRingHom (constRingHom 1 c)) = _
    rw [PointedMapGerm.pullback_constRingHom, map_sub]
    ring
  · change (pointBlowupChartGerm (ζ - c)).pullbackRingHom
      (e.forward.pullbackRingHom (coordinate (1 : Fin 2))) =
        E.forward.pullbackRingHom ((pointBlowupChartGerm ζ).pullbackRingHom (coordinate 1))
    rw [hey, pointBlowupChartGerm_pullback_one, pointBlowupChartGerm_pullback_one, hEy]

/-- The quotient by `y`, its residue, and its pointed remainder are
constructed from any analytic translation vanishing at the origin. -/
theorem exists_parameterTranslation_blowup_lift
    (a : Germ 1) (ha : a ∈ maximalIdeal 1) :
    ∃ b : Germ 1, ∃ c : ℂ, ∃ e E : PointedEquivGerm 2,
      b ∈ maximalIdeal 1 ∧
      a = coordinate (0 : Fin 1) * (b + constRingHom 1 c) ∧
      e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinate 0 + hyperplaneExtension 1 a ∧
      E.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinate 0 + hyperplaneExtension 1 b ∧
      (∀ q : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 q) =
        hyperplaneExtension 1 q) ∧
      (∀ q : Germ 1, E.forward.pullbackRingHom (hyperplaneExtension 1 q) =
        hyperplaneExtension 1 q) ∧
      ∀ ζ : ℂ, e.forward.comp (pointBlowupChartGerm (ζ - c)) =
        (pointBlowupChartGerm ζ).comp E.forward := by
  have hdiv : coordinate (0 : Fin 1) ∣ a := by
    rw [← Ideal.mem_span_singleton, ← pow_one (coordinate (0 : Fin 1)),
      ← maximalIdeal_one_pow_eq_span_coordinate_pow, pow_one]
    exact ha
  obtain ⟨q, hq⟩ := hdiv
  let c := valueRingHom 1 q
  let b := q - constRingHom 1 c
  have hb : b ∈ maximalIdeal 1 := by simp [b, c, mem_maximalIdeal_iff]
  have hfactor : a = coordinate (0 : Fin 1) * (b + constRingHom 1 c) := by
    simpa only [b, sub_add_cancel] using hq
  obtain ⟨e, hex, hea⟩ := exists_parameterTranslation a ha
  obtain ⟨E, hEx, hEa⟩ := exists_parameterTranslation b hb
  exact ⟨b, c, e, E, hb, hfactor, hex, hEx, hea, hEa,
    fun ζ ↦ parameterTranslation_blowup_identity a b c ζ hfactor e E hex hea hEx hEa⟩

/-- A translation of order at least two does not shift the exceptional
center. Its divided translation still vanishes at the new origin. -/
theorem exists_parameterTranslation_zero_center_lift
    (a : Germ 1) (ha : a ∈ maximalIdeal 1 ^ 2) :
    ∃ b : Germ 1, ∃ e E : PointedEquivGerm 2,
      b ∈ maximalIdeal 1 ∧ a = coordinate (0 : Fin 1) * b ∧
      e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinate 0 + hyperplaneExtension 1 a ∧
      E.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinate 0 + hyperplaneExtension 1 b ∧
      ∀ ζ : ℂ, e.forward.comp (pointBlowupChartGerm ζ) =
        (pointBlowupChartGerm ζ).comp E.forward := by
  have ha₁ : a ∈ maximalIdeal 1 := by
    simpa only [pow_one] using Ideal.pow_le_pow_right (by decide : 1 ≤ 2) ha
  obtain ⟨b, c, e, E, hb, hfactor, hex, hEx, _hea, _hEa, hlift⟩ :=
    exists_parameterTranslation_blowup_lift a ha₁
  have hq : b + constRingHom 1 c ∈ maximalIdeal 1 := by
    have hmul : coordinate (0 : Fin 1) ^ 1 * (b + constRingHom 1 c) ∈
        maximalIdeal 1 ^ (1 + 1) := by simpa only [pow_one, ← hfactor] using ha
    simpa only [pow_one] using (coordinate_pow_mul_mem_pow_add_iff 1 1 _).mp hmul
  have hc : c = 0 := by
    have h := (maximalIdeal 1).sub_mem hq hb
    simpa only [add_sub_cancel_left, mem_maximalIdeal_iff, valueRingHom_const] using h
  subst c
  refine ⟨b, e, E, hb, ?_, hex, hEx, ?_⟩
  · simpa only [map_zero, add_zero] using hfactor
  · intro ζ
    simpa only [sub_zero] using hlift ζ

end OnLeConjecture.Analytic.Germ
