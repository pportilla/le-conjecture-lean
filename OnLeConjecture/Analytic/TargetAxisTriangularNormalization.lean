/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SecondCoordinateAnalyticSubtraction
public import OnLeConjecture.Analytic.UnitCoordinateScaling

/-!
# Triangular target changes along the first coordinate

Two analytic subtractions and multiplication by a unit give the target
change needed to normalize the two odd coefficients on a critical axis.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

theorem firstCoordinateProjection_comp_firstTwo (g : PointedMapGerm 2 3) :
    firstCoordinateProjection.comp g.firstTwo = g.firstCoordinateTriple := by
  apply ext_components
  intro i
  rw [component_comp_eq_pullback, firstCoordinateProjection_component,
    pullback_coordinate, firstTwo_component, firstCoordinateTriple_component]
  rfl

theorem firstCoordinateTriple_eq_of_first_component
    (g h : PointedMapGerm 2 3) (heq : g.1.component 0 = h.1.component 0) :
    g.firstCoordinateTriple = h.firstCoordinateTriple := by
  apply ext_components
  intro i
  simp only [firstCoordinateTriple_component, heq]

/-- Normalize two coordinates by an analytic triangular target change.
The multiplier and the quotient depend only on the fixed first coordinate. -/
theorem exists_target_axis_triangular_normalization
    (g : PointedMapGerm 2 3) (A C u v : Germ 1)
    (hA : A ∈ maximalIdeal 1) (hC : C ∈ maximalIdeal 1) (hu : IsUnit u) :
    ∃ h : PointedMapGerm 2 3, g.RightLeftEquivalent h ∧
      h.1.component 0 = g.1.component 0 ∧
      h.1.component 1 =
        (g.1.component 1 - g.firstCoordinateTriple.pullbackRingHom A) *
          g.firstCoordinateTriple.pullbackRingHom u ∧
      h.1.component 2 = g.1.component 2 - g.firstCoordinateTriple.pullbackRingHom C -
        (g.1.component 1 - g.firstCoordinateTriple.pullbackRingHom A) *
          g.firstCoordinateTriple.pullbackRingHom v := by
  obtain ⟨f, hgf, hf0, hf1, hf2⟩ := g.exists_target_secondAnalyticSubtraction A hA
  let q : Germ 2 := firstCoordinateProjection.pullbackRingHom C +
    coordinate 1 * firstCoordinateProjection.pullbackRingHom v
  have hq : q ∈ maximalIdeal 2 :=
    (maximalIdeal 2).add_mem (firstCoordinateProjection.pullback_mem_maximalIdeal hC)
      ((maximalIdeal 2).mul_mem_right _ (coordinate_mem_maximalIdeal 1))
  obtain ⟨f', hff', hf'0, hf'1, hf'2⟩ := f.exists_target_subtraction q hq
  have hfirst : f.firstCoordinateTriple = g.firstCoordinateTriple :=
    firstCoordinateTriple_eq_of_first_component f g hf0
  have hfirst' : f'.firstCoordinateTriple = g.firstCoordinateTriple :=
    firstCoordinateTriple_eq_of_first_component f' g (hf'0.trans hf0)
  have hqpull : f.firstTwo.pullbackRingHom q =
      g.firstCoordinateTriple.pullbackRingHom C +
        f.1.component 1 * g.firstCoordinateTriple.pullbackRingHom v := by
    have hcomp : firstCoordinateProjection.comp f.firstTwo = g.firstCoordinateTriple :=
      (firstCoordinateProjection_comp_firstTwo f).trans hfirst
    have hscalar (a : Germ 1) : f.firstTwo.pullbackRingHom
        (firstCoordinateProjection.pullbackRingHom a) =
          g.firstCoordinateTriple.pullbackRingHom a := by
      change (f.firstTwo.pullbackRingHom.comp firstCoordinateProjection.pullbackRingHom) a = _
      rw [← pullbackRingHom_comp, hcomp]
    simp only [q, map_add, map_mul, pullback_coordinate, firstTwo_component, hscalar]
    rfl
  let units : Fin 3 → Germ 3 := ![1, firstCoordinateTripleProjection.pullbackRingHom u, 1]
  have hunits : ∀ i, IsUnit (units i) := by
    intro i
    fin_cases i
    · exact isUnit_one
    · exact hu.map firstCoordinateTripleProjection.pullbackRingHom
    · exact isUnit_one
  obtain ⟨e, he⟩ := Germ.exists_equiv_coordinate_mul_units units hunits
  let h := e.forward.comp f'
  have hfh : f'.RightLeftEquivalent h := by
    refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, comp_identity]
  have hcomponent (i : Fin 3) : h.1.component i =
      f'.1.component i * f'.pullbackRingHom (units i) := by
    change (e.forward.comp f').1.component i = _
    rw [component_comp_eq_pullback, ← pullback_coordinate, he, map_mul, pullback_coordinate]
  refine ⟨h, hgf.trans (hff'.trans hfh), ?_, ?_, ?_⟩
  · rw [hcomponent]
    change f'.1.component 0 * f'.pullbackRingHom 1 = _
    rw [map_one, mul_one, hf'0, hf0]
  · have hscalar : f'.pullbackRingHom
        (firstCoordinateTripleProjection.pullbackRingHom u) =
        g.firstCoordinateTriple.pullbackRingHom u := by
      change (f'.pullbackRingHom.comp firstCoordinateTripleProjection.pullbackRingHom) u = _
      rw [← pullbackRingHom_comp]
      change f'.firstCoordinateTriple.pullbackRingHom u = _
      rw [hfirst']
    simpa only [units, Matrix.cons_val_one, Matrix.cons_val_zero,
      hf'1, hf1, hscalar] using hcomponent 1
  · rw [hcomponent]
    change f'.1.component 2 * f'.pullbackRingHom 1 = _
    rw [map_one, mul_one, hf'2, hqpull, hf2, hf1]
    ring

end OnLeConjecture.Analytic.PointedMapGerm
