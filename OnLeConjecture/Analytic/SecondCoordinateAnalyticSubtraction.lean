/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SecondCoordinateSubtraction
public import OnLeConjecture.Analytic.SecondCoordinatePolynomialSubtraction
public import OnLeConjecture.Analytic.FiniteParametricMorse

/-!
# Analytic second-coordinate subtraction for triples

An arbitrary convergent one-variable germ vanishing at zero can be
subtracted from the second coordinate while fixing the first and third.
The coordinate identities and the preservation of common Jacobian
divisors hold for analytic germs, without a polynomial restriction.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Projection of a triple to its first scalar coordinate. -/
@[expose] noncomputable def firstCoordinateTripleProjection : PointedMapGerm 3 1 :=
  firstCoordinateProjection.comp firstTwoProjection

@[simp] theorem firstCoordinateTripleProjection_component (i : Fin 1) :
    firstCoordinateTripleProjection.1.component i = Germ.coordinate (0 : Fin 3) := by
  rw [firstCoordinateTripleProjection, component_comp_eq_pullback,
    firstCoordinateProjection_component, pullback_coordinate, firstTwoProjection_component]
  rfl

/-- The pointed scalar map defined by the first component of a triple. -/
@[expose] noncomputable def firstCoordinateTriple (g : PointedMapGerm 2 3) :
    PointedMapGerm 2 1 := firstCoordinateTripleProjection.comp g

@[simp] theorem firstCoordinateTriple_component (g : PointedMapGerm 2 3) (i : Fin 1) :
    g.firstCoordinateTriple.1.component i = g.1.component 0 := by
  rw [firstCoordinateTriple, component_comp_eq_pullback,
    firstCoordinateTripleProjection_component, pullback_coordinate]

private theorem firstCoordinateTripleProjection_comp_of_component
    (f : PointedMapGerm 3 3) (hf : f.1.component 0 = Germ.coordinate 0) :
    firstCoordinateTripleProjection.comp f = firstCoordinateTripleProjection := by
  apply ext_components
  intro i
  rw [component_comp_eq_pullback, firstCoordinateTripleProjection_component,
    pullback_coordinate, hf]

/-- The shear subtracting an arbitrary analytic germ has the analytic
inverse which adds that same germ. -/
theorem exists_secondCoordinateAnalyticSubtraction
    (q : Germ 1) (hq : q ∈ Germ.maximalIdeal 1) :
    ∃ e : PointedEquivGerm 3,
      e.forward.1.component 0 = Germ.coordinate 0 ∧
      e.forward.1.component 1 = Germ.coordinate 1 -
        firstCoordinateTripleProjection.pullbackRingHom q ∧
      e.forward.1.component 2 = Germ.coordinate 2 := by
  let v := firstCoordinateTripleProjection.pullbackRingHom q
  have hv : v ∈ Germ.maximalIdeal 3 :=
    firstCoordinateTripleProjection.pullback_mem_maximalIdeal hq
  obtain ⟨f, hf⟩ := exists_with_components
    (![Germ.coordinate 0, Germ.coordinate 1 - v, Germ.coordinate 2] : Fin 3 → Germ 3)
    (by
      intro i
      fin_cases i
      · exact Germ.coordinate_mem_maximalIdeal 0
      · exact (Germ.maximalIdeal 3).sub_mem (Germ.coordinate_mem_maximalIdeal 1) hv
      · exact Germ.coordinate_mem_maximalIdeal 2)
  obtain ⟨g, hg⟩ := exists_with_components
    (![Germ.coordinate 0, Germ.coordinate 1 + v, Germ.coordinate 2] : Fin 3 → Germ 3)
    (by
      intro i
      fin_cases i
      · exact Germ.coordinate_mem_maximalIdeal 0
      · exact (Germ.maximalIdeal 3).add_mem (Germ.coordinate_mem_maximalIdeal 1) hv
      · exact Germ.coordinate_mem_maximalIdeal 2)
  have hfix (a : PointedMapGerm 3 3) (ha : a.1.component 0 = Germ.coordinate 0) :
      a.pullbackRingHom v = v := by
    change (a.pullbackRingHom.comp firstCoordinateTripleProjection.pullbackRingHom) q = _
    rw [← pullbackRingHom_comp, firstCoordinateTripleProjection_comp_of_component a ha]
  have hfpull := hfix f (hf 0)
  have hgpull := hfix g (hg 0)
  let e : PointedEquivGerm 3 :=
    { forward := f
      inverse := g
      forward_inverse := by
        apply ext_components
        intro i
        fin_cases i
        · change (f.comp g).1.component 0 = Germ.coordinate 0
          rw [component_comp_eq_pullback, hf 0]
          change g.pullbackRingHom (Germ.coordinate 0) = Germ.coordinate 0
          rw [pullback_coordinate, hg 0]
          rfl
        · change (f.comp g).1.component 1 = Germ.coordinate 1
          rw [component_comp_eq_pullback, hf 1]
          change g.pullbackRingHom (Germ.coordinate 1 - v) = Germ.coordinate 1
          rw [map_sub, pullback_coordinate, hg 1, hgpull]
          exact add_sub_cancel_right _ _
        · change (f.comp g).1.component 2 = Germ.coordinate 2
          rw [component_comp_eq_pullback, hf 2]
          change g.pullbackRingHom (Germ.coordinate 2) = Germ.coordinate 2
          rw [pullback_coordinate, hg 2]
          rfl
      inverse_forward := by
        apply ext_components
        intro i
        fin_cases i
        · change (g.comp f).1.component 0 = Germ.coordinate 0
          rw [component_comp_eq_pullback, hg 0]
          change f.pullbackRingHom (Germ.coordinate 0) = Germ.coordinate 0
          rw [pullback_coordinate, hf 0]
          rfl
        · change (g.comp f).1.component 1 = Germ.coordinate 1
          rw [component_comp_eq_pullback, hg 1]
          change f.pullbackRingHom (Germ.coordinate 1 + v) = Germ.coordinate 1
          rw [map_add, pullback_coordinate, hf 1, hfpull]
          exact sub_add_cancel _ _
        · change (g.comp f).1.component 2 = Germ.coordinate 2
          rw [component_comp_eq_pullback, hg 2]
          change f.pullbackRingHom (Germ.coordinate 2) = Germ.coordinate 2
          rw [pullback_coordinate, hf 2]
          rfl }
  exact ⟨e, hf 0, hf 1, hf 2⟩

/-- Analytic second-coordinate subtraction fixes the other two components. -/
theorem exists_target_secondAnalyticSubtraction
    (g : PointedMapGerm 2 3) (q : Germ 1) (hq : q ∈ Germ.maximalIdeal 1) :
    ∃ g' : PointedMapGerm 2 3,
      g.RightLeftEquivalent g' ∧
      g'.1.component 0 = g.1.component 0 ∧
      g'.1.component 1 = g.1.component 1 - g.firstCoordinateTriple.pullbackRingHom q ∧
      g'.1.component 2 = g.1.component 2 := by
  obtain ⟨e, hzero, hone, htwo⟩ := exists_secondCoordinateAnalyticSubtraction q hq
  refine ⟨e.forward.comp g, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, comp_identity]
  · rw [component_comp_eq_pullback, hzero, pullback_coordinate]
  · rw [component_comp_eq_pullback, hone, map_sub, pullback_coordinate,
      firstCoordinateTriple, pullbackRingHom_comp]
    rfl
  · rw [component_comp_eq_pullback, htwo, pullback_coordinate]

end PointedMapGerm

namespace Germ

/-- The scalar analytic chain rule has a single term. -/
theorem partialDerivative_oneVariable_pullback {n : ℕ}
    (i : Fin n) (q : Germ 1) (f : PointedMapGerm n 1) :
    partialDerivative i (f.pullbackRingHom q) =
      f.pullbackRingHom (partialDerivative 0 q) * partialDerivative i (f.1.component 0) := by
  change partialDerivative i (compPointed q f) = _
  rw [partialDerivative_compPointed_sum]
  simp only [Fin.sum_univ_one]
  rfl

/-- Subtracting an analytic function of the first component preserves
exactly the common divisors of the three Jacobian minors. -/
theorem dvd_minors_secondAnalyticSubtraction_iff
    (f : PointedMapGerm 2 1) (Q H D : Germ 2) (q : Germ 1) :
    (D ∣ jacobian (f.1.component 0) (Q - f.pullbackRingHom q) ∧
      D ∣ jacobian (f.1.component 0) H ∧ D ∣ jacobian (Q - f.pullbackRingHom q) H) ↔
    (D ∣ jacobian (f.1.component 0) Q ∧
      D ∣ jacobian (f.1.component 0) H ∧ D ∣ jacobian Q H) := by
  have hfirst : jacobian (f.1.component 0) (Q - f.pullbackRingHom q) =
      jacobian (f.1.component 0) Q := by
    simp only [jacobian_eq, partialDerivative_sub, partialDerivative_oneVariable_pullback]
    ring
  have hthird : jacobian (Q - f.pullbackRingHom q) H =
      jacobian Q H - f.pullbackRingHom (partialDerivative 0 q) *
        jacobian (f.1.component 0) H := by
    simp only [jacobian_eq, partialDerivative_sub, partialDerivative_oneVariable_pullback]
    ring
  rw [hfirst, hthird]
  constructor
  · rintro ⟨hPQ, hPH, hQH⟩
    refine ⟨hPQ, hPH, ?_⟩
    have hsum := dvd_add hQH
      (dvd_mul_of_dvd_right hPH (f.pullbackRingHom (partialDerivative 0 q)))
    simpa only [sub_add_cancel] using hsum
  · rintro ⟨hPQ, hPH, hQH⟩
    exact ⟨hPQ, hPH, dvd_sub hQH (dvd_mul_of_dvd_right hPH _)⟩

end Germ

namespace PointedMapGerm

/-- The common-divisor equivalence for an analytic target shear of a triple. -/
theorem dvd_minors_of_secondAnalyticSubtraction_iff
    (g g' : PointedMapGerm 2 3) (q : Germ 1)
    (hzero : g'.1.component 0 = g.1.component 0)
    (hone : g'.1.component 1 = g.1.component 1 - g.firstCoordinateTriple.pullbackRingHom q)
    (htwo : g'.1.component 2 = g.1.component 2) (D : Germ 2) :
    (D ∣ Germ.jacobian (g'.1.component 0) (g'.1.component 1) ∧
      D ∣ Germ.jacobian (g'.1.component 0) (g'.1.component 2) ∧
      D ∣ Germ.jacobian (g'.1.component 1) (g'.1.component 2)) ↔
    (D ∣ Germ.jacobian (g.1.component 0) (g.1.component 1) ∧
      D ∣ Germ.jacobian (g.1.component 0) (g.1.component 2) ∧
      D ∣ Germ.jacobian (g.1.component 1) (g.1.component 2)) := by
  rw [hzero, hone, htwo]
  simpa only [firstCoordinateTriple_component] using
    Germ.dvd_minors_secondAnalyticSubtraction_iff g.firstCoordinateTriple
      (g.1.component 1) (g.1.component 2) D q

end PointedMapGerm

end OnLeConjecture.Analytic
