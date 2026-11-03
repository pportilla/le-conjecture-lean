/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism
public import OnLeConjecture.Analytic.MonicTriangularFinite
public import OnLeConjecture.Analytic.RamifiedPreparedPairTransport

/-!
# Polynomial subtraction from the second target coordinate

The shear `(z₀,z₁,z₂) ↦ (z₀,z₁-p(z₀),z₂)` has an explicit analytic
inverse. The coordinate identities and preservation of common divisors
of all three independent Jacobian minors are proved below.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- A polynomial with zero constant term can be subtracted from the
second target coordinate by an invertible pointed analytic germ. -/
theorem exists_secondCoordinatePolynomialSubtraction
    (p : _root_.Polynomial ℂ) (hp : p.coeff 0 = 0) :
    ∃ e : PointedEquivGerm 3,
      e.forward.1.component 0 = Germ.coordinate 0 ∧
      e.forward.1.component 1 =
        Germ.coordinate 1 - _root_.Polynomial.aeval (Germ.coordinate 0) p ∧
      e.forward.1.component 2 = Germ.coordinate 2 := by
  let v : Germ 3 := _root_.Polynomial.aeval (Germ.coordinate 0) p
  have hv : v ∈ Germ.maximalIdeal 3 := by
    obtain ⟨q, hq⟩ := _root_.Polynomial.X_dvd_iff.mpr hp
    dsimp [v]
    rw [hq, map_mul, _root_.Polynomial.aeval_X]
    exact (Germ.maximalIdeal 3).mul_mem_right _ (Germ.coordinate_mem_maximalIdeal 0)
  obtain ⟨f, hf⟩ := exists_with_components
    (![Germ.coordinate 0, Germ.coordinate 1 - v, Germ.coordinate 2] : Fin 3 → Germ 3)
    (by
      intro index
      fin_cases index
      · exact Germ.coordinate_mem_maximalIdeal 0
      · exact (Germ.maximalIdeal 3).sub_mem (Germ.coordinate_mem_maximalIdeal 1) hv
      · exact Germ.coordinate_mem_maximalIdeal 2)
  obtain ⟨g, hg⟩ := exists_with_components
    (![Germ.coordinate 0, Germ.coordinate 1 + v, Germ.coordinate 2] : Fin 3 → Germ 3)
    (by
      intro index
      fin_cases index
      · exact Germ.coordinate_mem_maximalIdeal 0
      · exact (Germ.maximalIdeal 3).add_mem (Germ.coordinate_mem_maximalIdeal 1) hv
      · exact Germ.coordinate_mem_maximalIdeal 2)
  have hfpull : f.pullbackRingHom v = v := by
    rw [Germ.pointed_pullback_polynomial_aeval, pullback_coordinate, hf 0]
    rfl
  have hgpull : g.pullbackRingHom v = v := by
    rw [Germ.pointed_pullback_polynomial_aeval, pullback_coordinate, hg 0]
    rfl
  let e : PointedEquivGerm 3 :=
    { forward := f
      inverse := g
      forward_inverse := by
        apply ext_components
        intro index
        fin_cases index
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
        intro index
        fin_cases index
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

/-- The second-coordinate shear replaces precisely the requested scalar
component and is a right-left equivalence of the original germ. -/
theorem exists_target_secondPolynomialSubtraction
    (g : PointedMapGerm 2 3) (p : _root_.Polynomial ℂ) (hp : p.coeff 0 = 0) :
    ∃ g' : PointedMapGerm 2 3,
      g.RightLeftEquivalent g' ∧
      g'.1.component 0 = g.1.component 0 ∧
      g'.1.component 1 = g.1.component 1 - _root_.Polynomial.aeval (g.1.component 0) p ∧
      g'.1.component 2 = g.1.component 2 := by
  obtain ⟨e, hzero, hone, htwo⟩ := exists_secondCoordinatePolynomialSubtraction p hp
  refine ⟨e.forward.comp g, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, comp_identity]
  · rw [component_comp_eq_pullback, hzero, pullback_coordinate]
  · rw [component_comp_eq_pullback, hone, map_sub, pullback_coordinate,
      Germ.pointed_pullback_polynomial_aeval, pullback_coordinate]
  · rw [component_comp_eq_pullback, htwo, pullback_coordinate]

end PointedMapGerm

namespace Germ

/-- The polynomial chain rule for partial derivatives of analytic germs. -/
theorem partialDerivative_polynomial_aeval
    {n : ℕ} (i : Fin n) (f : Germ n) (p : _root_.Polynomial ℂ) :
    partialDerivative i (_root_.Polynomial.aeval f p) =
      _root_.Polynomial.aeval f p.derivative * partialDerivative i f := by
  simpa only [partialDerivation_apply, smul_eq_mul] using (partialDerivation i).map_aeval p f

/-- The minor of the first and second components is unchanged. -/
theorem jacobian_secondPolynomialSubtraction_first
    (P Q : Germ 2) (p : _root_.Polynomial ℂ) :
    jacobian P (Q - _root_.Polynomial.aeval P p) = jacobian P Q := by
  simp only [jacobian_eq, partialDerivative_sub, partialDerivative_polynomial_aeval]
  ring

/-- The remaining changed minor differs by a multiple of the first-third minor. -/
theorem jacobian_secondPolynomialSubtraction_third
    (P Q H : Germ 2) (p : _root_.Polynomial ℂ) :
    jacobian (Q - _root_.Polynomial.aeval P p) H =
      jacobian Q H - _root_.Polynomial.aeval P p.derivative * jacobian P H := by
  simp only [jacobian_eq, partialDerivative_sub, partialDerivative_polynomial_aeval]
  ring

/-- Common divisors of all three independent Jacobian minors are preserved
in both directions by the second-coordinate polynomial shear. -/
theorem dvd_minors_secondPolynomialSubtraction_iff
    (P Q H D : Germ 2) (p : _root_.Polynomial ℂ) :
    (D ∣ jacobian P (Q - _root_.Polynomial.aeval P p) ∧
      D ∣ jacobian P H ∧ D ∣ jacobian (Q - _root_.Polynomial.aeval P p) H) ↔
    (D ∣ jacobian P Q ∧ D ∣ jacobian P H ∧ D ∣ jacobian Q H) := by
  rw [jacobian_secondPolynomialSubtraction_first, jacobian_secondPolynomialSubtraction_third]
  constructor
  · rintro ⟨hPQ, hPH, hQH⟩
    refine ⟨hPQ, hPH, ?_⟩
    have hsum := dvd_add hQH (dvd_mul_of_dvd_right hPH (_root_.Polynomial.aeval P p.derivative))
    simpa only [sub_add_cancel] using hsum
  · rintro ⟨hPQ, hPH, hQH⟩
    exact ⟨hPQ, hPH, dvd_sub hQH (dvd_mul_of_dvd_right hPH _)⟩

end Germ

namespace PointedMapGerm

/-- The transformed analytic map has exactly the same common minor divisors. -/
theorem dvd_minors_of_secondPolynomialSubtraction_iff
    (g g' : PointedMapGerm 2 3) (p : _root_.Polynomial ℂ)
    (hzero : g'.1.component 0 = g.1.component 0)
    (hone : g'.1.component 1 = g.1.component 1 - _root_.Polynomial.aeval (g.1.component 0) p)
    (htwo : g'.1.component 2 = g.1.component 2) (D : Germ 2) :
    (D ∣ Germ.jacobian (g'.1.component 0) (g'.1.component 1) ∧
      D ∣ Germ.jacobian (g'.1.component 0) (g'.1.component 2) ∧
      D ∣ Germ.jacobian (g'.1.component 1) (g'.1.component 2)) ↔
    (D ∣ Germ.jacobian (g.1.component 0) (g.1.component 1) ∧
      D ∣ Germ.jacobian (g.1.component 0) (g.1.component 2) ∧
      D ∣ Germ.jacobian (g.1.component 1) (g.1.component 2)) := by
  rw [hzero, hone, htwo]
  exact Germ.dvd_minors_secondPolynomialSubtraction_iff _ _ _ _ p

end PointedMapGerm

end OnLeConjecture.Analytic
