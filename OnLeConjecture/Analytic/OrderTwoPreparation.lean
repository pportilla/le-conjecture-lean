/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.EvenOuterConvergence
public import OnLeConjecture.Analytic.OrderOnePreparation
public import OnLeConjecture.PlaneCurve.ParametricMorse

/-!
# Analytic preparation in order two

This file proves analytic division by a quadratic normal form and uses the
parametric Morse lemma to prove Weierstrass preparation for plane analytic
germs of order two in the first coordinate.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Evaluation at the origin commutes with extension from the parameter
hyperplane. -/
theorem valueRingHom_hyperplaneExtension (r : Germ 1) :
    Germ.valueRingHom 2 (Germ.hyperplaneExtension 1 r) =
      Germ.valueRingHom 1 r := by
  exact PointedMapGerm.valueRingHom_pullback
    (Germ.hyperplaneTailGerm 1) r

/-- The differential of an extended parameter germ vanishes in the first
coordinate direction. -/
theorem differential_hyperplaneExtension_firstCoordinate (r : Germ 1) :
    Germ.differential (Germ.hyperplaneExtension 1 r)
      (Germ.firstCoordinateVector 1) = 0 := by
  change Germ.differential (Germ.hyperplaneExtension 1 r)
    (Germ.coordinateVector (0 : Fin 2)) = 0
  rw [← Germ.valueRingHom_partialDerivative,
    Germ.partialDerivative_zero_hyperplaneExtension]
  exact map_zero (Germ.valueRingHom 2)

/-- Differentiating the canonical first coordinate division formula. -/
theorem partialDerivative_firstCoordinate_decomposition (f : Germ 2) :
    Germ.partialDerivative (0 : Fin 2) f =
      Germ.firstCoordinateTail f +
        Germ.coordinate (0 : Fin 2) *
          Germ.partialDerivative (0 : Fin 2)
            (Germ.firstCoordinateTail f) := by
  have h := congrArg (Germ.partialDerivative (0 : Fin 2))
    (Germ.firstCoordinate_decomposition f)
  rw [Germ.partialDerivative_add, Germ.partialDerivative_mul,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_zero_hyperplaneExtension] at h
  simpa using h

/-- The first derivative at the origin is the value of the first analytic
Hadamard quotient. -/
theorem value_partialDerivative_firstCoordinate (f : Germ 2) :
    Germ.valueRingHom 2 (Germ.partialDerivative (0 : Fin 2) f) =
      Germ.valueRingHom 2 (Germ.firstCoordinateTail f) := by
  rw [Germ.partialDerivative_firstCoordinate_decomposition]
  simp

/-- The second derivative at the origin is twice the value of the second
analytic Hadamard quotient. -/
theorem value_secondPartialDerivative_firstCoordinate (f : Germ 2) :
    Germ.valueRingHom 2
        (Germ.partialDerivative (0 : Fin 2)
          (Germ.partialDerivative (0 : Fin 2) f)) =
      2 * Germ.valueRingHom 2
        (Germ.firstCoordinateTailIterate 2 f) := by
  have h := congrArg (Germ.partialDerivative (0 : Fin 2))
    (Germ.partialDerivative_firstCoordinate_decomposition f)
  rw [Germ.partialDerivative_add, Germ.partialDerivative_mul,
    Germ.partialDerivative_coordinate_same] at h
  have hvalue := congrArg (Germ.valueRingHom 2) h
  simp only [map_add, map_mul,
    Germ.valueRingHom_coordinate, zero_mul, one_mul, add_zero] at hvalue
  rw [hvalue, Germ.value_partialDerivative_firstCoordinate]
  change Germ.valueRingHom 2
      (Germ.firstCoordinateTail (Germ.firstCoordinateTail f)) +
      Germ.valueRingHom 2
        (Germ.firstCoordinateTail (Germ.firstCoordinateTail f)) =
    2 * Germ.valueRingHom 2
      (Germ.firstCoordinateTailIterate 2 f)
  rw [show Germ.firstCoordinateTailIterate 2 f =
      Germ.firstCoordinateTail (Germ.firstCoordinateTail f) by
    simp [Germ.firstCoordinateTailIterate_succ]]
  ring

/-- Division by a first coordinate translated by a parameter germ. -/
theorem exists_add_parameter_division
    (h : Germ 1) (hh : h ∈ Germ.maximalIdeal 1) (a : Germ 2) :
    ∃ q : Germ 2, ∃ r : Germ 1,
      a = (Germ.coordinate (0 : Fin 2) +
          Germ.hyperplaneExtension 1 h) * q +
        Germ.hyperplaneExtension 1 r := by
  let t : Germ 2 := Germ.coordinate (0 : Fin 2) +
    Germ.hyperplaneExtension 1 h
  have htMaximal : t ∈ Germ.maximalIdeal 2 := by
    apply (Germ.maximalIdeal 2).add_mem
    · exact Germ.coordinate_mem_maximalIdeal _
    · exact (Germ.hyperplaneTailGerm 1).pullback_mem_maximalIdeal hh
  have htDerivative :
      Germ.differential t (Germ.firstCoordinateVector 1) ≠ 0 := by
    rw [Germ.differential_add]
    change Germ.differential (Germ.coordinate (0 : Fin 2))
        (Germ.firstCoordinateVector 1) +
      Germ.differential (Germ.hyperplaneExtension 1 h)
        (Germ.firstCoordinateVector 1) ≠ 0
    rw [Germ.differential_coordinate_apply,
      Germ.differential_hyperplaneExtension_firstCoordinate, add_zero]
    simp [Germ.firstCoordinateVector]
  obtain ⟨e, heCoordinate, heExtension⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      t htMaximal htDerivative
  let b : Germ 2 := e.pullbackAlgEquiv.symm a
  let q : Germ 2 := e.pullbackAlgEquiv (Germ.firstCoordinateTail b)
  let r : Germ 1 := Germ.firstCoordinateCoefficient b
  refine ⟨q, r, ?_⟩
  have hdecomposition := Germ.firstCoordinate_decomposition b
  calc
    a = e.pullbackAlgEquiv b := by
      exact (e.pullbackAlgEquiv.apply_symm_apply a).symm
    _ = e.pullbackAlgEquiv
        (Germ.coordinate (0 : Fin 2) * Germ.firstCoordinateTail b +
          Germ.hyperplaneExtension 1 r) := by
      exact congrArg e.pullbackAlgEquiv hdecomposition
    _ = t * q + Germ.hyperplaneExtension 1 r := by
      rw [map_add, map_mul, heCoordinate, heExtension]

/-- Analytic division by `x² + h(y)` with a remainder of degree at most one
in `x`. -/
theorem exists_quadraticNormalForm_division
    (h : Germ 1) (hh : h ∈ Germ.maximalIdeal 1) (a : Germ 2) :
    ∃ q : Germ 2, ∃ r₀ r₁ : Germ 1,
      a = (Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.hyperplaneExtension 1 h) * q +
          Germ.hyperplaneExtension 1 r₀ +
          Germ.coordinate (0 : Fin 2) * Germ.hyperplaneExtension 1 r₁ := by
  obtain ⟨A, B, hAB⟩ :=
    Germ.exists_quadratic_decomposition_of_invariantDescent
      Germ.quadraticInvariantDescent_of_convergent_compression a
  obtain ⟨Aq, r₀, hA⟩ := Germ.exists_add_parameter_division h hh A
  obtain ⟨Bq, r₁, hB⟩ := Germ.exists_add_parameter_division h hh B
  let q : Germ 2 := Germ.quadraticSubstitutionAlgHom Aq +
    Germ.coordinate (0 : Fin 2) * Germ.quadraticSubstitutionAlgHom Bq
  refine ⟨q, r₀, r₁, ?_⟩
  have hsubstitution (c : Germ 1) :
      Germ.quadraticSubstitutionAlgHom (Germ.hyperplaneExtension 1 c) =
        Germ.hyperplaneExtension 1 c :=
    Germ.quadraticSubstitution_hyperplaneExtension c
  calc
    a = Germ.quadraticSubstitutionAlgHom A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticSubstitutionAlgHom B := hAB
    _ = Germ.quadraticSubstitutionAlgHom
          ((Germ.coordinate (0 : Fin 2) +
              Germ.hyperplaneExtension 1 h) * Aq +
            Germ.hyperplaneExtension 1 r₀) +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticSubstitutionAlgHom
            ((Germ.coordinate (0 : Fin 2) +
                Germ.hyperplaneExtension 1 h) * Bq +
              Germ.hyperplaneExtension 1 r₁) := by rw [hA, hB]
    _ = (Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.hyperplaneExtension 1 h) * q +
          Germ.hyperplaneExtension 1 r₀ +
          Germ.coordinate (0 : Fin 2) *
            Germ.hyperplaneExtension 1 r₁ := by
      simp only [map_add, map_mul,
        Germ.quadraticSubstitutionAlgHom_coordinate_zero, hsubstitution]
      ring

/-- A coordinate germ transverse to the parameter direction satisfies a
monic quadratic equation modulo `x² + h(y)`. The quotient in that equation
is a unit. -/
theorem exists_quadratic_annihilator
    (h : Germ 1) (hh : h ∈ Germ.maximalIdeal 1)
    (a : Germ 2) (haMaximal : a ∈ Germ.maximalIdeal 2)
    (haDerivative : Germ.differential a
      (Germ.firstCoordinateVector 1) ≠ 0) :
    ∃ p : Polynomial (Germ 1), ∃ w : Germ 2,
      p.Monic ∧ p.natDegree = 2 ∧
        (∀ k, k < 2 → p.coeff k ∈ Germ.maximalIdeal 1) ∧
        IsUnit w ∧
        Polynomial.eval₂ (Germ.hyperplaneExtension 1) a p =
          (Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.hyperplaneExtension 1 h) * w := by
  obtain ⟨q, r₀, r₁, ha⟩ :=
    Germ.exists_quadraticNormalForm_division h hh a
  let x : Germ 2 := Germ.coordinate (0 : Fin 2)
  let H : Germ 2 := Germ.hyperplaneExtension 1 h
  let A : Germ 2 := Germ.hyperplaneExtension 1 r₀
  let B : Germ 2 := Germ.hyperplaneExtension 1 r₁
  let g : Germ 2 := x ^ 2 + H
  have hgValue : Germ.valueRingHom 2 g = 0 := by
    simp [g, x, H, Germ.valueRingHom_hyperplaneExtension,
      Germ.mem_maximalIdeal_iff.mp hh]
  have hgDerivative : Germ.differential g
      (Germ.firstCoordinateVector 1) = 0 := by
    rw [show g = x * x + H by simp [g, pow_two]]
    rw [Germ.differential_add, Germ.differential_mul]
    simp [x, H, Germ.valueRingHom_coordinate,
      Germ.differential_hyperplaneExtension_firstCoordinate]
  have hAValue : Germ.valueRingHom 2 A = Germ.valueRingHom 1 r₀ := by
    exact Germ.valueRingHom_hyperplaneExtension r₀
  have hBValue : Germ.valueRingHom 2 B = Germ.valueRingHom 1 r₁ := by
    exact Germ.valueRingHom_hyperplaneExtension r₁
  have hAFirstDerivative : Germ.differential A
      (Germ.firstCoordinateVector 1) = 0 := by
    exact Germ.differential_hyperplaneExtension_firstCoordinate r₀
  have hBFirstDerivative : Germ.differential B
      (Germ.firstCoordinateVector 1) = 0 := by
    exact Germ.differential_hyperplaneExtension_firstCoordinate r₁
  have ha' : a = g * q + A + x * B := by
    simpa only [g, x, H, A, B] using ha
  have hr₀Value : Germ.valueRingHom 1 r₀ = 0 := by
    have hvalue := congrArg (Germ.valueRingHom 2) ha'
    rw [map_add, map_add, map_mul, map_mul, hgValue,
      Germ.valueRingHom_coordinate, zero_mul, zero_mul, add_zero,
      zero_add, hAValue] at hvalue
    rw [Germ.mem_maximalIdeal_iff] at haMaximal
    exact hvalue.symm.trans haMaximal
  have hr₀Maximal : r₀ ∈ Germ.maximalIdeal 1 := by
    exact Germ.mem_maximalIdeal_iff.mpr hr₀Value
  have haDerivativeValue :
      Germ.differential a (Germ.firstCoordinateVector 1) =
        Germ.valueRingHom 1 r₁ := by
    have hdifferential := congrArg Germ.differential ha'
    have happly := congrArg
      (fun L : Source 2 →L[ℂ] ℂ ↦ L (Germ.firstCoordinateVector 1))
      hdifferential
    rw [Germ.differential_add, Germ.differential_add,
      Germ.differential_mul, Germ.differential_mul] at happly
    simp only [add_apply, smul_apply] at happly
    rw [hgValue, hgDerivative, hAFirstDerivative,
      Germ.valueRingHom_coordinate,
      Germ.differential_coordinate_apply, hBFirstDerivative,
      hBValue] at happly
    simpa [x] using happly
  have hr₁Value : Germ.valueRingHom 1 r₁ ≠ 0 := by
    rw [← haDerivativeValue]
    exact haDerivative
  let w : Germ 2 := B ^ 2 + q * (2 * x * B + g * q)
  have hwValue : Germ.valueRingHom 2 w =
      Germ.valueRingHom 1 r₁ ^ 2 := by
    simp [w, hgValue, x, hBValue]
  have hwUnit : IsUnit w := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    rw [hwValue]
    exact pow_ne_zero 2 hr₁Value
  let p : Polynomial (Germ 1) :=
    Polynomial.monomial 2 1 + Polynomial.monomial 1 (-(2 * r₀)) +
      Polynomial.monomial 0 (r₀ ^ 2 + h * r₁ ^ 2)
  have hpDegreeLe : p.natDegree ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    simp [show 2 ≠ k by omega, show 1 ≠ k by omega,
      show 0 ≠ k by omega]
  have hpCoeffTwo : p.coeff 2 = 1 := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpDegree : p.natDegree = 2 := by
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hpDegreeLe
      (by rw [hpCoeffTwo]
          exact one_ne_zero)
  have hpMonic : p.Monic := by
    change p.coeff p.natDegree = 1
    rw [hpDegree, hpCoeffTwo]
  have hpCoeffZero : p.coeff 0 = r₀ ^ 2 + h * r₁ ^ 2 := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpCoeffOne : p.coeff 1 = -(2 * r₀) := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpMaximal : ∀ k, k < 2 →
      p.coeff k ∈ Germ.maximalIdeal 1 := by
    intro k hk
    interval_cases k
    · rw [hpCoeffZero]
      exact (Germ.maximalIdeal 1).add_mem
        (by simpa [pow_two] using
          (Germ.maximalIdeal 1).mul_mem_left r₀ hr₀Maximal)
        (Ideal.mul_mem_right (r₁ ^ 2) (Germ.maximalIdeal 1) hh)
    · rw [hpCoeffOne]
      exact (Germ.maximalIdeal 1).neg_mem
        ((Germ.maximalIdeal 1).mul_mem_left 2 hr₀Maximal)
  refine ⟨p, w, hpMonic, hpDegree, hpMaximal, hwUnit, ?_⟩
  dsimp only [p]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add,
    Polynomial.eval₂_monomial, Polynomial.eval₂_monomial,
    Polynomial.eval₂_monomial]
  simp only [map_one, map_neg, map_mul, map_add, map_pow, one_mul,
    pow_zero, mul_one, map_ofNat]
  simp only [w, g, x, H, A, B] at ha' ⊢
  rw [ha']
  ring

/-- Analytic Weierstrass preparation holds for every plane germ of order two
in the first coordinate. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_two
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 2) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f 2 := by
  have hcoefficients :=
    Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular
  have hfValue : Germ.valueRingHom 2 f = 0 := by
    have hzero := hcoefficients.2 0 (by omega)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hzero
    simpa using hzero
  have hfMaximal : f ∈ Germ.maximalIdeal 2 := by
    exact Germ.mem_maximalIdeal_iff.mpr hfValue
  have hfirst : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2) f) = 0 := by
    rw [Germ.value_partialDerivative_firstCoordinate]
    have hone := hcoefficients.2 1 (by omega)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hone
    simpa [Germ.firstCoordinateTailIterate_succ] using hone
  have hsecond : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.partialDerivative (0 : Fin 2) f)) ≠ 0 := by
    rw [Germ.value_secondPartialDerivative_firstCoordinate]
    have htwo := hcoefficients.1
    rw [Germ.value_firstCoordinateTaylorCoefficient] at htwo
    exact mul_ne_zero (by norm_num) htwo
  obtain ⟨e, h, heNormal, heExtension, heParameter, hh⟩ :=
    OnLeConjecture.PlaneCurve.exists_parametric_morse_normal_form
      f hfMaximal hfirst hsecond
  let a : Germ 2 :=
    e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2))
  have haMaximal : a ∈ Germ.maximalIdeal 2 := by
    change e.forward.pullbackRingHom
      (Germ.coordinate (0 : Fin 2)) ∈ Germ.maximalIdeal 2
    exact e.forward.pullback_mem_maximalIdeal
      (Germ.coordinate_mem_maximalIdeal (0 : Fin 2))
  have haComponent : e.forward.1.component (0 : Fin 2) = a := by
    exact (e.forward.pullback_coordinate (0 : Fin 2)).symm
  have hJacobian : Germ.coordinateJacobian e.forward =
      Germ.partialDerivative (0 : Fin 2) a := by
    rw [Germ.coordinateJacobian_eq, haComponent, heParameter,
      Germ.partialDerivative_coordinate_same,
      Germ.partialDerivative_coordinate_ne (by decide)]
    ring
  have haPartialUnit : IsUnit
      (Germ.partialDerivative (0 : Fin 2) a) := by
    rw [← hJacobian]
    exact Germ.PointedEquivGerm.coordinateJacobian_isUnit e
  have haDerivative : Germ.differential a
      (Germ.firstCoordinateVector 1) ≠ 0 := by
    change Germ.differential a
      (Germ.coordinateVector (0 : Fin 2)) ≠ 0
    rw [← Germ.valueRingHom_partialDerivative]
    exact Germ.valueRingHom_ne_zero_of_isUnit haPartialUnit
  obtain ⟨p, w, hpMonic, hpDegree, hpMaximal, hwUnit, hfactor⟩ :=
    Germ.exists_quadratic_annihilator h hh a haMaximal haDerivative
  have hpullEvaluation :
      e.pullbackAlgEquiv (Germ.firstCoordinatePolynomialEvaluation p) =
        Polynomial.eval₂ (Germ.hyperplaneExtension 1) a p := by
    have hcoefficientMap :
        e.pullbackAlgEquiv.toRingEquiv.toRingHom.comp
          (Germ.hyperplaneExtension 1) =
        Germ.hyperplaneExtension 1 := by
      apply RingHom.ext
      intro r
      exact heExtension r
    rw [Germ.firstCoordinatePolynomialEvaluation]
    calc
      e.pullbackAlgEquiv
          (Polynomial.eval₂ (Germ.hyperplaneExtension 1)
            (Germ.coordinate (0 : Fin 2)) p) =
          Polynomial.eval₂
            (e.pullbackAlgEquiv.toRingEquiv.toRingHom.comp
              (Germ.hyperplaneExtension 1))
            (e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2))) p :=
        Polynomial.hom_eval₂ p (Germ.hyperplaneExtension 1)
          e.pullbackAlgEquiv.toRingEquiv.toRingHom
          (Germ.coordinate (0 : Fin 2))
      _ = Polynomial.eval₂ (Germ.hyperplaneExtension 1) a p := by
        rw [hcoefficientMap]
  have hpullFactor :
      e.pullbackAlgEquiv (Germ.firstCoordinatePolynomialEvaluation p) =
        e.pullbackAlgEquiv f * w := by
    rw [hpullEvaluation, heNormal]
    exact hfactor
  let v : Germ 2 := e.pullbackAlgEquiv.symm w
  have hvUnit : IsUnit v := by
    exact hwUnit.map e.pullbackAlgEquiv.symm
  have hback : Germ.firstCoordinatePolynomialEvaluation p = f * v := by
    calc
      Germ.firstCoordinatePolynomialEvaluation p =
          e.pullbackAlgEquiv.symm
            (e.pullbackAlgEquiv
              (Germ.firstCoordinatePolynomialEvaluation p)) := by
        exact (e.pullbackAlgEquiv.symm_apply_apply
          (Germ.firstCoordinatePolynomialEvaluation p)).symm
      _ = e.pullbackAlgEquiv.symm
          (e.pullbackAlgEquiv f * w) := by rw [hpullFactor]
      _ = f * v := by
        rw [map_mul, e.pullbackAlgEquiv.symm_apply_apply]
  let u : Germ 2 := (↑(hvUnit.unit⁻¹) : Germ 2)
  have huUnit : IsUnit u := Units.isUnit hvUnit.unit⁻¹
  have hvInverse : v * u = 1 := by
    calc
      v * u = (↑hvUnit.unit : Germ 2) *
          (↑(hvUnit.unit⁻¹) : Germ 2) := by
        rw [hvUnit.unit_spec]
      _ = 1 := Units.mul_inv hvUnit.unit
  refine ⟨p, u, hpMonic, hpDegree, hpMaximal, huUnit, ?_⟩
  calc
    f = f * (v * u) := by rw [hvInverse, mul_one]
    _ = (f * v) * u := by rw [mul_assoc]
    _ = Germ.firstCoordinatePolynomialEvaluation p * u := by rw [hback]

/-- The completed image closure condition holds in order two. -/
theorem completedWeierstrassImageClosureAtOrder_two :
    Germ.CompletedWeierstrassImageClosureAtOrder 2 :=
  (Germ.completedWeierstrassImageClosureAtOrder_iff 2).2
    fun _f hregular ↦
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_two hregular

end Germ

end OnLeConjecture.Analytic
