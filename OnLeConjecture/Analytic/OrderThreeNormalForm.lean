/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CubicResidueConvergence

/-!
# Analytic preparation for a cubic normal form

This file constructs the characteristic polynomial of a transverse analytic
coordinate modulo `x³ + h(y)`. The cubic division theorem shows that the
resulting annihilating relation has an analytic quotient. The quotient is a
unit when the coordinate is transverse to the parameter hyperplane.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

private theorem cubic_annihilator_identity {R : Type*} [CommRing R]
    (a q x h A B C : R)
    (ha : a = (x ^ 3 + h) * q + A + x * B + x ^ 2 * C) :
    a ^ 3 - 3 * A * a ^ 2 + (3 * A ^ 2 + 3 * B * C * h) * a +
        (-A ^ 3 - 3 * A * B * C * h + B ^ 3 * h - C ^ 3 * h ^ 2) =
      (x ^ 3 + h) *
        (q * (a ^ 2 + a * (A + x * B + x ^ 2 * C) +
            (A + x * B + x ^ 2 * C) ^ 2 -
            3 * A * (a + (A + x * B + x ^ 2 * C)) +
            (3 * A ^ 2 + 3 * B * C * h)) +
          B ^ 3 + 3 * B ^ 2 * C * x + 3 * B * C ^ 2 * x ^ 2 -
            C ^ 3 * h + C ^ 3 * x ^ 3) := by
  rw [ha]
  ring

/-- A coordinate germ transverse to the parameter direction satisfies a
monic cubic equation modulo `x³ + h(y)`. The quotient is a unit. -/
theorem exists_cubic_annihilator
    (h : Germ 1) (hh : h ∈ Germ.maximalIdeal 1)
    (a : Germ 2) (haMaximal : a ∈ Germ.maximalIdeal 2)
    (haDerivative : Germ.differential a
      (Germ.firstCoordinateVector 1) ≠ 0) :
    ∃ p : Polynomial (Germ 1), ∃ w : Germ 2,
      p.Monic ∧ p.natDegree = 3 ∧
        (∀ k, k < 3 → p.coeff k ∈ Germ.maximalIdeal 1) ∧
        IsUnit w ∧
        Polynomial.eval₂ (Germ.hyperplaneExtension 1) a p =
          (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.hyperplaneExtension 1 h) * w := by
  obtain ⟨q, r₀, r₁, r₂, ha⟩ :=
    Germ.exists_cubicNormalForm_division h hh a
  let x : Germ 2 := Germ.coordinate (0 : Fin 2)
  let H : Germ 2 := Germ.hyperplaneExtension 1 h
  let A : Germ 2 := Germ.hyperplaneExtension 1 r₀
  let B : Germ 2 := Germ.hyperplaneExtension 1 r₁
  let C : Germ 2 := Germ.hyperplaneExtension 1 r₂
  let g : Germ 2 := x ^ 3 + H
  let v : Germ 2 := A + x * B + x ^ 2 * C
  have hHValue : Germ.valueRingHom 2 H = 0 := by
    simp [H, Germ.valueRingHom_hyperplaneExtension,
      Germ.mem_maximalIdeal_iff.mp hh]
  have hxValue : Germ.valueRingHom 2 x = 0 := by
    simp [x]
  have hgValue : Germ.valueRingHom 2 g = 0 := by
    simp [g, hxValue, hHValue]
  have hgDerivative : Germ.differential g
      (Germ.firstCoordinateVector 1) = 0 := by
    rw [show g = (x * x) * x + H by simp [g, pow_succ]]
    rw [Germ.differential_add, Germ.differential_mul,
      Germ.differential_mul]
    simp [x, H, Germ.valueRingHom_coordinate,
      Germ.differential_hyperplaneExtension_firstCoordinate]
  have hAValue : Germ.valueRingHom 2 A = Germ.valueRingHom 1 r₀ :=
    Germ.valueRingHom_hyperplaneExtension r₀
  have hBValue : Germ.valueRingHom 2 B = Germ.valueRingHom 1 r₁ :=
    Germ.valueRingHom_hyperplaneExtension r₁
  have hAFirstDerivative : Germ.differential A
      (Germ.firstCoordinateVector 1) = 0 :=
    Germ.differential_hyperplaneExtension_firstCoordinate r₀
  have hBFirstDerivative : Germ.differential B
      (Germ.firstCoordinateVector 1) = 0 :=
    Germ.differential_hyperplaneExtension_firstCoordinate r₁
  have hCFirstDerivative : Germ.differential C
      (Germ.firstCoordinateVector 1) = 0 :=
    Germ.differential_hyperplaneExtension_firstCoordinate r₂
  have ha' : a = g * q + A + x * B + x ^ 2 * C := by
    simpa only [g, x, H, A, B, C] using ha
  have haValue : Germ.valueRingHom 2 a = 0 :=
    Germ.mem_maximalIdeal_iff.mp haMaximal
  have hr₀Value : Germ.valueRingHom 1 r₀ = 0 := by
    have hvalue := congrArg (Germ.valueRingHom 2) ha'
    rw [map_add, map_add, map_add, map_mul, map_mul, map_mul,
      map_pow, hgValue, hxValue] at hvalue
    norm_num at hvalue
    rw [hAValue] at hvalue
    exact hvalue.symm.trans haValue
  have hr₀Maximal : r₀ ∈ Germ.maximalIdeal 1 :=
    Germ.mem_maximalIdeal_iff.mpr hr₀Value
  have haDerivativeValue :
      Germ.differential a (Germ.firstCoordinateVector 1) =
        Germ.valueRingHom 1 r₁ := by
    have haExpanded : a = g * q + A + x * B + (x * x) * C := by
      simpa only [pow_two] using ha'
    have hdifferential := congrArg Germ.differential haExpanded
    have happly := congrArg
      (fun L : Source 2 →L[ℂ] ℂ ↦ L (Germ.firstCoordinateVector 1))
      hdifferential
    rw [Germ.differential_add, Germ.differential_add,
      Germ.differential_add, Germ.differential_mul,
      Germ.differential_mul, Germ.differential_mul,
      Germ.differential_mul] at happly
    simp only [add_apply, smul_apply] at happly
    rw [hgValue, hgDerivative, hAFirstDerivative, hxValue,
      Germ.differential_coordinate_apply, hBFirstDerivative,
      hCFirstDerivative, hBValue] at happly
    simpa [x] using happly
  have hr₁Value : Germ.valueRingHom 1 r₁ ≠ 0 := by
    rw [← haDerivativeValue]
    exact haDerivative
  let w : Germ 2 :=
    q * (a ^ 2 + a * v + v ^ 2 - 3 * A * (a + v) +
      (3 * A ^ 2 + 3 * B * C * H)) +
      B ^ 3 + 3 * B ^ 2 * C * x + 3 * B * C ^ 2 * x ^ 2 -
        C ^ 3 * H + C ^ 3 * x ^ 3
  have hvValue : Germ.valueRingHom 2 v = 0 := by
    simp [v, hxValue, hAValue, hr₀Value]
  have hwValue : Germ.valueRingHom 2 w =
      Germ.valueRingHom 1 r₁ ^ 3 := by
    simp [w, haValue, hvValue, hAValue, hr₀Value,
      hBValue, hHValue, hxValue]
  have hwUnit : IsUnit w := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    rw [hwValue]
    exact pow_ne_zero 3 hr₁Value
  let c₂ : Germ 1 := -(3 * r₀)
  let c₁ : Germ 1 := 3 * r₀ ^ 2 + 3 * r₁ * r₂ * h
  let c₀ : Germ 1 :=
    -r₀ ^ 3 - 3 * r₀ * r₁ * r₂ * h + r₁ ^ 3 * h -
      r₂ ^ 3 * h ^ 2
  let p : Polynomial (Germ 1) :=
    Polynomial.monomial 3 1 + Polynomial.monomial 2 c₂ +
      Polynomial.monomial 1 c₁ + Polynomial.monomial 0 c₀
  have hpDegreeLe : p.natDegree ≤ 3 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    simp [show 3 ≠ k by omega, show 2 ≠ k by omega,
      show 1 ≠ k by omega, show 0 ≠ k by omega]
  have hpCoeffThree : p.coeff 3 = 1 := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpDegree : p.natDegree = 3 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hpDegreeLe
      (by rw [hpCoeffThree]
          exact one_ne_zero)
  have hpMonic : p.Monic := by
    change p.coeff p.natDegree = 1
    rw [hpDegree, hpCoeffThree]
  have hpCoeffZero : p.coeff 0 = c₀ := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpCoeffOne : p.coeff 1 = c₁ := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpCoeffTwo : p.coeff 2 = c₂ := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    norm_num
  have hpMaximal : ∀ k, k < 3 →
      p.coeff k ∈ Germ.maximalIdeal 1 := by
    intro k hk
    rw [Germ.mem_maximalIdeal_iff]
    interval_cases k
    · rw [hpCoeffZero]
      simp [c₀, hr₀Value, Germ.mem_maximalIdeal_iff.mp hh]
    · rw [hpCoeffOne]
      simp [c₁, hr₀Value, Germ.mem_maximalIdeal_iff.mp hh]
    · rw [hpCoeffTwo]
      simp [c₂, hr₀Value]
  refine ⟨p, w, hpMonic, hpDegree, hpMaximal, hwUnit, ?_⟩
  dsimp only [p, c₂, c₁, c₀]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add,
    Polynomial.eval₂_add, Polynomial.eval₂_monomial,
    Polynomial.eval₂_monomial, Polynomial.eval₂_monomial,
    Polynomial.eval₂_monomial]
  simp only [map_one, map_neg, map_mul, map_add, map_sub, map_pow, one_mul,
    pow_zero, pow_one, mul_one, map_ofNat]
  simp only [w, v, g, x, H, A, B, C] at ha' ⊢
  convert cubic_annihilator_identity a q
      (Germ.coordinate (0 : Fin 2)) (Germ.hyperplaneExtension 1 h)
      (Germ.hyperplaneExtension 1 r₀) (Germ.hyperplaneExtension 1 r₁)
      (Germ.hyperplaneExtension 1 r₂) ha' using 1
  all_goals ring

/-- A parameter preserving cubic normal form gives analytic Weierstrass
preparation of order three. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_three_of_cubicNormalForm
    {f : Germ 2} (e : PointedEquivGerm 2) (h : Germ 1)
    (hh : h ∈ Germ.maximalIdeal 1)
    (heNormal : e.pullbackAlgEquiv f =
      Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.hyperplaneExtension 1 h)
    (heExtension : ∀ q : Germ 1,
      e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
        Germ.hyperplaneExtension 1 q)
    (heParameter : e.forward.1.component (1 : Fin 2) =
      Germ.coordinate (1 : Fin 2)) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f 3 := by
  let a : Germ 2 :=
    e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2))
  have haMaximal : a ∈ Germ.maximalIdeal 2 := by
    change e.forward.pullbackRingHom
      (Germ.coordinate (0 : Fin 2)) ∈ Germ.maximalIdeal 2
    exact e.forward.pullback_mem_maximalIdeal
      (Germ.coordinate_mem_maximalIdeal (0 : Fin 2))
  have haComponent : e.forward.1.component (0 : Fin 2) = a :=
    (e.forward.pullback_coordinate (0 : Fin 2)).symm
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
    Germ.exists_cubic_annihilator h hh a haMaximal haDerivative
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
  have hvUnit : IsUnit v :=
    hwUnit.map e.pullbackAlgEquiv.symm
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

end Germ

end OnLeConjecture.Analytic
